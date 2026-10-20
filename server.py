"""Захват Кудрово — онлайн-игра для Telegram (бот + мини-приложение + API).

Переменные окружения:
  BOT_TOKEN     — токен бота от @BotFather
  BASE_URL      — адрес сервиса, например https://kudrovogame.onrender.com
  DATABASE_URL  — строка подключения к Postgres (Supabase, Session pooler)
  ADMIN_IDS     — твой Telegram ID (узнать: написать боту /myid), можно несколько через запятую

Правила:
  * Игрок один раз выбирает территорию: основывает новую на свободной соте
    или вступает в уже существующую. Сменить нельзя.
  * Все игроки одной территории — команда: их тапы складываются в общую копилку.
    10 тапов — воин, 100 — пушка, 1000 — танк.
  * Любой участник может отправить общий резерв в защиту или в атаку на соседнюю соту.
  * Если атака сильнее защиты, сота переходит к команде атакующих,
    а её защитники переходят на сторону победителя.
  * Админ задаёт названия территорий и отключает то, что не входит в Кудрово.
"""
import asyncio
import hashlib
import hmac
import json
import math
import os
import random
import time
from urllib.parse import parse_qsl, urlsplit

import asyncpg
from aiogram import Bot, Dispatcher
from aiogram.filters import Command, CommandStart
from aiogram.types import (
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    MenuButtonWebApp,
    Message,
    WebAppInfo,
)
from aiogram.webhook.aiohttp_server import SimpleRequestHandler
from aiohttp import web

BOT_TOKEN = os.environ["BOT_TOKEN"]
BASE_URL = os.environ["BASE_URL"].rstrip("/")
DATABASE_URL = os.environ["DATABASE_URL"].strip()
ADMIN_IDS = {int(x) for x in os.getenv("ADMIN_IDS", "").replace(" ", "").split(",") if x}
PORT = int(os.getenv("PORT", "8080"))

WEBHOOK_PATH = "/tg/" + hashlib.sha256(BOT_TOKEN.encode()).hexdigest()[:24]
WEBHOOK_SECRET = hashlib.sha256(("secret:" + BOT_TOKEN).encode()).hexdigest()[:32]
HERE = os.path.dirname(os.path.abspath(__file__))

# ---------------------------------------------------------------- Карта
# Прямоугольник, который покрывает Кудрово. Лишнее обрезается по границе из OpenStreetMap.
BOUNDS = {"south": 59.893, "north": 59.918, "west": 30.488, "east": 30.548}
HEX_RADIUS_M = 230          # размер одной соты (радиус в метрах)
MAX_TAPS_PER_SEC = 15       # защита от автокликеров (на одного игрока)


def build_grid():
    lat0 = (BOUNDS["south"] + BOUNDS["north"]) / 2
    m_lat = 111_320.0
    m_lon = 111_320.0 * math.cos(math.radians(lat0))
    width = (BOUNDS["east"] - BOUNDS["west"]) * m_lon
    height = (BOUNDS["north"] - BOUNDS["south"]) * m_lat
    dx, dy = math.sqrt(3) * HEX_RADIUS_M, 1.5 * HEX_RADIUS_M
    cols, rows = math.ceil(width / dx) + 1, math.ceil(height / dy) + 1

    cells = []
    for r in range(rows):
        for c in range(cols):
            x = c * dx + (dx / 2 if r % 2 else 0)
            y = r * dy
            lat, lon = BOUNDS["south"] + y / m_lat, BOUNDS["west"] + x / m_lon
            poly = []
            for k in range(6):
                a = math.radians(60 * k - 30)
                poly.append([
                    round(lat + HEX_RADIUS_M * math.sin(a) / m_lat, 6),
                    round(lon + HEX_RADIUS_M * math.cos(a) / m_lon, 6),
                ])
            cells.append({"id": r * cols + c, "center": [round(lat, 6), round(lon, 6)], "poly": poly})

    def neighbors(i):
        c, r = i % cols, i // cols
        d = ([(-1, 0), (1, 0), (0, -1), (1, -1), (0, 1), (1, 1)] if r % 2
             else [(-1, 0), (1, 0), (-1, -1), (0, -1), (-1, 1), (0, 1)])
        return [(r + dr) * cols + (c + dc) for dc, dr in d
                if 0 <= c + dc < cols and 0 <= r + dr < rows]

    nbrs = [neighbors(i) for i in range(len(cells))]
    bounds = [[BOUNDS["south"] - 0.002, BOUNDS["west"] - 0.003],
              [BOUNDS["north"] + 0.003, BOUNDS["east"] + 0.006]]
    return {"bounds": bounds, "cells": cells, "neighbors": nbrs}


GRID = build_grid()
N_CELLS = len(GRID["cells"])
NEIGHBORS = GRID["neighbors"]
GRID_JSON = json.dumps(GRID, separators=(",", ":"))


def power(w, c, t):
    return w + c * 10 + t * 100


POINTS_PER_CELL = 100

# Цвета команд. Лидер может выбрать любой из них.
TEAM_COLORS = ["#e74c3c", "#3498db", "#2ecc71", "#9b59b6", "#f39c12", "#1abc9c",
               "#e84393", "#f1c40f", "#00cec9", "#6c5ce7", "#d35400", "#fd79a8",
               "#27ae60", "#0984e3", "#b33939", "#ffffff"]


# ---------------------------------------------------------------- База данных
# Команда (territory/faction) = все игроки, выбравшие одну территорию.
# id команды = номер соты, на которой её основали.
SCHEMA = """
create table if not exists meta (key text primary key, value text);
create table if not exists factions (
    id int primary key,
    taps bigint not null default 0,
    rw bigint not null default 0,
    rc bigint not null default 0,
    rt bigint not null default 0
);
create table if not exists players3 (
    id bigint primary key,
    name text not null,
    faction int,
    taps bigint not null default 0,
    last_tap double precision not null default 0
);
create table if not exists cells3 (
    id int primary key,
    name text,
    owner int references factions(id),
    disabled boolean not null default false,
    gw bigint not null default 0,
    gc bigint not null default 0,
    gt bigint not null default 0
);
"""


async def init_db(pool):
    async with pool.acquire() as con:
        await con.execute(SCHEMA)
        existing = {r["id"] for r in await con.fetch("select id from cells3")}
        old = {}
        try:  # переносим названия и вырезанные границы из прошлой версии
            old = {r["id"]: (r["name"], r["disabled"]) for r in await con.fetch(
                "select id, name, disabled from cells2")}
        except Exception:
            pass
        new = [(i, old.get(i, (None, False))[0], old.get(i, (None, False))[1], random.randint(5, 30))
               for i in range(N_CELLS) if i not in existing]
        if new:
            await con.executemany(
                "insert into cells3(id, name, disabled, gw) values($1, $2, $3, $4)", new)
        await con.execute("delete from cells3 where id >= $1", N_CELLS)
        # лидер и цвет команды
        await con.execute("alter table factions add column if not exists leader bigint")
        await con.execute("alter table factions add column if not exists color text")
        await con.execute("update factions f set leader=(select min(id) from players3 p where p.faction=f.id) "
                          "where leader is null")
        for r in await con.fetch("select id from factions where color is null order by id"):
            await con.execute("update factions set color=$2 where id=$1", r["id"], await free_color(con))


async def free_color(con):
    """Цвет, который сейчас реже всего используется командами."""
    used = [r["color"] for r in await con.fetch("select color from factions where color is not null")]
    return min(TEAM_COLORS[:-1], key=lambda c: (used.count(c), random.random()))


async def dissolve_if_empty(con, fid):
    """Если у команды не осталось сот — команда распадается, игроки выбирают заново.
    Возвращает id игроков распавшейся команды."""
    if fid is None:
        return []
    if await con.fetchval("select count(*) from cells3 where owner=$1", fid):
        return []
    members = [r["id"] for r in await con.fetch("select id from players3 where faction=$1", fid)]
    await con.execute("update players3 set faction=null where faction=$1", fid)
    await con.execute("delete from factions where id=$1", fid)
    return members


# ---------------------------------------------------------------- Граница Кудрово
OVERPASS_URLS = ["https://overpass-api.de/api/interpreter",
                 "https://overpass.kumi.systems/api/interpreter"]
OVERPASS_QUERY = ('[out:json][timeout:60];'
                  'relation["boundary"="administrative"]["name"="Кудрово"];out geom;')


async def fetch_kudrovo_boundary():
    """Скачивает границу Кудрово из OpenStreetMap: список отрезков [(lat1,lon1,lat2,lon2)]."""
    import aiohttp
    last = None
    for url in OVERPASS_URLS:
        try:
            async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=90)) as s:
                async with s.post(url, data={"data": OVERPASS_QUERY},
                                  headers={"User-Agent": "kudrovo-game/1.0"}) as r:
                    r.raise_for_status()
                    data = await r.json(content_type=None)
            rels = [e for e in data.get("elements", []) if e.get("type") == "relation"]
            if not rels:
                raise RuntimeError("граница Кудрово не найдена")
            rels.sort(key=lambda e: e.get("tags", {}).get("admin_level") != "8")
            segs = []
            for m in rels[0].get("members", []):
                if m.get("type") != "way" or m.get("role") not in ("outer", "inner", ""):
                    continue
                g = m.get("geometry") or []
                for a, b in zip(g, g[1:]):
                    segs.append((a["lat"], a["lon"], b["lat"], b["lon"]))
            if len(segs) < 3:
                raise RuntimeError("пустая граница")
            return segs
        except Exception as e:
            last = e
    raise RuntimeError(f"не удалось скачать границу: {last}")


def inside(lat, lon, segs):
    """Точка внутри границы? (правило чёт-нечет по всем отрезкам)"""
    res = False
    for y1, x1, y2, x2 in segs:
        if (y1 > lat) != (y2 > lat):
            if lon < x1 + (lat - y1) * (x2 - x1) / (y2 - y1):
                res = not res
    return res


async def trim_to_kudrovo(pool):
    """Отключает соты, центр которых вне границы Кудрово. Возвращает (в игре, отключено)."""
    segs = await fetch_kudrovo_boundary()
    lats = [s[0] for s in segs]
    lons = [s[1] for s in segs]
    if (min(lats) < BOUNDS["south"] - 0.001 or max(lats) > BOUNDS["north"] + 0.001
            or min(lons) < BOUNDS["west"] - 0.001 or max(lons) > BOUNDS["east"] + 0.001):
        print(f"[КАРТА] ВНИМАНИЕ: Кудрово выходит за сетку. Граница: "
              f"юг {min(lats):.4f} север {max(lats):.4f} запад {min(lons):.4f} восток {max(lons):.4f}",
              flush=True)
    out = [c["id"] for c in GRID["cells"] if not inside(c["center"][0], c["center"][1], segs)]
    async with pool.acquire() as con:
        async with con.transaction():
            owners = [r["owner"] for r in await con.fetch(
                "select distinct owner from cells3 where owner is not null and id = any($1::int[])", out)]
            await con.execute("update cells3 set disabled=false")
            await con.execute("update cells3 set disabled=true, owner=null where id = any($1::int[])", out)
            for fid in owners:
                await dissolve_if_empty(con, fid)
            await con.execute("insert into meta(key, value) values('trimmed', '1') "
                              "on conflict (key) do update set value='1'")
    invalidate_world()
    return N_CELLS - len(out), len(out)


async def auto_trim(app):
    """Один раз после первого запуска обрезает карту по границе Кудрово."""
    try:
        async with app["pool"].acquire() as con:
            if await con.fetchval("select value from meta where key='trimmed'"):
                return
        kept, removed = await trim_to_kudrovo(app["pool"])
        print(f"[КАРТА] обрезано по границе Кудрово: в игре {kept}, отключено {removed}", flush=True)
        for admin in ADMIN_IDS:
            await notify(app, admin, f"🗺 Карта обрезана по границе Кудрово: в игре {kept} территорий, "
                                     f"отключено {removed}. Поправить можно кнопкой ✂️ в игре.")
    except Exception as e:
        print(f"[КАРТА] не получилось обрезать автоматически: {e}", flush=True)


# ---------------------------------------------------------------- Проверка игрока
class AuthError(Exception):
    pass


def check_init_data(init_data: str) -> dict:
    """Проверяет подпись Telegram, чтобы никто не мог играть за другого."""
    data = dict(parse_qsl(init_data, keep_blank_values=True))
    received = data.pop("hash", None)
    if not received:
        raise AuthError("Открой игру через Telegram")
    check = "\n".join(f"{k}={v}" for k, v in sorted(data.items()))
    secret = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
    calc = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(calc, received):
        raise AuthError("Неверная подпись Telegram")
    if time.time() - int(data.get("auth_date", 0)) > 86400:
        raise AuthError("Сессия устарела, открой игру заново")
    return json.loads(data["user"])


def display_name(user: dict) -> str:
    name = (user.get("first_name") or "").strip()
    if user.get("username"):
        name = (name + " @" + user["username"]).strip()
    return name[:40] or "Игрок"


KNOWN_PLAYERS = {}   # кого уже записали в базу (id -> имя)


async def player_from_request(request):
    try:
        body = await request.json()
    except Exception:
        raise web.HTTPBadRequest(text=json.dumps({"error": "Плохой запрос"}), content_type="application/json")
    try:
        user = check_init_data(body.get("initData", ""))
    except (AuthError, KeyError, ValueError) as e:
        raise web.HTTPUnauthorized(text=json.dumps({"error": str(e) or "Нет доступа"}), content_type="application/json")
    uid = int(user["id"])
    name = display_name(user)
    if KNOWN_PLAYERS.get(uid) != name:
        async with request.app["pool"].acquire() as con:
            await con.execute(
                "insert into players3(id, name) values($1, $2) "
                "on conflict (id) do update set name = excluded.name",
                uid, name)
        KNOWN_PLAYERS[uid] = name
    return uid, body


def err(msg, status=400):
    return web.json_response({"error": msg}, status=status)


def cell_id(body):
    try:
        cid = int(body["cell"])
    except Exception:
        return None
    return cid if 0 <= cid < N_CELLS else None


def fname(fid, names):
    return names.get(fid) or "Территория без названия"


# ---------------------------------------------------------------- Общее состояние мира
# Карта и рейтинг одинаковы для всех игроков, поэтому сервер собирает их не чаще
# раза в WORLD_TTL секунд и отдаёт всем один и тот же готовый JSON.
# После любого действия (атака, защита, выбор, название...) кэш сразу обновляется.
WORLD_TTL = 1.0
WORLD = {"t": 0.0}
WORLD_LOCK = asyncio.Lock()
COLORS_JSON = json.dumps(TEAM_COLORS)


def invalidate_world():
    WORLD["t"] = 0.0


async def get_world(con):
    if time.monotonic() - WORLD["t"] < WORLD_TTL:
        return WORLD
    async with WORLD_LOCK:
        if time.monotonic() - WORLD["t"] < WORLD_TTL:
            return WORLD
        started = time.monotonic()
        cells = await con.fetch("select id, name, owner, disabled, gw, gc, gt from cells3 order by id")
        names = {r["id"]: r["name"] for r in cells}
        facs = {r["id"]: dict(r) for r in await con.fetch(
            "select f.*, (select count(*) from players3 p where p.faction=f.id) as members, "
            "(select count(*) from cells3 c where c.owner=f.id) as cells from factions f")}
        # Очки: 100 за каждую соту + сила армии (защита всех сот + резерв) + 1 за каждые 10 тапов
        garrison = {}
        for r in cells:
            if r["owner"] is not None:
                garrison[r["owner"]] = garrison.get(r["owner"], 0) + power(r["gw"], r["gc"], r["gt"])
        for f in facs.values():
            f["power"] = garrison.get(f["id"], 0) + power(f["rw"], f["rc"], f["rt"])
            f["points"] = f["cells"] * POINTS_PER_CELL + f["power"] + f["taps"] // 10
        ranking = sorted(facs.values(), key=lambda f: (-f["points"], -f["cells"], -f["members"], f["id"]))
        WORLD.update({
            "names": names,
            "facs": facs,
            "rank": {f["id"]: i + 1 for i, f in enumerate(ranking)},
            "cells_json": json.dumps([
                {"id": r["id"], "name": r["name"], "owner": r["owner"],
                 "ownerName": fname(r["owner"], names) if r["owner"] is not None else None,
                 "members": facs[r["owner"]]["members"] if r["owner"] in facs else 0,
                 "color": facs[r["owner"]]["color"] if r["owner"] in facs else None,
                 "home": r["owner"] == r["id"],
                 "disabled": r["disabled"], "w": r["gw"], "c": r["gc"], "t": r["gt"]}
                for r in cells], ensure_ascii=False, separators=(",", ":")),
            "top_json": json.dumps([
                {"id": f["id"], "name": fname(f["id"], names), "n": f["cells"], "members": f["members"],
                 "color": f["color"], "points": f["points"], "power": f["power"]}
                for f in ranking], ensure_ascii=False, separators=(",", ":")),
            "t": time.monotonic(),
        })
        took = time.monotonic() - started
        if took > 0.5:
            print(f"[НАГРУЗКА] сбор карты занял {took:.2f} с", flush=True)
        return WORLD


async def build_state(con, uid):
    """Готовый JSON состояния для игрока: общий мир из кэша + его личные данные."""
    w = await get_world(con)
    r = await con.fetchrow(
        "select p.id, p.name, p.faction, p.taps as ptaps, f.taps, f.rw, f.rc, f.rt, f.color, f.leader "
        "from players3 p left join factions f on f.id = p.faction where p.id=$1", uid)
    me = {"id": r["id"], "name": r["name"], "faction": r["faction"], "taps": r["ptaps"]}
    team = None
    if r["faction"] is not None and r["taps"] is not None:
        fid = r["faction"]
        team = {"id": fid, "name": fname(fid, w["names"]), "taps": r["taps"],
                "rw": r["rw"], "rc": r["rc"], "rt": r["rt"],
                "members": w["facs"].get(fid, {}).get("members", 1),
                "color": r["color"], "leader": r["leader"] == uid}
    personal = json.dumps({"me": me, "team": team, "admin": uid in ADMIN_IDS,
                           "rank": w["rank"].get(r["faction"])}, ensure_ascii=False)
    return (personal[:-1] + ',"cells":' + w["cells_json"] + ',"top":' + w["top_json"]
            + ',"colors":' + COLORS_JSON + '}')


def state_response(state, msg=None):
    body = state if msg is None else '{"msg":' + json.dumps(msg, ensure_ascii=False) + ',"state":' + state + '}'
    return web.Response(text=body, content_type="application/json")


async def notify(app, user_id, text):
    try:
        await app["bot"].send_message(user_id, text)
    except Exception:
        pass  # игрок мог не запускать бота или заблокировать его


async def notify_many(app, ids, text):
    for uid in list(ids)[:200]:
        await notify(app, uid, text)
        await asyncio.sleep(0.05)


# ---------------------------------------------------------------- API
async def index(request):
    return web.FileResponse(os.path.join(HERE, "static", "index.html"),
                            headers={"Cache-Control": "no-cache"})


async def grid(request):
    return web.Response(text=GRID_JSON, content_type="application/json",
                        headers={"Cache-Control": "no-cache"})


async def health(request):
    return web.Response(text="ok")


async def api_state(request):
    uid, _ = await player_from_request(request)
    async with request.app["pool"].acquire() as con:
        return state_response(await build_state(con, uid))


async def api_tap(request):
    """Тапы игрока идут в общую копилку его команды."""
    uid, body = await player_from_request(request)
    try:
        n = max(0, int(body.get("n", 0)))
    except (TypeError, ValueError):
        return err("Плохой запрос")
    async with request.app["pool"].acquire() as con:
        async with con.transaction():
            p = await con.fetchrow("select * from players3 where id=$1 for update", uid)
            if p["faction"] is None:
                return err("Сначала выбери территорию")
            now = time.time()
            elapsed = now - p["last_tap"] if p["last_tap"] else 2
            allowed = int(min(n, elapsed * MAX_TAPS_PER_SEC + 5, 200))
            await con.execute("update players3 set taps=taps+$2, last_tap=$3 where id=$1",
                              uid, allowed, now)
            f = await con.fetchrow("select * from factions where id=$1 for update", p["faction"])
            old, new = f["taps"], f["taps"] + allowed
            f = await con.fetchrow(
                "update factions set taps=$2, rw=rw+$3, rc=rc+$4, rt=rt+$5 where id=$1 "
                "returning id, taps, rw, rc, rt",
                f["id"], new, new // 10 - old // 10, new // 100 - old // 100, new // 1000 - old // 1000)
    return web.json_response({"team": dict(f), "accepted": allowed})


async def api_choose(request):
    """Выбор территории — один раз. Свободная сота: основать новую территорию.
    Чужая сота: вступить в команду, которой она принадлежит."""
    uid, body = await player_from_request(request)
    cid = cell_id(body)
    if cid is None:
        return err("Нет такой территории")
    async with request.app["pool"].acquire() as con:
        async with con.transaction():
            p = await con.fetchrow("select * from players3 where id=$1 for update", uid)
            if p["faction"] is not None:
                return err("Ты уже выбрал территорию — сменить её нельзя")
            cell = await con.fetchrow("select * from cells3 where id=$1 for update", cid)
            if cell["disabled"]:
                return err("Эта территория не входит в игру")
            if cell["owner"] is None:
                await con.execute("insert into factions(id, leader, color) values($1, $2, $3) "
                                  "on conflict do nothing", cid, uid, await free_color(con))
                await con.execute("update cells3 set owner=$1 where id=$1", cid)
                fid, msg = cid, "Ты основал территорию! Зови друзей — их тапы будут складываться с твоими."
            else:
                fid = cell["owner"]
                msg = "Ты вступил в команду! Ваши тапы теперь общие."
            await con.execute("update players3 set faction=$2 where id=$1", uid, fid)
        invalidate_world()
        return state_response(await build_state(con, uid), msg)


async def api_defend(request):
    """Весь общий резерв команды уходит в защиту выбранной соты."""
    uid, body = await player_from_request(request)
    cid = cell_id(body)
    if cid is None:
        return err("Нет такой территории")
    async with request.app["pool"].acquire() as con:
        async with con.transaction():
            p = await con.fetchrow("select * from players3 where id=$1", uid)
            if p["faction"] is None:
                return err("Сначала выбери территорию")
            f = await con.fetchrow("select * from factions where id=$1 for update", p["faction"])
            cell = await con.fetchrow("select * from cells3 where id=$1 for update", cid)
            if cell["owner"] != p["faction"]:
                return err("Это не ваша территория")
            if power(f["rw"], f["rc"], f["rt"]) <= 0:
                return err("Резерв пуст — тапайте!")
            await con.execute("update cells3 set gw=gw+$2, gc=gc+$3, gt=gt+$4 where id=$1",
                              cid, f["rw"], f["rc"], f["rt"])
            await con.execute("update factions set rw=0, rc=0, rt=0 where id=$1", f["id"])
        invalidate_world()
        return state_response(await build_state(con, uid), "Армия ушла в защиту")


async def api_attack(request):
    """Весь общий резерв команды идёт в атаку на соседнюю соту."""
    uid, body = await player_from_request(request)
    cid = cell_id(body)
    if cid is None:
        return err("Нет такой территории")
    alerts = []
    async with request.app["pool"].acquire() as con:
        async with con.transaction():
            p = await con.fetchrow("select * from players3 where id=$1", uid)
            if p["faction"] is None:
                return err("Сначала выбери территорию")
            fid = p["faction"]
            f = await con.fetchrow("select * from factions where id=$1 for update", fid)
            cell = await con.fetchrow("select * from cells3 where id=$1 for update", cid)
            if cell["disabled"]:
                return err("Эта территория не входит в игру")
            if cell["owner"] == fid:
                return err("Это ваша территория")
            owned = {r["id"] for r in await con.fetch("select id from cells3 where owner=$1", fid)}
            if not any(n in owned for n in NEIGHBORS[cid]):
                return err("Нападать можно только на соседние территории")
            A = power(f["rw"], f["rc"], f["rt"])
            D = power(cell["gw"], cell["gc"], cell["gt"])
            if A <= 0:
                return err("Резерв пуст — тапайте!")
            names = {r["id"]: r["name"] for r in await con.fetch("select id, name from cells3")}
            name = fname(cid, names)
            team = fname(fid, names)
            victim = cell["owner"]
            victims = ([r["id"] for r in await con.fetch(
                "select id from players3 where faction=$1", victim)] if victim is not None else [])
            if A > D:
                keep = 1 - D / A
                sw, sc, st = (math.floor(f["rw"] * keep), math.floor(f["rc"] * keep),
                              math.floor(f["rt"] * keep))
                # защитники переходят на сторону победителя
                await con.execute(
                    "update cells3 set owner=$2, gw=gw+$3, gc=gc+$4, gt=gt+$5 where id=$1",
                    cid, fid, sw, sc, st)
                await con.execute("update factions set rw=0, rc=0, rt=0 where id=$1", fid)
                msg = f"«{name}» захвачена! Защитники (сила {D}) перешли к вам"
                if victim is not None:
                    gone = await dissolve_if_empty(con, victim)
                    text = f"⚠️ «{team}» захватила вашу территорию «{name}» (атаку вёл {p['name']})."
                    if gone:
                        text += " У вашей команды не осталось земли — выбери территорию заново."
                    alerts.append((victims, text))
            else:
                keep_d = max(0.0, 1 - (A / 2) / D)
                await con.execute(
                    "update cells3 set gw=$2, gc=$3, gt=$4 where id=$1", cid,
                    math.floor(cell["gw"] * keep_d), math.floor(cell["gc"] * keep_d),
                    math.floor(cell["gt"] * keep_d))
                await con.execute("update factions set rw=0, rc=0, rt=0 where id=$1", fid)
                msg = f"Атака отбита. Защита «{name}» ослабла"
                if victim is not None:
                    alerts.append((victims, f"🛡 «{team}» напала на «{name}», но защита выстояла."))
            others = [r["id"] for r in await con.fetch(
                "select id from players3 where faction=$1 and id<>$2", fid, uid)]
            alerts.append((others, f"⚔️ {p['name']} отправил армию вашей команды на «{name}»: {msg}"))
        invalidate_world()
        state = await build_state(con, uid)
    for ids, text in alerts:
        asyncio.create_task(notify_many(request.app, ids, text))
    return state_response(state, msg)


async def api_color(request):
    """Лидер команды меняет цвет своей территории."""
    uid, body = await player_from_request(request)
    color = str(body.get("color", "")).lower()
    if color not in TEAM_COLORS:
        return err("Такого цвета нет")
    async with request.app["pool"].acquire() as con:
        p = await con.fetchrow("select faction from players3 where id=$1", uid)
        if p["faction"] is None:
            return err("Сначала выбери территорию")
        leader = await con.fetchval("select leader from factions where id=$1", p["faction"])
        if leader != uid:
            return err("Цвет меняет только лидер команды")
        await con.execute("update factions set color=$2 where id=$1", p["faction"], color)
        invalidate_world()
        return state_response(await build_state(con, uid), "Цвет команды изменён")


async def api_name(request):
    """Название соты может менять только админ."""
    uid, body = await player_from_request(request)
    if uid not in ADMIN_IDS:
        return err("Названия задаёт только админ", 403)
    cid = cell_id(body)
    if cid is None:
        return err("Нет такой территории")
    name = str(body.get("name", "")).strip()[:30] or None
    async with request.app["pool"].acquire() as con:
        await con.execute("update cells3 set name=$2 where id=$1", cid, name)
        invalidate_world()
        return state_response(await build_state(con, uid), "Название сохранено")


async def api_toggle(request):
    """Админ включает/отключает соту (то, что не Кудрово)."""
    uid, body = await player_from_request(request)
    if uid not in ADMIN_IDS:
        return err("Только для админа", 403)
    cid = cell_id(body)
    if cid is None:
        return err("Нет такой территории")
    async with request.app["pool"].acquire() as con:
        async with con.transaction():
            cell = await con.fetchrow("select * from cells3 where id=$1 for update", cid)
            if cell["disabled"]:
                await con.execute("update cells3 set disabled=false where id=$1", cid)
                msg = "Территория снова в игре"
            else:
                await con.execute("update cells3 set disabled=true, owner=null where id=$1", cid)
                await dissolve_if_empty(con, cell["owner"])
                msg = "Территория убрана из игры"
        invalidate_world()
        return state_response(await build_state(con, uid), msg)


# ---------------------------------------------------------------- Бот
dp = Dispatcher()
APP = {}


def play_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="🗺 Играть", web_app=WebAppInfo(url=BASE_URL + "/"))
    ]])


@dp.message(CommandStart())
async def cmd_start(message: Message):
    await message.answer(
        "Захват Кудрово! Выбери свою территорию или вступи в команду друзей. "
        "Тапайте вместе — тапы складываются, — собирайте воинов, пушки и танки "
        "и захватывайте соседей.",
        reply_markup=play_keyboard())


@dp.message(Command("myid"))
async def cmd_myid(message: Message):
    await message.answer(f"Твой Telegram ID: {message.from_user.id}")


@dp.message(Command("trim"))
async def cmd_trim(message: Message):
    """Админ: заново обрезать карту по границе Кудрово (сбрасывает ручные правки границ)."""
    if message.from_user.id not in ADMIN_IDS:
        return
    await message.answer("Скачиваю границу Кудрово…")
    try:
        kept, removed = await trim_to_kudrovo(APP["pool"])
        await message.answer(f"Готово: в игре {kept} территорий, отключено {removed}.")
    except Exception as e:
        await message.answer(f"Не получилось: {e}")


# ---------------------------------------------------------------- Запуск
def check_database_url():
    try:
        u = urlsplit(DATABASE_URL)
        host, user, port = u.hostname or "", u.username or "", u.port
    except Exception:
        host = user = ""
        port = None
    print(f"[БАЗА] подключаюсь: пользователь={user!r} адрес={host!r} порт={port}", flush=True)
    if "[" in DATABASE_URL or "YOUR-PASSWORD" in DATABASE_URL:
        raise SystemExit("[БАЗА] ОШИБКА: в DATABASE_URL остался [YOUR-PASSWORD] или квадратные скобки — "
                         "впиши свой пароль без скобок.")
    if host.startswith("db.") and host.endswith(".supabase.co"):
        raise SystemExit("[БАЗА] ОШИБКА: это строка Direct connection, Render к ней не подключится. "
                         "Возьми в Supabase: Connect -> Session pooler (адрес ...pooler.supabase.com).")


async def on_startup(app):
    check_database_url()
    app["pool"] = await asyncpg.create_pool(DATABASE_URL, min_size=1, max_size=8,
                                            statement_cache_size=0)
    await init_db(app["pool"])
    APP["pool"] = app["pool"]
    bot = app["bot"]
    await bot.set_webhook(BASE_URL + WEBHOOK_PATH, secret_token=WEBHOOK_SECRET,
                          drop_pending_updates=False)
    await bot.set_chat_menu_button(
        menu_button=MenuButtonWebApp(text="Играть", web_app=WebAppInfo(url=BASE_URL + "/")))
    app["trim_task"] = asyncio.create_task(auto_trim(app))


async def on_cleanup(app):
    if "pool" in app:
        await app["pool"].close()
    await app["bot"].session.close()


def make_app():
    app = web.Application()
    app["bot"] = Bot(BOT_TOKEN)
    app.router.add_get("/", index)
    app.router.add_get("/health", health)
    app.router.add_get("/api/grid", grid)
    app.router.add_post("/api/state", api_state)
    app.router.add_post("/api/tap", api_tap)
    app.router.add_post("/api/choose", api_choose)
    app.router.add_post("/api/defend", api_defend)
    app.router.add_post("/api/attack", api_attack)
    app.router.add_post("/api/name", api_name)
    app.router.add_post("/api/color", api_color)
    app.router.add_post("/api/toggle", api_toggle)
    SimpleRequestHandler(dispatcher=dp, bot=app["bot"], secret_token=WEBHOOK_SECRET).register(
        app, path=WEBHOOK_PATH)
    app.on_startup.append(on_startup)
    app.on_cleanup.append(on_cleanup)
    return app


if __name__ == "__main__":
    web.run_app(make_app(), host="0.0.0.0", port=PORT)
