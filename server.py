"""Захват Кудрово — онлайн-игра для Telegram (бот + мини-приложение + API).

Переменные окружения:
  BOT_TOKEN     — токен бота от @BotFather
  BASE_URL      — адрес сервиса, например https://kudrovogame.onrender.com
  DATABASE_URL  — строка подключения к Postgres (Supabase, Session pooler)
  ADMIN_IDS     — твой Telegram ID (узнать: написать боту /myid), можно несколько через запятую

Правила:
  * Каждый игрок один раз выбирает свободную территорию — это его дом, сменить нельзя.
  * Тапы дают армию в резерв: 10 тапов — воин, 100 — пушка, 1000 — танк.
  * Резерв можно отправить в защиту своей территории или в атаку на соседнюю.
  * Если атака сильнее защиты, территория переходит к атакующему,
    а её защитники переходят на сторону победителя.
  * Админ задаёт названия территорий и отключает те, что не входят в Кудрово.
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
# Прямоугольник, который покрывает Кудрово. Лишние соты админ отключает в игре.
BOUNDS = {"south": 59.893, "north": 59.918, "west": 30.488, "east": 30.548}
HEX_RADIUS_M = 230          # размер одной территории (радиус соты в метрах)
MAX_TAPS_PER_SEC = 15       # защита от автокликеров


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


# ---------------------------------------------------------------- База данных
SCHEMA = """
create table if not exists players2 (
    id bigint primary key,
    name text not null,
    home int,
    taps bigint not null default 0,
    rw bigint not null default 0,
    rc bigint not null default 0,
    rt bigint not null default 0,
    last_tap double precision not null default 0
);
create table if not exists cells2 (
    id int primary key,
    name text,
    owner bigint references players2(id),
    disabled boolean not null default false,
    gw bigint not null default 0,
    gc bigint not null default 0,
    gt bigint not null default 0
);
"""


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
    """Отключает территории, центр которых вне границы Кудрово. Возвращает (в игре, отключено)."""
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
            await con.execute("update cells2 set disabled=false")
            await con.execute("update players2 set home=null where home = any($1::int[])", out)
            await con.execute("update cells2 set disabled=true, owner=null where id = any($1::int[])", out)
            await con.execute("insert into meta(key, value) values('trimmed', '1') "
                              "on conflict (key) do update set value='1'")
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
                                     f"отключено {removed}. Поправить можно кнопками в игре.")
    except Exception as e:
        print(f"[КАРТА] не получилось обрезать автоматически: {e}", flush=True)


async def init_db(pool):
    async with pool.acquire() as con:
        await con.execute(SCHEMA)
        await con.execute("create table if not exists meta (key text primary key, value text)")
        existing = {r["id"] for r in await con.fetch("select id from cells2")}
        old_names = {}
        try:  # названия из первой версии игры, если ты уже успел их задать
            old_names = {r["id"]: r["name"] for r in await con.fetch(
                "select id, name from cells where name is not null")}
        except Exception:
            pass
        new = [(i, old_names.get(i), random.randint(5, 30))
               for i in range(N_CELLS) if i not in existing]
        if new:
            await con.executemany("insert into cells2(id, name, gw) values($1, $2, $3)", new)
        await con.execute("delete from cells2 where id >= $1", N_CELLS)


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
    async with request.app["pool"].acquire() as con:
        await con.execute(
            "insert into players2(id, name) values($1, $2) "
            "on conflict (id) do update set name = excluded.name",
            uid, display_name(user))
    return uid, body


def err(msg, status=400):
    return web.json_response({"error": msg}, status=status)


def cell_id(body):
    try:
        cid = int(body["cell"])
    except Exception:
        return None
    return cid if 0 <= cid < N_CELLS else None


async def build_state(con, uid):
    me = await con.fetchrow("select id, name, home, taps, rw, rc, rt from players2 where id=$1", uid)
    cells = await con.fetch(
        "select c.id, c.name, c.owner, c.disabled, c.gw, c.gc, c.gt, p.name as oname, p.home as ohome "
        "from cells2 c left join players2 p on p.id = c.owner order by c.id")
    top = await con.fetch(
        "select p.name, count(*) as n from cells2 c join players2 p on p.id = c.owner "
        "group by p.id, p.name order by n desc limit 10")
    return {
        "me": dict(me),
        "admin": uid in ADMIN_IDS,
        "cells": [{"id": r["id"], "name": r["name"], "owner": r["owner"], "ownerName": r["oname"],
                   "home": r["owner"] is not None and r["ohome"] == r["id"],
                   "disabled": r["disabled"], "w": r["gw"], "c": r["gc"], "t": r["gt"]}
                  for r in cells],
        "top": [{"name": r["name"], "n": r["n"]} for r in top],
    }


async def notify(app, user_id, text):
    try:
        await app["bot"].send_message(user_id, text)
    except Exception:
        pass  # игрок мог не запускать бота или заблокировать его


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
        return web.json_response(await build_state(con, uid))


async def api_tap(request):
    uid, body = await player_from_request(request)
    try:
        n = max(0, int(body.get("n", 0)))
    except (TypeError, ValueError):
        return err("Плохой запрос")
    async with request.app["pool"].acquire() as con:
        async with con.transaction():
            p = await con.fetchrow("select * from players2 where id=$1 for update", uid)
            now = time.time()
            elapsed = now - p["last_tap"] if p["last_tap"] else 2
            allowed = int(min(n, elapsed * MAX_TAPS_PER_SEC + 5, 200))
            old, new = p["taps"], p["taps"] + allowed
            row = await con.fetchrow(
                "update players2 set taps=$2, rw=rw+$3, rc=rc+$4, rt=rt+$5, last_tap=$6 "
                "where id=$1 returning id, name, home, taps, rw, rc, rt",
                uid, new, new // 10 - old // 10, new // 100 - old // 100,
                new // 1000 - old // 1000, now)
    return web.json_response({"me": dict(row), "accepted": allowed})


async def api_choose(request):
    """Выбор своей территории — один раз (снова только если потерял всё)."""
    uid, body = await player_from_request(request)
    cid = cell_id(body)
    if cid is None:
        return err("Нет такой территории")
    async with request.app["pool"].acquire() as con:
        async with con.transaction():
            await con.fetchrow("select id from players2 where id=$1 for update", uid)
            if await con.fetchval("select count(*) from cells2 where owner=$1", uid):
                return err("Ты уже выбрал территорию — сменить её нельзя")
            cell = await con.fetchrow("select * from cells2 where id=$1 for update", cid)
            if cell["disabled"]:
                return err("Эта территория не входит в игру")
            if cell["owner"] is not None:
                return err("Эта территория уже занята — выбери свободную")
            await con.execute("update cells2 set owner=$2 where id=$1", cid, uid)
            await con.execute("update players2 set home=$2 where id=$1", uid, cid)
        return web.json_response({"msg": "Это теперь твоя территория!", "state": await build_state(con, uid)})


async def api_defend(request):
    """Весь резерв уходит в защиту выбранной своей территории."""
    uid, body = await player_from_request(request)
    cid = cell_id(body)
    if cid is None:
        return err("Нет такой территории")
    async with request.app["pool"].acquire() as con:
        async with con.transaction():
            p = await con.fetchrow("select * from players2 where id=$1 for update", uid)
            cell = await con.fetchrow("select * from cells2 where id=$1 for update", cid)
            if cell["owner"] != uid:
                return err("Это не твоя территория")
            if power(p["rw"], p["rc"], p["rt"]) <= 0:
                return err("Резерв пуст — потапай!")
            await con.execute("update cells2 set gw=gw+$2, gc=gc+$3, gt=gt+$4 where id=$1",
                              cid, p["rw"], p["rc"], p["rt"])
            await con.execute("update players2 set rw=0, rc=0, rt=0 where id=$1", uid)
        return web.json_response({"msg": "Армия ушла в защиту", "state": await build_state(con, uid)})


async def api_attack(request):
    """Весь резерв идёт в атаку на выбранную территорию."""
    uid, body = await player_from_request(request)
    cid = cell_id(body)
    if cid is None:
        return err("Нет такой территории")
    victim = None
    async with request.app["pool"].acquire() as con:
        async with con.transaction():
            p = await con.fetchrow("select * from players2 where id=$1 for update", uid)
            cell = await con.fetchrow("select * from cells2 where id=$1 for update", cid)
            if cell["disabled"]:
                return err("Эта территория не входит в игру")
            if cell["owner"] == uid:
                return err("Это твоя территория")
            owned = {r["id"] for r in await con.fetch("select id from cells2 where owner=$1", uid)}
            if not owned:
                return err("Сначала выбери свою территорию")
            if not any(n in owned for n in NEIGHBORS[cid]):
                return err("Нападать можно только на соседние территории")
            A = power(p["rw"], p["rc"], p["rt"])
            D = power(cell["gw"], cell["gc"], cell["gt"])
            if A <= 0:
                return err("Резерв пуст — потапай!")
            name = cell["name"] or f"Территория {cid + 1}"
            if A > D:
                keep = 1 - D / A
                sw, sc, st = (math.floor(p["rw"] * keep), math.floor(p["rc"] * keep),
                              math.floor(p["rt"] * keep))
                # защитники переходят на сторону победителя
                await con.execute(
                    "update cells2 set owner=$2, gw=gw+$3, gc=gc+$4, gt=gt+$5 where id=$1",
                    cid, uid, sw, sc, st)
                await con.execute("update players2 set rw=0, rc=0, rt=0 where id=$1", uid)
                joined = power(cell["gw"], cell["gc"], cell["gt"])
                msg = f"{name} захвачена! К тебе перешли защитники (сила {joined})"
                if cell["owner"] is not None:
                    victim = (cell["owner"], f"⚠️ {p['name']} захватил твою территорию «{name}»! "
                                             f"Открой игру и отбей её.")
            else:
                keep_d = max(0.0, 1 - (A / 2) / D)
                await con.execute(
                    "update cells2 set gw=$2, gc=$3, gt=$4 where id=$1", cid,
                    math.floor(cell["gw"] * keep_d), math.floor(cell["gc"] * keep_d),
                    math.floor(cell["gt"] * keep_d))
                await con.execute("update players2 set rw=0, rc=0, rt=0 where id=$1", uid)
                msg = f"Атака отбита. Защита «{name}» ослабла"
                if cell["owner"] is not None:
                    victim = (cell["owner"], f"🛡 {p['name']} напал на «{name}», но защита выстояла.")
        state = await build_state(con, uid)
    if victim:
        await notify(request.app, *victim)
    return web.json_response({"msg": msg, "state": state})


async def api_name(request):
    """Название территории может менять только админ."""
    uid, body = await player_from_request(request)
    if uid not in ADMIN_IDS:
        return err("Названия задаёт только админ", 403)
    cid = cell_id(body)
    if cid is None:
        return err("Нет такой территории")
    name = str(body.get("name", "")).strip()[:30] or None
    async with request.app["pool"].acquire() as con:
        await con.execute("update cells2 set name=$2 where id=$1", cid, name)
        return web.json_response({"msg": "Название сохранено", "state": await build_state(con, uid)})


async def api_toggle(request):
    """Админ включает/отключает территорию (то, что не Кудрово)."""
    uid, body = await player_from_request(request)
    if uid not in ADMIN_IDS:
        return err("Только для админа", 403)
    cid = cell_id(body)
    if cid is None:
        return err("Нет такой территории")
    async with request.app["pool"].acquire() as con:
        async with con.transaction():
            cell = await con.fetchrow("select * from cells2 where id=$1 for update", cid)
            if cell["disabled"]:
                await con.execute("update cells2 set disabled=false where id=$1", cid)
                msg = "Территория снова в игре"
            else:
                await con.execute("update players2 set home=null where home=$1", cid)
                await con.execute("update cells2 set disabled=true, owner=null where id=$1", cid)
                msg = "Территория убрана из игры"
        return web.json_response({"msg": msg, "state": await build_state(con, uid)})


# ---------------------------------------------------------------- Бот
dp = Dispatcher()


def play_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="🗺 Играть", web_app=WebAppInfo(url=BASE_URL + "/"))
    ]])


@dp.message(CommandStart())
async def cmd_start(message: Message):
    await message.answer(
        "Захват Кудрово! Выбери свою территорию, тапай, собирай армию — воинов, пушки и танки — "
        "и захватывай соседей. Карта общая для всех игроков.",
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


APP = {}


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
    app["pool"] = await asyncpg.create_pool(DATABASE_URL, min_size=1, max_size=5,
                                            statement_cache_size=0)
    await init_db(app["pool"])
    bot = app["bot"]
    await bot.set_webhook(BASE_URL + WEBHOOK_PATH, secret_token=WEBHOOK_SECRET,
                          drop_pending_updates=False)
    await bot.set_chat_menu_button(
        menu_button=MenuButtonWebApp(text="Играть", web_app=WebAppInfo(url=BASE_URL + "/")))
    APP["pool"] = app["pool"]
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
    app.router.add_post("/api/toggle", api_toggle)
    SimpleRequestHandler(dispatcher=dp, bot=app["bot"], secret_token=WEBHOOK_SECRET).register(
        app, path=WEBHOOK_PATH)
    app.on_startup.append(on_startup)
    app.on_cleanup.append(on_cleanup)
    return app


if __name__ == "__main__":
    web.run_app(make_app(), host="0.0.0.0", port=PORT)
