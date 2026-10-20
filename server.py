"""Захват Кудрово — онлайн-игра для Telegram (бот + мини-приложение + API).

Переменные окружения:
  BOT_TOKEN     — токен бота от @BotFather
  BASE_URL      — адрес сервиса, например https://kudrovo-game.onrender.com
  DATABASE_URL  — строка подключения к Postgres (Supabase, Session pooler)
  ADMIN_IDS     — твой Telegram ID (узнать: написать боту /myid), можно несколько через запятую
"""
import hashlib
import hmac
import json
import math
import os
import random
import time
from urllib.parse import parse_qsl

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
DATABASE_URL = os.environ["DATABASE_URL"]
ADMIN_IDS = {int(x) for x in os.getenv("ADMIN_IDS", "").replace(" ", "").split(",") if x}
PORT = int(os.getenv("PORT", "8080"))

WEBHOOK_PATH = "/tg/" + hashlib.sha256(BOT_TOKEN.encode()).hexdigest()[:24]
WEBHOOK_SECRET = hashlib.sha256(("secret:" + BOT_TOKEN).encode()).hexdigest()[:32]
HERE = os.path.dirname(os.path.abspath(__file__))

# ---------------------------------------------------------------- Карта
# Прямоугольник, который покрывает Кудрово. Подвинь, если нужно.
BOUNDS = {"south": 59.893, "north": 59.918, "west": 30.488, "east": 30.548}
HEX_RADIUS_M = 230          # размер одного района (радиус соты в метрах)
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

# ---------------------------------------------------------------- База данных
SCHEMA = """
create table if not exists players (
    id bigint primary key,
    name text not null,
    taps bigint not null default 0,
    w bigint not null default 0,
    c bigint not null default 0,
    t bigint not null default 0,
    last_tap double precision not null default 0
);
create table if not exists cells (
    id int primary key,
    name text,
    owner bigint references players(id),
    def bigint not null
);
"""


async def init_db(pool):
    async with pool.acquire() as con:
        await con.execute(SCHEMA)
        existing = {r["id"] for r in await con.fetch("select id from cells")}
        new = [(i, random.randint(5, 30)) for i in range(N_CELLS) if i not in existing]
        if new:
            await con.executemany("insert into cells(id, def) values($1, $2)", new)
        await con.execute("delete from cells where id >= $1", N_CELLS)


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
            "insert into players(id, name) values($1, $2) "
            "on conflict (id) do update set name = excluded.name",
            uid, display_name(user))
    return uid, body


def err(msg, status=400):
    return web.json_response({"error": msg}, status=status)


async def build_state(con, uid):
    me = await con.fetchrow("select id, name, taps, w, c, t from players where id=$1", uid)
    cells = await con.fetch(
        "select c.id, c.name, c.owner, c.def, p.name as oname "
        "from cells c left join players p on p.id = c.owner order by c.id")
    top = await con.fetch(
        "select p.name, count(*) as n from cells c join players p on p.id = c.owner "
        "group by p.id, p.name order by n desc limit 10")
    return {
        "me": dict(me),
        "admin": uid in ADMIN_IDS,
        "cells": [{"id": r["id"], "name": r["name"], "owner": r["owner"],
                   "ownerName": r["oname"], "def": r["def"]} for r in cells],
        "top": [{"name": r["name"], "n": r["n"]} for r in top],
    }


# ---------------------------------------------------------------- API
async def index(request):
    return web.FileResponse(os.path.join(HERE, "static", "index.html"),
                            headers={"Cache-Control": "no-cache"})


async def grid(request):
    return web.Response(text=GRID_JSON, content_type="application/json",
                        headers={"Cache-Control": "public, max-age=300"})


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
            p = await con.fetchrow("select * from players where id=$1 for update", uid)
            now = time.time()
            elapsed = now - p["last_tap"] if p["last_tap"] else 2
            allowed = int(min(n, elapsed * MAX_TAPS_PER_SEC + 5, 200))
            old, new = p["taps"], p["taps"] + allowed
            row = await con.fetchrow(
                "update players set taps=$2, w=w+$3, c=c+$4, t=t+$5, last_tap=$6 "
                "where id=$1 returning id, name, taps, w, c, t",
                uid, new, new // 10 - old // 10, new // 100 - old // 100,
                new // 1000 - old // 1000, now)
    return web.json_response({"me": dict(row), "accepted": allowed})


async def api_attack(request):
    uid, body = await player_from_request(request)
    try:
        cid = int(body["cell"])
        assert 0 <= cid < N_CELLS
    except Exception:
        return err("Нет такого района")
    async with request.app["pool"].acquire() as con:
        async with con.transaction():
            p = await con.fetchrow("select * from players where id=$1 for update", uid)
            cell = await con.fetchrow("select * from cells where id=$1 for update", cid)
            if cell["owner"] == uid:
                return err("Это уже твой район")
            owned = {r["id"] for r in await con.fetch("select id from cells where owner=$1", uid)}
            if owned and not any(n in owned for n in NEIGHBORS[cid]):
                return err("Можно нападать только на соседние районы")
            power = p["w"] + p["c"] * 10 + p["t"] * 100
            if power <= 0:
                return err("Нет армии — потапай!")
            if power > cell["def"]:
                keep = 1 - cell["def"] / power
                await con.execute(
                    "update players set w=$2, c=$3, t=$4 where id=$1", uid,
                    math.floor(p["w"] * keep), math.floor(p["c"] * keep), math.floor(p["t"] * keep))
                await con.execute("update cells set owner=$2, def=5 where id=$1", cid, uid)
                msg = "Район захвачен!"
            else:
                new_def = max(1, cell["def"] - power // 2)
                await con.execute("update players set w=0, c=0, t=0 where id=$1", uid)
                await con.execute("update cells set def=$2 where id=$1", cid, new_def)
                msg = f"Атака отбита. Оборона ослабла до {new_def}"
        return web.json_response({"msg": msg, "state": await build_state(con, uid)})


async def api_fortify(request):
    uid, body = await player_from_request(request)
    try:
        cid = int(body["cell"])
    except Exception:
        return err("Нет такого района")
    async with request.app["pool"].acquire() as con:
        async with con.transaction():
            p = await con.fetchrow("select * from players where id=$1 for update", uid)
            cell = await con.fetchrow("select * from cells where id=$1 for update", cid)
            if not cell or cell["owner"] != uid:
                return err("Это не твой район")
            power = p["w"] + p["c"] * 10 + p["t"] * 100
            if power <= 0:
                return err("Нет армии — потапай!")
            await con.execute("update cells set def=def+$2 where id=$1", cid, power)
            await con.execute("update players set w=0, c=0, t=0 where id=$1", uid)
        return web.json_response({"msg": "Район укреплён", "state": await build_state(con, uid)})


async def api_name(request):
    """Название района может менять только админ."""
    uid, body = await player_from_request(request)
    if uid not in ADMIN_IDS:
        return err("Названия районов задаёт только админ", 403)
    try:
        cid = int(body["cell"])
        assert 0 <= cid < N_CELLS
    except Exception:
        return err("Нет такого района")
    name = str(body.get("name", "")).strip()[:30] or None
    async with request.app["pool"].acquire() as con:
        await con.execute("update cells set name=$2 where id=$1", cid, name)
        return web.json_response({"msg": "Название сохранено", "state": await build_state(con, uid)})


# ---------------------------------------------------------------- Бот
dp = Dispatcher()


def play_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="🗺 Играть", web_app=WebAppInfo(url=BASE_URL + "/"))
    ]])


@dp.message(CommandStart())
async def cmd_start(message: Message):
    await message.answer(
        "Захват Кудрово! Тапай, собирай армию — воинов, пушки и танки — "
        "и захватывай районы города. Карта общая для всех игроков.",
        reply_markup=play_keyboard())


@dp.message(Command("myid"))
async def cmd_myid(message: Message):
    await message.answer(f"Твой Telegram ID: {message.from_user.id}")


# ---------------------------------------------------------------- Запуск
def check_database_url():
    from urllib.parse import urlsplit
    try:
        u = urlsplit(DATABASE_URL.strip())
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
    app["pool"] = await asyncpg.create_pool(DATABASE_URL.strip(), min_size=1, max_size=5,
                                            statement_cache_size=0)
    await init_db(app["pool"])
    bot = app["bot"]
    await bot.set_webhook(BASE_URL + WEBHOOK_PATH, secret_token=WEBHOOK_SECRET,
                          drop_pending_updates=False)
    await bot.set_chat_menu_button(
        menu_button=MenuButtonWebApp(text="Играть", web_app=WebAppInfo(url=BASE_URL + "/")))


async def on_cleanup(app):
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
    app.router.add_post("/api/attack", api_attack)
    app.router.add_post("/api/fortify", api_fortify)
    app.router.add_post("/api/name", api_name)
    SimpleRequestHandler(dispatcher=dp, bot=app["bot"], secret_token=WEBHOOK_SECRET).register(
        app, path=WEBHOOK_PATH)
    app.on_startup.append(on_startup)
    app.on_cleanup.append(on_cleanup)
    return app


if __name__ == "__main__":
    web.run_app(make_app(), host="0.0.0.0", port=PORT)
