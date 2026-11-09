import asyncio
import html
import math
import os
import random
import re
import sqlite3
import threading
import time
import traceback
from collections import Counter, defaultdict
from datetime import datetime
from difflib import SequenceMatcher
from functools import lru_cache

import httpx
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.error import BadRequest
from telegram.ext import (
    ApplicationBuilder,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)
from telethon import TelegramClient
from telethon.errors import FloodWaitError, UsernameInvalidError
from telethon.tl.functions.account import CheckUsernameRequest
from telethon.tl.types import User

# ====================== НАСТРОЙКИ ======================
TOKEN = "9060929202:AAEVuRSuDZqr0zPRVLd6U5mY8PubJgP8wIc"   # токен от @BotFather
API_ID = int(os.getenv("API_ID", "0"))              # с my.telegram.org (необязательно)
API_HASH = os.getenv("API_HASH", "ТВОЙ_API_HASH")   # с my.telegram.org (необязательно)
SESSION = "checker"

ADMIN_USERNAMES = ["uyke4o"]    # администраторы (юзернеймы без @). ID привязывается при первом /start

SUPPORT_URL = "https://t.me/whiteofme"
BUY_URL = "https://t.me/whiteofme"
FREE_LIMIT = 3          # бесплатных 5-буквенных ников (всего)
SIX_LIMIT = 10          # бесплатных 6-буквенных ников за час
SIX_WINDOW = 3600       # через сколько секунд после исчерпания лимит обновляется
COOLDOWN = 5            # пауза между поисками, секунд
DB_PATH = "users.db"

WORDS_URL = (
    "https://raw.githubusercontent.com/first20hours/google-10000-english/"
    "master/google-10000-english-no-swears.txt"
)
TIME_LIMIT = 10
CONCURRENCY = 20
# ========================================================

USE_TG = API_ID != 0 and API_HASH != "ТВОЙ_API_HASH"

HEADERS = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/124 Safari/537.36"}
FRAGMENT_LISTED = ("available", "on auction", "sold", "for sale", "auction")

WORDS: list[str] = []
TAKEN: set[str] = set()
TG: TelegramClient | None = None
TG_LOCK = asyncio.Lock()
FLOOD_UNTIL = 0.0
LOOP: asyncio.AbstractEventLoop | None = None
BOT = None
ADMIN_IDS: set[int] = set()
DEBUG_ON = True
START_TIME = time.time()

# модель "красивых слияний букв" (строится из списка слов при запуске)
ALL_WORDS: list[str] = []
WORDSET: set[str] = set()
RANK: dict[str, int] = {}
COUNTS: dict = {}
TOTALS: dict = {}
OPTIONS: dict = {}
PRICE_BASE = {5: 20.0, 6: 5.0}   # ориентир цены в TON при читабельности 5 (настрой под рынок)


# ---------------------- отладка в Telegram ----------------------
async def _send_debug(aid: int, text: str):
    try:
        await BOT.send_message(aid, "🐞 " + text[:4000], parse_mode="HTML")
    except Exception:
        pass


def debug(text: str):
    """Пишет в консоль и отправляет администраторам в Telegram."""
    print(f"[{datetime.now().strftime('%d.%m %H:%M:%S')}] " + html.unescape(re.sub(r"<[^>]+>", "", text)))
    if DEBUG_ON and BOT is not None and LOOP is not None:
        for aid in list(ADMIN_IDS):
            asyncio.run_coroutine_threadsafe(_send_debug(aid, text), LOOP)


def ulabel(user) -> str:
    uname = f"@{user.username}" if user.username else "без username"
    return html.escape(f"{user.id} | {uname} | {user.full_name}")


# ---------------------- база пользователей ----------------------
DB_LOCK = threading.Lock()


def db(query, params=(), fetch=False):
    with DB_LOCK:
        con = sqlite3.connect(DB_PATH)
        try:
            cur = con.execute(query, params)
            rows = cur.fetchall() if fetch else None
            con.commit()
            return rows
        finally:
            con.close()


def init_db():
    db(
        "CREATE TABLE IF NOT EXISTS users ("
        "id INTEGER PRIMARY KEY, username TEXT DEFAULT '', "
        "free_used INTEGER DEFAULT 0, premium_until INTEGER DEFAULT 0, forever INTEGER DEFAULT 0, "
        "six_left INTEGER DEFAULT 10, six_reset INTEGER DEFAULT 0)"
    )
    for col, ddl in (("six_left", "INTEGER DEFAULT 10"), ("six_reset", "INTEGER DEFAULT 0")):
        try:
            db(f"ALTER TABLE users ADD COLUMN {col} {ddl}")
        except sqlite3.OperationalError:
            pass
    db("CREATE TABLE IF NOT EXISTS admins (id INTEGER PRIMARY KEY, username TEXT DEFAULT '')")
    ADMIN_IDS.update(r[0] for r in db("SELECT id FROM admins", fetch=True))


def bind_admin(uid: int, username: str):
    db("INSERT OR REPLACE INTO admins (id, username) VALUES (?, ?)", (uid, username))
    ADMIN_IDS.add(uid)
    debug(f"👑 Администратор привязан: {uid} @{html.escape(username)}")


def check_admin(user) -> bool:
    """Админ определяется по ID. По юзернейму привязка происходит один раз:
    если для этого юзернейма ID ещё не привязан."""
    if user is None:
        return False
    if user.id in ADMIN_IDS:
        return True
    uname = (user.username or "").lower()
    if uname and uname in ADMIN_USERNAMES:
        if not db("SELECT id FROM admins WHERE username=?", (uname,), fetch=True):
            bind_admin(user.id, uname)
            return True
    return False


def touch_user(user):
    if user is None:
        return
    uname = (user.username or "").lower()
    db(
        "INSERT INTO users (id, username) VALUES (?, ?) ON CONFLICT(id) DO UPDATE SET "
        "username = CASE WHEN excluded.username != '' THEN excluded.username ELSE users.username END",
        (user.id, uname),
    )


def get_user(uid: int):
    rows = db(
        "SELECT id, username, free_used, premium_until, forever, six_left, six_reset FROM users WHERE id=?",
        (uid,), fetch=True,
    )
    if not rows:
        return None
    r = rows[0]
    return {"id": r[0], "username": r[1], "free_used": r[2], "premium_until": r[3],
            "forever": r[4], "six_left": r[5], "six_reset": r[6]}


def is_premium(uid: int) -> bool:
    if uid in ADMIN_IDS:
        return True
    u = get_user(uid)
    return bool(u and (u["forever"] or u["premium_until"] > time.time()))


def free_left(uid: int) -> int:
    u = get_user(uid)
    return max(0, FREE_LIMIT - (u["free_used"] if u else 0))


def use_free(uid: int):
    db("UPDATE users SET free_used = free_used + 1 WHERE id=?", (uid,))


def six_status(uid: int):
    """(сколько осталось 6-буквенных ников, секунд до обновления лимита).
    Лимит обновляется до 10 только если он был полностью израсходован и прошёл час."""
    u = get_user(uid)
    if not u:
        return SIX_LIMIT, 0
    left, reset = u["six_left"], u["six_reset"]
    if left <= 0 and reset and time.time() >= reset:
        db("UPDATE users SET six_left=?, six_reset=0 WHERE id=?", (SIX_LIMIT, uid))
        return SIX_LIMIT, 0
    wait = max(0, int(reset - time.time())) if left <= 0 else 0
    return max(left, 0), wait


def use_six(uid: int):
    db("UPDATE users SET six_left = MAX(six_left - 1, 0) WHERE id=?", (uid,))
    u = get_user(uid)
    if u and u["six_left"] <= 0:
        db("UPDATE users SET six_reset=? WHERE id=?", (int(time.time() + SIX_WINDOW), uid))


def grant(uid: int, seconds):
    """seconds=None -> навсегда."""
    db("INSERT OR IGNORE INTO users (id, username) VALUES (?, '')", (uid,))
    if seconds is None:
        db("UPDATE users SET forever=1 WHERE id=?", (uid,))
    else:
        u = get_user(uid)
        base = max(time.time(), u["premium_until"])
        db("UPDATE users SET premium_until=? WHERE id=?", (int(base + seconds), uid))


def revoke(uid: int):
    db("UPDATE users SET premium_until=0, forever=0 WHERE id=?", (uid,))


def minutes(sec: int) -> int:
    return max(1, (sec + 59) // 60)


def parse_duration(s: str):
    """'7' или '7d' - дни, '5h' - часы, '30m' - минуты, '1d12h30m' - вместе, 'forever' - навсегда.
    Возвращает секунды (None = навсегда) или бросает ValueError."""
    s = s.lower().strip()
    if s in ("forever", "навсегда"):
        return None
    units = {"": 86400, "d": 86400, "д": 86400, "h": 3600, "ч": 3600, "m": 60, "м": 60}
    matches = list(re.finditer(r"(\d+)([dhmдчм]?)", s))
    if not matches or "".join(m.group(0) for m in matches) != s:
        raise ValueError
    total = sum(int(m.group(1)) * units[m.group(2)] for m in matches)
    if total <= 0:
        raise ValueError
    return total


def fmt_duration(sec: int) -> str:
    d, rem = divmod(int(sec), 86400)
    h, rem = divmod(rem, 3600)
    m = rem // 60
    parts = []
    if d:
        parts.append(f"{d} дн.")
    if h:
        parts.append(f"{h} ч.")
    if m:
        parts.append(f"{m} мин.")
    return " ".join(parts) or "0 мин."


def status_line(uid: int) -> str:
    if uid in ADMIN_IDS:
        return "👑 <b>Администратор</b>: все функции без ограничений"
    u = get_user(uid)
    if u and u["forever"]:
        return "✅ Твоя подписка: <b>навсегда</b>"
    if u and u["premium_until"] > time.time():
        until = datetime.fromtimestamp(u["premium_until"]).strftime("%d.%m.%Y %H:%M")
        return f"✅ Твоя подписка активна до <b>{until}</b>"
    l6, w6 = six_status(uid)
    s6 = f"{l6} из {SIX_LIMIT} в час" + (f" (обновится через {minutes(w6)} мин)" if l6 <= 0 else "")
    return (
        "Твой тариф: <b>Free</b>\n"
        f"• 5 букв: осталось {free_left(uid)} из {FREE_LIMIT}\n"
        f"• 6 букв: осталось {s6}"
    )


def label(uid: int) -> str:
    u = get_user(uid)
    return f"{uid} (@{u['username']})" if u and u["username"] else str(uid)


def describe(uid: int) -> str:
    u = get_user(uid)
    if not u:
        return "нет в базе"
    if u["forever"]:
        sub = "навсегда"
    elif u["premium_until"] > time.time():
        sub = "до " + datetime.fromtimestamp(u["premium_until"]).strftime("%d.%m.%Y %H:%M")
    else:
        sub = "нет"
    l6, _ = six_status(uid)
    return (f"подписка: {sub}; 5 букв использовано: {u['free_used']}/{FREE_LIMIT}; "
            f"6 букв осталось: {l6}/{SIX_LIMIT}")


# ---------------------- поиск пользователей (для админки) ----------------------
def local_lookup(arg: str):
    arg = arg.strip()
    if arg.isdigit():
        return int(arg)
    rows = db("SELECT id FROM users WHERE username=?", (arg.lstrip("@").lower(),), fetch=True)
    return rows[0][0] if rows else None


async def aresolve_user(arg: str):
    """Для обработчиков бота (async)."""
    uid = local_lookup(arg)
    if uid is not None:
        return uid
    name = arg.strip().lstrip("@").lower()
    if TG is not None and name:
        try:
            ent = await asyncio.wait_for(TG.get_entity(name), 15)
            if isinstance(ent, User):
                db("INSERT OR IGNORE INTO users (id, username) VALUES (?, ?)", (ent.id, name))
                return ent.id
        except Exception:
            pass
    return None


def resolve_user(arg: str):
    """Для консоли (отдельный поток)."""
    uid = local_lookup(arg)
    if uid is not None:
        return uid
    name = arg.strip().lstrip("@").lower()
    if TG is not None and LOOP is not None and name:
        try:
            ent = asyncio.run_coroutine_threadsafe(TG.get_entity(name), LOOP).result(15)
            if isinstance(ent, User):
                db("INSERT OR IGNORE INTO users (id, username) VALUES (?, ?)", (ent.id, name))
                return ent.id
        except Exception:
            pass
    return None


# ---------------------- поиск ников ----------------------
async def load_words():
    global ALL_WORDS, WORDS, WORDSET, RANK
    if os.path.exists("words.txt"):
        raw = open("words.txt", encoding="utf-8").read().split()
    else:
        async with httpx.AsyncClient(timeout=15) as c:
            raw = (await c.get(WORDS_URL)).text.split()
    ordered, seen = [], set()
    for w in raw:
        w = w.lower()
        if w.isalpha() and w.isascii() and 3 <= len(w) <= 12 and w not in seen:
            seen.add(w)
            ordered.append(w)
    ALL_WORDS = ordered
    WORDSET = set(ordered)
    RANK = {w: i for i, w in enumerate(ordered)}
    WORDS = sorted(w for w in ordered if len(w) in (5, 6))
    build_model(ordered)


# ---------------------- красивые слияния букв, читабельность, цена ----------------------
BAD_PARTS = ("fuck", "shit", "cunt", "dick", "cock", "porn", "nazi", "rape", "slut", "whor",
             "nigg", "fagg", "twat", "pussy", "bitch", "cum", "anal", "sex", "hitl")
VOWELS = set("aeiouy")
LETTERS = "abcdefghijklmnopqrstuvwxyz"
PHONETIC = (("c", "k"), ("k", "c"), ("s", "z"), ("z", "s"), ("ph", "f"), ("f", "ph"),
            ("y", "i"), ("i", "y"), ("ck", "k"), ("x", "ks"), ("ee", "i"), ("oo", "u"))


def build_model(words):
    """Строит модель 'какие буквы обычно идут друг за другом' по английским словам."""
    global COUNTS, TOTALS, OPTIONS
    counts = defaultdict(Counter)
    for w in words:
        s = "^^" + w + "$"
        for i in range(2, len(s)):
            counts[s[i - 2:i]][s[i]] += 1
    COUNTS = {k: dict(v) for k, v in counts.items()}
    TOTALS = {k: sum(v.values()) for k, v in COUNTS.items()}
    OPTIONS = {}
    for k, v in COUNTS.items():
        chars = [c for c in v if c != "$"]
        if chars:
            OPTIONS[k] = (chars, [v[c] for c in chars])
    readability.cache_clear()


def avg_logprob(word: str) -> float:
    s = "^^" + word + "$"
    total = 0.0
    for i in range(2, len(s)):
        ctx, ch = s[i - 2:i], s[i]
        c = COUNTS.get(ctx)
        if c:
            p = (c.get(ch, 0) + 0.1) / (TOTALS[ctx] + 2.7)
        else:
            p = 1 / 27
        total += math.log(p)
    return total / (len(s) - 2)


@lru_cache(maxsize=100000)
def readability(word: str) -> int:
    """Читабельность 1-10: насколько ник похож на нормальное английское слово и легко читается."""
    if not COUNTS:
        return 5
    if not any(ch in VOWELS for ch in word):
        return 1
    score = 10 - (-avg_logprob(word) - 1.5) * 4.5
    run = best = 0
    for ch in word:
        if ch in VOWELS:
            run = 0
        else:
            run += 1
            best = max(best, run)
    if best >= 4:
        score -= 3
    elif best == 3:
        score -= 1
    if re.search(r"(.)\1\1", word):
        score -= 3
    score -= 0.7 * sum(ch in "qxzj" for ch in word)
    return int(max(1, min(10, round(score))))


def fmt_ton(v: float) -> str:
    v = max(v, 1.0)
    return f"{v:.1f}".rstrip("0").rstrip(".") if v < 10 else str(int(round(v)))


def estimate_price(word: str):
    """Очень грубая оценка (в TON). Это не реальная цена: ник не продаётся на Fragment."""
    x = PRICE_BASE.get(len(word), 5.0) * (1.35 ** (readability(word) - 5))
    if word in WORDSET:
        x *= 2.5
        if RANK.get(word, 10 ** 9) < 1500:
            x *= 2
    x *= 0.7 ** sum(ch in "qxzj" for ch in word)
    return fmt_ton(x * 0.6), fmt_ton(x * 1.6)


def nick_card(name: str, like: str = "") -> str:
    r = readability(name)
    lo, hi = estimate_price(name)
    kind = "реальное слово" if name in WORDSET else "красивое слияние букв"
    text = (
        f"✅ Найден ник: <code>@{name}</code>\n\n"
        f"📖 Читабельность: <b>{r}/10</b>\n"
        f"🏷 Тип: {kind}\n"
        f"💰 Примерная цена на Fragment: <b>≈ {lo}–{hi} TON</b> (оценка бота, не реальная цена)"
    )
    if like:
        sim = int(SequenceMatcher(None, like, name).ratio() * 100)
        text += f"\n🔤 Похоже на «{html.escape(like)}»: {sim}%"
    return text + "\n\nНажми на ник, чтобы скопировать."


def gen_blends(length: int, n: int, prefix: str = "", suffix: str = "", min_read: int = 7):
    """Генерирует произносимые слова-'слияния', похожие на английские, лучшие по читабельности вперёд."""
    if not OPTIONS:
        return []
    body_len = length - len(suffix)
    if len(prefix) > body_len or body_len <= 0:
        return []
    out: dict[str, int] = {}
    attempts = 0
    while len(out) < n and attempts < n * 12:
        attempts += 1
        w = prefix
        ok = True
        while len(w) < body_len:
            opt = OPTIONS.get(("^^" + w)[-2:])
            if not opt:
                ok = False
                break
            w += random.choices(opt[0], opt[1])[0]
        if not ok:
            continue
        w += suffix
        if len(w) != length or w in out or w in WORDSET or any(b in w for b in BAD_PARTS):
            continue
        r = readability(w)
        if r >= min_read:
            out[w] = r
    items = sorted(out.items(), key=lambda kv: kv[1] + random.uniform(0, 1.5), reverse=True)
    return [w for w, _ in items]


def similar_candidates(target: str, length: int, prefix: str, suffix: str, limit: int = 500):
    """Ники нужной длины, похожие на слово target: правки, фонетические замены, словарные соседи."""
    t = target.lower()
    frontier = {t}
    for _ in range(abs(len(t) - length)):
        nxt = set()
        for w in frontier:
            n = len(w)
            if n > length:
                for i in range(n):
                    nxt.add(w[:i] + w[i + 1:])
            elif n < length:
                for i in range(n + 1):
                    for c in LETTERS:
                        nxt.add(w[:i] + c + w[i:])
        if len(nxt) > 200:
            nxt = set(random.sample(sorted(nxt), 200))
        frontier = nxt
    base = [w for w in frontier if len(w) == length]
    forms = set(base)
    for w in base[:60]:
        for i in range(length):
            for c in LETTERS:
                forms.add(w[:i] + c + w[i + 1:])
        for i in range(length - 1):
            forms.add(w[:i] + w[i + 1] + w[i] + w[i + 2:])
    for a, b in PHONETIC:
        for w in base[:60] + [t]:
            if a in w:
                forms.add(w.replace(a, b))
    forms.update(w for w in WORDS if len(w) == length)

    scored = []
    for w in forms:
        if len(w) != length or not w.startswith(prefix) or not w.endswith(suffix):
            continue
        if any(b in w for b in BAD_PARTS):
            continue
        r = readability(w)
        if r < 5:
            continue
        sim = SequenceMatcher(None, t, w).ratio()
        if sim < 0.5:
            continue
        scored.append((sim * 0.6 + r / 10 * 0.4, w))
    scored.sort(reverse=True)
    return [w for _, w in scored[:limit]]


def build_pool(length: int, mode: str, prefix: str, suffix: str, like: str, seen: set):
    """Список ников-кандидатов для проверки (в порядке проверки)."""
    if like:
        pool = similar_candidates(like, length, prefix, suffix)
    else:
        dict_pool = []
        if mode in ("all", "words"):
            dict_pool = [w for w in WORDS if len(w) == length and w.startswith(prefix) and w.endswith(suffix)]
            random.shuffle(dict_pool)
        blends = gen_blends(length, 400, prefix, suffix) if mode in ("all", "blends") else []
        if mode == "all":
            pool, di, bi = [], 0, 0
            while di < len(dict_pool) or bi < len(blends):
                if bi < len(blends):
                    pool.extend(blends[bi:bi + 2])
                    bi += 2
                if di < len(dict_pool):
                    pool.append(dict_pool[di])
                    di += 1
        else:
            pool = dict_pool or blends
    return [w for w in pool if w not in TAKEN and w not in seen]


async def check_tme(client: httpx.AsyncClient, name: str):
    try:
        r = await client.get(f"https://t.me/{name}")
        if r.status_code != 200:
            return None
        m = re.search(r'<meta property="og:title" content="([^"]*)"', r.text)
        if not m:
            return None
        return m.group(1).startswith("Telegram: Contact @")
    except Exception:
        return None


async def check_fragment(client: httpx.AsyncClient, name: str):
    try:
        r = await client.get(f"https://fragment.com/username/{name}")
        if r.status_code != 200:
            return None
        m = re.search(r'tm-section-header-status[^>]*>([^<]+)<', r.text)
        if not m:
            return False
        status = m.group(1).strip().lower()
        return any(s in status for s in FRAGMENT_LISTED)
    except Exception:
        return None


async def check_settable(name: str):
    global FLOOD_UNTIL
    if TG is None or time.time() < FLOOD_UNTIL:
        return None
    async with TG_LOCK:
        try:
            return bool(await TG(CheckUsernameRequest(name)))
        except FloodWaitError as e:
            FLOOD_UNTIL = time.time() + e.seconds
            debug(f"⚠️ Telegram ограничил проверки профиля на {e.seconds} сек.")
            return None
        except UsernameInvalidError:
            return False
        except Exception:
            return None


async def search(length: int, want: int, prefix: str, suffix: str, mode: str = "all", like: str = "", seen=None):
    cands = await asyncio.to_thread(build_pool, length, mode, prefix, suffix, like, seen or set())
    found: list[str] = []
    checked = 0
    deadline = time.monotonic() + TIME_LIMIT
    it = iter(cands)

    async with httpx.AsyncClient(headers=HEADERS, timeout=4, follow_redirects=True) as client:
        async def worker():
            nonlocal checked
            for w in it:
                if time.monotonic() > deadline or len(found) >= want:
                    return
                free = await check_tme(client, w)
                checked += 1
                if free is None:
                    continue
                if not free:
                    TAKEN.add(w)
                    continue
                listed = await check_fragment(client, w)
                if listed is True:
                    TAKEN.add(w)
                    continue
                if listed is None:
                    continue
                ok = await check_settable(w)         # необязательная проверка у Telegram
                if ok is False:
                    TAKEN.add(w)
                else:                                # True или None (проверка выключена/недоступна)
                    found.append(w)

        await asyncio.gather(*[worker() for _ in range(CONCURRENCY)])

    return found, checked, len(cands)


# ---------------------- интерфейс ----------------------
def main_kb(uid: int | None = None):
    rows = [
        [InlineKeyboardButton("🛟 Поддержка", url=SUPPORT_URL)],
        [InlineKeyboardButton("🔎 Поиск", callback_data="menu:search")],
        [InlineKeyboardButton("💎 Подписка", callback_data="menu:sub")],
    ]
    if uid is not None and uid in ADMIN_IDS:
        rows.append([InlineKeyboardButton("🛠 Админ-панель", callback_data="adm:menu")])
    return InlineKeyboardMarkup(rows)


def search_kb(premium: bool):
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("6 букв", callback_data="search:6")],
        [InlineKeyboardButton("5 букв", callback_data="search:5")],
        [InlineKeyboardButton("⚙️ Фильтры" if premium else "🔒 Фильтры", callback_data="menu:filters")],
        [InlineKeyboardButton("⬅️ Назад", callback_data="menu:main")],
    ])


def found_kb(length: int, name: str):
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🔄 Искать ещё", callback_data=f"again:{length}")],
        [InlineKeyboardButton("🔨 Fragment", url=f"https://fragment.com/username/{name}"),
         InlineKeyboardButton("✈️ Telegram", url=f"https://t.me/{name}")],
        [InlineKeyboardButton("🏠 В меню", callback_data="menu:main")],
    ])


def notfound_kb(length: int):
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🔄 Искать ещё", callback_data=f"again:{length}")],
        [InlineKeyboardButton("🏠 В меню", callback_data="menu:main")],
    ])


def lock_kb():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("💎 Подписка", callback_data="menu:sub")],
        [InlineKeyboardButton("🏠 В меню", callback_data="menu:main")],
    ])


def sub_kb():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🛒 Как купить", url=BUY_URL)],
        [InlineKeyboardButton("⬅️ Назад", callback_data="menu:main")],
    ])


def filters_kb(f):
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("Начало слова", callback_data="flt:prefix"),
         InlineKeyboardButton("Конец слова", callback_data="flt:suffix")],
        [InlineKeyboardButton("🔤 Похоже на слово", callback_data="flt:like")],
        [InlineKeyboardButton(f"Режим: {MODE_NAMES[f.get('mode', 'all')]}", callback_data="flt:mode")],
        [InlineKeyboardButton("🗑 Сбросить", callback_data="flt:reset")],
        [InlineKeyboardButton("⬅️ Назад", callback_data="menu:search")],
    ])


MAIN_TEXT = "👋 <b>FEORA SEARCH</b>\n\nПоиск свободных красивых ников для Telegram."
SEARCH_TEXT = "🔎 <b>Поиск ников по фильтрам</b>\n\n5 и 6 значные ники: реальные слова и красивые слияния букв, похожие на английские слова. Бот выдаёт по одному нику с оценкой читабельности. Выбери длину или настрой фильтры."
LOCK5_TEXT = (
    "🔒 <b>Бесплатные поиски закончились</b>\n\n"
    f"На тарифе Free доступно {FREE_LIMIT} поиска 5-буквенных ников. "
    "Оформи подписку, чтобы искать 5 букв без ограничений и открыть фильтры.\n\n"
    "6-буквенные ники доступны с лимитом."
)


def lock6_text(wait: int) -> str:
    return (
        "🔒 <b>Лимит 6-буквенных ников исчерпан</b>\n\n"
        f"На тарифе Free доступно {SIX_LIMIT} ников в час. "
        f"Лимит обновится через <b>{minutes(wait)} мин</b>.\n\n"
        "С подпиской лимита нет."
    )


def sub_text(uid: int) -> str:
    return (
        "💎 <b>Подписка</b>\n\n"
        "<b>Что даёт подписка:</b>\n"
        "• Доступ к фильтрам (начало и конец слова, режим «слова / слияния букв», поиск ника, похожего на твоё слово)\n"
        "• Доступ к поиску 5-буквенных ников без ограничений\n"
        "• Поиск 6-буквенных ников без лимита\n\n"
        "<b>Без подписки (Free):</b>\n"
        f"• 5 букв: {FREE_LIMIT} поиска, дальше нужна подписка\n"
        f"• 6 букв: {SIX_LIMIT} ников в час. Если лимит израсходован полностью, через час он обновляется "
        f"на {SIX_LIMIT} ников. Если лимит не потрачен до конца, новые не добавляются\n"
        "• Фильтры закрыты\n\n"
        "<b>Расценки:</b>\n"
        "1 день — 40 ⭐ / 70 ₽\n"
        "7 дней — 150 ⭐ / 200 ₽\n"
        "Месяц — 400 ⭐ / 500 ₽\n"
        "Навсегда — 650 ⭐ / 850 ₽\n\n"
        "<b>Как купить:</b> нажми кнопку ниже, напиши в личку нужный тариф и оплати. "
        "После оплаты подписка будет выдана на твой аккаунт.\n\n"
        f"{status_line(uid)}"
    )


def get_filters(context: ContextTypes.DEFAULT_TYPE) -> dict:
    return context.user_data.setdefault("f", {"prefix": "", "suffix": "", "mode": "all", "like": ""})


MODE_NAMES = {"all": "Всё", "words": "Слова", "blends": "Слияния букв"}


def filters_text(f: dict) -> str:
    return (
        "⚙️ <b>Фильтры</b>\n\n"
        f"Начало слова: <b>{html.escape(f['prefix']) or '—'}</b>\n"
        f"Конец слова: <b>{html.escape(f['suffix']) or '—'}</b>\n"
        f"Похоже на слово: <b>{html.escape(f.get('like', '')) or '—'}</b>\n"
        f"Режим: <b>{MODE_NAMES[f.get('mode', 'all')]}</b>\n\n"
        "Режимы: «Слова» ищет реальные английские слова, «Слияния букв» красивые произносимые сочетания, «Всё» и то и другое."
    )


async def safe_edit(q, text, kb):
    try:
        await q.edit_message_text(text, reply_markup=kb, parse_mode="HTML")
    except BadRequest:
        pass   # "message is not modified"


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    is_new = get_user(user.id) is None
    touch_user(user)
    check_admin(user)
    debug(f"{'🆕 НОВЫЙ' if is_new else '↩️ повторно'} /start: {ulabel(user)}")
    await update.message.reply_text(MAIN_TEXT, reply_markup=main_kb(user.id), parse_mode="HTML")


async def do_search(q, context: ContextTypes.DEFAULT_TYPE, length: int, new_message: bool):
    """Один поиск: выдаёт один ник. new_message=True - результат приходит новым сообщением
    (старый найденный ник остаётся в чате)."""
    uid = q.from_user.id
    f = get_filters(context)
    is_admin = uid in ADMIN_IDS

    if context.user_data.get("busy"):
        await q.answer("Подожди, поиск ещё идёт")
        return
    cd = COOLDOWN - (time.monotonic() - context.user_data.get("last", -1000.0))
    if cd > 0 and not is_admin:
        await q.answer(f"Подожди ещё {math.ceil(cd)} сек.")
        return

    state = {"msg": None}

    async def show(text, kb):
        if new_message:
            if state["msg"] is None:
                state["msg"] = await q.message.reply_text(text, reply_markup=kb, parse_mode="HTML")
            else:
                try:
                    await state["msg"].edit_text(text, reply_markup=kb, parse_mode="HTML")
                except BadRequest:
                    pass
        else:
            await safe_edit(q, text, kb)

    premium = is_premium(uid)
    if not premium:
        if length == 5 and free_left(uid) <= 0:
            await q.answer()
            await show(LOCK5_TEXT, lock_kb())
            return
        if length == 6:
            left6, wait6 = six_status(uid)
            if left6 <= 0:
                await q.answer()
                await show(lock6_text(wait6), lock_kb())
                return

    await q.answer()
    context.user_data["busy"] = True
    prefix, suffix = (f["prefix"], f["suffix"]) if premium else ("", "")
    mode, like = (f.get("mode", "all"), f.get("like", "")) if premium else ("all", "")
    seen = context.user_data.setdefault("seen", set())
    try:
        await show(f"⏳ Ищу {length}-буквенный ник, это займёт до {TIME_LIMIT} секунд...", None)
        found, checked, total = await search(length, 1, prefix, suffix, mode, like, seen)
    finally:
        context.user_data["busy"] = False
        context.user_data["last"] = time.monotonic()

    debug(
        f"🔎 {ulabel(q.from_user)} | {length} букв | "
        + (f"найден @{found[0]}" if found else "не найдено")
        + f" | проверено {checked} из {total}"
        + (f" | фильтры: {html.escape(prefix)}*{html.escape(suffix)}" if (prefix or suffix) else "")
    )

    if found:
        name = found[0]
        if len(seen) > 300:
            seen.clear()
        seen.add(name)
        if not premium:
            if length == 5:
                use_free(uid)
            else:
                use_six(uid)
        text = nick_card(name, like)
        if not premium:
            if length == 5:
                text += f"\n\n🎁 Осталось бесплатных поисков 5 букв: {free_left(uid)} из {FREE_LIMIT}"
            else:
                l6, w6 = six_status(uid)
                text += f"\n\n🎁 Осталось 6-буквенных ников: {l6} из {SIX_LIMIT} в час"
                if l6 <= 0:
                    text += f" (обновится через {minutes(w6)} мин)"
        kb = found_kb(length, name)
    else:
        text = f"😕 {length} букв: ничего не нашлось (проверено {checked} из {total}).\nЛимит не потрачен, попробуй ещё раз."
        if total == 0 and like:
            text += "\nПод это слово не удалось подобрать варианты, попробуй другое слово или сними другие фильтры."
        kb = notfound_kb(length)
    left = int(FLOOD_UNTIL - time.time())
    if left > 0:
        text += f"\n\n⚠️ Telegram временно ограничил проверки, подожди ~{left} сек."
    await show(text, kb)


# ---------------------- админ-панель ----------------------
ADM_BACK = InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Админ-панель", callback_data="adm:menu")]])
DUR_HELP = "Срок: дни (7 или 7d), часы (5h), минуты (30m), можно вместе: 1d12h30m, или forever."


def adm_kb():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📊 Статистика", callback_data="adm:stats"),
         InlineKeyboardButton("👥 Подписчики", callback_data="adm:list")],
        [InlineKeyboardButton("➕ Выдать", callback_data="adm:give"),
         InlineKeyboardButton("➖ Забрать", callback_data="adm:revoke")],
        [InlineKeyboardButton("ℹ️ Инфо о пользователе", callback_data="adm:info")],
        [InlineKeyboardButton("📣 Рассылка", callback_data="adm:bc")],
        [InlineKeyboardButton(f"🐞 Отладка: {'ВКЛ' if DEBUG_ON else 'ВЫКЛ'}", callback_data="adm:debug")],
        [InlineKeyboardButton("🧹 Сбросить кэш ников", callback_data="adm:clear")],
        [InlineKeyboardButton("⬅️ В меню", callback_data="menu:main")],
    ])


ADM_TEXT = (
    "🛠 <b>Админ-панель</b>\n\n"
    "Команды: <code>/give @user 7</code>, <code>/revoke @user</code>, <code>/info @user</code>, <code>/admin</code>\n"
    + DUR_HELP
)


def stats_text() -> str:
    now = int(time.time())
    total = db("SELECT COUNT(*) FROM users", fetch=True)[0][0]
    active = db("SELECT COUNT(*) FROM users WHERE forever=1 OR premium_until>?", (now,), fetch=True)[0][0]
    forever = db("SELECT COUNT(*) FROM users WHERE forever=1", fetch=True)[0][0]
    flood = int(FLOOD_UNTIL - time.time())
    return (
        "📊 <b>Статистика</b>\n\n"
        f"Пользователей: <b>{total}</b>\n"
        f"С подпиской: <b>{active}</b> (навсегда: {forever})\n"
        f"На Free: <b>{total - active}</b>\n"
        f"Слов в базе: {len(WORDS)}\n"
        f"Кэш занятых ников: {len(TAKEN)}\n"
        f"Проверка профиля: {'подключена' if TG else 'отключена'}"
        + (f", лимит Telegram ещё {flood} сек." if flood > 0 else "") + "\n"
        f"Отладка: {'вкл' if DEBUG_ON else 'выкл'}\n"
        f"Работает: {fmt_duration(time.time() - START_TIME)}"
    )


def list_text() -> str:
    rows = db("SELECT id FROM users WHERE forever=1 OR premium_until>? ORDER BY forever DESC, premium_until DESC LIMIT 40",
              (int(time.time()),), fetch=True)
    if not rows:
        return "👥 Пользователей с подпиской нет."
    return "👥 <b>Подписчики</b> (до 40):\n\n" + "\n".join(
        html.escape(f"{label(uid)}: {describe(uid)}") for (uid,) in rows)


async def admin_give(target: str, dur: str) -> str:
    uid = await aresolve_user(target)
    if uid is None:
        return "Пользователь не найден. Укажи числовой ID или @username."
    try:
        seconds = parse_duration(dur)
    except ValueError:
        return "Не понял срок. " + DUR_HELP
    grant(uid, seconds)
    term = "навсегда" if seconds is None else "на " + fmt_duration(seconds)
    try:
        await BOT.send_message(uid, f"🎉 Тебе выдана подписка {term}. Нажми /start, чтобы пользоваться.")
        sent = ""
    except Exception:
        sent = "\n(Уведомление не отправлено: пользователь ещё не запускал бота.)"
    return f"✅ Подписка выдана: {html.escape(label(uid))} {term}.\n{html.escape(describe(uid))}{sent}"


async def admin_revoke(target: str) -> str:
    uid = await aresolve_user(target)
    if uid is None:
        return "Пользователь не найден."
    revoke(uid)
    return f"✅ Подписка снята: {html.escape(label(uid))}"


async def admin_info(target: str) -> str:
    uid = await aresolve_user(target)
    if uid is None:
        return "Пользователь не найден."
    return f"ℹ️ {html.escape(label(uid))}: {html.escape(describe(uid))}"


async def admin_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not check_admin(update.effective_user):
        return
    cmd = update.message.text.split()[0].lstrip("/").split("@")[0].lower()
    a = context.args
    if cmd == "admin":
        await update.message.reply_text(ADM_TEXT, reply_markup=adm_kb(), parse_mode="HTML")
    elif cmd == "give" and len(a) == 2:
        await update.message.reply_text(await admin_give(a[0], a[1]), parse_mode="HTML")
    elif cmd == "revoke" and len(a) == 1:
        await update.message.reply_text(await admin_revoke(a[0]), parse_mode="HTML")
    elif cmd == "info" and len(a) == 1:
        await update.message.reply_text(await admin_info(a[0]), parse_mode="HTML")
    else:
        await update.message.reply_text("Примеры: /give @user 7, /give 123456 5h, /revoke @user, /info @user")


async def admin_callback(q, context: ContextTypes.DEFAULT_TYPE, data: str):
    global DEBUG_ON
    await q.answer()
    action = data.split(":")[1]
    context.user_data.pop("adm_await", None)

    if action == "menu":
        await safe_edit(q, ADM_TEXT, adm_kb())
    elif action == "stats":
        await safe_edit(q, stats_text(), ADM_BACK)
    elif action == "list":
        await safe_edit(q, list_text(), ADM_BACK)
    elif action == "give":
        context.user_data["adm_await"] = "give"
        await safe_edit(q, "➕ Отправь ID или @username и срок через пробел.\n"
                           "Примеры: <code>@user 7</code>, <code>123456 5h</code>, <code>@user forever</code>\n" + DUR_HELP, ADM_BACK)
    elif action == "revoke":
        context.user_data["adm_await"] = "revoke"
        await safe_edit(q, "➖ Отправь ID или @username, у кого забрать подписку.", ADM_BACK)
    elif action == "info":
        context.user_data["adm_await"] = "info"
        await safe_edit(q, "ℹ️ Отправь ID или @username.", ADM_BACK)
    elif action == "bc":
        context.user_data["adm_await"] = "broadcast"
        await safe_edit(q, "📣 Отправь текст рассылки одним сообщением (обычный текст). Перед отправкой покажу предпросмотр.", ADM_BACK)
    elif action == "bcgo":
        text = context.user_data.pop("bc_text", None)
        if not text:
            await safe_edit(q, "Нет текста для рассылки.", ADM_BACK)
            return
        ids = [r[0] for r in db("SELECT id FROM users", fetch=True)]
        await safe_edit(q, f"📣 Отправляю {len(ids)} пользователям...", None)
        ok = fail = 0
        for uid in ids:
            try:
                await BOT.send_message(uid, text)
                ok += 1
            except Exception:
                fail += 1
            await asyncio.sleep(0.06)
        debug(f"📣 Рассылка завершена: доставлено {ok}, не доставлено {fail}")
        await safe_edit(q, f"📣 Готово. Доставлено: <b>{ok}</b>, не доставлено: <b>{fail}</b>.", ADM_BACK)
    elif action == "bccancel":
        context.user_data.pop("bc_text", None)
        await safe_edit(q, ADM_TEXT, adm_kb())
    elif action == "debug":
        DEBUG_ON = not DEBUG_ON
        await safe_edit(q, ADM_TEXT, adm_kb())
    elif action == "clear":
        TAKEN.clear()
        await safe_edit(q, "🧹 Кэш занятых ников очищен.", ADM_BACK)


async def admin_text(update: Update, context: ContextTypes.DEFAULT_TYPE, mode: str) -> bool:
    """Обработка текста, который админ отправил в ответ на запрос панели. True - обработано."""
    text = update.message.text.strip()
    parts = text.split()
    if mode == "give":
        if len(parts) != 2:
            await update.message.reply_text("Нужно два значения: ID или @username и срок. Например: @user 7")
            return True
        context.user_data.pop("adm_await", None)
        await update.message.reply_text(await admin_give(parts[0], parts[1]), reply_markup=ADM_BACK, parse_mode="HTML")
    elif mode in ("revoke", "info"):
        if len(parts) != 1:
            await update.message.reply_text("Нужен один ID или @username.")
            return True
        context.user_data.pop("adm_await", None)
        res = await (admin_revoke(parts[0]) if mode == "revoke" else admin_info(parts[0]))
        await update.message.reply_text(res, reply_markup=ADM_BACK, parse_mode="HTML")
    elif mode == "broadcast":
        context.user_data.pop("adm_await", None)
        context.user_data["bc_text"] = text
        n = db("SELECT COUNT(*) FROM users", fetch=True)[0][0]
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("✅ Отправить", callback_data="adm:bcgo"),
                                    InlineKeyboardButton("❌ Отмена", callback_data="adm:bccancel")]])
        await update.message.reply_text(f"Рассылка уйдёт <b>{n}</b> пользователям:\n\n{html.escape(text)}",
                                        reply_markup=kb, parse_mode="HTML")
    else:
        return False
    return True


# ---------------------- обработчики ----------------------
async def on_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    data = q.data
    uid = q.from_user.id
    touch_user(q.from_user)
    check_admin(q.from_user)
    f = get_filters(context)

    if data.startswith("adm:"):
        if uid not in ADMIN_IDS:
            await q.answer("Нет доступа", show_alert=True)
            return
        await admin_callback(q, context, data)
        return

    if data.startswith("search:") or data.startswith("again:"):
        await do_search(q, context, int(data.split(":")[1]), new_message=data.startswith("again:"))
        return

    # --- фильтры только по подписке ---
    if (data == "menu:filters" or data.startswith("flt:")) and not is_premium(uid):
        await q.answer("🔒 Фильтры доступны только по подписке", show_alert=True)
        return

    await q.answer()

    if data == "menu:main":
        context.user_data.pop("await", None)
        await safe_edit(q, MAIN_TEXT, main_kb(uid))
    elif data == "menu:search":
        context.user_data.pop("await", None)
        await safe_edit(q, SEARCH_TEXT + "\n\n" + status_line(uid), search_kb(is_premium(uid)))
    elif data == "menu:sub":
        await safe_edit(q, sub_text(uid), sub_kb())
    elif data == "menu:filters":
        context.user_data.pop("await", None)
        await safe_edit(q, filters_text(f), filters_kb(f))
    elif data == "flt:prefix":
        context.user_data["await"] = "prefix"
        await safe_edit(q, "Отправь, с чего должен начинаться ник (английские буквы, до 4), например <b>st</b>.\nЧтобы убрать фильтр, отправь <b>-</b>",
                        InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Отмена", callback_data="menu:filters")]]))
    elif data == "flt:suffix":
        context.user_data["await"] = "suffix"
        await safe_edit(q, "Отправь, чем должен заканчиваться ник (английские буквы, до 4), например <b>er</b>.\nЧтобы убрать фильтр, отправь <b>-</b>",
                        InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Отмена", callback_data="menu:filters")]]))
    elif data == "flt:like":
        context.user_data["await"] = "like"
        await safe_edit(q, "Отправь английское слово (3-12 букв), на которое должен быть похож ник, например <b>phoenix</b>.\nЧтобы убрать фильтр, отправь <b>-</b>",
                        InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Отмена", callback_data="menu:filters")]]))
    elif data == "flt:mode":
        order = ["all", "words", "blends"]
        f["mode"] = order[(order.index(f.get("mode", "all")) + 1) % len(order)]
        await safe_edit(q, filters_text(f), filters_kb(f))
    elif data == "flt:reset":
        f.update({"prefix": "", "suffix": "", "mode": "all", "like": ""})
        await safe_edit(q, filters_text(f), filters_kb(f))


async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    adm_mode = context.user_data.get("adm_await")
    if adm_mode and check_admin(user):
        if await admin_text(update, context, adm_mode):
            return

    mode = context.user_data.get("await")
    if not mode or not is_premium(user.id):
        return
    f = get_filters(context)
    value = update.message.text.strip().lower()
    minlen, maxlen = (3, 12) if mode == "like" else (1, 4)
    if value == "-":
        value = ""
    elif not (value.isalpha() and value.isascii() and minlen <= len(value) <= maxlen):
        await update.message.reply_text(f"Нужны только английские буквы, от {minlen} до {maxlen}. Попробуй ещё раз или отправь - чтобы убрать фильтр.")
        return
    f[mode] = value
    context.user_data.pop("await", None)
    await update.message.reply_text(filters_text(f), reply_markup=filters_kb(f), parse_mode="HTML")


async def check(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not check_admin(update.effective_user):
        return
    if not context.args:
        await update.message.reply_text("Использование: /check ник")
        return
    name = context.args[0].lstrip("@").lower()
    async with httpx.AsyncClient(headers=HEADERS, timeout=5, follow_redirects=True) as c:
        free = await check_tme(c, name)
        listed = await check_fragment(c, name) if free else None
    tme = {True: "свободен", False: "занят", None: "не удалось проверить"}[free]
    frag = {True: "выставлен", False: "не выставлен", None: "-"}[listed]
    if TG is None:
        setl = "проверка отключена (нет API_ID/API_HASH)"
    else:
        s = await check_settable(name)
        setl = {True: "можно поставить", False: "нельзя поставить", None: "не удалось проверить"}[s]
    await update.message.reply_text(f"@{name}\nt.me: {tme}\nFragment: {frag}\nВ профиль: {setl}")


async def on_error(update, context: ContextTypes.DEFAULT_TYPE):
    err = context.error
    tb = "".join(traceback.format_exception(type(err), err, err.__traceback__))
    who = ulabel(update.effective_user) if isinstance(update, Update) and update.effective_user else "—"
    debug(f"❗ <b>Ошибка</b> (пользователь: {who})\n<pre>{html.escape(tb[-3000:])}</pre>")


# ---------------------- консоль администратора ----------------------
CONSOLE_HELP = (
    "Команды (вводи прямо в это окно, то же самое можно делать в Telegram через /admin):\n"
    "  give <id или @username> <срок>              выдать подписку (например: give @user 7  /  give 123456 5h  /  give @user forever)\n"
    "  revoke <id или @username>                   забрать подписку\n"
    "  info <id или @username>                     информация о пользователе\n"
    "  list                                        все пользователи с подпиской\n"
    "  help                                        эта справка\n"
    "Срок: 7 или 7d = дни, 5h = часы, 30m = минуты, можно вместе: 1d12h30m. forever = навсегда.\n"
    "Тарифы: 1 день = 1, 7 дней = 7, месяц = 30."
)


def notify(uid: int, text: str) -> bool:
    try:
        asyncio.run_coroutine_threadsafe(BOT.send_message(uid, text, parse_mode="HTML"), LOOP).result(10)
        return True
    except Exception:
        return False


def console_loop():
    print("\n=== Консоль администратора ===")
    print(CONSOLE_HELP)
    while True:
        try:
            line = input()
        except (EOFError, KeyboardInterrupt):
            return
        parts = line.split()
        if not parts:
            continue
        cmd = parts[0].lower()
        try:
            if cmd == "help":
                print(CONSOLE_HELP)
            elif cmd == "give" and len(parts) == 3:
                uid = resolve_user(parts[1])
                if uid is None:
                    print("Пользователь не найден. Укажи числовой ID или @username (если он есть в Telegram).")
                    continue
                try:
                    seconds = parse_duration(parts[2])
                except ValueError:
                    print("Срок: например 7 или 7d (дни), 5h (часы), 30m (минуты), 1d12h, forever")
                    continue
                grant(uid, seconds)
                term = "навсегда" if seconds is None else "на " + fmt_duration(seconds)
                sent = notify(uid, f"🎉 Тебе выдана подписка {term}. Нажми /start, чтобы пользоваться.")
                debug(f"Консоль: выдана подписка {html.escape(label(uid))} {term}. {html.escape(describe(uid))}."
                      + ("" if sent else " (Уведомление не отправлено: пользователь ещё не запускал бота.)"))
            elif cmd == "revoke" and len(parts) == 2:
                uid = resolve_user(parts[1])
                if uid is None:
                    print("Пользователь не найден.")
                    continue
                revoke(uid)
                debug(f"Консоль: подписка снята {html.escape(label(uid))}")
            elif cmd == "info" and len(parts) == 2:
                uid = resolve_user(parts[1])
                print(f"{label(uid)}: {describe(uid)}" if uid else "Пользователь не найден.")
            elif cmd == "list":
                rows = db("SELECT id FROM users WHERE forever=1 OR premium_until>?", (int(time.time()),), fetch=True)
                if not rows:
                    print("Пользователей с подпиской нет.")
                for (uid,) in rows:
                    print(f"{label(uid)}: {describe(uid)}")
            else:
                print("Неизвестная команда. Введи help")
        except Exception as e:
            print(f"Ошибка: {e}")


# ---------------------- запуск ----------------------
async def post_init(app):
    global TG, LOOP, BOT
    LOOP = asyncio.get_running_loop()
    BOT = app.bot
    await load_words()
    print(f"Слов загружено: {len(WORDS)}")
    if USE_TG:
        TG = TelegramClient(SESSION, API_ID, API_HASH)
        await TG.connect()
        print("Проверка через аккаунт Telegram подключена")
        # заранее находим ID администраторов по юзернейму, чтобы отладка пришла сразу
        for name in ADMIN_USERNAMES:
            if db("SELECT id FROM admins WHERE username=?", (name,), fetch=True):
                continue
            try:
                ent = await asyncio.wait_for(TG.get_entity(name), 15)
                if isinstance(ent, User):
                    bind_admin(ent.id, name)
            except Exception:
                pass
    else:
        print("API_ID/API_HASH не заданы: проверка 'можно ли поставить в профиль' отключена")
    if not ADMIN_IDS:
        print(f"Администратор ещё не привязан: открой бота с аккаунта @{ADMIN_USERNAMES[0]} и нажми /start")
    debug(f"✅ Бот запущен. Слов: {len(WORDS)}, проверка профиля: {'вкл' if TG else 'выкл'}")
    threading.Thread(target=console_loop, daemon=True).start()


async def post_shutdown(app):
    if TG:
        await TG.disconnect()


def ensure_login():
    c = TelegramClient(SESSION, API_ID, API_HASH)
    c.start()
    c.disconnect()


def main():
    init_db()
    if USE_TG:
        ensure_login()
    app = (
        ApplicationBuilder()
        .token(TOKEN)
        .post_init(post_init)
        .post_shutdown(post_shutdown)
        .build()
    )
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("check", check))
    app.add_handler(CommandHandler(["admin", "give", "revoke", "info"], admin_command))
    app.add_handler(CallbackQueryHandler(on_button))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.add_error_handler(on_error)
    app.run_polling()


if __name__ == "__main__":
    main()
