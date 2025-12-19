import logging
import os
import re
import asyncio
import json
import base64
import time
import subprocess
import threading
from pathlib import Path
from urllib.parse import parse_qs, urlencode, urlparse, urlunparse
import urllib.request

from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, InputMediaPhoto, LabeledPrice, Update
from telegram.error import BadRequest, NetworkError, TimedOut
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    PreCheckoutQueryHandler,
    filters,
)
from telegram.request import HTTPXRequest
import yt_dlp
from yt_dlp.utils import DownloadError
import imageio_ffmpeg


logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger(__name__)
logging.getLogger("httpx").setLevel(logging.WARNING)
logging.getLogger("httpcore").setLevel(logging.CRITICAL)
logging.getLogger("telegram").setLevel(logging.CRITICAL)
logging.getLogger("telegram.ext").setLevel(logging.CRITICAL)

DOWNLOAD_DIR = Path("downloads")
DOWNLOAD_DIR.mkdir(parents=True, exist_ok=True)

MAX_FILE_SIZE_BYTES = 50 * 1024 * 1024  # ~50 Mo
IMAGE_EXTENSIONS = {"jpg", "jpeg", "png", "webp", "bmp"}

BOT_USERNAME = os.getenv("BOT_USERNAME")
SHARE_PROMPTED_CHATS: set[int] = set()

TIKTOK_FILE_ID_CACHE: dict[str, str] = {}
TIKTOK_FILE_ID_CACHE_MAX = 200

USER_STORE_PATH = Path("user_store.json")
USER_STORE_LOCK = asyncio.Lock()

PREMIUM_DURATION_SECONDS = 30 * 24 * 60 * 60
PREMIUM_30D_STARS = 299
CREDITS_10_STARS = 99
CREDITS_50_STARS = 399
FREE_EFFECTS_PER_DAY = 2
AD_EVERY_SUCCESS_COUNT = 5

def _int_env(name: str, default: int) -> int:
    raw = os.getenv(name)
    if not raw:
        return default
    try:
        v = int(raw)
    except ValueError:
        return default
    return v if v > 0 else default

MAX_CONCURRENT_DOWNLOADS = _int_env("MAX_CONCURRENT_DOWNLOADS", 1)
MAX_CONCURRENT_FFMPEG_JOBS = _int_env("MAX_CONCURRENT_FFMPEG_JOBS", 1)
CLEANUP_DOWNLOADS_MAX_AGE_HOURS = _int_env("CLEANUP_DOWNLOADS_MAX_AGE_HOURS", 72)

DOWNLOAD_SEMAPHORE = asyncio.Semaphore(MAX_CONCURRENT_DOWNLOADS)
FFMPEG_SEMAPHORE = asyncio.Semaphore(MAX_CONCURRENT_FFMPEG_JOBS)

_YTDLP_COOKIEFILE_READY = False
_YTDLP_COOKIEFILE: str | None = None


def _get_ytdlp_cookiefile() -> str | None:
    global _YTDLP_COOKIEFILE_READY
    global _YTDLP_COOKIEFILE

    def _split_netscape_fields(line: str) -> list[str] | None:
        s = line.strip("\r\n")
        if not s:
            return None
        if s.startswith("#HttpOnly_"):
            s = s[len("#HttpOnly_") :]
            http_only = True
        else:
            http_only = False
        if s.lstrip().startswith("#"):
            return None
        parts = s.split("\t")
        if len(parts) < 7:
            parts = re.split(r"\s+", s.strip())
        if len(parts) < 7:
            return None
        if len(parts) > 7:
            parts = parts[:6] + [" ".join(parts[6:])]
        if http_only:
            parts[0] = "#HttpOnly_" + parts[0]
        return parts

    def _looks_like_netscape(text: str) -> bool:
        for line in text.splitlines():
            if _split_netscape_fields(line) is not None:
                return True
        return False

    def _normalize_netscape_text(text: str) -> str:
        stripped = text.lstrip()
        json_candidate: str | None = None

        if stripped.startswith("\"") or stripped.startswith("'"):
            q = stripped[0]
            if stripped.endswith(q) and len(stripped) >= 2:
                json_candidate = stripped[1:-1]
        if json_candidate is None:
            json_candidate = stripped

        data = None
        if json_candidate.startswith("[") or json_candidate.startswith("{"):
            try:
                data = json.loads(json_candidate)
            except Exception:
                data = None
        elif ("[" in json_candidate) or ("{" in json_candidate):
            idxs = [i for i in (json_candidate.find("["), json_candidate.find("{")) if i >= 0]
            start = min(idxs) if idxs else -1
            if start >= 0:
                try:
                    data = json.loads(json_candidate[start:])
                except Exception:
                    data = None

        if data is not None:
            cookies: list[dict] = []
            if isinstance(data, list):
                cookies = [c for c in data if isinstance(c, dict)]
            elif isinstance(data, dict):
                if isinstance(data.get("cookies"), list):
                    cookies = [c for c in data.get("cookies") if isinstance(c, dict)]
                else:
                    cookies = [data] if isinstance(data, dict) else []

            if cookies:
                lines: list[str] = []
                for c in cookies:
                    domain = c.get("domain")
                    name = c.get("name")
                    if not isinstance(domain, str) or not domain.strip():
                        continue
                    if not isinstance(name, str) or not name:
                        continue
                    domain = domain.strip()
                    include_subdomains = "TRUE" if domain.startswith(".") else "FALSE"
                    path = c.get("path")
                    path = path if isinstance(path, str) and path else "/"
                    secure = "TRUE" if bool(c.get("secure")) else "FALSE"
                    expiry = c.get("expirationDate")
                    if not isinstance(expiry, (int, float)):
                        expiry = c.get("expires")
                    if not isinstance(expiry, (int, float)):
                        expiry = 0
                    value = c.get("value")
                    value = value if isinstance(value, str) else ""
                    http_only = bool(c.get("httpOnly") or c.get("httponly") or c.get("http_only"))
                    domain_field = ("#HttpOnly_" + domain) if http_only else domain
                    lines.append(
                        "\t".join(
                            [
                                domain_field,
                                include_subdomains,
                                path,
                                secure,
                                str(int(expiry)),
                                name,
                                value,
                            ]
                        )
                    )
                out_text = "\n".join(lines)
                if not out_text.endswith("\n"):
                    out_text += "\n"
                return out_text

        had_trailing_nl = text.endswith("\n")
        lines: list[str] = []
        for line in text.splitlines():
            if not line:
                lines.append(line)
                continue
            if line.lstrip().startswith("#") and not line.startswith("#HttpOnly_"):
                lines.append(line)
                continue
            parts = _split_netscape_fields(line)
            if parts is None:
                lines.append(line)
                continue
            lines.append("\t".join(parts))
        out_text = "\n".join(lines)
        if had_trailing_nl and not out_text.endswith("\n"):
            out_text += "\n"
        return out_text

    if _YTDLP_COOKIEFILE_READY:
        return _YTDLP_COOKIEFILE

    _YTDLP_COOKIEFILE_READY = True

    cookie_path = os.getenv("YTDLP_COOKIES_PATH")
    if cookie_path and os.path.exists(cookie_path):
        try:
            txt = Path(cookie_path).read_text(encoding="utf-8", errors="ignore")
            if _looks_like_netscape(txt):
                _YTDLP_COOKIEFILE = cookie_path
                return _YTDLP_COOKIEFILE
            logger.warning("yt-dlp cookies path: invalid Netscape format; ignoring")
        except OSError:
            pass
        _YTDLP_COOKIEFILE = None
        return None

    raw = os.getenv("YTDLP_COOKIES")
    if not raw:
        _YTDLP_COOKIEFILE = None
        return None

    raw = raw.strip()
    if raw.lower().startswith("base64:"):
        b64 = raw.split(":", 1)[1].strip()
        try:
            raw = base64.b64decode(b64).decode("utf-8", errors="ignore")
        except Exception:
            _YTDLP_COOKIEFILE = None
            return None

    if "\\n" in raw and "\n" not in raw:
        raw = raw.replace("\\n", "\n")

    if "\\t" in raw and "\t" not in raw:
        raw = raw.replace("\\t", "\t")

    raw = _normalize_netscape_text(raw)
    if "# netscape http cookie file" not in raw.lower():
        raw = "# Netscape HTTP Cookie File\n" + raw

    out = DOWNLOAD_DIR / "ytdlp_cookies.txt"
    try:
        out.write_text(raw, encoding="utf-8")
    except OSError:
        _YTDLP_COOKIEFILE = None
        return None

    try:
        size = out.stat().st_size
        sample = out.read_text(encoding="utf-8", errors="ignore")[:20000]
        lower = sample.lower()
        has_netscape = _looks_like_netscape(sample)
        has_youtube = "youtube.com" in lower
        has_google = "google.com" in lower

        needed = [
            "sid",
            "hsid",
            "ssid",
            "apisid",
            "sapisid",
            "__secure-1psid",
            "__secure-3psid",
            "visitor_info1_live",
        ]
        present = [k for k in needed if k in lower]
        has_auth = bool(present)
        logger.info(
            "yt-dlp cookies file: size=%d bytes, netscape=%s, youtube=%s, google=%s, auth=%s, auth_keys=%s",
            int(size),
            "yes" if has_netscape else "no",
            "yes" if has_youtube else "no",
            "yes" if has_google else "no",
            "yes" if has_auth else "no",
            ",".join(present) if present else "-",
        )
    except OSError:
        pass

    try:
        full = out.read_text(encoding="utf-8", errors="ignore")
        if not _looks_like_netscape(full):
            logger.warning("yt-dlp cookies: invalid Netscape format; ignoring")
            try:
                non_comment: list[str] = []
                for ln in full.splitlines():
                    s = ln.strip("\r\n")
                    if not s:
                        continue
                    if s.lstrip().startswith("#") and not s.startswith("#HttpOnly_"):
                        continue
                    non_comment.append(s[:300])
                    if len(non_comment) >= 5:
                        break
                if non_comment:
                    logger.info("yt-dlp cookies: first non-comment lines: %s", " | ".join(non_comment))
            except Exception:
                pass
            try:
                out.unlink()
            except OSError:
                pass
            _YTDLP_COOKIEFILE = None
            return None
    except OSError:
        _YTDLP_COOKIEFILE = None
        return None

    _YTDLP_COOKIEFILE = str(out)
    return _YTDLP_COOKIEFILE

def _safe_remove(path: str | None) -> None:
    if not isinstance(path, str) or not path:
        return
    try:
        os.remove(path)
    except OSError:
        return

def _cleanup_download_dir_if_needed() -> None:
    if CLEANUP_DOWNLOADS_MAX_AGE_HOURS <= 0:
        return
    if not DOWNLOAD_DIR.exists() or not DOWNLOAD_DIR.is_dir():
        return
    cutoff = time.time() - (CLEANUP_DOWNLOADS_MAX_AGE_HOURS * 3600)
    for p in DOWNLOAD_DIR.iterdir():
        if not p.is_file():
            continue
        try:
            if p.stat().st_mtime >= cutoff:
                continue
        except OSError:
            continue
        _safe_remove(str(p))

def _start_healthcheck_server_if_needed() -> None:
    port_raw = os.getenv("PORT")
    if not port_raw:
        return
    try:
        port = int(port_raw)
    except ValueError:
        return
    if port <= 0:
        return

    class _HealthHandler(BaseHTTPRequestHandler):
        def do_GET(self) -> None:  # noqa: N802
            if self.path in ("/", "/health", "/healthz"):
                self.send_response(200)
                self.send_header("Content-Type", "text/plain; charset=utf-8")
                self.end_headers()
                self.wfile.write(b"ok")
                return
            self.send_response(404)
            self.end_headers()

        def log_message(self, format: str, *args) -> None:  # noqa: A002
            return

    try:
        server = ThreadingHTTPServer(("0.0.0.0", port), _HealthHandler)
    except OSError:
        return

    t = threading.Thread(target=server.serve_forever, daemon=True)
    t.start()


def _today_key() -> str:
    return time.strftime("%Y-%m-%d", time.gmtime())


def _load_user_store_sync() -> dict:
    if not USER_STORE_PATH.exists():
        return {}
    try:
        raw = USER_STORE_PATH.read_text(encoding="utf-8")
        data = json.loads(raw) if raw else {}
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def _save_user_store_sync(store: dict) -> None:
    tmp = USER_STORE_PATH.with_suffix(".tmp")
    tmp.write_text(json.dumps(store, ensure_ascii=False), encoding="utf-8")
    os.replace(tmp, USER_STORE_PATH)


async def _read_user_store() -> dict:
    async with USER_STORE_LOCK:
        return await asyncio.to_thread(_load_user_store_sync)


async def _write_user_store(store: dict) -> None:
    async with USER_STORE_LOCK:
        await asyncio.to_thread(_save_user_store_sync, store)


async def _get_user_record(user_id: int) -> dict:
    if not isinstance(user_id, int) or user_id <= 0:
        return {}
    store = await _read_user_store()
    key = str(user_id)
    rec = store.get(key)
    if not isinstance(rec, dict):
        rec = {}
    return rec


def _is_premium_now(rec: dict) -> bool:
    until = rec.get("premium_until")
    return isinstance(until, (int, float)) and int(until) > int(time.time())


def _get_credits(rec: dict) -> int:
    c = rec.get("credits")
    return int(c) if isinstance(c, (int, float)) and int(c) > 0 else 0


async def _grant_premium(user_id: int, seconds: int) -> None:
    if seconds <= 0:
        return
    async with USER_STORE_LOCK:
        store = await asyncio.to_thread(_load_user_store_sync)
        key = str(user_id)
        rec = store.get(key)
        if not isinstance(rec, dict):
            rec = {}
        now = int(time.time())
        base = int(rec.get("premium_until")) if isinstance(rec.get("premium_until"), (int, float)) else 0
        if base < now:
            base = now
        rec["premium_until"] = base + int(seconds)
        store[key] = rec
        await asyncio.to_thread(_save_user_store_sync, store)


async def _add_credits(user_id: int, amount: int) -> None:
    if amount <= 0:
        return
    async with USER_STORE_LOCK:
        store = await asyncio.to_thread(_load_user_store_sync)
        key = str(user_id)
        rec = store.get(key)
        if not isinstance(rec, dict):
            rec = {}
        cur = int(rec.get("credits")) if isinstance(rec.get("credits"), (int, float)) else 0
        rec["credits"] = max(0, cur + int(amount))
        store[key] = rec
        await asyncio.to_thread(_save_user_store_sync, store)


async def _plan_effect_entitlement(user_id: int) -> str | None:
    async with USER_STORE_LOCK:
        store = await asyncio.to_thread(_load_user_store_sync)
        key = str(user_id)
        rec = store.get(key)
        if not isinstance(rec, dict):
            rec = {}

        if _is_premium_now(rec):
            return "premium"

        today = _today_key()
        used_day = rec.get("effects_free_day")
        used_count = rec.get("effects_free_used")
        if used_day != today:
            used_count = 0
        used_count = int(used_count) if isinstance(used_count, (int, float)) else 0
        if used_count < FREE_EFFECTS_PER_DAY:
            return "free"

        credits = _get_credits(rec)
        if credits > 0:
            return "credit"

        return None


async def _finalize_effect_entitlement(user_id: int, kind: str | None) -> None:
    if kind not in ("premium", "free", "credit"):
        return
    if kind == "premium":
        return
    async with USER_STORE_LOCK:
        store = await asyncio.to_thread(_load_user_store_sync)
        key = str(user_id)
        rec = store.get(key)
        if not isinstance(rec, dict):
            rec = {}

        today = _today_key()
        used_day = rec.get("effects_free_day")
        used_count = rec.get("effects_free_used")
        if used_day != today:
            used_day = today
            used_count = 0
        used_count = int(used_count) if isinstance(used_count, (int, float)) else 0

        if kind == "free":
            rec["effects_free_day"] = used_day
            rec["effects_free_used"] = used_count + 1
        elif kind == "credit":
            credits = _get_credits(rec)
            rec["credits"] = max(0, credits - 1)

        store[key] = rec
        await asyncio.to_thread(_save_user_store_sync, store)


async def _bump_success_and_should_show_ad(user_id: int) -> bool:
    if AD_EVERY_SUCCESS_COUNT <= 0:
        return False
    async with USER_STORE_LOCK:
        store = await asyncio.to_thread(_load_user_store_sync)
        key = str(user_id)
        rec = store.get(key)
        if not isinstance(rec, dict):
            rec = {}
        cnt = rec.get("success_count")
        cnt = int(cnt) if isinstance(cnt, (int, float)) else 0
        cnt += 1
        rec["success_count"] = cnt
        store[key] = rec
        await asyncio.to_thread(_save_user_store_sync, store)
        return (cnt % AD_EVERY_SUCCESS_COUNT) == 0


def _format_premium_until(ts: int, lang: str) -> str:
    try:
        dt = time.gmtime(int(ts))
        return time.strftime("%d/%m/%Y", dt) if lang == "fr" else time.strftime("%Y-%m-%d", dt)
    except Exception:
        return ""


def _ref_link_for_user(user_id: int) -> str | None:
    bot_link = _get_bot_link()
    if not bot_link:
        return None
    if not isinstance(user_id, int) or user_id <= 0:
        return None
    return bot_link + "?start=" + f"ref_{user_id}"


async def _apply_referral(new_user_id: int, ref_user_id: int) -> bool:
    if not isinstance(new_user_id, int) or not isinstance(ref_user_id, int):
        return False
    if new_user_id <= 0 or ref_user_id <= 0:
        return False
    if new_user_id == ref_user_id:
        return False

    async with USER_STORE_LOCK:
        store = await asyncio.to_thread(_load_user_store_sync)

        new_key = str(new_user_id)
        new_rec = store.get(new_key)
        if not isinstance(new_rec, dict):
            new_rec = {}
        if new_rec.get("referred_by"):
            return False

        new_rec["referred_by"] = str(ref_user_id)
        store[new_key] = new_rec

        ref_key = str(ref_user_id)
        ref_rec = store.get(ref_key)
        if not isinstance(ref_rec, dict):
            ref_rec = {}
        ref_count = ref_rec.get("ref_count")
        ref_count = int(ref_count) if isinstance(ref_count, (int, float)) else 0
        ref_rec["ref_count"] = ref_count + 1
        ref_credits = _get_credits(ref_rec)
        ref_rec["credits"] = ref_credits + 5
        store[ref_key] = ref_rec

        new_credits = _get_credits(new_rec)
        new_rec["credits"] = new_credits + 2
        store[new_key] = new_rec

        await asyncio.to_thread(_save_user_store_sync, store)
        return True


class _YtDlpLogger:
    def debug(self, msg):
        logger.debug("yt-dlp: %s", msg)

    def info(self, msg):
        logger.debug("yt-dlp: %s", msg)

    def warning(self, msg):
        logger.debug("yt-dlp: %s", msg)

    def error(self, msg):
        logger.error("yt-dlp: %s", msg)


COMMON_YDL_OPTS = {
    "quiet": True,
    "no_warnings": True,
    "noprogress": True,
    "logger": _YtDlpLogger(),
    "ffmpeg_location": os.getenv("YTDLP_FFMPEG_LOCATION")
    or imageio_ffmpeg.get_ffmpeg_exe(),
    "http_headers": {
        "User-Agent": os.getenv(
            "YTDLP_USER_AGENT",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0 Safari/537.36",
        ),
        "Accept-Language": os.getenv("YTDLP_ACCEPT_LANGUAGE", "en-US,en;q=0.9,fr;q=0.8"),
    },
}

_cookiefile = _get_ytdlp_cookiefile()
if _cookiefile:
    COMMON_YDL_OPTS["cookiefile"] = _cookiefile
    logger.info("yt-dlp cookies: enabled")
else:
    logger.info("yt-dlp cookies: not configured")


def _is_youtube_antibot_error(error_text: str) -> bool:
    if not isinstance(error_text, str) or not error_text:
        return False
    s = error_text.lower()
    return (
        "sign in to confirm" in s
        or "confirm you’re not a bot" in s
        or "confirm you're not a bot" in s
    )


def _youtube_antibot_user_message(lang: str) -> str:
    if lang == "fr":
        return (
            "⚠️ YouTube bloque ce serveur (vérification anti-bot).\n\n"
            "✅ TikTok/Instagram/Facebook/etc. marchent souvent.\n"
            "❌ Pour YouTube, si tu es l’admin: ajoute des cookies YouTube sur Koyeb "
            "(variable `YTDLP_COOKIES`, format cookies.txt)."
        )
    return (
        "⚠️ YouTube is blocking this server (anti-bot verification).\n\n"
        "✅ TikTok/Instagram/Facebook/etc. often work.\n"
        "❌ For YouTube, if you are the admin: add YouTube cookies on Koyeb "
        "(env var `YTDLP_COOKIES`, cookies.txt format)."
    )


def get_user_lang(update: Update) -> str:
    """Retourne 'fr' si l'utilisateur est en français, sinon 'en'."""
    language_code = None
    if update.effective_user is not None:
        language_code = update.effective_user.language_code
    if language_code and language_code.lower().startswith("fr"):
        return "fr"
    return "en"


def get_message(key: str, lang: str) -> str:
    messages = {
        "start": {
            "fr": (
                "🚀 Téléchargeur vidéo & audio\n\n"
                "🔗 Colle un lien et je m'occupe du reste.\n\n"
                "🧪 Exemple : https://www.youtube.com/watch?v=abc123"
            ),
            "en": (
                "🚀 Video & audio downloader\n\n"
                "🔗 Paste a link and I do the rest.\n\n"
                "🧪 Example: https://www.youtube.com/watch?v=abc123"
            ),
        },
        "help": {
            "fr": (
                "ℹ️ Aide\n\n"
                "✅ Comment télécharger :\n"
                "1) 🔗 Envoie un lien\n"
                "2) 🎬 Vidéo / 🎧 Audio (ou ✨ Effets)\n"
                "3) ⚡ Choisis la qualité (HD/SD)\n"
                "4) 🌍 Langue audio (si dispo)\n"
                "5) 📩 Je t'envoie le fichier\n\n"
                "🆕 Nouvelles fonctionnalités :\n"
                "- 📶 Progression en direct (%, taille, vitesse, ETA)\n"
                "- 🌍 Langue audio (🎧 Original / 🇫🇷 FR / 🇬🇧 EN, selon la vidéo)\n"
                "- ⚡ TikTok rapide: certaines vidéos peuvent partir quasi instant\n"
                "- ✨ Effets: copie le look (couleurs/contraste/saturation) d'une vidéo\n\n"
                "📦 Limite : ~50 Mo par fichier."
            ),
            "en": (
                "ℹ️ Help\n\n"
                "✅ How to download:\n"
                "1) 🔗 Send a link\n"
                "2) 🎬 Video / 🎧 Audio (or ✨ Effects)\n"
                "3) ⚡ Pick quality (HD/SD)\n"
                "4) 🌍 Pick audio language (if available)\n"
                "5) 📩 I send you the file\n\n"
                "🆕 New features:\n"
                "- 📶 Live progress (%, size, speed, ETA)\n"
                "- 🌍 Audio language (🎧 Original / 🇫🇷 FR / 🇬🇧 EN, depends on the video)\n"
                "- ⚡ Fast TikTok: some videos can be sent almost instantly\n"
                "- ✨ Effects: copy the look (colors/contrast/saturation) from a reference\n\n"
                "📦 Limit: ~50 MB per file."
            ),
        },
        "menu": {
            "fr": "🏠 Menu principal :",
            "en": "🏠 Main menu:",
        },
        "supported_sites": {
            "fr": "🌐 Sites supportés : YouTube, X/Twitter, Instagram, Facebook, TikTok.",
            "en": "🌐 Supported sites: YouTube, X/Twitter, Instagram, Facebook, TikTok.",
        },
        "prompt_send_link": {
            "fr": "🔗 Envoie un lien pour commencer.",
            "en": "🔗 Send a link to get started.",
        },
        "share_cta": {
            "fr": "🤝 Si ce bot t'aide, partage-le à un ami :",
            "en": "🤝 If this bot helps you, share it with a friend:",
        },
        "share_button": {
            "fr": "🚀 Partager le bot",
            "en": "🚀 Share the bot",
        },
        "menu_button": {
            "fr": "🏠 Menu",
            "en": "🏠 Menu",
        },
        "help_button": {
            "fr": "ℹ️ Aide",
            "en": "ℹ️ Help",
        },
        "sites_button": {
            "fr": "🌐 Sites",
            "en": "🌐 Sites",
        },
        "premium_button": {
            "fr": "⭐ Premium",
            "en": "⭐ Premium",
        },
        "premium_menu_title": {
            "fr": "⭐ Premium & Crédits",
            "en": "⭐ Premium & Credits",
        },
        "premium_buy_month": {
            "fr": "⭐ Premium 30j",
            "en": "⭐ Premium 30d",
        },
        "premium_buy_credits10": {
            "fr": "🎟️ 10 crédits",
            "en": "🎟️ 10 credits",
        },
        "premium_buy_credits50": {
            "fr": "🎟️ 50 crédits",
            "en": "🎟️ 50 credits",
        },
        "premium_my_ref": {
            "fr": "🎁 Mon lien parrainage",
            "en": "🎁 My referral link",
        },
        "premium_need_more": {
            "fr": "🔒 Cette option est Premium (ou nécessite des crédits).",
            "en": "🔒 This option is Premium (or requires credits).",
        },
        "referral_bonus": {
            "fr": "🎁 Parrainage activé ! Tu gagnes +2 crédits et ton ami +5 crédits.",
            "en": "🎁 Referral activated! You get +2 credits and your friend gets +5 credits.",
        },
        "ad_text": {
            "fr": (
                "📢 Sponsorisé\n"
                "⭐ Passe en Premium pour enlever les pubs + débloquer ✨ Effets illimités."
            ),
            "en": (
                "📢 Sponsored\n"
                "⭐ Go Premium to remove ads + unlock unlimited ✨ Effects."
            ),
        },
        "retry_button": {
            "fr": "🔁 Réessayer",
            "en": "🔁 Retry",
        },
        "try_sd_button": {
            "fr": "⚡ Passer en SD",
            "en": "⚡ Try SD",
        },
        "try_hd_button": {
            "fr": "✨ Passer en HD",
            "en": "✨ Try HD",
        },
        "choose_audio_lang": {
            "fr": "🌍 Choisis la langue de l'audio :",
            "en": "🌍 Choose the audio language:",
        },
        "audio_lang_orig": {
            "fr": "🎧 Original",
            "en": "🎧 Original",
        },
        "audio_lang_fr": {
            "fr": "🇫🇷 Français",
            "en": "🇫🇷 French",
        },
        "audio_lang_en": {
            "fr": "🇬🇧 Anglais",
            "en": "🇬🇧 English",
        },
        "audio_lang_unavailable": {
            "fr": "⚠️ Audio {wanted} indisponible pour cette vidéo. Je garde l'audio 🎧 original.",
            "en": "⚠️ {wanted} audio not available for this video. Keeping 🎧 original audio.",
        },
        "error_try_again": {
            "fr": "❌ Oups, ça n'a pas marché. Tu peux réessayer.",
            "en": "❌ Something went wrong. You can try again.",
        },
        "invalid_url": {
            "fr": (
                "⚠️ Envoie un lien valide (URL commençant par http/https). "
                "Utilise /help si besoin."
            ),
            "en": (
                "⚠️ Please send a valid link (URL starting with http/https). "
                "Use /help if needed."
            ),
        },
        "processing": {
            "fr": "⏳ Téléchargement en cours…",
            "en": "⏳ Downloading…",
        },
        "too_big": {
            "fr": (
                "📦 Vidéo trop grande ({size_mb:.1f} Mo). Essaie une vidéo plus "
                "courte ou de plus basse qualité."
            ),
            "en": (
                "📦 Video is too large ({size_mb:.1f} MB). Try a shorter or "
                "lower-quality video."
            ),
        },
        "cleaned": {
            "fr": "🧹 Fichier supprimé de mon côté pour économiser de l'espace.",
            "en": "🧹 File removed on my side to save space.",
        },
        "choose_type": {
            "fr": "🎛️ Choisis un format :",
            "en": "🎛️ Choose a format:",
        },
        "effects_button": {
            "fr": "✨ Effets",
            "en": "✨ Effects",
        },
        "effects_intro": {
            "fr": "✨ Effets Visuels\n\nChoisis ton mode :",
            "en": "✨ Visual Effects\n\nChoose your mode:",
        },
        "effects_mode_preset": {
            "fr": "🎨 Galerie d'effets",
            "en": "🎨 Effects Gallery",
        },
        "effects_mode_steal": {
            "fr": "🔥 Voler le style d'une vidéo",
            "en": "🔥 Steal video style",
        },
        "effects_choose_preset": {
            "fr": "🎨 Choisis ton effet :",
            "en": "🎨 Choose your effect:",
        },
        "effects_preset_selected": {
            "fr": "✅ Effet sélectionné : {effect_name}\n{effect_desc}\n\n📹 Envoie maintenant ta vidéo pour appliquer l'effet.",
            "en": "✅ Effect selected: {effect_name}\n{effect_desc}\n\n📹 Now send your video to apply the effect.",
        },
        "effects_steal_intro": {
            "fr": "🔥 Mode Vol de Style\n\nEnvoie le lien d'une vidéo dont tu veux copier le look (couleurs, ambiance, contraste).",
            "en": "🔥 Style Stealing Mode\n\nSend the link of a video whose look you want to copy (colors, mood, contrast).",
        },
        "effects_need_ref": {
            "fr": "❌ Erreur : impossible de charger la vidéo de référence.",
            "en": "❌ Error: unable to load reference video.",
        },
        "effects_ready": {
            "fr": "✅ Style capturé ! Envoie maintenant ta vidéo pour appliquer l'effet.",
            "en": "✅ Style captured! Now send your video to apply the effect.",
        },
        "effects_processing": {
            "fr": "⚙️ Application de l'effet en cours…",
            "en": "⚙️ Applying effect…",
        },
        "effects_done": {
            "fr": "✨ Effet appliqué avec succès !",
            "en": "✨ Effect applied successfully!",
        },
        "photo_disabled": {
            "fr": "🚫 Le téléchargement de photos est désactivé sur ce bot.",
            "en": "🚫 Photo downloading is disabled on this bot.",
        },
        "choose_quality": {
            "fr": "🎚️ Choisis la qualité de la vidéo :",
            "en": "🎚️ Choose the video quality:",
        },
        "no_photo": {
            "fr": (
                "🖼️ Aucune photo téléchargeable n'a été trouvée pour ce lien. "
                "(Ex: post uniquement vidéo ou contenu non supporté.)"
            ),
            "en": (
                "🖼️ No downloadable photo was found for this link. "
                "(E.g. video-only post or unsupported content.)"
            ),
        },
        "no_video": {
            "fr": (
                "🎬 Aucune vidéo téléchargeable n'a été trouvée pour ce lien. "
                "(Ex: tweet sans vidéo ou contenu non supporté.)"
            ),
            "en": (
                "🎬 No downloadable video was found for this link. "
                "(E.g. tweet without video or unsupported content.)"
            ),
        },
        "no_url_saved": {
            "fr": (
                "🔗 Je n'ai pas de lien enregistré. Envoie-moi d'abord un lien "
                "vidéo."
            ),
            "en": (
                "🔗 I don't have any link saved. Please send me a video link "
                "first."
            ),
        },
        "error": {
            "fr": (
                "❌ Erreur : {error}\nVérifie le lien ou réessaie. Sites "
                "supportés : YouTube, Twitter, Instagram, Facebook."
            ),
            "en": (
                "❌ Error: {error}\nCheck the link or try again. Supported "
                "sites: YouTube, Twitter, Instagram, Facebook."
            ),
        },
    }
    return messages[key][lang]


def _get_bot_link() -> str | None:
    if not BOT_USERNAME:
        return None
    uname = BOT_USERNAME.strip()
    if uname.startswith("@"):
        uname = uname[1:]
    if not uname:
        return None
    return f"https://t.me/{uname}"


def _maybe_set_bot_username(username: str | None) -> None:
    global BOT_USERNAME
    if BOT_USERNAME:
        return
    if not username or not isinstance(username, str):
        return
    uname = username.strip()
    if uname.startswith("@"):
        uname = uname[1:]
    if not uname:
        return
    BOT_USERNAME = uname


def _get_share_url(lang: str) -> str | None:
    bot_link = _get_bot_link()
    if not bot_link:
        return None
    share_text = (
        "Télécharge tes vidéos facilement ici" if lang == "fr" else "Download videos easily here"
    )
    return "https://t.me/share/url?" + urlencode({"url": bot_link, "text": share_text})


def _ad_keyboard(lang: str) -> InlineKeyboardMarkup:
    share_url = _get_share_url(lang)
    row: list[InlineKeyboardButton] = [
        InlineKeyboardButton(get_message("premium_button", lang), callback_data="menu_premium")
    ]
    if share_url:
        row.append(InlineKeyboardButton(get_message("share_button", lang), url=share_url))
    return InlineKeyboardMarkup([row])


async def _maybe_send_ad_after_success(message, lang: str) -> None:
    chat = getattr(message, "chat", None)
    user_id = None
    if chat and getattr(chat, "type", None) == "private":
        user_id = getattr(chat, "id", None)
    if not isinstance(user_id, int) or user_id <= 0:
        return

    rec = await _get_user_record(user_id)
    if _is_premium_now(rec):
        return

    should = await _bump_success_and_should_show_ad(user_id)
    if not should:
        return

    try:
        await message.reply_text(
            get_message("ad_text", lang),
            reply_markup=_ad_keyboard(lang),
            disable_web_page_preview=True,
        )
    except (BadRequest, TimedOut, NetworkError):
        pass


def _main_menu_keyboard(lang: str) -> InlineKeyboardMarkup:
    share_url = _get_share_url(lang)
    buttons = [
        [
            InlineKeyboardButton(get_message("help_button", lang), callback_data="menu_help"),
            InlineKeyboardButton(get_message("sites_button", lang), callback_data="menu_sites"),
        ]
    ]
    buttons.append(
        [InlineKeyboardButton(get_message("premium_button", lang), callback_data="menu_premium")]
    )
    if share_url:
        buttons.append(
            [
                InlineKeyboardButton(get_message("share_button", lang), url=share_url),
                InlineKeyboardButton(get_message("menu_button", lang), callback_data="menu_main"),
            ]
        )
    else:
        buttons.append(
            [InlineKeyboardButton(get_message("menu_button", lang), callback_data="menu_main")]
        )
    return InlineKeyboardMarkup(buttons)


def _action_keyboard(lang: str, action: str, quality: str | None) -> InlineKeyboardMarkup:
    buttons: list[list[InlineKeyboardButton]] = []
    if action == "video":
        retry_data = f"retry_video_{quality or 'hd'}"
        row: list[InlineKeyboardButton] = [
            InlineKeyboardButton(get_message("retry_button", lang), callback_data=retry_data)
        ]
        if quality == "hd":
            row.append(
                InlineKeyboardButton(get_message("try_sd_button", lang), callback_data="retry_video_sd")
            )
        elif quality == "sd":
            row.append(
                InlineKeyboardButton(get_message("try_hd_button", lang), callback_data="retry_video_hd")
            )
        buttons.append(row)
    elif action == "audio":
        buttons.append(
            [InlineKeyboardButton(get_message("retry_button", lang), callback_data="retry_audio")]
        )
    buttons.append(
        [InlineKeyboardButton(get_message("menu_button", lang), callback_data="menu_main")]
    )
    return InlineKeyboardMarkup(buttons)


async def _maybe_send_share_prompt(message, lang: str) -> None:
    chat_id = getattr(message, "chat_id", None)
    if not isinstance(chat_id, int):
        return
    if chat_id in SHARE_PROMPTED_CHATS:
        return
    keyboard = _main_menu_keyboard(lang)
    if not _get_bot_link():
        return
    await message.reply_text(
        get_message("share_cta", lang),
        reply_markup=keyboard,
        disable_web_page_preview=True,
    )
    SHARE_PROMPTED_CHATS.add(chat_id)


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    _maybe_set_bot_username(getattr(context.bot, "username", None))
    lang = get_user_lang(update)
    msg = update.message or update.effective_message
    if not msg:
        return
    args = getattr(context, "args", None)
    if isinstance(args, list) and args:
        arg0 = args[0]
        if isinstance(arg0, str) and arg0.startswith("ref_"):
            ref_part = arg0[4:]
            try:
                ref_id = int(ref_part)
            except Exception:
                ref_id = 0
            if ref_id > 0 and update.effective_user:
                ok = await _apply_referral(update.effective_user.id, ref_id)
                if ok:
                    await msg.reply_text(get_message("referral_bonus", lang))
    await msg.reply_text(
        get_message("start", lang),
        reply_markup=_main_menu_keyboard(lang),
        disable_web_page_preview=True,
    )


async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    _maybe_set_bot_username(getattr(context.bot, "username", None))
    lang = get_user_lang(update)
    msg = update.message or update.effective_message
    if not msg:
        return
    await msg.reply_text(
        get_message("help", lang),
        reply_markup=_main_menu_keyboard(lang),
        disable_web_page_preview=True,
    )


async def menu_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    _maybe_set_bot_username(getattr(context.bot, "username", None))
    lang = get_user_lang(update)
    msg = update.message or update.effective_message
    if not msg:
        return
    await msg.reply_text(
        get_message("menu", lang),
        reply_markup=_main_menu_keyboard(lang),
        disable_web_page_preview=True,
    )


async def menu_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not query:
        return
    _maybe_set_bot_username(getattr(context.bot, "username", None))
    try:
        await query.answer()
    except (BadRequest, NetworkError, TimedOut):
        pass
    lang = get_user_lang(update)
    data = query.data or ""
    if data == "menu_main":
        await query.message.reply_text(
            get_message("menu", lang),
            reply_markup=_main_menu_keyboard(lang),
            disable_web_page_preview=True,
        )
        return
    if data == "menu_help":
        await query.message.reply_text(
            get_message("help", lang),
            reply_markup=_main_menu_keyboard(lang),
            disable_web_page_preview=True,
        )
    elif data == "menu_sites":
        await query.message.reply_text(
            get_message("supported_sites", lang),
            reply_markup=_main_menu_keyboard(lang),
            disable_web_page_preview=True,
        )
    elif data == "menu_premium":
        await _send_premium_menu(query.message, update, lang)


def is_http_url(text: str) -> bool:
    return text.startswith("http://") or text.startswith("https://")


def extract_first_url(text: str) -> str | None:
    match = re.search(r"https?://\S+", text)
    if not match:
        return None
    url = match.group(0)
    return url.rstrip(".,;:!?)]}")


def normalize_url(url: str) -> str:
    try:
        parsed = urlparse(url)
        host = parsed.netloc.lower()
        path = parsed.path

        if ("x.com" in host or "twitter.com" in host) and "/status/" in path:
            return f"{parsed.scheme}://{parsed.netloc}{path}"

        if "tiktok.com" in host and ("/photo/" in path or "/video/" in path):
            return f"{parsed.scheme}://{parsed.netloc}{path}"
    except Exception:  # pylint: disable=broad-except
        return url

    return url


_TIKTOK_VIDEO_ID_RE = re.compile(r"/video/(\d+)")


def _tiktok_video_id_from_url(url: str) -> str | None:
    try:
        path = urlparse(url).path
    except Exception:  # pylint: disable=broad-except
        return None
    m = _TIKTOK_VIDEO_ID_RE.search(path)
    if not m:
        return None
    return m.group(1)


def _cache_tiktok_file_id(video_id: str, file_id: str) -> None:
    if not video_id or not file_id:
        return
    if video_id in TIKTOK_FILE_ID_CACHE:
        TIKTOK_FILE_ID_CACHE.pop(video_id, None)
    TIKTOK_FILE_ID_CACHE[video_id] = file_id
    if len(TIKTOK_FILE_ID_CACHE) > TIKTOK_FILE_ID_CACHE_MAX:
        oldest = next(iter(TIKTOK_FILE_ID_CACHE))
        TIKTOK_FILE_ID_CACHE.pop(oldest, None)


def _ffmpeg_exe() -> str:
    return imageio_ffmpeg.get_ffmpeg_exe()


def _clamp(val: float, lo: float, hi: float) -> float:
    if val < lo:
        return lo
    if val > hi:
        return hi
    return val


def _extract_video_style(video_path: str) -> dict[str, float]:
    """Extraction avancée du style visuel: couleurs, contraste, saturation, température, vignette."""
    exe = _ffmpeg_exe()
    vf = "select='not(mod(n,50))',signalstats,metadata=print:file=-"
    cmd = [
        exe,
        "-hide_banner",
        "-i",
        video_path,
        "-vf",
        vf,
        "-an",
        "-f",
        "null",
        "-",
    ]
    p = subprocess.run(cmd, capture_output=True, text=True, check=False)
    out = (p.stdout or "") + "\n" + (p.stderr or "")

    values: dict[str, list[float]] = {}
    for m in re.finditer(r"lavfi\.signalstats\.([A-Z]+)=([0-9.]+)", out):
        k = m.group(1)
        v = float(m.group(2))
        values.setdefault(k, []).append(v)

    def _avg(key: str) -> float:
        arr = values.get(key) or []
        if not arr:
            return 0.0
        return sum(arr) / float(len(arr))

    yavg = _avg("YAVG")
    ylow = _avg("YLOW")
    yhigh = _avg("YHIGH")
    uavg = _avg("UAVG")
    vavg = _avg("VAVG")
    ulow = _avg("ULOW")
    uhigh = _avg("UHIGH")
    vlow = _avg("VLOW")
    vhigh = _avg("VHIGH")

    temp = (vavg - 128.0) / 128.0
    tint = (uavg - 128.0) / 128.0

    return {
        "yavg": yavg,
        "yrange": max(1.0, yhigh - ylow),
        "crange": max(1.0, ((uhigh - ulow) + (vhigh - vlow)) / 2.0),
        "temp": temp,
        "tint": tint,
        "uavg": uavg,
        "vavg": vavg,
    }


def _extract_signalstats(video_path: str) -> dict[str, float]:
    return _extract_video_style(video_path)


def _compute_eq_params(src: dict[str, float], ref: dict[str, float]) -> tuple[float, float, float]:
    b = (ref.get("yavg", 0.0) - src.get("yavg", 0.0)) / 255.0
    b = _clamp(b, -0.35, 0.35)

    c = ref.get("yrange", 1.0) / max(1.0, src.get("yrange", 1.0))
    c = _clamp(c, 0.7, 1.6)

    s = ref.get("crange", 1.0) / max(1.0, src.get("crange", 1.0))
    s = _clamp(s, 0.6, 1.8)

    return b, c, s


PRESET_EFFECTS = {
    "cinematic": {
        "name_fr": "🎬 Cinématique",
        "name_en": "🎬 Cinematic",
        "desc_fr": "Teal & Orange, look film",
        "desc_en": "Teal & Orange, film look",
        "filters": [
            "eq=contrast=1.15:saturation=0.9:brightness=-0.02",
            "curves=preset=color_negative",
            "colorbalance=rs=0.1:gs=-0.05:bs=-0.15:rm=0.05:bm=-0.1:rh=-0.05:gh=0.02:bh=0.08",
            "unsharp=5:5:0.8:3:3:0.4",
        ],
    },
    "vintage": {
        "name_fr": "📼 Vintage",
        "name_en": "📼 Vintage",
        "desc_fr": "Rétro, grain, vignette",
        "desc_en": "Retro, grain, vignette",
        "filters": [
            "eq=contrast=1.2:saturation=0.7:brightness=0.05:gamma=1.1",
            "curves=r='0/0 0.5/0.48 1/0.95':g='0/0.05 0.5/0.5 1/0.95':b='0/0.1 0.5/0.52 1/1'",
            "noise=alls=8:allf=t+u",
            "vignette=angle=PI/4",
        ],
    },
    "neon": {
        "name_fr": "💎 Néon",
        "name_en": "💎 Neon",
        "desc_fr": "Cyberpunk, couleurs explosives",
        "desc_en": "Cyberpunk, explosive colors",
        "filters": [
            "eq=contrast=1.3:saturation=1.6:brightness=-0.08",
            "hue=s=1.4",
            "colorbalance=rm=0.15:bm=0.2:bs=0.15",
            "unsharp=7:7:1.2:5:5:0.0",
        ],
    },
    "bw_artistic": {
        "name_fr": "⬛ N&B Artistique",
        "name_en": "⬛ Artistic B&W",
        "desc_fr": "Noir & blanc contrasté",
        "desc_en": "High contrast black & white",
        "filters": [
            "hue=s=0",
            "eq=contrast=1.25:brightness=0.02:gamma=0.95",
            "curves=preset=strong_contrast",
            "vignette=angle=PI/3:mode=forward",
        ],
    },
    "warm_sunset": {
        "name_fr": "🌅 Coucher de soleil",
        "name_en": "🌅 Warm Sunset",
        "desc_fr": "Ambiance chaude dorée",
        "desc_en": "Warm golden vibe",
        "filters": [
            "eq=contrast=1.1:saturation=1.2:brightness=0.03",
            "colorbalance=rs=0.2:gs=0.05:bs=-0.15:rm=0.15:gm=0.02:bm=-0.1",
            "curves=r='0/0 0.5/0.55 1/1':g='0/0 0.5/0.52 1/0.98':b='0/0 0.5/0.45 1/0.9'",
        ],
    },
    "cool_nordic": {
        "name_fr": "❄️ Nordique",
        "name_en": "❄️ Nordic Cool",
        "desc_fr": "Ambiance froide bleue",
        "desc_en": "Cool blue mood",
        "filters": [
            "eq=contrast=1.15:saturation=0.85:brightness=-0.02",
            "colorbalance=rs=-0.1:bs=0.2:rm=-0.08:bm=0.15:rh=-0.05:bh=0.1",
            "curves=r='0/0.05 0.5/0.48 1/0.95':g='0/0.02 0.5/0.5 1/0.98':b='0/0 0.5/0.52 1/1'",
        ],
    },
    "glitch": {
        "name_fr": "⚡ Glitch",
        "name_en": "⚡ Glitch",
        "desc_fr": "Effet glitch distorsion",
        "desc_en": "Glitch distortion effect",
        "filters": [
            "eq=contrast=1.4:saturation=1.5:brightness=0.05",
            "rgbashift=rh=2:gh=-2:bv=2",
            "noise=alls=15:allf=t",
        ],
    },
    "film_noir": {
        "name_fr": "🎭 Film Noir",
        "name_en": "🎭 Film Noir",
        "desc_fr": "Classique noir & blanc dramatique",
        "desc_en": "Classic dramatic black & white",
        "filters": [
            "hue=s=0",
            "eq=contrast=1.4:brightness=-0.05:gamma=0.85",
            "curves=all='0/0 0.3/0.2 0.7/0.8 1/1'",
            "vignette=angle=PI/2.5:mode=forward",
        ],
    },
}


def _apply_preset_effect(in_path: str, out_path: str, preset: str) -> None:
    """Applique un effet prédéfini avec filtres ffmpeg avancés."""
    exe = _ffmpeg_exe()
    effect = PRESET_EFFECTS.get(preset)
    if not effect:
        raise ValueError(f"Unknown preset: {preset}")

    vf = ",".join(effect["filters"])
    cmd = [
        exe,
        "-hide_banner",
        "-y",
        "-i",
        in_path,
        "-map",
        "0:v:0",
        "-map",
        "0:a?",
        "-vf",
        vf,
        "-c:v",
        "libx264",
        "-preset",
        "veryfast",
        "-crf",
        "23",
        "-c:a",
        "aac",
        "-b:a",
        "128k",
        "-movflags",
        "+faststart",
        out_path,
    ]
    subprocess.run(cmd, capture_output=True, text=True, check=True)


def _apply_stolen_style(
    in_path: str, out_path: str, src_style: dict[str, float], ref_style: dict[str, float]
) -> None:
    """Applique le style 'volé' d'une vidéo de référence avec color grading avancé."""
    exe = _ffmpeg_exe()

    b = (ref_style.get("yavg", 0.0) - src_style.get("yavg", 0.0)) / 255.0
    b = _clamp(b, -0.35, 0.35)

    c = ref_style.get("yrange", 1.0) / max(1.0, src_style.get("yrange", 1.0))
    c = _clamp(c, 0.7, 1.6)

    s = ref_style.get("crange", 1.0) / max(1.0, src_style.get("crange", 1.0))
    s = _clamp(s, 0.6, 1.8)

    temp_shift = ref_style.get("temp", 0.0) - src_style.get("temp", 0.0)
    temp_shift = _clamp(temp_shift, -0.3, 0.3)

    tint_shift = ref_style.get("tint", 0.0) - src_style.get("tint", 0.0)
    tint_shift = _clamp(tint_shift, -0.3, 0.3)

    rs = temp_shift * 0.4
    bs = -temp_shift * 0.4
    gs = tint_shift * 0.3

    filters = [
        f"eq=brightness={b:.4f}:contrast={c:.4f}:saturation={s:.4f}",
        f"colorbalance=rs={rs:.3f}:gs={gs:.3f}:bs={bs:.3f}",
    ]

    vf = ",".join(filters)
    cmd = [
        exe,
        "-hide_banner",
        "-y",
        "-i",
        in_path,
        "-map",
        "0:v:0",
        "-map",
        "0:a?",
        "-vf",
        vf,
        "-c:v",
        "libx264",
        "-preset",
        "veryfast",
        "-crf",
        "23",
        "-c:a",
        "aac",
        "-b:a",
        "128k",
        "-movflags",
        "+faststart",
        out_path,
    ]
    subprocess.run(cmd, capture_output=True, text=True, check=True)


def _apply_eq_filter(in_path: str, out_path: str, brightness: float, contrast: float, saturation: float) -> None:
    exe = _ffmpeg_exe()
    vf = f"eq=brightness={brightness:.4f}:contrast={contrast:.4f}:saturation={saturation:.4f}"
    cmd = [
        exe,
        "-hide_banner",
        "-y",
        "-i",
        in_path,
        "-map",
        "0:v:0",
        "-map",
        "0:a?",
        "-vf",
        vf,
        "-c:v",
        "libx264",
        "-preset",
        "veryfast",
        "-crf",
        "23",
        "-c:a",
        "aac",
        "-b:a",
        "128k",
        "-movflags",
        "+faststart",
        out_path,
    ]
    subprocess.run(cmd, capture_output=True, text=True, check=True)


async def _download_telegram_video_to_file(
    update: Update, context: ContextTypes.DEFAULT_TYPE, out_path: str
) -> bool:
    msg = update.message
    if not msg:
        return False

    file_id = None
    if msg.video:
        file_id = msg.video.file_id
    elif msg.document and msg.document.mime_type and msg.document.mime_type.startswith("video/"):
        file_id = msg.document.file_id

    if not file_id:
        return False

    tg_file = await context.bot.get_file(file_id)
    await tg_file.download_to_drive(custom_path=out_path)
    return os.path.exists(out_path)


async def _download_reference_video_for_effects(
    message,
    url: str,
    lang: str,
) -> tuple[str | None, dict[str, float] | None]:
    try:
        parsed = urlparse(url)
        host = parsed.netloc.lower()
        if host.endswith("vm.tiktok.com") or host.endswith("vt.tiktok.com"):
            resolved = await asyncio.to_thread(_resolve_final_url, url)
            url = normalize_url(resolved)
    except Exception:
        pass

    ydl_opts = {
        **COMMON_YDL_OPTS,
        "format": "bv*[height<=720]+ba/b[height<=720]/best[height<=720]/worst",
        "outtmpl": str(DOWNLOAD_DIR / "effects_ref_%(id)s.%(ext)s"),
        "noplaylist": True,
        "merge_output_format": "mp4",
        "socket_timeout": 60,
        "retries": 3,
        "fragment_retries": 3,
        "extractor_retries": 3,
    }

    filename = None
    progress_message = await message.reply_text(
        "⬇️ Démarrage du téléchargement…" if lang == "fr" else "⬇️ Starting download…"
    )
    loop = asyncio.get_running_loop()
    ydl_opts["progress_hooks"] = [
        _make_progress_hook(loop, progress_message, lang, "video")
    ]

    def _download() -> str | None:
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)
            fname = ydl.prepare_filename(info)
            ydl.download([url])
            return fname

    try:
        async with DOWNLOAD_SEMAPHORE:
            filename = await asyncio.to_thread(_download)
    except DownloadError as e:
        error_text = str(e)
        logger.info("Download error while fetching effects reference: %s", error_text)
        try:
            await progress_message.edit_text("❌ Erreur" if lang == "fr" else "❌ Error")
        except Exception:
            pass
        if _is_youtube_antibot_error(error_text):
            try:
                await message.reply_text(_youtube_antibot_user_message(lang))
            except Exception:
                pass
        return None, None
    except Exception:
        logger.exception("Unexpected error while fetching effects reference")
        try:
            await progress_message.edit_text("❌ Erreur" if lang == "fr" else "❌ Error")
        except Exception:
            pass
        return None, None

    if not filename or not os.path.exists(filename):
        try:
            await progress_message.edit_text("❌ Erreur" if lang == "fr" else "❌ Error")
        except Exception:
            pass
        return None, None

    try:
        await progress_message.edit_text(
            "🔎 Analyse de la vidéo…" if lang == "fr" else "🔎 Analyzing video…"
        )
    except Exception:
        pass

    async with FFMPEG_SEMAPHORE:
        stats = await asyncio.to_thread(_extract_signalstats, filename)

    try:
        await progress_message.edit_text("✅ Terminé" if lang == "fr" else "✅ Done")
    except Exception:
        pass

    return filename, stats


def _format_bytes(num: int | float | None) -> str:
    if not isinstance(num, (int, float)) or num <= 0:
        return "?"
    step = 1024.0
    units = ["B", "KB", "MB", "GB", "TB"]
    n = float(num)
    u = 0
    while n >= step and u < len(units) - 1:
        n /= step
        u += 1
    if u == 0:
        return f"{int(n)} {units[u]}"
    return f"{n:.1f} {units[u]}"


def _format_eta(seconds: int | float | None) -> str:
    if not isinstance(seconds, (int, float)) or seconds <= 0:
        return "?"
    s = int(seconds)
    m, s = divmod(s, 60)
    h, m = divmod(m, 60)
    if h:
        return f"{h:d}h{m:02d}m"
    if m:
        return f"{m:d}m{s:02d}s"
    return f"{s:d}s"


def _make_progress_hook(loop, progress_message, lang: str, kind: str):
    last = {"t": 0.0, "text": ""}

    def _schedule(text: str) -> None:
        if not text or text == last["text"]:
            return
        now = time.monotonic()
        if now - last["t"] < 1.0:
            return
        last["t"] = now
        last["text"] = text

        try:
            fut = asyncio.run_coroutine_threadsafe(
                progress_message.edit_text(text), loop
            )

            def _done(f):
                try:
                    f.result()
                except Exception:
                    pass

            fut.add_done_callback(_done)
        except Exception:
            return

    def hook(d: dict) -> None:
        status = d.get("status")
        if status == "downloading":
            downloaded = d.get("downloaded_bytes")
            total = d.get("total_bytes")
            if total is None:
                total = d.get("total_bytes_estimate")
            speed = d.get("speed")
            eta = d.get("eta")

            pct = None
            if isinstance(downloaded, (int, float)) and isinstance(total, (int, float)) and total > 0:
                pct = int((float(downloaded) / float(total)) * 100)
            pct_txt = f"{pct}%" if pct is not None else "?%"

            if lang == "fr":
                title = "⬇️ Téléchargement vidéo…" if kind == "video" else "⬇️ Téléchargement audio…"
                line1 = f"{pct_txt} • {_format_bytes(downloaded)} / {_format_bytes(total)}"
                line2 = f"⚡ {_format_bytes(speed)}/s • ⏱️ {_format_eta(eta)}"
            else:
                title = "⬇️ Downloading video…" if kind == "video" else "⬇️ Downloading audio…"
                line1 = f"{pct_txt} • {_format_bytes(downloaded)} / {_format_bytes(total)}"
                line2 = f"⚡ {_format_bytes(speed)}/s • ⏱️ {_format_eta(eta)}"
            _schedule("\n".join([title, line1, line2]))
            return

        if status == "finished":
            text = (
                "✅ Téléchargement terminé. 📦 Préparation…"
                if lang == "fr"
                else "✅ Download finished. 📦 Preparing…"
            )
            _schedule(text)

    return hook


def _extract_tiktok_direct_candidate(
    url: str, quality: str
) -> tuple[str | None, str | None, str | None]:
    ydl_opts = {
        **COMMON_YDL_OPTS,
        "skip_download": True,
        "noplaylist": True,
    }

    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
        info = ydl.extract_info(url, download=False)

    if not isinstance(info, dict):
        return None, None, None

    title = info.get("title") if isinstance(info.get("title"), str) else None
    video_id = info.get("id") if isinstance(info.get("id"), str) else None

    formats = info.get("formats") or []
    if not isinstance(formats, list):
        formats = []

    candidates: list[dict] = []
    for f in formats:
        if not isinstance(f, dict):
            continue
        u = f.get("url")
        if not (isinstance(u, str) and u.startswith("http")):
            continue
        protocol = (f.get("protocol") or "").lower()
        if "m3u8" in protocol:
            continue
        ext = (f.get("ext") or "").lower()
        if ext and ext != "mp4":
            continue
        vcodec = f.get("vcodec")
        if vcodec in (None, "none"):
            continue
        candidates.append(f)

    def _score(fmt: dict) -> tuple[int, float]:
        h = fmt.get("height")
        height = h if isinstance(h, int) else 0
        t = fmt.get("tbr")
        tbr = float(t) if isinstance(t, (int, float)) else 0.0
        return height, tbr

    if quality == "sd":
        filtered = [c for c in candidates if isinstance(c.get("height"), int) and c["height"] <= 720]
        if filtered:
            candidates = filtered

    def _pick(require_audio: bool) -> str | None:
        pool = candidates
        if require_audio:
            pool = [c for c in pool if c.get("acodec") not in (None, "none")]
        if not pool:
            return None
        best = max(pool, key=_score)
        u = best.get("url")
        return u if isinstance(u, str) else None

    direct_url = _pick(require_audio=True) or _pick(require_audio=False)
    return direct_url, title, video_id


async def handle_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.message:
        return

    _maybe_set_bot_username(getattr(context.bot, "username", None))

    lang = get_user_lang(update)
    raw_text = (update.message.text or update.message.caption or "").strip()

    if context.user_data.get("effects_waiting_ref_url"):
        url = extract_first_url(raw_text)
        if not url:
            await update.message.reply_text(get_message("effects_steal_intro", lang))
            return

        context.user_data.pop("effects_waiting_ref_url", None)

        old_ref = context.user_data.get("effects_ref_file")
        if isinstance(old_ref, str) and os.path.exists(old_ref):
            _safe_remove(old_ref)

        ref_file, ref_stats = await _download_reference_video_for_effects(update.message, url, lang)
        if not ref_file or not ref_stats:
            context.user_data.pop("effects_entitlement_kind", None)
            context.user_data.pop("effects_mode", None)
            await update.message.reply_text(get_message("error_try_again", lang))
            return

        context.user_data["effects_ref_file"] = ref_file
        context.user_data["effects_ref_stats"] = ref_stats
        context.user_data["effects_waiting_video"] = True
        await update.message.reply_text(get_message("effects_ready", lang))
        return

    if context.user_data.get("effects_waiting_video"):
        if extract_first_url(raw_text):
            context.user_data.pop("effects_waiting_video", None)
            context.user_data.pop("effects_ref_stats", None)
            context.user_data.pop("effects_preset_id", None)
            context.user_data.pop("effects_mode", None)
            context.user_data.pop("effects_entitlement_kind", None)
            old_ref = context.user_data.pop("effects_ref_file", None)
            if isinstance(old_ref, str) and os.path.exists(old_ref):
                _safe_remove(old_ref)

        has_video = bool(update.message.video) or bool(
            update.message.document
            and update.message.document.mime_type
            and update.message.document.mime_type.startswith("video/")
        )
        if not has_video:
            preset_id = context.user_data.get("effects_preset_id")
            if preset_id:
                preset = PRESET_EFFECTS.get(preset_id)
                if preset:
                    effect_name = preset[f"name_{lang}"]
                    effect_desc = preset[f"desc_{lang}"]
                    await update.message.reply_text(
                        get_message("effects_preset_selected", lang).format(
                            effect_name=effect_name, effect_desc=effect_desc
                        )
                    )
                    return
            await update.message.reply_text(get_message("effects_ready", lang))
            return

        chat_id = update.effective_chat.id if update.effective_chat else 0
        ts = int(time.time())
        user_path = str(DOWNLOAD_DIR / f"effects_user_{chat_id}_{ts}.mp4")
        out_path = str(DOWNLOAD_DIR / f"effects_out_{chat_id}_{ts}.mp4")

        ok = False
        try:
            ok = await _download_telegram_video_to_file(update, context, user_path)
        except Exception:
            ok = False

        if not ok:
            await update.message.reply_text(get_message("error_try_again", lang))
            return

        progress = await update.message.reply_text(get_message("effects_processing", lang))

        entitlement_kind = context.user_data.get("effects_entitlement_kind")
        if not isinstance(entitlement_kind, str):
            entitlement_kind = None
        sent_ok = False

        effects_mode = context.user_data.get("effects_mode")
        preset_id = context.user_data.get("effects_preset_id")
        ref_stats = context.user_data.get("effects_ref_stats")

        try:
            if effects_mode == "preset" and preset_id:
                async with FFMPEG_SEMAPHORE:
                    await asyncio.to_thread(_apply_preset_effect, user_path, out_path, preset_id)
            elif effects_mode == "steal" and isinstance(ref_stats, dict):
                async with FFMPEG_SEMAPHORE:
                    src_stats = await asyncio.to_thread(_extract_video_style, user_path)
                    await asyncio.to_thread(_apply_stolen_style, user_path, out_path, src_stats, ref_stats)
            else:
                context.user_data.pop("effects_waiting_video", None)
                context.user_data.pop("effects_entitlement_kind", None)
                await update.message.reply_text(get_message("error_try_again", lang))
                return

            if os.path.exists(out_path):
                file_size = os.path.getsize(out_path)
                if file_size > MAX_FILE_SIZE_BYTES:
                    size_mb = file_size / (1024 * 1024)
                    await update.message.reply_text(
                        get_message("too_big", lang).format(size_mb=size_mb)
                    )
                    return

                sent = False
                for attempt in range(2):
                    try:
                        with open(out_path, "rb") as retry_file:
                            try:
                                await update.message.reply_video(
                                    video=retry_file,
                                    read_timeout=600.0,
                                    write_timeout=600.0,
                                )
                            except TypeError:
                                await update.message.reply_video(video=retry_file)
                        sent = True
                        break
                    except TimedOut:
                        if attempt == 0:
                            await asyncio.sleep(2)
                            continue
                        sent = False

                if not sent:
                    with open(out_path, "rb") as doc_file:
                        try:
                            await update.message.reply_document(
                                document=doc_file,
                                read_timeout=600.0,
                                write_timeout=600.0,
                            )
                        except TypeError:
                            await update.message.reply_document(document=doc_file)
                    sent = True
                await update.message.reply_text(get_message("effects_done", lang))
                sent_ok = True

        except Exception:
            logger.exception("Error while applying effects")
            await update.message.reply_text(get_message("error_try_again", lang))
        finally:
            context.user_data.pop("effects_waiting_video", None)
            context.user_data.pop("effects_mode", None)
            context.user_data.pop("effects_preset_id", None)
            context.user_data.pop("effects_entitlement_kind", None)
            if sent_ok and update.effective_user:
                try:
                    await _finalize_effect_entitlement(update.effective_user.id, entitlement_kind)
                except Exception:
                    pass
            for p in (user_path, out_path):
                if p and os.path.exists(p):
                    _safe_remove(p)
            try:
                await progress.edit_text("✅" if lang == "fr" else "✅")
            except Exception:
                pass
        return

    if not raw_text:
        return

    url = extract_first_url(raw_text)
    if not url:
        await update.message.reply_text(
            get_message("prompt_send_link", lang),
            reply_markup=_main_menu_keyboard(lang),
            disable_web_page_preview=True,
        )
        return

    url = normalize_url(url)

    logger.info("Received URL: %s", url)

    if not is_http_url(url):
        await update.message.reply_text(get_message("invalid_url", lang))
        return

    # Sauvegarde le dernier lien et propose un choix Vidéo / Audio
    context.user_data["last_url"] = url

    buttons = [
        [
            InlineKeyboardButton("🎬 Vidéo", callback_data="type_video"),
            InlineKeyboardButton("🎧 Audio", callback_data="type_audio"),
        ]
    ]
    buttons.append(
        [InlineKeyboardButton(get_message("effects_button", lang), callback_data="type_effects")]
    )
    share_url = _get_share_url(lang)
    if share_url:
        buttons.append(
            [
                InlineKeyboardButton(get_message("share_button", lang), url=share_url),
                InlineKeyboardButton(get_message("menu_button", lang), callback_data="menu_main"),
            ]
        )
    else:
        buttons.append(
            [InlineKeyboardButton(get_message("menu_button", lang), callback_data="menu_main")]
        )
    keyboard = InlineKeyboardMarkup(buttons)

    await update.message.reply_text(
        get_message("choose_type", lang),
        reply_markup=keyboard,
        disable_web_page_preview=True,
    )


async def process_url(message, url: str, lang: str, quality: str, audio_lang: str = "orig") -> None:
    """Télécharge l'URL donnée avec la qualité choisie et envoie la vidéo."""

    if not isinstance(audio_lang, str) or audio_lang not in ("orig", "fr", "en"):
        audio_lang = "orig"

    tiktok_video_id = None
    try:
        parsed = urlparse(url)
        host = parsed.netloc.lower()
        if host.endswith("vm.tiktok.com") or host.endswith("vt.tiktok.com"):
            try:
                resolved = await asyncio.to_thread(_resolve_final_url, url)
                url = normalize_url(resolved)
            except Exception:  # pylint: disable=broad-except
                pass
            parsed = urlparse(url)
            host = parsed.netloc.lower()

        if "tiktok.com" in host and "/video/" in parsed.path and audio_lang == "orig":
            tiktok_video_id = _tiktok_video_id_from_url(url)
            if tiktok_video_id:
                cached = TIKTOK_FILE_ID_CACHE.get(tiktok_video_id)
                if cached:
                    try:
                        sent = await message.reply_video(video=cached)
                        video_obj = getattr(sent, "video", None)
                        file_id = getattr(video_obj, "file_id", None) if video_obj else None
                        if file_id:
                            _cache_tiktok_file_id(tiktok_video_id, file_id)
                        await _maybe_send_ad_after_success(message, lang)
                        await _maybe_send_share_prompt(message, lang)
                        return
                    except (BadRequest, TimedOut, NetworkError):
                        pass

            direct_url = None
            title_direct = None
            vid_from_info = None
            try:
                async with DOWNLOAD_SEMAPHORE:
                    direct_url, title_direct, vid_from_info = await asyncio.to_thread(
                        _extract_tiktok_direct_candidate, url, quality
                    )
            except DownloadError as e:
                logger.info("TikTok direct extract failed: %s", e)
            except Exception as e:  # pylint: disable=broad-except
                logger.debug("TikTok direct extract failed: %s", e)

            if direct_url:
                try:
                    sent = await message.reply_video(
                        video=direct_url,
                        caption=title_direct or "",
                    )
                    vid_key = tiktok_video_id or vid_from_info
                    video_obj = getattr(sent, "video", None)
                    file_id = getattr(video_obj, "file_id", None) if video_obj else None
                    if vid_key and file_id:
                        _cache_tiktok_file_id(vid_key, file_id)
                    await _maybe_send_ad_after_success(message, lang)
                    await _maybe_send_share_prompt(message, lang)
                    return
                except (BadRequest, TimedOut, NetworkError):
                    pass
    except Exception as e:  # pylint: disable=broad-except
        logger.debug("TikTok instant mode skipped: %s", e)

    wanted_label = None
    if audio_lang == "fr":
        wanted_label = "🇫🇷 Français" if lang == "fr" else "🇫🇷 French"
    elif audio_lang == "en":
        wanted_label = "🇬🇧 Anglais" if lang == "fr" else "🇬🇧 English"

    audio_pref = "ba"
    if audio_lang == "fr":
        audio_pref = "ba[language~='^fr']"
    elif audio_lang == "en":
        audio_pref = "ba[language~='^en']"

    if quality == "sd":
        # SD: max 480p pour un bon compromis qualité / taille
        video_format = (
            f"bv*[height<=720]+{audio_pref}/"
            "bv*[height<=720]+ba/b[height<=720]/best[height<=720]/worst"
        )
    else:  # hd par défaut
        # HD: max 1080p pour la meilleure qualité tout en respectant la limite de taille
        video_format = (
            f"bv*[height<=1080]+{audio_pref}/"
            "bv*[height<=1080]+ba/b[height<=1080]/best[height<=1080]/best"
        )

    ydl_opts = {
        **COMMON_YDL_OPTS,
        "format": video_format,
        "outtmpl": str(DOWNLOAD_DIR / "%(title)s.%(ext)s"),
        "noplaylist": True,
        "merge_output_format": "mp4",
    }

    filename = None
    progress_message = None
    try:
        progress_message = await message.reply_text(
            "⬇️ Démarrage du téléchargement…" if lang == "fr" else "⬇️ Starting download…"
        )
        loop = asyncio.get_running_loop()
        ydl_opts["progress_hooks"] = [
            _make_progress_hook(loop, progress_message, lang, "video")
        ]

        def _download() -> tuple[str | None, bool]:
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(url, download=False)
                has_requested_audio = True
                if audio_lang in ("fr", "en"):
                    has_requested_audio = False
                    formats = info.get("formats") or []
                    if isinstance(formats, list):
                        for f in formats:
                            if not isinstance(f, dict):
                                continue
                            acodec = f.get("acodec")
                            if acodec in (None, "none"):
                                continue
                            vcodec = f.get("vcodec")
                            if vcodec not in (None, "none"):
                                continue
                            flang = f.get("language")
                            if isinstance(flang, str) and flang.lower().startswith(audio_lang):
                                has_requested_audio = True
                                break
                fname = ydl.prepare_filename(info)
                ydl.download([url])
                return fname, has_requested_audio

        async with DOWNLOAD_SEMAPHORE:
            filename, has_requested_audio = await asyncio.to_thread(_download)

        if wanted_label and not has_requested_audio:
            await message.reply_text(
                get_message("audio_lang_unavailable", lang).format(wanted=wanted_label)
            )

        try:
            await progress_message.edit_text(
                "📤 Envoi vers Telegram…" if lang == "fr" else "📤 Sending to Telegram…"
            )
        except Exception:
            pass

        if not filename or not os.path.exists(filename):
            raise RuntimeError("Downloaded file not found")

        file_size = os.path.getsize(filename)
        if file_size > MAX_FILE_SIZE_BYTES:
            size_mb = file_size / (1024 * 1024)
            await message.reply_text(
                get_message("too_big", lang).format(size_mb=size_mb),
                reply_markup=_action_keyboard(lang, "video", quality),
            )
            if progress_message is not None:
                try:
                    await progress_message.edit_text(
                        "📦 Fichier trop gros" if lang == "fr" else "📦 File too large"
                    )
                except Exception:
                    pass
            _safe_remove(filename)
            return

        title = os.path.basename(filename)
        sent = None
        try:
            with open(filename, "rb") as video_file:
                try:
                    await message.reply_video(
                        video=video_file,
                        caption=title,
                        read_timeout=600.0,
                        write_timeout=600.0,
                    )
                except TypeError:
                    await message.reply_video(video=video_file, caption=title)
        except (TimedOut, NetworkError):
            # L'envoi peut quand même réussir côté Telegram, on log juste pour debug
            logger.debug("Timed out while sending video; it may still have been delivered.")

        if tiktok_video_id and sent is not None:
            video_obj = getattr(sent, "video", None)
            file_id = getattr(video_obj, "file_id", None) if video_obj else None
            if file_id:
                _cache_tiktok_file_id(tiktok_video_id, file_id)

        _safe_remove(filename)
        await message.reply_text(get_message("cleaned", lang))
        await _maybe_send_ad_after_success(message, lang)
        await _maybe_send_share_prompt(message, lang)

        try:
            await progress_message.edit_text("✅ Terminé" if lang == "fr" else "✅ Done")
        except Exception:
            pass

    except DownloadError as e:
        error_text = str(e)
        logger.info("Download error while processing URL: %s", error_text)
        if progress_message is not None:
            try:
                await progress_message.edit_text(
                    "❌ Échec du téléchargement" if lang == "fr" else "❌ Download failed"
                )
            except Exception:
                pass
        if _is_youtube_antibot_error(error_text):
            await message.reply_text(
                _youtube_antibot_user_message(lang),
                reply_markup=_action_keyboard(lang, "video", quality),
            )
        elif "No video could be found" in error_text:
            await message.reply_text(
                get_message("no_video", lang),
                reply_markup=_action_keyboard(lang, "video", quality),
            )
        else:
            await message.reply_text(
                get_message("error_try_again", lang),
                reply_markup=_action_keyboard(lang, "video", quality),
            )
        if filename and os.path.exists(filename):
            _safe_remove(filename)

    except Exception as e:  # pylint: disable=broad-except
        logger.exception("Error while processing URL: %s", e)
        if progress_message is not None:
            try:
                await progress_message.edit_text(
                    "❌ Erreur" if lang == "fr" else "❌ Error"
                )
            except Exception:
                pass
        await message.reply_text(
            get_message("error_try_again", lang),
            reply_markup=_action_keyboard(lang, "video", quality),
        )
        if filename and os.path.exists(filename):
            _safe_remove(filename)


async def process_audio_url(message, url: str, lang: str) -> None:
    """Télécharge uniquement l'audio et l'envoie."""

    ydl_opts = {
        **COMMON_YDL_OPTS,
        "format": "bestaudio/best",
        "outtmpl": str(DOWNLOAD_DIR / "%(title)s.%(ext)s"),
        "noplaylist": True,
        # Évite la correction de conteneur m4a qui peut poser problème sous Windows
        "fixup": "never",
    }

    filename = None
    progress_message = None
    try:
        progress_message = await message.reply_text(
            "⬇️ Démarrage du téléchargement…" if lang == "fr" else "⬇️ Starting download…"
        )
        loop = asyncio.get_running_loop()
        ydl_opts["progress_hooks"] = [
            _make_progress_hook(loop, progress_message, lang, "audio")
        ]

        def _download() -> str | None:
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(url, download=False)
                fname = ydl.prepare_filename(info)
                ydl.download([url])
                return fname

        async with DOWNLOAD_SEMAPHORE:
            filename = await asyncio.to_thread(_download)

        try:
            await progress_message.edit_text(
                "📤 Envoi vers Telegram…" if lang == "fr" else "📤 Sending to Telegram…"
            )
        except Exception:
            pass

        if not filename or not os.path.exists(filename):
            raise RuntimeError("Downloaded file not found")

        file_size = os.path.getsize(filename)
        if file_size > MAX_FILE_SIZE_BYTES:
            size_mb = file_size / (1024 * 1024)
            await message.reply_text(
                get_message("too_big", lang).format(size_mb=size_mb),
                reply_markup=_action_keyboard(lang, "audio", None),
            )
            if progress_message is not None:
                try:
                    await progress_message.edit_text(
                        "📦 Fichier trop gros" if lang == "fr" else "📦 File too large"
                    )
                except Exception:
                    pass
            _safe_remove(filename)
            return

        title = os.path.basename(filename)
        try:
            with open(filename, "rb") as audio_file:
                await message.reply_audio(
                    audio=audio_file,
                    caption=title,
                )
        except (TimedOut, NetworkError):
            logger.debug(
                "Timed out while sending audio; it may still have been delivered."
            )

        _safe_remove(filename)
        await message.reply_text(get_message("cleaned", lang))
        await _maybe_send_ad_after_success(message, lang)
        await _maybe_send_share_prompt(message, lang)

        if progress_message is not None:
            try:
                await progress_message.edit_text("✅ Terminé" if lang == "fr" else "✅ Done")
            except Exception:
                pass

    except DownloadError as e:
        error_text = str(e)
        logger.info("Download error while processing audio URL: %s", error_text)
        if progress_message is not None:
            try:
                await progress_message.edit_text(
                    "❌ Échec du téléchargement" if lang == "fr" else "❌ Download failed"
                )
            except Exception:
                pass
        if _is_youtube_antibot_error(error_text):
            await message.reply_text(
                _youtube_antibot_user_message(lang),
                reply_markup=_action_keyboard(lang, "audio", None),
            )
        elif "No video could be found" in error_text:
            await message.reply_text(
                get_message("no_video", lang),
                reply_markup=_action_keyboard(lang, "audio", None),
            )
        else:
            await message.reply_text(
                get_message("error_try_again", lang),
                reply_markup=_action_keyboard(lang, "audio", None),
            )
        if filename and os.path.exists(filename):
            _safe_remove(filename)

    except Exception as e:  # pylint: disable=broad-except
        logger.exception("Error while processing audio URL")
        if progress_message is not None:
            try:
                await progress_message.edit_text(
                    "❌ Erreur" if lang == "fr" else "❌ Error"
                )
            except Exception:
                pass
        await message.reply_text(
            get_message("error_try_again", lang),
            reply_markup=_action_keyboard(lang, "audio", None),
        )
        if filename and os.path.exists(filename):
            _safe_remove(filename)


def _extract_image_info_from_html(page_url: str) -> tuple[str | None, str | None]:
    try:
        req = urllib.request.Request(
            page_url,
            headers={
                "User-Agent": (
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/122.0 Safari/537.36"
                ),
                "Accept-Language": "en-US,en;q=0.9,fr;q=0.8",
            },
        )
        with urllib.request.urlopen(req, timeout=15) as resp:
            content_type = resp.headers.get("Content-Type", "")
            charset = "utf-8"
            if "charset=" in content_type:
                charset = content_type.split("charset=")[-1].split(";")[0].strip()
            html_bytes = resp.read()
            html_text = html_bytes.decode(charset, errors="ignore")
    except Exception:  # pylint: disable=broad-except
        logger.exception("Error fetching HTML for image extraction")
        return None, None

    image_url = None
    metas = re.findall(r"<meta[^>]+>", html_text, flags=re.IGNORECASE)
    for meta in metas:
        lower_meta = meta.lower()
        if "og:image" in lower_meta or "twitter:image" in lower_meta:
            m = re.search(r'content=["\']([^"\']+)["\']', meta, re.IGNORECASE)
            if m:
                image_url = m.group(1)
                break

    if not image_url:
        return None, None

    title_match = re.search(
        r"<title[^>]*>(.*?)</title>",
        html_text,
        re.IGNORECASE | re.DOTALL,
    )
    title = title_match.group(1).strip() if title_match else None
    return image_url, title


def _download_url_to_file(download_url: str, filename: str) -> None:
    req = urllib.request.Request(
        download_url,
        headers={
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/122.0 Safari/537.36"
            ),
        },
    )
    with urllib.request.urlopen(req, timeout=30) as resp, open(
        filename, "wb"
    ) as out_file:
        out_file.write(resp.read())


def _download_url_to_file_with_referer(
    download_url: str, filename: str, referer_url: str | None
) -> None:
    headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/122.0 Safari/537.36"
        )
    }
    if referer_url:
        headers["Referer"] = referer_url

    req = urllib.request.Request(download_url, headers=headers)
    with urllib.request.urlopen(req, timeout=30) as resp, open(
        filename, "wb"
    ) as out_file:
        out_file.write(resp.read())


def _extract_tiktok_photo_urls_from_html(page_url: str) -> tuple[list[str], str | None]:
    try:
        req = urllib.request.Request(
            page_url,
            headers={
                "User-Agent": (
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/122.0 Safari/537.36"
                ),
                "Accept-Language": "en-US,en;q=0.9,fr;q=0.8",
                "Accept-Encoding": "identity",
            },
        )
        with urllib.request.urlopen(req, timeout=20) as resp:
            content_type = resp.headers.get("Content-Type", "")
            charset = "utf-8"
            if "charset=" in content_type:
                charset = content_type.split("charset=")[-1].split(";")[0].strip()
            html_text = resp.read().decode(charset, errors="ignore")
    except Exception:  # pylint: disable=broad-except
        logger.exception("Error fetching TikTok HTML")
        return [], None

    script_id = None
    script_match = re.search(
        r'<script[^>]+id=["\']__UNIVERSAL_DATA_FOR_REHYDRATION__["\'][^>]*>(.*?)</script>',
        html_text,
        re.IGNORECASE | re.DOTALL,
    )
    if not script_match:
        script_match = re.search(
            r'<script[^>]+id=["\']SIGI_STATE["\'][^>]*>(.*?)</script>',
            html_text,
            re.IGNORECASE | re.DOTALL,
        )
        if script_match:
            script_id = "SIGI_STATE"
    else:
        script_id = "__UNIVERSAL_DATA_FOR_REHYDRATION__"
    if not script_match:
        return [], None

    json_text = script_match.group(1).strip()

    def _strip_js_assignment(text: str) -> str:
        t = text.strip()
        t = re.sub(
            r'^\s*window\[(?:"|\")?SIGI_STATE(?:"|\")?\]\s*=\s*',
            "",
            t,
            flags=re.IGNORECASE,
        )
        t = re.sub(
            r"^\s*window\[(?:'|\")?SIGI_STATE(?:'|\")?\]\s*=\s*",
            "",
            t,
            flags=re.IGNORECASE,
        )
        t = re.sub(
            r"^\s*window\[(?:'|\")?__UNIVERSAL_DATA_FOR_REHYDRATION__(?:'|\")?\]\s*=\s*",
            "",
            t,
            flags=re.IGNORECASE,
        )
        t = re.sub(
            r"^\s*window\.(?:SIGI_STATE|__UNIVERSAL_DATA_FOR_REHYDRATION__)\s*=\s*",
            "",
            t,
            flags=re.IGNORECASE,
        )
        t = t.strip()
        if t.endswith(";"):
            t = t[:-1]
        t = t.strip()
        if not (t.startswith("{") or t.startswith("[")):
            start = t.find("{")
            end = t.rfind("}")
            if start != -1 and end != -1 and end > start:
                t = t[start : end + 1]
        return t.strip()

    json_text = _strip_js_assignment(json_text)
    logger.info(
        "TikTok embedded JSON candidate (type=%s, chars=%d)",
        script_id,
        len(json_text),
    )
    try:
        data = json.loads(json_text)
    except Exception:  # pylint: disable=broad-except
        logger.exception("Error parsing TikTok embedded JSON")
        return [], None

    def _urls_from_image_post_dict(image_post: dict) -> list[str]:
        images = image_post.get("images")
        if not isinstance(images, list):
            return []
        urls: list[str] = []
        for img in images:
            if not isinstance(img, dict):
                continue
            candidates = []
            for k in ("imageURL", "displayImage", "cover", "staticImage"):
                v = img.get(k)
                if isinstance(v, dict):
                    candidates.append(v)
            for candidate in candidates:
                url_list = candidate.get("urlList")
                if isinstance(url_list, list):
                    for u in url_list:
                        if isinstance(u, str) and u.startswith("http"):
                            urls.append(u)
                            break
        return urls

    def _walk(obj) -> tuple[list[str], str | None]:
        if isinstance(obj, dict):
            if "imagePost" in obj and isinstance(obj.get("imagePost"), dict):
                urls = _urls_from_image_post_dict(obj["imagePost"])
                desc = obj.get("desc") if isinstance(obj.get("desc"), str) else None
                if urls:
                    return urls, desc
            for v in obj.values():
                urls, desc = _walk(v)
                if urls:
                    return urls, desc
        elif isinstance(obj, list):
            for it in obj:
                urls, desc = _walk(it)
                if urls:
                    return urls, desc
        return [], None

    urls, desc = _walk(data)
    if urls:
        deduped: list[str] = []
        seen = set()
        for u in urls:
            if u not in seen:
                deduped.append(u)
                seen.add(u)
        return deduped, desc

    return [], None


async def process_photo_url(message, url: str, lang: str) -> None:
    """Télécharge une photo (si disponible) et l'envoie."""

    await message.reply_text(get_message("photo_disabled", lang))
    return

    filename = None
    try:
        parsed = urlparse(url)
        host = parsed.netloc.lower()
        logger.info("Processing photo URL (host=%s): %s", host, url)

        # Cas spécial X/Twitter
        if "x.com" in host or "twitter.com" in host:
            info = None

            def _extract_twitter_info() -> dict | None:
                ydl_opts = {
                    "skip_download": True,
                    "ignore_no_formats_error": True,
                }
                with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                    return ydl.extract_info(url, download=False)

            try:
                info = await asyncio.to_thread(_extract_twitter_info)
            except DownloadError:
                info = None

            image_url = None
            title = None

            if info:
                thumbs = info.get("thumbnails") or []
                if thumbs:
                    best = max(thumbs, key=lambda t: t.get("width") or 0)
                    image_url = best.get("url")
                title = info.get("title")

            if image_url:
                image_url = _twitter_image_url_to_orig(image_url)

            if not image_url:
                image_url, title_html = await asyncio.to_thread(
                    _extract_image_info_from_html, url
                )
                title = title or title_html

            if not image_url:
                photo_urls, title_syn = await asyncio.to_thread(
                    _extract_twitter_photo_urls_from_syndication, url
                )
                if photo_urls:
                    title = title_syn or title or "image"
                    safe_title = re.sub(r"[\\/:*?\"<>|]", "_", title)

                    downloaded_files: list[str] = []
                    try:
                        for idx, photo_url in enumerate(photo_urls[:10]):
                            parsed_img = urlparse(photo_url)
                            img_ext = os.path.splitext(parsed_img.path)[1].lower().lstrip(".")
                            image_ext = img_ext if img_ext in IMAGE_EXTENSIONS else "jpg"
                            out_path = str(
                                DOWNLOAD_DIR / f"{safe_title}_{idx + 1}.{image_ext}"
                            )
                            await asyncio.to_thread(
                                _download_url_to_file_with_referer,
                                photo_url,
                                out_path,
                                url,
                            )
                            downloaded_files.append(out_path)

                        if not downloaded_files:
                            await message.reply_text(get_message("no_photo", lang))
                            return

                        media = []
                        handles = []
                        try:
                            for i, fpath in enumerate(downloaded_files):
                                photo_file = open(fpath, "rb")
                                handles.append(photo_file)
                                media.append(
                                    InputMediaPhoto(
                                        media=photo_file,
                                        caption=title if i == 0 else None,
                                    )
                                )
                            await message.reply_media_group(media=media)
                        finally:
                            for h in handles:
                                try:
                                    h.close()
                                except OSError:
                                    pass

                        for fpath in downloaded_files:
                            try:
                                os.remove(fpath)
                            except OSError:
                                pass
                        await message.reply_text(get_message("cleaned", lang))
                        return
                    except Exception:  # pylint: disable=broad-except
                        for fpath in downloaded_files:
                            try:
                                os.remove(fpath)
                            except OSError:
                                pass
                        raise

            if not image_url:
                await message.reply_text(get_message("no_photo", lang))
                return

            title = title or "image"
            parsed_img = urlparse(image_url)
            img_ext = os.path.splitext(parsed_img.path)[1].lower().lstrip(".")
            image_ext = img_ext if img_ext in IMAGE_EXTENSIONS else "jpg"
            safe_title = re.sub(r"[\\/:*?\"<>|]", "_", title)
            filename = str(DOWNLOAD_DIR / f"{safe_title}.{image_ext}")

            await asyncio.to_thread(_download_url_to_file, image_url, filename)

            if not os.path.exists(filename):
                raise RuntimeError("Downloaded image not found")

            file_size = os.path.getsize(filename)
            if file_size > MAX_FILE_SIZE_BYTES:
                size_mb = file_size / (1024 * 1024)
                await message.reply_text(
                    get_message("too_big", lang).format(size_mb=size_mb)
                )
                os.remove(filename)
                return

            with open(filename, "rb") as photo_file:
                await message.reply_photo(photo=photo_file, caption=title)

            os.remove(filename)
            await message.reply_text(get_message("cleaned", lang))
            return

        # TikTok liens courts
        if host.endswith("vm.tiktok.com") or host.endswith("vt.tiktok.com"):
            resolved = await asyncio.to_thread(_resolve_final_url, url)
            resolved = normalize_url(resolved)
            logger.info("Resolved TikTok short link: %s -> %s", url, resolved)
            url = resolved
            parsed = urlparse(url)
            host = parsed.netloc.lower()

        # TikTok canonique
        if "tiktok.com" in host:
            tiktok_path = urlparse(url).path
            photo_urls, title_tk = await asyncio.to_thread(
                _extract_tiktok_photo_urls_from_html, url
            )
            if photo_urls:
                logger.info("TikTok photo extraction: %d image(s)", len(photo_urls))
                title = title_tk or "image"
                safe_title = re.sub(r"[\\/:*?\"<>|]", "_", title)

                downloaded_files: list[str] = []
                try:
                    for idx, photo_url in enumerate(photo_urls[:10]):
                        parsed_img = urlparse(photo_url)
                        img_ext = os.path.splitext(parsed_img.path)[1].lower().lstrip(".")
                        image_ext = img_ext if img_ext in IMAGE_EXTENSIONS else "jpg"
                        out_path = str(
                            DOWNLOAD_DIR / f"{safe_title}_{idx + 1}.{image_ext}"
                        )
                        await asyncio.to_thread(
                            _download_url_to_file_with_referer,
                            photo_url,
                            out_path,
                            url,
                        )
                        downloaded_files.append(out_path)

                    if not downloaded_files:
                        await message.reply_text(get_message("no_photo", lang))
                        return

                    media = []
                    handles = []
                    try:
                        for i, fpath in enumerate(downloaded_files):
                            photo_file = open(fpath, "rb")
                            handles.append(photo_file)
                            media.append(
                                InputMediaPhoto(
                                    media=photo_file,
                                    caption=title if i == 0 else None,
                                )
                            )
                        await message.reply_media_group(media=media)
                    finally:
                        for h in handles:
                            try:
                                h.close()
                            except OSError:
                                pass

                    for fpath in downloaded_files:
                        try:
                            os.remove(fpath)
                        except OSError:
                            pass
                    await message.reply_text(get_message("cleaned", lang))
                    return
                except Exception:  # pylint: disable=broad-except
                    for fpath in downloaded_files:
                        try:
                            os.remove(fpath)
                        except OSError:
                            pass
                    raise

            if "/photo/" in tiktok_path:
                image_url, title_html = await asyncio.to_thread(
                    _extract_image_info_from_html, url
                )
                if image_url:
                    title = title_html or "image"
                    safe_title = re.sub(r"[\\/:*?\"<>|]", "_", title)
                    parsed_img = urlparse(image_url)
                    img_ext = os.path.splitext(parsed_img.path)[1].lower().lstrip(".")
                    image_ext = img_ext if img_ext in IMAGE_EXTENSIONS else "jpg"
                    filename = str(DOWNLOAD_DIR / f"{safe_title}.{image_ext}")

                    await asyncio.to_thread(_download_url_to_file, image_url, filename)

                    if not os.path.exists(filename):
                        raise RuntimeError("Downloaded image not found")

                    file_size = os.path.getsize(filename)
                    if file_size > MAX_FILE_SIZE_BYTES:
                        size_mb = file_size / (1024 * 1024)
                        await message.reply_text(
                            get_message("too_big", lang).format(size_mb=size_mb)
                        )
                        os.remove(filename)
                        return

                    with open(filename, "rb") as photo_file:
                        await message.reply_photo(photo=photo_file, caption=title)

                    os.remove(filename)
                    await message.reply_text(get_message("cleaned", lang))
                    return

                logger.info("TikTok photo extraction returned 0 images for photo URL")
                await message.reply_text(get_message("no_photo", lang))
                return

        # Autres sites : tentative via yt-dlp
        info = None

        def _extract_other_info() -> dict | None:
            ydl_opts = {
                "skip_download": True,
            }
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                return ydl.extract_info(url, download=False)

        info = await asyncio.to_thread(_extract_other_info)

        if not info:
            await message.reply_text(get_message("no_photo", lang))
            return

        image_url = None
        image_ext = "jpg"

        # 1) Cas d'une URL qui pointe déjà directement vers une image
        parsed = urlparse(url)
        direct_ext = os.path.splitext(parsed.path)[1].lower().lstrip(".")
        if direct_ext in IMAGE_EXTENSIONS:
            image_url = url
            image_ext = direct_ext
        else:
            # 2) Utiliser l'URL et l'extension issues des métadonnées yt-dlp
            info_url = info.get("url")
            info_ext = (info.get("ext") or "").lower()
            if info_url and info_ext in IMAGE_EXTENSIONS:
                image_url = info_url
                image_ext = info_ext
            else:
                # 3) Chercher dans les miniatures et prendre la plus grande
                thumbs = info.get("thumbnails") or []
                if thumbs:
                    best = max(thumbs, key=lambda t: t.get("width") or 0)
                    image_url = best.get("url")
                    if image_url:
                        thumb_path = urlparse(image_url).path
                        thumb_ext = os.path.splitext(thumb_path)[1].lower().lstrip(".")
                        if thumb_ext in IMAGE_EXTENSIONS:
                            image_ext = thumb_ext

        if not image_url:
            await message.reply_text(get_message("no_photo", lang))
            return

        title = info.get("title") or "image"
        safe_title = re.sub(r"[\\/:*?\"<>|]", "_", title)
        filename = str(DOWNLOAD_DIR / f"{safe_title}.{image_ext}")

        await asyncio.to_thread(_download_url_to_file, image_url, filename)

        if not os.path.exists(filename):
            raise RuntimeError("Downloaded image not found")

        file_size = os.path.getsize(filename)
        if file_size > MAX_FILE_SIZE_BYTES:
            size_mb = file_size / (1024 * 1024)
            await message.reply_text(
                get_message("too_big", lang).format(size_mb=size_mb)
            )
            os.remove(filename)
            return

        with open(filename, "rb") as photo_file:
            await message.reply_photo(photo=photo_file, caption=title)

        os.remove(filename)
        await message.reply_text(get_message("cleaned", lang))

    except DownloadError as e:
        logger.exception("Download error while processing photo URL")
        error_text = str(e)
        if "Unsupported URL" in error_text:
            # Dernière tentative : lecture directe du HTML pour récupérer une image
            image_url, title_html = await asyncio.to_thread(
                _extract_image_info_from_html, url
            )
            if not image_url:
                await message.reply_text(get_message("no_photo", lang))
            else:
                image_ext = "jpg"
                parsed_img = urlparse(image_url)
                img_ext = os.path.splitext(parsed_img.path)[1].lower().lstrip(".")
                if img_ext in IMAGE_EXTENSIONS:
                    image_ext = img_ext

                title = title_html or "image"
                safe_title = re.sub(r"[\\/:*?\"<>|]", "_", title)
                filename = str(DOWNLOAD_DIR / f"{safe_title}.{image_ext}")

                try:
                    await asyncio.to_thread(
                        _download_url_to_file, image_url, filename
                    )

                    if not os.path.exists(filename):
                        raise RuntimeError("Downloaded image not found")

                    file_size = os.path.getsize(filename)
                    if file_size > MAX_FILE_SIZE_BYTES:
                        size_mb = file_size / (1024 * 1024)
                        await message.reply_text(
                            get_message("too_big", lang).format(size_mb=size_mb)
                        )
                        os.remove(filename)
                        return

                    with open(filename, "rb") as photo_file:
                        await message.reply_photo(photo=photo_file, caption=title)

                    os.remove(filename)
                    await message.reply_text(get_message("cleaned", lang))

                except Exception as inner_e:  # pylint: disable=broad-except
                    logger.exception("Error while processing HTML photo fallback")
                    await message.reply_text(
                        get_message("error", lang).format(error=str(inner_e))
                    )
                    if filename and os.path.exists(filename):
                        try:
                            os.remove(filename)
                        except OSError:
                            pass
        else:
            await message.reply_text(
                get_message("error", lang).format(error=error_text)
            )
            if filename and os.path.exists(filename):
                try:
                    os.remove(filename)
                except OSError:
                    pass

    except Exception as e:  # pylint: disable=broad-except
        logger.exception("Error while processing photo URL")
        await message.reply_text(
            get_message("error", lang).format(error=str(e))
        )
        if filename and os.path.exists(filename):
            try:
                os.remove(filename)
            except OSError:
                pass


async def quality_callback(
    update: Update, context: ContextTypes.DEFAULT_TYPE
) -> None:
    """Callback pour le choix de qualité HD/SD."""

    query = update.callback_query
    if not query:
        return

    _maybe_set_bot_username(getattr(context.bot, "username", None))

    try:
        await query.answer()
    except (BadRequest, NetworkError, TimedOut):
        pass

    lang = get_user_lang(update)
    url = context.user_data.get("last_url")
    if not url:
        await query.message.reply_text(get_message("no_url_saved", lang))
        return

    data = query.data or ""
    quality = "hd" if data == "quality_hd" else "sd"

    context.user_data["last_action"] = "video"
    context.user_data["last_quality"] = quality
    context.user_data.setdefault("last_audio_lang", "orig")

    keyboard = InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton(get_message("audio_lang_orig", lang), callback_data="alang_orig"),
                InlineKeyboardButton(get_message("audio_lang_fr", lang), callback_data="alang_fr"),
                InlineKeyboardButton(get_message("audio_lang_en", lang), callback_data="alang_en"),
            ]
        ]
    )
    await query.message.reply_text(
        get_message("choose_audio_lang", lang),
        reply_markup=keyboard,
        disable_web_page_preview=True,
    )


async def audio_lang_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not query:
        return

    _maybe_set_bot_username(getattr(context.bot, "username", None))

    try:
        await query.answer()
    except (BadRequest, NetworkError, TimedOut):
        pass

    lang = get_user_lang(update)
    url = context.user_data.get("last_url")
    if not url:
        await query.message.reply_text(get_message("no_url_saved", lang))
        return

    quality = context.user_data.get("last_quality")
    if quality not in ("hd", "sd"):
        quality = "hd"

    data = query.data or ""
    audio_lang = "orig"
    if data == "alang_fr":
        audio_lang = "fr"
    elif data == "alang_en":
        audio_lang = "en"

    context.user_data["last_audio_lang"] = audio_lang
    await process_url(query.message, url, lang, quality, audio_lang)


async def type_callback(
    update: Update, context: ContextTypes.DEFAULT_TYPE
) -> None:
    """Callback pour le choix Vidéo / Audio."""

    query = update.callback_query
    if not query:
        return

    _maybe_set_bot_username(getattr(context.bot, "username", None))

    try:
        await query.answer()
    except (BadRequest, NetworkError, TimedOut):
        pass

    lang = get_user_lang(update)
    url = context.user_data.get("last_url")
    if not url:
        await query.message.reply_text(get_message("no_url_saved", lang))
        return

    data = query.data or ""
    logger.info("Type callback: %s (url=%s)", data, url)
    if data == "type_video":
        context.user_data["last_action"] = "video"
        keyboard = InlineKeyboardMarkup(
            [
                [
                    InlineKeyboardButton("🔼 HD (meilleure qualité)", callback_data="quality_hd"),
                    InlineKeyboardButton("🔽 SD (rapide)", callback_data="quality_sd"),
                ]
            ]
        )
        await query.message.reply_text(
            get_message("choose_quality", lang), reply_markup=keyboard
        )
    elif data == "type_audio":
        context.user_data["last_action"] = "audio"
        context.user_data.pop("last_quality", None)
        await process_audio_url(query.message, url, lang)
    elif data == "type_effects":
        if update.effective_user:
            kind = await _plan_effect_entitlement(update.effective_user.id)
            if kind is None:
                await query.message.reply_text(
                    get_message("premium_need_more", lang),
                    reply_markup=_premium_keyboard(lang),
                )
                return
            context.user_data["effects_entitlement_kind"] = kind
        
        keyboard = InlineKeyboardMarkup(
            [
                [
                    InlineKeyboardButton(
                        get_message("effects_mode_preset", lang), callback_data="effect_mode_preset"
                    )
                ],
                [
                    InlineKeyboardButton(
                        get_message("effects_mode_steal", lang), callback_data="effect_mode_steal"
                    )
                ],
            ]
        )
        await query.message.reply_text(get_message("effects_intro", lang), reply_markup=keyboard)
    elif data == "type_photo":
        await query.message.reply_text(get_message("photo_disabled", lang))


async def effect_mode_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Callback pour choix du mode effet: preset ou vol de style."""
    query = update.callback_query
    if not query:
        return

    _maybe_set_bot_username(getattr(context.bot, "username", None))

    try:
        await query.answer()
    except (BadRequest, NetworkError, TimedOut):
        pass

    lang = get_user_lang(update)
    data = query.data or ""

    if data == "effect_mode_preset":
        buttons = []
        for preset_id, preset in PRESET_EFFECTS.items():
            name = preset[f"name_{lang}"]
            buttons.append(
                [InlineKeyboardButton(name, callback_data=f"effect_preset_{preset_id}")]
            )
        keyboard = InlineKeyboardMarkup(buttons)
        await query.message.reply_text(get_message("effects_choose_preset", lang), reply_markup=keyboard)

    elif data == "effect_mode_steal":
        context.user_data["effects_mode"] = "steal"
        context.user_data["effects_waiting_ref_url"] = True
        await query.message.reply_text(get_message("effects_steal_intro", lang))


async def effect_preset_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Callback pour sélection d'un effet prédéfini."""
    query = update.callback_query
    if not query:
        return

    _maybe_set_bot_username(getattr(context.bot, "username", None))

    try:
        await query.answer()
    except (BadRequest, NetworkError, TimedOut):
        pass

    lang = get_user_lang(update)
    data = query.data or ""

    if not data.startswith("effect_preset_"):
        return

    preset_id = data.split("_", 2)[2]
    preset = PRESET_EFFECTS.get(preset_id)
    if not preset:
        await query.message.reply_text(get_message("error_try_again", lang))
        return

    context.user_data["effects_mode"] = "preset"
    context.user_data["effects_preset_id"] = preset_id
    context.user_data["effects_waiting_video"] = True

    effect_name = preset[f"name_{lang}"]
    effect_desc = preset[f"desc_{lang}"]
    await query.message.reply_text(
        get_message("effects_preset_selected", lang).format(
            effect_name=effect_name, effect_desc=effect_desc
        )
    )


async def retry_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not query:
        return

    _maybe_set_bot_username(getattr(context.bot, "username", None))

    try:
        await query.answer()
    except (BadRequest, NetworkError, TimedOut):
        pass

    lang = get_user_lang(update)
    url = context.user_data.get("last_url")
    if not url:
        await query.message.reply_text(get_message("no_url_saved", lang))
        return

    data = query.data or ""
    if data.startswith("retry_video_"):
        quality = data.split("_", 2)[2]
        if quality not in ("hd", "sd"):
            quality = "hd"
        context.user_data["last_action"] = "video"
        context.user_data["last_quality"] = quality
        audio_lang = context.user_data.get("last_audio_lang")
        if not isinstance(audio_lang, str) or audio_lang not in ("orig", "fr", "en"):
            audio_lang = "orig"
        await process_url(query.message, url, lang, quality, audio_lang)
        return

    if data == "retry_audio":
        context.user_data["last_action"] = "audio"
        context.user_data.pop("last_quality", None)
        await process_audio_url(query.message, url, lang)
        return


def _premium_keyboard(lang: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton(
                    get_message("premium_buy_month", lang), callback_data="premium_buy_month"
                )
            ],
            [
                InlineKeyboardButton(
                    get_message("premium_buy_credits10", lang),
                    callback_data="premium_buy_credits10",
                ),
                InlineKeyboardButton(
                    get_message("premium_buy_credits50", lang),
                    callback_data="premium_buy_credits50",
                ),
            ],
            [
                InlineKeyboardButton(
                    get_message("premium_my_ref", lang), callback_data="premium_my_ref"
                )
            ],
            [InlineKeyboardButton(get_message("menu_button", lang), callback_data="menu_main")],
        ]
    )


async def _send_premium_menu(message, update: Update, lang: str) -> None:
    if not message or not update.effective_user:
        return
    rec = await _get_user_record(update.effective_user.id)
    now = int(time.time())
    until = rec.get("premium_until")
    until_i = int(until) if isinstance(until, (int, float)) else 0
    credits = _get_credits(rec)
    if until_i > now:
        status_line = (
            f"✅ Premium actif jusqu'au {_format_premium_until(until_i, lang)}"
            if lang == "fr"
            else f"✅ Premium active until {_format_premium_until(until_i, lang)}"
        )
    else:
        status_line = "🆓 Mode gratuit" if lang == "fr" else "🆓 Free mode"
    credits_line = (
        f"🎟️ Crédits: {credits}" if lang == "fr" else f"🎟️ Credits: {credits}"
    )
    ref_link = _ref_link_for_user(update.effective_user.id)
    ref_line = (
        ("🎁 Ton lien parrainage: " + ref_link)
        if (lang == "fr" and ref_link)
        else (("🎁 Your referral link: " + ref_link) if ref_link else "")
    )
    text = get_message("premium_menu_title", lang) + "\n\n" + status_line + "\n" + credits_line
    if ref_line:
        text += "\n\n" + ref_line
    await message.reply_text(text, reply_markup=_premium_keyboard(lang), disable_web_page_preview=True)


async def premium_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    _maybe_set_bot_username(getattr(context.bot, "username", None))
    lang = get_user_lang(update)
    msg = update.message or update.effective_message
    if not msg:
        return
    await _send_premium_menu(msg, update, lang)


async def premium_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not query:
        return
    _maybe_set_bot_username(getattr(context.bot, "username", None))
    try:
        await query.answer()
    except (BadRequest, NetworkError, TimedOut):
        pass
    lang = get_user_lang(update)
    data = query.data or ""
    user = update.effective_user
    chat = update.effective_chat
    if not user or not chat:
        return

    if data == "premium_my_ref":
        ref_link = _ref_link_for_user(user.id)
        if not ref_link:
            await query.message.reply_text(get_message("error_try_again", lang))
            return
        await query.message.reply_text(ref_link, disable_web_page_preview=True)
        return

    if data == "premium_buy_month":
        payload = f"cx|premium_30d|{user.id}"
        prices = [LabeledPrice(label="Premium 30d", amount=PREMIUM_30D_STARS)]
        await context.bot.send_invoice(
            chat_id=chat.id,
            title=("⭐ Premium 30 jours" if lang == "fr" else "⭐ Premium 30 days"),
            description=(
                "Sans pubs + Effets illimités + priorité"
                if lang == "fr"
                else "No ads + unlimited Effects + priority"
            ),
            payload=payload,
            provider_token="",
            currency="XTR",
            prices=prices,
        )
        return

    if data == "premium_buy_credits10":
        payload = f"cx|credits_10|{user.id}"
        prices = [LabeledPrice(label="10 credits", amount=CREDITS_10_STARS)]
        await context.bot.send_invoice(
            chat_id=chat.id,
            title=("🎟️ Pack 10 crédits" if lang == "fr" else "🎟️ 10 credits pack"),
            description=(
                "Utilise-les pour ✨ Effets et options premium"
                if lang == "fr"
                else "Use them for ✨ Effects and premium options"
            ),
            payload=payload,
            provider_token="",
            currency="XTR",
            prices=prices,
        )
        return

    if data == "premium_buy_credits50":
        payload = f"cx|credits_50|{user.id}"
        prices = [LabeledPrice(label="50 credits", amount=CREDITS_50_STARS)]
        await context.bot.send_invoice(
            chat_id=chat.id,
            title=("🎟️ Pack 50 crédits" if lang == "fr" else "🎟️ 50 credits pack"),
            description=(
                "Utilise-les pour ✨ Effets et options premium"
                if lang == "fr"
                else "Use them for ✨ Effects and premium options"
            ),
            payload=payload,
            provider_token="",
            currency="XTR",
            prices=prices,
        )
        return


async def precheckout_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = getattr(update, "pre_checkout_query", None)
    if not query:
        return
    payload = getattr(query, "invoice_payload", None)
    ok = isinstance(payload, str) and payload.startswith("cx|")
    try:
        await query.answer(ok=ok, error_message=(None if ok else "Invalid invoice"))
    except Exception:
        pass


async def successful_payment_handler(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.message or update.effective_message
    if not msg or not update.effective_user:
        return
    sp = getattr(msg, "successful_payment", None)
    if not sp:
        return
    payload = getattr(sp, "invoice_payload", None)
    if not isinstance(payload, str) or not payload.startswith("cx|"):
        return
    parts = payload.split("|")
    if len(parts) < 3:
        return
    product = parts[1]
    try:
        target_user_id = int(parts[2])
    except Exception:
        target_user_id = update.effective_user.id

    lang = get_user_lang(update)
    if target_user_id != update.effective_user.id:
        target_user_id = update.effective_user.id

    if product == "premium_30d":
        await _grant_premium(target_user_id, PREMIUM_DURATION_SECONDS)
        await msg.reply_text(
            "✅ Premium activé !" if lang == "fr" else "✅ Premium activated!",
            reply_markup=_main_menu_keyboard(lang),
        )
        return

    if product == "credits_10":
        await _add_credits(target_user_id, 10)
        await msg.reply_text(
            "✅ +10 crédits ajoutés !" if lang == "fr" else "✅ +10 credits added!",
            reply_markup=_main_menu_keyboard(lang),
        )
        return

    if product == "credits_50":
        await _add_credits(target_user_id, 50)
        await msg.reply_text(
            "✅ +50 crédits ajoutés !" if lang == "fr" else "✅ +50 credits added!",
            reply_markup=_main_menu_keyboard(lang),
        )
        return


def main() -> None:
    token = os.getenv("TELEGRAM_BOT_TOKEN")
    if not token:
        raise RuntimeError(
            "TELEGRAM_BOT_TOKEN environment variable is not set. "
            "Please set it to your bot token from BotFather."
        )

    _start_healthcheck_server_if_needed()
    try:
        _cleanup_download_dir_if_needed()
    except Exception:
        logger.exception("Startup cleanup failed")

    async def _post_init(app: Application) -> None:
        try:
            me = await app.bot.get_me()
            _maybe_set_bot_username(getattr(me, "username", None))
        except Exception:
            logger.exception("Bot post_init failed")

    request = HTTPXRequest(
        read_timeout=600.0,
        write_timeout=600.0,
        connect_timeout=10.0,
        pool_timeout=10.0,
    )

    application = (
        Application.builder()
        .token(token)
        .request(request)
        .post_init(_post_init)
        .build()
    )

    application.add_handler(CommandHandler("start", start))
    application.add_handler(CommandHandler("menu", menu_command))
    application.add_handler(CommandHandler("help", help_command))
    application.add_handler(CommandHandler("premium", premium_command))
    application.add_handler(CallbackQueryHandler(menu_callback, pattern="^menu_"))
    application.add_handler(CallbackQueryHandler(retry_callback, pattern="^retry_"))
    application.add_handler(CallbackQueryHandler(audio_lang_callback, pattern="^alang_"))
    application.add_handler(CallbackQueryHandler(type_callback, pattern="^type_"))
    application.add_handler(CallbackQueryHandler(effect_mode_callback, pattern="^effect_mode_"))
    application.add_handler(CallbackQueryHandler(effect_preset_callback, pattern="^effect_preset_"))
    application.add_handler(CallbackQueryHandler(quality_callback, pattern="^quality_"))
    application.add_handler(CallbackQueryHandler(premium_callback, pattern="^premium_"))
    application.add_handler(PreCheckoutQueryHandler(precheckout_callback))
    application.add_handler(MessageHandler(filters.SUCCESSFUL_PAYMENT, successful_payment_handler))
    application.add_handler(
        MessageHandler(filters.ALL & ~filters.COMMAND, handle_message)
    )

    async def _error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
        _ = update
        err = getattr(context, "error", None)
        if err is None:
            return
        if isinstance(err, (TimedOut, NetworkError, BadRequest)):
            logger.debug("Telegram error suppressed: %s", err.__class__.__name__)
            return
        logger.error("Telegram handler error: %s", err, exc_info=err)

    application.add_error_handler(_error_handler)

    logger.info("Bot started. Press Ctrl+C to stop.")
    application.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
