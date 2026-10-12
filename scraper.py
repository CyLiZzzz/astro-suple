"""Suply · comparador de precios de suplementos (v0.3)

Junta las ofertas de varias tiendas online argentinas, las normaliza, agrupa el mismo producto
entre tiendas y guarda el historial de precios.

Uso:  python scraper.py
Genera:  datos.json (lo que lee el sitio), reporte.json (qué pasó en cada tienda) y precios.db.

Principios de funcionamiento
- Visitante educado: se identifica con un User-Agent honesto, respeta robots.txt (incluido crawl-delay),
  espacia los pedidos con una pausa variable, reintenta con espera creciente y respeta Retry-After.
- Si una tienda muestra señales de bloqueo (403 repetidos, captcha, desafío anti-bots) se detiene ahí:
  no intenta esquivarlo.
- Un producto o una página que falla no frena la corrida; una tienda que falla no frena a las demás.
- Cada enlace sale del mismo registro que el precio, así que lleva al producto (y a la variante) exacto.
"""
import email.utils
import gzip
import hashlib
import http.client
import json
import os
import random
import re
import socket
import sqlite3
import ssl
import statistics
import sys
import tempfile
import threading
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import urllib.robotparser
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from html import unescape

# ============================ CONFIGURACIÓN ============================
# tipo "auto": detecta Shopify / WooCommerce / otra.  "shopify", "woocommerce", "sitemap", "mercadolibre".
# patron: parte de la dirección de las páginas de producto.  marca: tienda de una sola marca.
# efectivo: descuento por transferencia o efectivo (0.15 = 15%).  filtrar_urls: False = leer todo el sitemap.
TIENDAS = [
    {"nombre": "Disfit", "base": "https://www.disfit.com.ar", "tipo": "sitemap", "patron": "/productos/"},
    {"nombre": "ENA Sport", "base": "https://www.enasport.com", "tipo": "shopify", "marca": "ENA"},
    {"nombre": "Recoleta al Fallo", "base": "https://recoletaalfallo.com.ar", "tipo": "auto", "efectivo": 0.15},
    {"nombre": "Suplementate", "base": "https://suplementate.com.ar", "tipo": "auto"},
    {"nombre": "Nutrición Muscular", "base": "https://nutricionmuscular.com.ar", "tipo": "auto"},
    {"nombre": "DeMusculos", "base": "https://www.demusculos.com", "tipo": "auto"},
    {"nombre": "Morashop", "base": "https://www.morashop.ar", "tipo": "auto"},
    {"nombre": "Rosario Suplementos", "base": "https://rosariosuplementos.com", "tipo": "auto"},
    {"nombre": "Gentech", "base": "https://www.gentech.com.ar", "tipo": "auto", "marca": "Gentech"},
    {"nombre": "Nutrishop", "base": "https://www.nutrishop.com.ar", "tipo": "sitemap"},
    {"nombre": "Mercado Libre", "tipo": "mercadolibre"},
]
ML_CONSULTAS = ["creatina monohidrato", "whey protein", "proteina en polvo", "pre entreno", "bcaa",
                "citrato de magnesio", "bisglicinato de magnesio", "omega 3", "vitamina d3", "multivitaminico",
                "colageno hidrolizado", "ganador de peso", "quemador de grasa", "barras proteicas", "electrolitos isotonico"]
ML_VENDEDORES = {"NUTRISHOP": "Nutrishop (Mercado Libre)"}  # nombre de usuario -> cómo se muestra

DB, SALIDA, REPORTE = "precios.db", "datos.json", "reporte.json"
CONTACTO = os.environ.get("SCRAPER_CONTACTO", "")       # ej. "contacto@tusitio.com": las tiendas pueden escribirte
PAUSA = 2.0               # segundos mínimos entre pedidos a un mismo sitio
VARIACION = 0.3           # la pausa varía ±30% para no ser un reloj
TIMEOUT = 30
REINTENTOS = 4
FALLAS_SEGUIDAS = 8       # pedidos fallidos seguidos a un sitio antes de dejarlo en paz
MAX_PAGINAS = 400         # tope de seguridad contra bucles (no limita el catálogo real)
MAX_SEGUNDOS_TIENDA = 3000
HILOS = 4                 # tiendas en paralelo (cada sitio igual se lee de a un pedido)
DIAS_HISTORIAL = 90
VERIFICAR_ENLACES = int(os.environ.get("SCRAPER_VERIFICAR", "2"))   # enlaces a comprobar por tienda (0 = ninguno)
PISO_CONSERVAR = 0.5      # si una tienda devuelve menos de este % de lo anterior, se conserva la lectura previa
TOL_TAMANO = 0.03         # tamaños a menos de 3% se consideran el mismo (907 g y 908 g, 2 lb y 900 g)
BOT = "Suply"
VERSION = "0.3"
UA = f"{BOT}/{VERSION} (comparador de precios; respeta robots.txt" + (f"; {CONTACTO}" if CONTACTO else "") + ")"

# ============================ NORMALIZACIÓN ============================
def sin_acentos(s):
    return "".join(c for c in unicodedata.normalize("NFD", str(s)) if unicodedata.category(c) != "Mn")


def clave_texto(s):
    return re.sub(r"[^a-z0-9]", "", sin_acentos(s).lower())


MARCAS = ["Star Nutrition", "One Fit", "ENA", "Gold Nutrition", "Integralmedica", "xBody Evolution", "Xtrength",
          "Nutremax", "Hoch Sport", "Nucleo Fit", "MuscleTech", "My Protein", "Optimum Nutrition",
          "Universal Nutrition", "BSN", "Body Advance", "Mervick", "Gentech", "Weider", "Pure Nutrition", "Vitalgen",
          "226ERS", "Granger", "Innova Naturals", "Proyec", "Natuliv", "NF Nutrition", "Aker", "Nutrex", "Dymatize",
          "VitaTech", "DMS", "Pulver", "Genetic", "Nutrilab", "Cellucor", "Ronnie Coleman"]
ALIAS_MARCAS = {"enasport": "ENA", "starnutritionargentina": "Star Nutrition", "star": "Star Nutrition",
                "onefitnutrition": "One Fit", "xtrenght": "Xtrength", "innovanaturals": "Innova Naturals",
                "optimumnutritionon": "Optimum Nutrition", "dmsnutrition": "DMS", "xbody": "xBody Evolution"}
MARCAS_GENERICAS = {"", "default", "sin marca", "varios", "otros", "generico", "genérico", "n/a"}
_CANON = {clave_texto(m): m for m in MARCAS}
_CANON.update(ALIAS_MARCAS)
_RE_MARCAS = [(m, re.compile(rf"(?<!\w){re.escape(m)}(?!\w)", re.I)) for m in sorted(MARCAS, key=len, reverse=True)]
_RE_MARCAS += [(c, re.compile(rf"(?<!\w){re.escape(a)}(?!\w)", re.I)) for a, c in
               (("ena sport", "ENA"), ("one fit nutrition", "One Fit"), ("xtrenght", "Xtrength"))]


def canon_marca(m):
    """Marca informada por la tienda: descarta las genéricas, unifica alias y mayúsculas."""
    m = re.sub(r"\s+", " ", str(m or "")).strip()
    if m.lower() in MARCAS_GENERICAS or len(m) > 40:
        return None
    return _CANON.get(clave_texto(m)) or (m.title() if m.isupper() else m)


def marca_de(texto, por_defecto=None):
    for canon, rx in _RE_MARCAS:
        if rx.search(texto):
            return canon
    return por_defecto


# Categorías (el orden importa; "re:" = expresión regular).
CATEGORIAS = [
    ("Creatina", ("creatina", "creatine")),
    ("Magnesio", ("magnesio",)),
    ("Omega 3", ("omega", "aceite de pescado", "fish oil")),
    ("Colágeno", ("colageno", "colágeno", "collagen")),
    ("Ganadores de peso", ("ganador", "mass gainer", "gainer", "mutant mass", "serious mass", "hard mass")),
    ("Quemadores", ("quemador", "termogenico", "termogénico", "carnitina", "fat burner", "burner", "re:\\bcla\\b")),
    ("Pre-entreno", ("pre war", "pre-entreno", "pre entreno", "preentreno", "pre workout", "pre work", "pump",
                     "oxido nitrico", "óxido nítrico", "beta alanine")),
    ("Aminoácidos", ("bcaa", "amino", "glutamina")),
    ("Hidratación", ("isotonico", "isotónico", "electrolito", "hidratante", "hidratacion", "hidratación")),
    ("Barras y snacks", ("barra", "barrita", "pancake", "snack", "re:\\bbars?\\b")),
    ("Proteína", ("whey", "protein", "proteína", "proteina", "isoprot", "ultra mass", "caseina", "caseína")),
    ("Vitaminas", ("vitamina", "multivit", "zma", "zinc", "ashwagandha")),
]
CATEGORIAS_VALIDAS = {c for c, _ in CATEGORIAS}
EXCLUIR = re.compile(r"\b(shakers?|botellas?|vasos?|mochilas?|bolsos?|guantes?|cintos?|combos?|packs?|kits?|remeras?|"
                     r"buzos?|shorts?|termos?|medidor|straps|muñequeras?|rodilleras?)\b", re.I)


def _hay(t, c):
    return bool(re.search(c[3:], t)) if c.startswith("re:") else c in t


def categoria(texto):
    t = str(texto).lower()
    if EXCLUIR.search(t):
        return None
    for nombre, claves in CATEGORIAS:
        if any(_hay(t, c) for c in claves):
            return nombre
    return None


# Variantes que NO se deben mezclar al comparar (primera que coincida). Incluye sinónimos.
TIPOS = {
    "Creatina": [("creapure", "creapure"), ("magnesio", "con magnesio"), ("colageno|colágeno", "con colágeno"),
                 ("electrolitos", "con electrolitos"), ("clorhidrato|\\bhcl\\b", "HCl")],
    "Proteína": [("isolate|isolada|aislada|aislado|isoprot", "aislada"), ("hidrolizad|hydrolyz", "hidrolizada"),
                 ("beef|carne|bovina", "de carne"), ("vegetal|plant|arveja|soja|pea\\b", "vegetal"),
                 ("caseina|caseína|micellar|micelar", "caseína")],
    "Magnesio": [("citrato", "citrato"), ("bisglicinato|glicinato|glycinate", "bisglicinato"), ("malato", "malato"),
                 ("treonato", "treonato"), ("cloruro", "cloruro"), ("duo|dúo", "duo")],
    "Aminoácidos": [("bcaa", "bcaa"), ("glutamina|glutamine", "glutamina"), ("amino", "aminoácidos")],
    "Pre-entreno": [("oxido nitrico|óxido nítrico", "óxido nítrico"), ("beta alanine", "beta alanina")],
    "Vitaminas": [("d3.*k2|k2", "D3 + K2"), ("d3|vitamina d", "vitamina D"), ("vitamina c", "vitamina C"),
                  ("b12", "B12"), ("multivit", "multivitamínico"), ("zma", "ZMA"), ("ashwagandha", "ashwagandha")],
    "Colágeno": [("hidrolizad|hydrolyz", "hidrolizado")],
    "Quemadores": [("carnitina", "L-carnitina"), ("\\bcla\\b", "CLA"), ("termog", "termogénico")],
    "Hidratación": [("isoton|isotón", "isotónica"), ("electrol", "electrolitos"), ("\\bgel", "gel")],
}
TIPO_POR_DEFECTO = {"Creatina": "monohidrato", "Proteína": "whey"}


def tipo_de(cat, texto):
    for patron, etiqueta in TIPOS.get(cat, []):
        if re.search(patron, texto, re.I):
            return etiqueta
    return TIPO_POR_DEFECTO.get(cat, "")


def numero(x):
    """Convierte '28.176', '28.176,50', '74900.00', 28176 o '$ 1,5' en float (formato argentino y anglosajón)."""
    if x is None or isinstance(x, bool):
        return None
    if isinstance(x, (int, float)):
        return float(x)
    s = re.sub(r"[^\d,.\-]", "", str(x))
    if not s or s in "-.,":
        return None
    if "," in s and "." in s:
        s = s.replace(".", "").replace(",", ".") if s.rfind(",") > s.rfind(".") else s.replace(",", "")
    elif "," in s:
        s = s.replace(",", ".") if re.search(r",\d{1,2}$", s) else s.replace(",", "")
    elif s.count(".") > 1 or re.search(r"\.\d{3}$", s):
        s = s.replace(".", "")
    try:
        return float(s)
    except ValueError:
        return None


_MASA = re.compile(r"(\d+(?:[.,]\d+)?)\s*(kilos?|kgs?|gramos?|grs?|g|libras?|lbs?|lb|onzas?|oz)\b", re.I)
UNIDADES = (r"(?:caps\w*|c[aá]psulas?|comprimidos?|tabs?|tabletas?|softgels?|perlas?|gomitas?|bars?|barras?|"
            r"barritas?|unidades?|sobres?|sticks?|geles?|pancakes?)")


def cantidad(texto):
    """(cantidad, unidad): gramos 'g' (todo se lleva a gramos) o unidades 'u' (cápsulas, barras...), o None.
    Si el texto trae gramos y libras ('2 lb (908 g)') se prefieren los gramos."""
    t = str(texto).lower()
    cand = []
    for m in _MASA.finditer(t):
        n, u = numero(m.group(1)), m.group(2)
        if n is None:
            continue
        explicito = u.startswith(("k", "g"))
        if u.startswith("k"):
            n *= 1000
        elif u.startswith(("lb", "libra")):
            n *= 453.592
        elif u.startswith(("oz", "onza")):
            n *= 28.3495
        if n >= 50:  # menos de 50 g suele ser una porción o dosis, no el envase
            cand.append((explicito, n))
    if cand:
        pref = [n for e, n in cand if e] or [n for _, n in cand]
        return int(round(max(pref))), "g"
    m = re.search(rf"(?:x\s*)?(\d{{1,4}})\s*{UNIDADES}\b", t) or re.search(rf"{UNIDADES}\s*[x×]?\s*(\d{{1,4}})\b", t)
    if m and 2 <= int(m.group(1)) <= 1000:
        return int(m.group(1)), "u"
    return None


_TRACK = re.compile(r"^(utm_|fbclid|gclid|mc_|_ga|ref$|ref_|srsltid|sca_esv|cart_)", re.I)


def limpiar_url(u):
    """Saca parámetros de seguimiento y fragmentos; conserva los que eligen la variante (variant=, attribute_...)."""
    p = urllib.parse.urlsplit(str(u).strip())
    q = [(k, v) for k, v in urllib.parse.parse_qsl(p.query, keep_blank_values=True) if not _TRACK.match(k)]
    return urllib.parse.urlunsplit((p.scheme, p.netloc, p.path, urllib.parse.urlencode(q), ""))


def limpiar(html, largo=260):
    t = re.sub(r"\s+", " ", unescape(re.sub(r"<[^>]+>", " ", html or ""))).strip()
    return t if len(t) <= largo else t[:largo].rsplit(" ", 1)[0] + "…"


ENCABEZADOS = [("beneficios", ("aportes y beneficios",)),
               ("nutri", ("información nutricional", "informacion nutricional", "tabla nutricional")),
               ("ingredientes", ("ingredientes",)),
               ("uso", ("sugerencia de uso", "modo de uso", "modo de empleo", "forma de uso", "cómo tomarlo", "como tomarlo"))]


def lineas(html):
    h = re.sub(r"(?i)<\s*/?\s*(br|p|li|tr|div|ul|ol|h[1-6]|table)\b[^>]*>", "\n", html or "")
    h = re.sub(r"(?i)</t[dh]\s*>", " | ", h)
    h = re.sub(r"<[^>]+>", " ", h)
    out = []
    for l in unescape(h).split("\n"):
        l = re.sub(r"[ \t\u00a0]+", " ", l).strip().strip("|").strip()
        if l:
            out.append(l)
    return out


def _encabezado(l):
    t = l.lower().strip(" *#✔•:")
    for clave, nombres in ENCABEZADOS:
        for n in nombres:
            if t == n:
                return clave, ""
            if l.lower().lstrip(" *#").startswith(n + ":"):
                return clave, l.split(":", 1)[1].strip()
    return None, ""


def secciones(html):
    """Beneficios, tabla nutricional, ingredientes y modo de uso de la ficha de un producto."""
    sec, actual = {}, None
    for l in lineas(html):
        clave, resto = _encabezado(l)
        if clave:
            actual = clave
            sec.setdefault(clave, [])
            if resto:
                sec[clave].append(resto)
        elif actual:
            sec[actual].append(l)
    out = {}
    b = [re.sub(r"^[✔•*\-–\s]+", "", l) for l in sec.get("beneficios", [])]
    b = [x for x in b if 8 <= len(x) <= 200][:8]
    if b:
        out["beneficios"] = b
    filas, porcion = [], ""
    for l in sec.get("nutri", []):
        ll = l.replace("*", "").strip()
        cel = [c.strip() for c in re.split(r"\s*\|\s*", ll) if c.strip()]
        if ll.lower().startswith("porci"):
            porcion = ll
        elif len(cel) >= 2 and not cel[0].lower().startswith("nutriente"):
            filas.append((cel + ["-", "-"])[:3] if len(cel) == 2 else cel[:3])
    if filas:
        out["nutri"] = {"porcion": porcion, "filas": filas}
    for clave, largo in (("ingredientes", 700), ("uso", 600)):
        t = " ".join(sec.get(clave, [])).strip()
        if t:
            out[clave] = t[:largo]
    return out


def registro(titulo, variante, precio, url, marca_def=None, extra="", marca_ext=None, lista=0, ean="", sku=""):
    """Oferta normalizada con todos los campos, o None si no sirve (se anota el motivo en ctx si se pasa)."""
    precio, lista = numero(precio), numero(lista) or 0.0
    titulo = re.sub(r"\s+", " ", str(titulo or "")).strip()
    cat = categoria(f"{titulo} {extra}")
    cant = cantidad(variante) or cantidad(titulo)
    if precio is None or not (100 <= precio <= 100_000_000) or not titulo or not url:
        return None
    if cat not in CATEGORIAS_VALIDAS or not cant:
        return None
    nombre = titulo if str(variante or "") in ("", "Default Title") else f"{titulo} - {variante}"
    return {"nombre": nombre, "titulo": titulo, "marca": marca_de(titulo) or canon_marca(marca_ext) or marca_def,
            "cat": cat, "tipo": tipo_de(cat, titulo), "cant": cant[0], "unidad": cant[1], "precio": precio,
            "url": limpiar_url(url), "lista": lista if lista > precio else 0.0, "ean": re.sub(r"\D", "", str(ean or "")),
            "sku": str(sku or ""), "imagen": "", "desc": "", "sabores": [], "info": {}}


# ============================ RED: educada y resistente ============================
class Bloqueado(Exception):
    """El sitio mostró señales de bloqueo: se deja de pedirle (no se intenta esquivar)."""


class ErrorHTTP(Exception):
    def __init__(self, codigo, url=""):
        super().__init__(f"HTTP {codigo} en {url}")
        self.codigo = codigo


class Resp:
    def __init__(self, status, texto, headers):
        self.status, self.texto, self.headers = status, texto, headers

    def json(self):
        return json.loads(self.texto)


_lock_red = threading.Lock()
_hosts = {}        # host -> {"lock", "ultimo", "fallas", "bloqueado"}
_robots = {}       # base -> (parser|None, crawl_delay)


def _host(url):
    h = urllib.parse.urlsplit(url).netloc
    with _lock_red:
        return _hosts.setdefault(h, {"lock": threading.Lock(), "ultimo": 0.0, "fallas": 0, "bloqueado": False})


def reiniciar_red():
    with _lock_red:
        _hosts.clear()
        _robots.clear()


def permitido(url):
    """True si el robots.txt nos deja leer la dirección. Guarda también el crawl-delay del sitio."""
    p = urllib.parse.urlsplit(url)
    base = f"{p.scheme}://{p.netloc}"
    if base not in _robots:
        rp, retraso = urllib.robotparser.RobotFileParser(), 0.0
        try:
            req = urllib.request.Request(f"{base}/robots.txt", headers={"User-Agent": UA})
            rp.parse(urllib.request.urlopen(req, timeout=15).read().decode("utf-8", "replace").splitlines())
            retraso = float(rp.crawl_delay(BOT) or rp.crawl_delay("*") or 0)
        except urllib.error.HTTPError as e:
            rp = None if e.code < 500 else "cerrado"   # 4xx: sin reglas; 5xx: por las dudas no se lee
        except Exception:
            rp = None
        _robots[base] = (rp, retraso)
    rp, _ = _robots[base]
    return rp is None or (rp != "cerrado" and rp.can_fetch(BOT, url))


def _esperar(url):
    h = _host(url)
    base = f"{urllib.parse.urlsplit(url).scheme}://{urllib.parse.urlsplit(url).netloc}"
    intervalo = max(PAUSA, (_robots.get(base) or (None, 0.0))[1])
    with h["lock"]:   # un pedido a la vez por sitio, aunque haya varios hilos
        espera = h["ultimo"] + intervalo * (1 + random.uniform(-VARIACION, VARIACION)) - time.monotonic()
        if espera > 0:
            time.sleep(espera)
        h["ultimo"] = time.monotonic()


def _retry_after(headers):
    v = headers.get("Retry-After") if headers else None
    if not v:
        return None
    try:
        return min(float(v), 300.0)
    except ValueError:
        try:
            return max(0.0, min(300.0, (email.utils.parsedate_to_datetime(v) - datetime.now(timezone.utc)).total_seconds()))
        except Exception:
            return None


_DESAFIO = re.compile(r"cf-browser-verification|cf-chl|just a moment|attention required|captcha|access denied|"
                      r"request blocked|verifying you are human|are you a robot", re.I)


def pedir(url, token=None, robots=True, cabeceras=None):
    """GET con pausa, reintentos con espera creciente y detección de bloqueo. Devuelve Resp (200 o 304)."""
    if robots and not permitido(url):
        raise PermissionError("el robots.txt del sitio no permite lectura automática")
    h = _host(url)
    if h["bloqueado"]:
        raise Bloqueado(f"{urllib.parse.urlsplit(url).netloc}: se dejó de pedir por señales de bloqueo")
    cab = {"User-Agent": UA, "Accept": "text/html,application/json;q=0.9,*/*;q=0.8",
           "Accept-Language": "es-AR,es;q=0.9", "Accept-Encoding": "gzip"}
    cab.update(cabeceras or {})
    if token:
        cab["Authorization"] = f"Bearer {token}"
    intento = 0
    while True:
        intento += 1
        _esperar(url)
        try:
            with urllib.request.urlopen(urllib.request.Request(url, headers=cab), timeout=TIMEOUT) as r:
                cuerpo = r.read()
                if (r.headers.get("Content-Encoding") or "").lower() == "gzip":
                    cuerpo = gzip.decompress(cuerpo)
                texto = cuerpo.decode(r.headers.get_content_charset() or "utf-8", "replace")
                if len(texto) < 30000 and _DESAFIO.search(texto[:6000]) and "json" not in (r.headers.get("Content-Type") or ""):
                    h["bloqueado"] = True
                    raise Bloqueado(f"{urllib.parse.urlsplit(url).netloc}: la página parece un desafío anti-bots")
                h["fallas"] = 0
                return Resp(r.status, texto, r.headers)
        except urllib.error.HTTPError as e:
            if e.code == 304:
                h["fallas"] = 0
                return Resp(304, "", e.headers)
            sitio = urllib.parse.urlsplit(url).netloc
            if e.code in (401, 403):          # acceso denegado: no se insiste ni se esquiva
                h["fallas"] += 1
                if h["fallas"] >= 3:
                    h["bloqueado"] = True
                    raise Bloqueado(f"{sitio}: acceso denegado ({e.code}) repetido")
                raise ErrorHTTP(e.code, url)
            if e.code == 429 or e.code >= 500:  # sobrecarga: se espera lo que pide el sitio y se reintenta
                h["fallas"] += 1
                if h["fallas"] >= FALLAS_SEGUIDAS:
                    h["bloqueado"] = True
                    raise Bloqueado(f"{sitio}: demasiados errores {e.code} seguidos")
                if intento > REINTENTOS:
                    raise ErrorHTTP(e.code, url)
                time.sleep(_retry_after(e.headers) or min(60, 2 ** intento) + random.uniform(0, 1))
                continue
            raise ErrorHTTP(e.code, url)     # 404 y similares: no se reintenta ni cuenta como falla del sitio
        except (urllib.error.URLError, socket.timeout, TimeoutError, ConnectionError, http.client.HTTPException, ssl.SSLError) as e:
            h["fallas"] += 1
            if h["fallas"] >= FALLAS_SEGUIDAS:
                h["bloqueado"] = True
                raise Bloqueado(f"{urllib.parse.urlsplit(url).netloc}: demasiados fallos de conexión seguidos")
            if intento > REINTENTOS:
                raise
            time.sleep(min(60, 2 ** intento) + random.uniform(0, 1))


def bajar(url, token=None, robots=True):
    return pedir(url, token=token, robots=robots).texto


class Ctx:
    """Seguimiento de una tienda durante la corrida: errores, motivos de descarte y tiempo."""
    def __init__(self, nombre):
        self.nombre, self.t0 = nombre, time.monotonic()
        self.errores, self.omitidos, self.paginas, self.leidos = [], Counter(), 0, 0
        self.bloqueada = self.vencida = False
        self.filas = []     # lo leído hasta ahora (sirve aunque la tienda corte a mitad)

    def error(self, donde, e):
        self.errores.append(f"{donde}: {e}"[:220])

    def omitir(self, motivo):
        self.omitidos[motivo] += 1

    def vence(self):
        if time.monotonic() - self.t0 > MAX_SEGUNDOS_TIENDA:
            self.vencida = True
        return self.vencida


class Cache:
    """Guarda por página el ETag y lo extraído, para pedir solo lo que cambió (pedidos condicionales)."""
    def __init__(self, con):
        self.con, self.lock = con, threading.Lock()
        with self.lock:
            con.execute("create table if not exists paginas(url text primary key, etag text, modificado text, filas text, fecha text)")

    def get(self, url):
        with self.lock:
            r = self.con.execute("select etag, modificado, filas from paginas where url=?", (url,)).fetchone()
        return (r[0], r[1], json.loads(r[2])) if r else None

    def put(self, url, etag, mod, filas):
        with self.lock:
            self.con.execute("insert or replace into paginas values (?,?,?,?,?)",
                             (url, etag or "", mod or "", json.dumps(filas, ensure_ascii=False), datetime.now(timezone.utc).isoformat()))


# ============================ LECTORES (paginación completa) ============================
def leer_shopify(t, ctx, cache=None):
    filas, pagina, vistos = ctx.filas, 1, set()
    while pagina <= MAX_PAGINAS and not ctx.vence():
        try:
            lote = pedir(f'{t["base"]}/products.json?limit=250&page={pagina}').json().get("products", [])
        except (Bloqueado, PermissionError):
            raise
        except Exception as e:
            ctx.error(f"página {pagina}", e)
            break
        ids = {p.get("id") for p in lote}
        if not lote or ids <= vistos:     # vacía, o la tienda repite la misma página: se terminó
            break
        vistos |= ids
        ctx.paginas += 1
        for p in lote:
            ctx.leidos += 1
            try:
                img = ((p.get("images") or [{}])[0]).get("src", "")
                desc, info = limpiar(p.get("body_html", "")), secciones(p.get("body_html", ""))
                sabores = [x for o in p.get("options", []) if str(o.get("name", "")).lower() in ("sabor", "sabores", "flavor")
                           for x in o.get("values", [])]
                for v in p.get("variants", []):
                    if v.get("available") is False:
                        ctx.omitir("sin_stock")
                        continue
                    # ?variant= hace que el enlace abra justo la variante (tamaño/sabor) que tiene este precio
                    url = f'{t["base"]}/products/{p.get("handle", "")}?variant={v.get("id")}'
                    r = registro(p.get("title", ""), v.get("title", ""), v.get("price"), url, t.get("marca"),
                                 p.get("product_type", ""), marca_ext=p.get("vendor"), lista=v.get("compare_at_price"),
                                 ean=v.get("barcode"), sku=v.get("sku"))
                    if not r:
                        ctx.omitir("no_es_suplemento_o_sin_tamano")
                        continue
                    r.update(imagen=img, desc=desc, sabores=sabores, info=info)
                    filas.append(r)
            except Exception as e:
                ctx.error(f"producto {p.get('handle')}", e)
        pagina += 1
    return filas


def _precio_woo(pr, clave):
    div = 10 ** int(pr.get("currency_minor_unit", 2) or 0)
    n = numero(pr.get(clave))
    return n / div if n is not None else None


def leer_woo(t, ctx, cache=None):
    filas, pagina, total = ctx.filas, 1, None
    while pagina <= MAX_PAGINAS and not ctx.vence():
        try:
            r = pedir(f'{t["base"]}/wp-json/wc/store/v1/products?per_page=100&page={pagina}')
            lote = r.json()
        except (Bloqueado, PermissionError):
            raise
        except Exception as e:
            ctx.error(f"página {pagina}", e)
            break
        if not isinstance(lote, list) or not lote:
            break
        total = total or int(r.headers.get("X-WP-TotalPages", 0) or 0) or None
        ctx.paginas += 1
        for p in lote:
            ctx.leidos += 1
            try:
                filas += _filas_woo(t, p, ctx)
            except (Bloqueado, PermissionError):
                raise
            except Exception as e:
                ctx.error(f"producto {p.get('name')}", e)
        if len(lote) < 100 or (total and pagina >= total):
            break
        pagina += 1
    return filas


def _filas_woo(t, p, ctx):
    if p.get("is_in_stock") is False:
        ctx.omitir("sin_stock")
        return []
    cats = " ".join(c.get("name", "") for c in p.get("categories", []))
    marcas = [b.get("name") for b in (p.get("brands") or [])]
    texto = p.get("description") or p.get("short_description") or ""
    base = dict(imagen=((p.get("images") or [{}])[0]).get("src", ""), desc=limpiar(p.get("short_description") or texto),
                info=secciones(texto), sabores=[x.get("name") for a in p.get("attributes", [])
                                                if str(a.get("name", "")).lower() in ("sabor", "sabores") for x in a.get("terms", [])])
    nombre, out = unescape(p.get("name", "")), []
    variaciones = []
    if p.get("type") == "variable" and p.get("variations"):    # un tamaño por variación, cada una con su precio y su enlace
        try:
            variaciones = pedir(f'{t["base"]}/wp-json/wc/store/v1/products?type=variation&parent={p.get("id")}&per_page=100').json()
        except (Bloqueado, PermissionError):
            raise
        except Exception as e:
            ctx.error(f"variaciones de {nombre}", e)
    for v in (variaciones if isinstance(variaciones, list) and variaciones else [p]):
        if v.get("is_in_stock") is False:
            ctx.omitir("sin_stock")
            continue
        pr = v.get("prices") or {}
        etiqueta = " ".join(str(a.get("value", "")) for a in v.get("attributes", []) if v is not p)
        url = v.get("permalink") or p.get("permalink", "")
        r = registro(nombre, etiqueta, _precio_woo(pr, "price"), url, t.get("marca"), cats,
                     marca_ext=marcas[0] if marcas else None, lista=_precio_woo(pr, "regular_price"), sku=v.get("sku"))
        if not r:
            ctx.omitir("no_es_suplemento_o_sin_tamano")
            continue
        r.update(base)
        out.append(r)
    return out


def urls_sitemap(t, ctx):
    pendientes, vistos, urls = [f'{t["base"]}/sitemap.xml'], set(), []
    while pendientes and len(vistos) < 200 and not ctx.vence():
        u = pendientes.pop()
        if u in vistos:
            continue
        vistos.add(u)
        try:
            xml = pedir(u).texto
        except (Bloqueado, PermissionError):
            raise
        except Exception as e:
            ctx.error(f"sitemap {u}", e)
            continue
        for loc in re.findall(r"<loc>\s*(.*?)\s*</loc>", xml):
            loc = unescape(loc)
            if loc.endswith(".xml") or ".xml?" in loc or ".xml.gz" in loc:
                pendientes.append(loc)
            elif t.get("patron", "") in loc:
                urls.append(loc)
    urls = list(dict.fromkeys(urls))
    if t.get("filtrar_urls", True):   # solo páginas cuya dirección sugiere una categoría que nos interesa
        urls = [u for u in urls if categoria(sin_acentos(u.rstrip("/").split("/")[-1]).replace("-", " "))]
    return urls


def productos_jsonld(html):
    out = []
    for bloque in re.findall(r'<script[^>]*application/ld\+json[^>]*>(.*?)</script>', html, re.S | re.I):
        try:
            pila = [json.loads(bloque.strip())]
        except ValueError:
            continue
        while pila:
            x = pila.pop()
            if isinstance(x, list):
                pila += x
            elif isinstance(x, dict):
                if "@graph" in x:
                    pila.append(x["@graph"])
                tipo = x.get("@type")
                if tipo == "Product" or (isinstance(tipo, list) and "Product" in tipo):
                    out.append(x)
    return out


def _ruta(u):
    return urllib.parse.urlsplit(str(u or "")).path.rstrip("/").lower()


def producto_principal(prods, url):
    """De todos los productos de la página elige SOLO el de esa página (descarta relacionados y recomendados)."""
    if len(prods) <= 1:
        return prods
    mia = [p for p in prods if _ruta(p.get("url") or p.get("@id")) == _ruta(url) and _ruta(url)]
    if mia:
        return mia[:1]
    slug = set(re.findall(r"[a-z0-9]+", sin_acentos(_ruta(url).split("/")[-1])))
    def afinidad(p):
        return len(slug & set(re.findall(r"[a-z0-9]+", sin_acentos(str(p.get("name", "")).lower()))))
    mejor = max(prods, key=afinidad)
    return [mejor] if afinidad(mejor) >= max(1, len(slug) // 2) else []


def _ofertas_ld(prod):
    o = prod.get("offers")
    if isinstance(o, dict) and isinstance(o.get("offers"), list):     # AggregateOffer con ofertas dentro
        o = o["offers"]
    return [x for x in (o if isinstance(o, list) else [o]) if isinstance(x, dict)]


def filas_de_pagina(t, url, ctx, html=None):
    """Filas de una página de producto: un precio por oferta/variante declarada, cada una con su enlace."""
    if html is None:
        html = pedir(url).texto
    ctx.paginas += 1
    filas = []
    for prod in producto_principal(productos_jsonld(html), url):
        marca = prod.get("brand")
        marca = marca.get("name") if isinstance(marca, dict) else marca
        gtin = next((prod[k] for k in ("gtin13", "gtin", "gtin12", "gtin14", "gtin8") if prod.get(k)), "")
        imagen = prod.get("image")
        imagen = imagen[0] if isinstance(imagen, list) and imagen else imagen
        imagen = imagen.get("url") if isinstance(imagen, dict) else imagen
        nombre, desc = unescape(str(prod.get("name", ""))), str(prod.get("description", ""))
        ofertas = _ofertas_ld(prod)
        rango = len(ofertas) == 1 and ofertas[0].get("@type") == "AggregateOffer" and ofertas[0].get("lowPrice") != ofertas[0].get("highPrice")
        if rango and not cantidad(nombre):
            ctx.omitir("precio_en_rango_sin_tamano")
            continue
        for of in ofertas:
            if "OutOfStock" in str(of.get("availability", "")):
                ctx.omitir("sin_stock")
                continue
            precio = of.get("price") if of.get("price") not in (None, "") else of.get("lowPrice")
            ou = of.get("url")
            enlace = ou if ou and _ruta(ou) == _ruta(url) else url      # solo se acepta un enlace de variante de ESTA página
            r = registro(nombre, of.get("name") if len(ofertas) > 1 else "", precio, enlace, t.get("marca"),
                         marca_ext=marca, ean=of.get("gtin13") or of.get("gtin") or gtin, sku=of.get("sku") or prod.get("sku"))
            if not r:
                ctx.omitir("no_es_suplemento_o_sin_tamano")
                continue
            r.update(imagen=imagen if isinstance(imagen, str) else "", desc=limpiar(desc), info=secciones(desc))
            filas.append(r)
    return filas


def leer_sitemap(t, ctx, cache=None):
    filas = ctx.filas
    for url in urls_sitemap(t, ctx):
        if ctx.vence():
            break
        try:
            previo = cache.get(url) if cache else None
            cab = {}
            if previo and previo[0]:
                cab["If-None-Match"] = previo[0]
            if previo and previo[1]:
                cab["If-Modified-Since"] = previo[1]
            r = pedir(url, cabeceras=cab or None)
            if r.status == 304 and previo:      # la página no cambió: se reutiliza lo ya extraído
                nuevas = previo[2]
                ctx.omitir("sin_cambios_304")
            else:
                nuevas = filas_de_pagina(t, url, ctx, html=r.texto)
                if cache:
                    cache.put(url, r.headers.get("ETag"), r.headers.get("Last-Modified"), nuevas)
            filas += nuevas
            ctx.leidos += 1
        except (Bloqueado, PermissionError):
            raise
        except Exception as e:
            ctx.error(url, e)    # una página que falla no frena a las demás
    return filas


def token_ml():
    if os.environ.get("ML_ACCESS_TOKEN"):
        return os.environ["ML_ACCESS_TOKEN"]
    cid, sec = os.environ.get("ML_CLIENT_ID"), os.environ.get("ML_CLIENT_SECRET")
    if not (cid and sec):
        return None
    datos = urllib.parse.urlencode({"grant_type": "client_credentials", "client_id": cid, "client_secret": sec}).encode()
    req = urllib.request.Request("https://api.mercadolibre.com/oauth/token", data=datos,
                                 headers={"Content-Type": "application/x-www-form-urlencoded", "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)["access_token"]


def leer_mercadolibre(t, ctx, cache=None):
    token = token_ml()
    if not token:
        raise RuntimeError("faltan credenciales: definí ML_CLIENT_ID y ML_CLIENT_SECRET (o ML_ACCESS_TOKEN)")
    etiquetas = {n.upper(): e for n, e in ML_VENDEDORES.items()}
    filas = ctx.filas
    for vendedor in [None] + list(ML_VENDEDORES):
        filtro = f"&nickname={urllib.parse.quote(vendedor)}" if vendedor else ""
        defecto = etiquetas.get(vendedor.upper(), "Mercado Libre") if vendedor else "Mercado Libre"
        for q in ML_CONSULTAS:
            offset, total = 0, None
            while offset < min(total if total is not None else 1000, 1000) and not ctx.vence():   # la API llega hasta 1000
                try:
                    d = pedir(f"https://api.mercadolibre.com/sites/MLA/search?q={urllib.parse.quote(q)}{filtro}&limit=50&offset={offset}",
                              token=token, robots=False).json()
                except Bloqueado:
                    raise
                except Exception as e:
                    ctx.error(f"búsqueda '{q}' offset {offset}", e)
                    break
                total = (d.get("paging") or {}).get("total", len(d.get("results", [])))
                res = d.get("results", [])
                ctx.paginas += 1
                for it in res:
                    ctx.leidos += 1
                    if it.get("condition") not in (None, "new"):
                        ctx.omitir("usado")
                        continue
                    r = registro(it.get("title", ""), "", it.get("price"), it.get("permalink", ""), lista=it.get("original_price"))
                    if r:
                        nick = str((it.get("seller") or {}).get("nickname", "")).upper()
                        r.update(tienda=etiquetas.get(nick, defecto), imagen=str(it.get("thumbnail", "")).replace("http://", "https://"))
                        filas.append(r)
                    else:
                        ctx.omitir("no_es_suplemento_o_sin_tamano")
                if len(res) < 50:
                    break
                offset += 50
    return filas


def detectar(t):
    try:
        d = pedir(f'{t["base"]}/products.json?limit=1').json()
        if isinstance(d, dict) and "products" in d:
            return "shopify"
    except Bloqueado:
        raise
    except Exception:
        pass
    try:
        if isinstance(pedir(f'{t["base"]}/wp-json/wc/store/v1/products?per_page=1').json(), list):
            return "woocommerce"
    except Bloqueado:
        raise
    except Exception:
        pass
    return "sitemap"


LECTORES = {"shopify": leer_shopify, "woocommerce": leer_woo, "sitemap": leer_sitemap, "mercadolibre": leer_mercadolibre}


def leer_tienda(t, cache=None):
    ctx = Ctx(t["nombre"])
    tipo = t["tipo"]
    try:
        if tipo == "auto":
            tipo = detectar(t)
        filas = LECTORES[tipo](t, ctx, cache)
    except Bloqueado as e:
        ctx.bloqueada = True
        ctx.error("bloqueo", e)
        filas = ctx.filas
    if t.get("efectivo"):
        for f in filas:
            f["efectivo"] = round(f["precio"] * (1 - t["efectivo"]))
    return filas, tipo, ctx


# ============================ AGRUPACIÓN ============================
PALABRAS_VACIAS = set("""de del la el los las con sin para por y e en a al un una o x doypack doy pack pote tarro frasco bolsa
sachet sobre polvo suplemento suplementos dietario dietaria nutricional nutricion deportivo deportiva original nuevo nueva oferta
promo envio gratis cuotas sabor sabores kg kgs g gr grs gramo gramos lb lbs libra libras oz ml l caps cap capsula capsulas
comprimido comprimidos tab tabs tableta tabletas softgel softgels unidad unidades u un barra barras sticks stick porciones porcion
proteina proteinas protein whey creatina creatine monohidrato monohidratada monohidratado monohydrate micronizada micronizado
magnesio omega vitamina vitaminas colageno collagen quemador termogenico aminoacidos aminoacido amino bcaa glutamina pre entreno
workout isotonico electrolitos hidratante ganador peso mass gainer snack concentrada concentrado isolate aislada aislado
hidrolizada hidrolizado vegetal citrato bisglicinato glicinato malato treonato cloruro""".split())
SABORES = ["dulce de leche", "frutos rojos", "cookies and cream", "cookies & cream", "sin sabor", "chocolate", "vainilla",
           "frutilla", "banana", "limon", "naranja", "sandia", "neutro", "neutra", "caramelo", "menta", "cafe", "moca", "mocca",
           "mango", "anana", "pina", "durazno", "manzana", "uva", "tropical", "cereza", "coco", "brownie", "tiramisu", "cookies",
           "maracuya", "pomelo", "lima", "frambuesa", "arandano", "kiwi", "fruit punch", "blue raspberry", "cola", "chicle",
           "cappuccino", "avellana", "pistacho", "mani", "peanut", "cacao", "banoffee", "oreo", "alfajor"]
_RE_SABOR = re.compile(r"\b(" + "|".join(re.escape(s) for s in sorted(SABORES, key=len, reverse=True)) + r")\b")


def firma(f):
    """Las palabras que distinguen la línea de un producto (sin marca, tamaño, sabor ni palabras genéricas)."""
    t = re.sub(r"(\d+)\s*%", r"\1pct", sin_acentos(f.get("nombre", "")).lower())
    t = _RE_SABOR.sub(" ", t)
    marca = set(re.findall(r"[a-z0-9]+", sin_acentos(f.get("marca") or "").lower()))
    out = set()
    for w in re.findall(r"[a-z0-9]+", t):
        if w in PALABRAS_VACIAS or w in marca or re.fullmatch(r"(x\d+|\d+x|\d+(?:[a-z]{1,4})?)", w) and not w.endswith("pct"):
            continue
        out.add(w)
    return frozenset(out)


def similitud(a, b):
    """1.0 iguales, None si una de las dos no dice nada (título genérico), 0..1 según palabras compartidas."""
    if not a and not b:
        return 1.0
    if not a or not b:
        return None
    j = len(a & b) / len(a | b)
    return max(j, 0.75) if (a <= b or b <= a) else j


def fusionables(a, b, fa, fb):
    if a.get("ean") and b.get("ean"):
        return a["ean"] == b["ean"]          # el código de barras manda: igual = mismo producto, distinto = no
    ra = (a["precio"] / a["cant"]) / (b["precio"] / b["cant"])
    r = max(ra, 1 / ra)
    s = similitud(fa, fb)
    if (a.get("marca") or "Sin marca") == "Sin marca":
        return bool(fa) and bool(fb) and s is not None and s >= 0.6 and r <= 2.0   # sin marca: solo con palabras propias en común
    if s is None:
        return r <= 1.3                       # uno es genérico: solo si el precio es muy parecido
    return s >= 0.5 and r <= 2.5


def _moda_tamano(fs):
    c = Counter(f["cant"] for f in fs)
    return sorted(c, key=lambda v: (-c[v], -(len(str(v)) - len(str(v).rstrip("0"))), v))[0]


def agrupar(filas):
    """Junta las ofertas del mismo producto de distintas tiendas, aunque los títulos estén redactados distinto."""
    buckets = defaultdict(list)
    for f in filas:
        f.setdefault("ean", "")
        buckets[(f.get("marca") or "Sin marca", f["cat"], f["tipo"], f["unidad"])].append(f)
    grupos = []
    for (marca, cat, tipo, unidad), fs in buckets.items():
        fs.sort(key=lambda f: f["cant"])
        clusters = []
        for f in fs:      # tamaños equivalentes (dentro de TOL_TAMANO del primero del grupo)
            if clusters and abs(f["cant"] - clusters[-1][0]["cant"]) / clusters[-1][0]["cant"] <= TOL_TAMANO:
                clusters[-1].append(f)
            else:
                clusters.append([f])
        for cl in clusters:
            cant = _moda_tamano(cl)
            firmas = [firma(f) for f in cl]
            padre = list(range(len(cl)))
            def raiz(i):
                while padre[i] != i:
                    padre[i] = padre[padre[i]]
                    i = padre[i]
                return i
            for i in range(len(cl)):
                for j in range(i + 1, len(cl)):
                    if raiz(i) != raiz(j) and fusionables(cl[i], cl[j], firmas[i], firmas[j]):
                        padre[raiz(j)] = raiz(i)
            comp = defaultdict(list)
            for i in range(len(cl)):
                comp[raiz(i)].append(i)
            for idx in comp.values():
                grupos.append(_armar_grupo(marca, cat, tipo, unidad, cant, [cl[i] for i in idx], [firmas[i] for i in idx]))
    return sorted(grupos, key=lambda g: (g["cat"], g["marca"], g["unidad"], g["cant"], g["linea"]))


def _armar_grupo(marca, cat, tipo, unidad, cant, fs, firmas):
    con_firma = [f for f in firmas if f]
    linea = " ".join(sorted(Counter(con_firma).most_common(1)[0][0])) if con_firma else ""
    por_tienda = {}
    for f in fs:
        tienda = f.get("tienda", "")
        if tienda not in por_tienda or f["precio"] < por_tienda[tienda]["precio"]:
            por_tienda[tienda] = f
    ofertas = []
    for tienda, f in por_tienda.items():
        o = {"store": tienda, "titulo": f.get("titulo") or f["nombre"], "price": f["precio"], "lista": f.get("lista") or None,
             "efectivo": f.get("efectivo") or None, "url": f["url"], "seen": (f.get("fecha") or "")[:10]}
        ofertas.append(o)
    # Con 3 o más tiendas, una oferta con precio por unidad muy fuera de lo normal casi seguro es otro producto (pack, otro tamaño)
    descartadas = 0
    if len(ofertas) >= 3:
        med = statistics.median(o["price"] for o in ofertas)
        buenas = [o for o in ofertas if med / 2.5 <= o["price"] <= med * 2.5]
        descartadas, ofertas = len(ofertas) - len(buenas), buenas
    ofertas.sort(key=lambda o: o["price"])
    def primero(campo, vacio):
        return next((f[campo] for f in fs if f.get(campo)), vacio)
    titulos = sorted((f.get("titulo") or f["nombre"] for f in fs), key=lambda s: (-len(firma({"nombre": s, "marca": marca})), len(s)))
    return {"marca": marca, "cat": cat, "tipo": tipo, "linea": linea, "cant": cant, "unidad": unidad,
            "name": re.split(r"\s+[-–]\s+", titulos[0])[0].strip() or titulos[0], "imagen": primero("imagen", ""),
            "desc": primero("desc", ""), "sabores": sorted({s for f in fs for s in (f.get("sabores") or [])}),
            "info": primero("info", {}), "ean": primero("ean", ""), "ofertas": ofertas, "hist": [], "descartadas": descartadas}


# ============================ VERIFICACIÓN DE ENLACES ============================
_VACIAS_VERIF = set("de del la el los las con sin para por y e en a al un una o x g gr grs kg kgs lb lbs caps cap".split())


def verificar_enlace(oferta, marca):
    """Abre el enlace y comprueba que la página sea del producto: sus palabras (marca, tipo, línea) deben estar
    en la página. True / False / None (None = el sitio no dejó comprobarlo)."""
    try:
        r = pedir(oferta["url"])
    except (Bloqueado, PermissionError):
        return None
    except Exception:
        return False
    pagina = set(re.findall(r"[a-z0-9]+", sin_acentos(r.texto[:400000]).lower()))
    palabras = {w for w in re.findall(r"[a-z0-9]+", sin_acentos(oferta["titulo"]).lower())
                if w not in _VACIAS_VERIF and not re.fullmatch(r"\d+[a-z]{0,4}", w)}
    return True if not palabras else len(palabras & pagina) / len(palabras) >= 0.6


# ============================ BASE DE DATOS Y SALIDA ============================
COLUMNAS = [("fecha", "text"), ("tienda", "text"), ("producto", "text"), ("marca", "text"), ("categoria", "text"),
            ("tipo", "text"), ("cantidad", "real"), ("unidad", "text"), ("precio", "real"), ("url", "text"),
            ("imagen", "text"), ("descripcion", "text"), ("sabores", "text"), ("info", "text"), ("lista", "real"),
            ("ean", "text"), ("efectivo", "real"), ("titulo", "text")]


def abrir_db():
    con = sqlite3.connect(DB, check_same_thread=False)
    con.execute("create table if not exists ofertas(" + ", ".join(f"{n} {t}" for n, t in COLUMNAS) + ")")
    existentes = {c[1] for c in con.execute("pragma table_info(ofertas)")}
    for n, t in COLUMNAS:
        if n not in existentes:
            con.execute(f"alter table ofertas add column {n} {t}")
    con.execute("create table if not exists historial(dia text, clave text, minimo real, primary key(dia, clave))")
    return con


def escribir_json(ruta, datos):
    """Escritura atómica: nunca queda un archivo a medias si algo se corta."""
    d = os.path.dirname(os.path.abspath(ruta))
    fd, tmp = tempfile.mkstemp(dir=d, suffix=".tmp")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            json.dump(datos, f, ensure_ascii=False, indent=1)
        json.load(open(tmp, encoding="utf-8"))   # comprobar que se lee bien antes de reemplazar
        os.replace(tmp, ruta)
    finally:
        if os.path.exists(tmp):
            os.remove(tmp)


def guardar_tienda(con, cache, t, filas, ctx, rep):
    etiquetas = {f.get("tienda", t["nombre"]) for f in filas} | {t["nombre"]}
    with cache.lock:
        marcas = ",".join("?" * len(etiquetas))
        antes = con.execute(f"select count(*) from ofertas where tienda in ({marcas})", tuple(etiquetas)).fetchone()[0]
        if antes >= 20 and len(filas) < antes * PISO_CONSERVAR:
            rep["estado"] = "conservada"
            rep["nota"] = f"leyó {len(filas)} ofertas y antes tenía {antes}: se conserva la lectura anterior"
            return
        for e in etiquetas:
            con.execute("delete from ofertas where tienda=?", (e,))
        fecha = datetime.now(timezone.utc).isoformat(timespec="seconds")
        nombres = ",".join(n for n, _ in COLUMNAS)
        con.executemany(f"insert into ofertas ({nombres}) values ({','.join('?' * len(COLUMNAS))})",
                        [(fecha, f.get("tienda", t["nombre"]), f["nombre"], f["marca"], f["cat"], f["tipo"], f["cant"], f["unidad"],
                          f["precio"], f["url"], f.get("imagen", ""), f.get("desc", ""), json.dumps(f.get("sabores") or [], ensure_ascii=False),
                          json.dumps(f.get("info") or {}, ensure_ascii=False), f.get("lista") or 0, f.get("ean", ""), f.get("efectivo") or 0,
                          f.get("titulo", "")) for f in filas])
        con.commit()
        rep["estado"] = "parcial" if (ctx.bloqueada or ctx.vencida) else "ok"


def main():
    inicio = time.time()
    con = abrir_db()
    cache = Cache(con)
    reportes = {}
    with ThreadPoolExecutor(max_workers=HILOS) as ex:
        trabajos = [(t, ex.submit(leer_tienda, t, cache)) for t in TIENDAS]
        for t, tr in trabajos:
            rep = reportes[t["nombre"]] = {"estado": "error", "ofertas": 0, "paginas": 0, "productos_leidos": 0,
                                           "omitidos": {}, "errores": [], "tipo": t["tipo"]}
            try:
                filas, tipo, ctx = tr.result()
            except PermissionError as e:
                rep.update(estado="omitida", nota=str(e))
                print(f'[{t["nombre"]}] omitida: {e}')
                continue
            except Exception as e:
                rep.update(estado="error", nota=str(e)[:200])
                print(f'[{t["nombre"]}] error: {e}')
                continue
            rep.update(tipo=tipo, ofertas=len(filas), paginas=ctx.paginas, productos_leidos=ctx.leidos,
                       omitidos=dict(ctx.omitidos), errores=ctx.errores[:25], errores_total=len(ctx.errores))
            guardar_tienda(con, cache, t, filas, ctx, rep)
            marca = {"ok": "", "parcial": " (parcial: bloqueo o tiempo)", "conservada": " (se conservó la lectura anterior)"}.get(rep["estado"], "")
            print(f'[{t["nombre"]}] {len(filas)} ofertas, {ctx.paginas} páginas, {len(ctx.errores)} errores ({tipo}){marca}')
    ahora = datetime.now(timezone.utc)
    fecha, dia = ahora.isoformat(timespec="seconds"), ahora.date().isoformat()
    with cache.lock:
        ult = con.execute("""select tienda, producto, marca, categoria, tipo, cantidad, unidad, precio, url, imagen, descripcion,
            sabores, info, lista, ean, efectivo, fecha, titulo from ofertas
            where (tienda, fecha) in (select tienda, max(fecha) from ofertas group by tienda)""").fetchall()
    filas = [dict(tienda=a, nombre=b, marca=c, cat=d, tipo=e, cant=int(g), unidad=h, precio=p, url=u, imagen=i or "", desc=d2 or "",
                  sabores=json.loads(s or "[]"), info=json.loads(inf or "{}"), lista=li or 0, ean=ean or "", efectivo=ef or 0,
                  fecha=fe, titulo=ti or b) for a, b, c, d, e, g, h, p, u, i, d2, s, inf, li, ean, ef, fe, ti in ult]
    productos = agrupar(filas)
    # Comprobación por muestreo: ¿el enlace lleva de verdad a ese producto?
    for t in TIENDAS:
        rep = reportes[t["nombre"]]
        muestra = [(g, o) for g in productos for o in g["ofertas"] if o["store"] == t["nombre"] or
                   (t["tipo"] == "mercadolibre" and "Mercado Libre" in o["store"])]
        random.Random(dia + t["nombre"]).shuffle(muestra)
        res = [verificar_enlace(o, g["marca"]) for g, o in muestra[:VERIFICAR_ENLACES]] if VERIFICAR_ENLACES else []
        if res:
            rep["enlaces_verificados"] = {"probados": len(res), "correctos": sum(r is True for r in res), "dudosos": sum(r is False for r in res)}
    corte = (ahora - timedelta(days=DIAS_HISTORIAL)).date().isoformat()
    with cache.lock:
        con.execute("delete from historial where dia < ?", (corte,))
        for g in productos:
            clave = "|".join(str(x) for x in (g["marca"], g["cat"], g["tipo"], g["cant"], g["unidad"])) + (f"|{g['linea']}" if g["linea"] else "")
            con.execute("insert or replace into historial values (?,?,?)", (dia, clave, g["ofertas"][0]["price"]))
            h = [[d, round(m)] for d, m in con.execute("select dia, minimo from historial where clave=? order by dia", (clave,))]
            g["hist"] = h if len(h) >= 2 else []
        con.commit()
    for g in productos:
        g.pop("descartadas", None)
    escribir_json(SALIDA, {"version": 2, "actualizado": fecha, "productos": productos})
    comparables = sum(len(p["ofertas"]) > 1 for p in productos)
    escribir_json(REPORTE, {"fecha": fecha, "segundos": round(time.time() - inicio), "productos": len(productos),
                            "comparables": comparables, "tiendas": reportes})
    print(f"{SALIDA}: {len(productos)} productos, {comparables} comparables entre 2 o más tiendas ({round(time.time() - inicio)} s)")
    if not productos:
        sys.exit(1)


if __name__ == "__main__":
    main()
