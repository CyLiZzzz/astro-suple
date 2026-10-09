"""Comparador de precios de suplementos: junta ofertas de varias tiendas online
y agrupa el mismo producto para compararlo entre tiendas.

Uso:  python scraper.py
Genera precios.db (historial de precios) y datos.json (lo que lee el sitio).
"""
import json
import os
import re
import sqlite3
import time
import urllib.error
import urllib.parse
import urllib.request
import urllib.robotparser
from datetime import datetime, timezone
from html import unescape

# Para sumar una tienda, agregá un bloque a esta lista.
#  tipo "shopify":      lee el catálogo JSON público (rápido y estable).
#  tipo "sitemap":      lee el mapa del sitio y los datos estructurados de cada
#                       producto (Tiendanube, WooCommerce y similares).
#  tipo "mercadolibre": usa la API oficial de Mercado Libre (pide credenciales).
#  patron: parte de la dirección que tienen las páginas de producto (opcional).
#  marca:  solo para tiendas de una única marca (ej. la tienda oficial de ENA).
TIENDAS = [
    {"nombre": "Disfit", "base": "https://www.disfit.com.ar", "tipo": "sitemap", "patron": "/productos/"},
    {"nombre": "ENA Sport", "base": "https://www.enasport.com", "tipo": "shopify", "marca": "ENA"},
    {"nombre": "Nutrishop", "base": "https://www.nutrishop.com.ar", "tipo": "sitemap"},
    {"nombre": "Mercado Libre", "tipo": "mercadolibre"},
]
# Búsquedas que se hacen en Mercado Libre.
ML_CONSULTAS = ["creatina monohidrato", "whey protein", "proteina en polvo", "pre entreno", "bcaa",
                "citrato de magnesio", "bisglicinato de magnesio", "omega 3", "vitamina d3",
                "multivitaminico", "colageno hidrolizado"]
# Tiendas que también venden en Mercado Libre: se muestran como tienda propia.
# Clave: nombre de usuario del vendedor en Mercado Libre. Valor: cómo se muestra en el sitio.
# (Verificar que "NUTRISHOP" sea el nombre exacto de usuario en su página de tienda oficial.)
ML_VENDEDORES = {"NUTRISHOP": "Nutrishop (Mercado Libre)"}

DB = "precios.db"
SALIDA = "datos.json"
PAUSA = 2                # segundos entre pedidos, para no sobrecargar a las tiendas
MAX_POR_TIENDA = 300     # tope de productos a leer por tienda en cada corrida
BOT = "SupleAKilo"
UA = {"User-Agent": f"Mozilla/5.0 (compatible; {BOT}/0.1)"}

MARCAS = ["Star Nutrition", "One Fit", "ENA", "Gold Nutrition", "Integralmedica", "xBody Evolution",
          "Xtrength", "Nutremax", "Hoch Sport", "Nucleo Fit", "MuscleTech", "My Protein",
          "Optimum Nutrition", "Universal Nutrition", "BSN", "Body Advance", "Mervick", "Gentech",
          "Weider", "Pure Nutrition", "Vitalgen", "226ERS", "Granger", "Innova Naturals", "Proyec",
          "Natuliv", "NF Nutrition"]

# El orden importa: gana la primera categoría que coincida.
CATEGORIAS = [
    ("Creatina", ("creatina",)),
    ("Magnesio", ("magnesio",)),
    ("Omega 3", ("omega", "aceite de pescado", "fish oil")),
    ("Colágeno", ("colageno", "colágeno", "collagen")),
    ("Pre-entreno", ("pre war", "pre-entreno", "pre entreno", "preentreno", "pre workout", "pre work",
                     "oxido nitrico", "óxido nítrico", "beta alanine")),
    ("Aminoácidos", ("bcaa", "amino", "glutamina")),
    ("Proteína", ("whey", "protein", "proteína", "proteina", "isoprot", "ultra mass")),
    ("Vitaminas", ("vitamina", "multivit", "zma", "zinc")),
]
EXCLUIR = re.compile(r"\b(bar|barra|barras|barrita|barritas|shaker|shakers|combo|pack|caja|gel)\b"
                     r"|remera|buzo|short|sobres?", re.I)

# Variantes del producto que NO se deben mezclar al compararlo (primera que coincida).
TIPOS = {
    "Creatina": [("creapure", "creapure"), ("magnesio", "con magnesio"),
                 ("colageno|colágeno", "con colágeno"), ("electrolitos", "con electrolitos")],
    "Proteína": [("isolate|isolada|isoprot", "aislada"), ("beef|carne", "de carne"), ("vegetal|plant", "vegetal")],
    "Magnesio": [("citrato", "citrato"), ("bisglicinato|glicinato", "bisglicinato"), ("malato", "malato"),
                 ("treonato", "treonato"), ("cloruro", "cloruro"), ("duo|dúo", "duo")],
    "Aminoácidos": [("bcaa", "bcaa"), ("glutamina", "glutamina"), ("amino", "aminoácidos")],
    "Pre-entreno": [("oxido nitrico|óxido nítrico", "óxido nítrico"), ("beta alanine", "beta alanina")],
    "Vitaminas": [("d3.*k2|k2", "D3 + K2"), ("d3|vitamina d", "vitamina D"), ("vitamina c", "vitamina C"),
                  ("b12", "B12"), ("multivit", "multivitamínico"), ("zma", "ZMA")],
    "Colágeno": [("hidrolizad", "hidrolizado")],
}
TIPO_POR_DEFECTO = {"Creatina": "monohidrato", "Proteína": "whey"}

UNIDADES = r"(?:caps\w*|c[aá]psulas?|comprimidos?|tabs?|tabletas?|softgels?|perlas?|gomitas?)"


def categoria(texto):
    t = texto.lower()
    if EXCLUIR.search(t):
        return None
    for nombre, claves in CATEGORIAS:
        if any(c in t for c in claves):
            return nombre
    return None


def cantidad(texto):
    """Devuelve (cantidad, unidad): gramos ('g') o cápsulas/comprimidos ('u'), o None."""
    t = texto.lower()
    m = re.search(r"(\d+(?:[.,]\d+)?)\s*(kgs?|grs?|gramos|g|lbs?)\b", t)
    if m:
        n = float(m.group(1).replace(",", "."))
        if m.group(2).startswith("kg"):
            n *= 1000
        elif m.group(2).startswith("lb"):
            n *= 453.6
        # Menos de 50 g suele ser una porción o una dosis, no el envase.
        if n >= 50:
            return int(round(n / 10) * 10), "g"
    m = re.search(rf"(?:x\s*)?(\d{{1,4}})\s*{UNIDADES}\b", t) or re.search(rf"{UNIDADES}\s*[x×]?\s*(\d{{1,4}})\b", t)
    if m and 10 <= int(m.group(1)) <= 1000:
        return int(m.group(1)), "u"
    return None


def marca_de(texto, por_defecto=None):
    for m in sorted(MARCAS, key=len, reverse=True):
        if re.search(rf"(?<!\w){re.escape(m)}(?!\w)", texto, re.I):
            return m
    return por_defecto


def tipo_de(cat, texto):
    for patron, etiqueta in TIPOS.get(cat, []):
        if re.search(patron, texto, re.I):
            return etiqueta
    return TIPO_POR_DEFECTO.get(cat, "")


def registro(titulo, variante, precio, url, marca_def=None, extra=""):
    """Arma una oferta normalizada, o devuelve None si no nos sirve."""
    try:
        precio = float(precio)
    except (TypeError, ValueError):
        return None
    cat = categoria(f"{titulo} {extra}")
    cant = cantidad(variante) or cantidad(titulo)
    if not cat or not cant or precio <= 0:
        return None
    nombre = titulo if variante in ("", "Default Title") else f"{titulo} - {variante}"
    return {"nombre": nombre, "marca": marca_de(titulo, marca_def), "cat": cat,
            "tipo": tipo_de(cat, titulo), "cant": cant[0], "unidad": cant[1], "precio": precio, "url": url}


# ---------- Descargas (respetando robots.txt) ----------
_robots = {}


def permitido(url):
    """True si el robots.txt del sitio nos deja leer esa dirección."""
    p = urllib.parse.urlparse(url)
    base = f"{p.scheme}://{p.netloc}"
    if base not in _robots:
        rp = urllib.robotparser.RobotFileParser()
        try:
            req = urllib.request.Request(f"{base}/robots.txt", headers=UA)
            rp.parse(urllib.request.urlopen(req, timeout=15).read().decode("utf-8", "replace").splitlines())
        except Exception:  # sin robots.txt legible: se asume permitido
            rp = None
        _robots[base] = rp
    rp = _robots[base]
    return rp is None or rp.can_fetch(BOT, url)


def bajar(url, token=None, robots=True):
    if robots and not permitido(url):
        raise PermissionError("el robots.txt del sitio no permite lectura automática")
    headers = dict(UA)
    if token:
        headers["Authorization"] = f"Bearer {token}"
    with urllib.request.urlopen(urllib.request.Request(url, headers=headers), timeout=30) as r:
        return r.read().decode("utf-8", "replace")


# ---------- Tiendas Shopify ----------
def leer_shopify(t):
    filas, pagina = [], 1
    while True:
        lote = json.loads(bajar(f'{t["base"]}/products.json?limit=250&page={pagina}')).get("products", [])
        if not lote:
            return filas
        for p in lote:
            for v in p.get("variants", []):
                if v.get("available") is False:
                    continue
                r = registro(p.get("title", ""), v.get("title", ""), v.get("price"),
                             f'{t["base"]}/products/{p.get("handle", "")}', t.get("marca"), p.get("product_type", ""))
                if r:
                    filas.append(r)
        pagina += 1
        time.sleep(PAUSA)


# ---------- Tiendas con sitemap + datos estructurados (JSON-LD) ----------
def urls_sitemap(t):
    pendientes, vistos, urls = [f'{t["base"]}/sitemap.xml'], set(), []
    while pendientes and len(vistos) < 20:
        u = pendientes.pop()
        if u in vistos:
            continue
        vistos.add(u)
        for loc in re.findall(r"<loc>\s*(.*?)\s*</loc>", bajar(u)):
            loc = unescape(loc)
            if loc.endswith(".xml"):
                pendientes.append(loc)
            elif t.get("patron", "") in loc:
                urls.append(loc)
        time.sleep(PAUSA)
    # Solo páginas cuya dirección sugiere una categoría que nos interesa.
    return [u for u in urls if categoria(u.rstrip("/").split("/")[-1].replace("-", " "))]


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


def precio_y_stock(prod):
    o = prod.get("offers")
    if isinstance(o, list):
        o = o[0] if o else {}
    if not isinstance(o, dict):
        return None, False
    try:
        precio = float(str(o.get("price") or o.get("lowPrice")))
    except ValueError:
        return None, False
    return precio, "OutOfStock" not in str(o.get("availability", ""))


def leer_sitemap(t):
    filas = []
    for url in urls_sitemap(t)[:MAX_POR_TIENDA]:
        try:
            for prod in productos_jsonld(bajar(url)):
                precio, hay = precio_y_stock(prod)
                r = hay and registro(unescape(str(prod.get("name", ""))), "", precio, url, t.get("marca"))
                if r:
                    filas.append(r)
        except Exception as e:
            print(f"  {url}: {e}")
        time.sleep(PAUSA)
    return filas


# ---------- Mercado Libre (API oficial) ----------
def token_ml():
    """Usa ML_ACCESS_TOKEN, o genera uno con ML_CLIENT_ID y ML_CLIENT_SECRET."""
    if os.environ.get("ML_ACCESS_TOKEN"):
        return os.environ["ML_ACCESS_TOKEN"]
    cid, sec = os.environ.get("ML_CLIENT_ID"), os.environ.get("ML_CLIENT_SECRET")
    if not (cid and sec):
        return None
    datos = urllib.parse.urlencode({"grant_type": "client_credentials", "client_id": cid,
                                    "client_secret": sec}).encode()
    req = urllib.request.Request("https://api.mercadolibre.com/oauth/token", data=datos,
                                 headers={"Content-Type": "application/x-www-form-urlencoded", "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)["access_token"]


def leer_mercadolibre(t):
    token = token_ml()
    if not token:
        raise RuntimeError("faltan credenciales: definí ML_CLIENT_ID y ML_CLIENT_SECRET (o ML_ACCESS_TOKEN)")
    etiquetas = {n.upper(): e for n, e in ML_VENDEDORES.items()}
    filas = []
    # Primero la búsqueda general, después una búsqueda por cada vendedor a seguir.
    for vendedor_buscado in [None] + list(ML_VENDEDORES):
        filtro = f"&nickname={urllib.parse.quote(vendedor_buscado)}" if vendedor_buscado else ""
        por_defecto = etiquetas.get(vendedor_buscado.upper(), "Mercado Libre") if vendedor_buscado else "Mercado Libre"
        for q in ML_CONSULTAS:
            for offset in (0, 50):
                url = (f"https://api.mercadolibre.com/sites/MLA/search?q={urllib.parse.quote(q)}"
                       f"{filtro}&limit=50&offset={offset}")
                res = json.loads(bajar(url, token=token, robots=False)).get("results", [])
                for it in res:
                    if it.get("condition") not in (None, "new"):
                        continue
                    r = registro(it.get("title", ""), "", it.get("price"), it.get("permalink", ""))
                    if r:
                        nick = str((it.get("seller") or {}).get("nickname", "")).upper()
                        r["tienda"] = etiquetas.get(nick, por_defecto)
                        filas.append(r)
                time.sleep(PAUSA)
                if len(res) < 50:
                    break
    return filas


LECTORES = {"shopify": leer_shopify, "sitemap": leer_sitemap, "mercadolibre": leer_mercadolibre}


# ---------- Comparación entre tiendas ----------
def agrupar(filas):
    """Junta las ofertas del mismo producto (marca + categoría + variante + cantidad)."""
    grupos = {}
    for f in filas:
        k = (f["marca"] or "Sin marca", f["cat"], f["tipo"], f["cant"], f["unidad"])
        g = grupos.setdefault(k, {"marca": k[0], "cat": k[1], "tipo": k[2], "cant": k[3], "unidad": k[4],
                                  "name": f["nombre"], "ofertas": {}})
        o = g["ofertas"].get(f["tienda"])
        if not o or f["precio"] < o["price"]:
            g["ofertas"][f["tienda"]] = {"store": f["tienda"], "price": f["precio"], "url": f["url"]}
    salida = []
    for g in grupos.values():
        g["ofertas"] = sorted(g["ofertas"].values(), key=lambda o: o["price"])
        salida.append(g)
    return sorted(salida, key=lambda g: (g["cat"], g["marca"], g["unidad"], g["cant"]))


def main():
    con = sqlite3.connect(DB)
    con.execute("""create table if not exists ofertas(fecha text, tienda text, producto text, marca text,
        categoria text, tipo text, cantidad real, unidad text, precio real, url text)""")
    fecha = datetime.now(timezone.utc).isoformat(timespec="seconds")
    for t in TIENDAS:
        try:
            filas = LECTORES[t["tipo"]](t)
        except PermissionError as e:
            print(f'[{t["nombre"]}] omitida: {e}')
            continue
        except Exception as e:  # si una tienda falla, seguimos con las otras
            print(f'[{t["nombre"]}] error: {e}')
            continue
        con.executemany("insert into ofertas values (?,?,?,?,?,?,?,?,?,?)",
                        [(fecha, f.get("tienda", t["nombre"]), f["nombre"], f["marca"], f["cat"], f["tipo"], f["cant"], f["unidad"],
                          f["precio"], f["url"]) for f in filas])
        print(f'[{t["nombre"]}] {len(filas)} ofertas guardadas')
    con.commit()
    # Para el sitio: la última corrida exitosa de cada tienda.
    ult = con.execute("""select tienda, producto, marca, categoria, tipo, cantidad, unidad, precio, url from ofertas
        where (tienda, fecha) in (select tienda, max(fecha) from ofertas group by tienda)""").fetchall()
    filas = [dict(tienda=a, nombre=b, marca=c, cat=d, tipo=e, cant=int(g), unidad=h, precio=p, url=u)
             for a, b, c, d, e, g, h, p, u in ult]
    productos = agrupar(filas)
    with open(SALIDA, "w", encoding="utf-8") as f:
        json.dump({"actualizado": fecha, "productos": productos}, f, ensure_ascii=False, indent=1)
    comparables = sum(len(p["ofertas"]) > 1 for p in productos)
    print(f"{SALIDA}: {len(productos)} productos, {comparables} comparables entre 2 o más tiendas")


if __name__ == "__main__":
    main()
