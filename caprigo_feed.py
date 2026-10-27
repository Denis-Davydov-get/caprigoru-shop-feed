"""
Фид для Яндекс.Директа: товары caprigo.ru «в наличии» со ссылками на caprigoshop.ru.

1. caprigo.ru (SPA, JSON API): /api/v1/goods?good_type_id=...&only_stock_items=true
   — все товары раздела каталога с фильтром «в наличии».
2. caprigoshop.ru (PrestaShop): обходим разделы мебели и собираем ссылки на товары.
3. Сопоставляем по артикулу (stock_number), по убыванию точности:
     exact — страница распродажи из наличия с полным артикулом («...-supersale-...»)
     sklad — страница складской программы («2212-sf027-sklad-...»)
     model — страница модели по базовому артикулу (2212, 33450-r-l и т.п.)
4. С каждой страницы caprigoshop берём цену, старую цену и картинку, чтобы цена
   в фиде совпадала с посадочной страницей (это проверяет модерация Директа).

Запуск:  python caprigo_feed.py [путь_к_фиду.xml]
Только стандартная библиотека Python 3.8+.
"""
import collections
import csv
import hashlib
import html
import json
import logging
import re
import sys
import time
import urllib.error
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from pathlib import Path
from xml.sax.saxutils import escape

SRC = "https://www.caprigo.ru"
SHOP = "https://www.caprigoshop.ru"
# Разделы каталога caprigo.ru (id из ссылки /catalog/<id>), из которых берём товары в наличии
GOOD_TYPES = ["19f69068-cd49-11e7-99d1-005056c00008"]  # МЕБЕЛЬ
UA = "Mozilla/5.0 (compatible; CaprigoFeedBot/1.0)"
SHOP_NAME = "Caprigo"
COMPANY = "Caprigo"
VENDOR = "Caprigo"
THREADS = 6
MIN_OFFERS = 20  # если товаров меньше — что-то сломалось, фид не обновляем

# Разделы caprigoshop.ru, которые не относятся к мебели для ванной — их не обходим
SHOP_SKIP = re.compile(r"kukhn|cveta|cvet-|stil|santekh|smesitel|unitaz|bide|vann[yi]$|dush|polotence|"
                       r"mylnic|ershik|kryuch|stakan|derzhatel|sidene|knopki|interer|kabinet|garderob|"
                       r"gostin|prikhozh|shkafy$|rasschitat|dizajn|zakaz")

HERE = Path(__file__).resolve().parent
DEFAULT_OUT = HERE / "feed" / "caprigo_feed.xml"
LOG_FILE = HERE / "caprigo_feed.log"

log = logging.getLogger("caprigo")


# ---------- HTTP ----------

def fetch(url, retries=3):
    err = None
    for attempt in range(1, retries + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA})
            with urllib.request.urlopen(req, timeout=60) as r:
                return r.read().decode("utf-8", "replace")
        except urllib.error.HTTPError as e:
            if e.code == 404:
                return None
            err = e
        except Exception as e:
            err = e
        log.warning("GET %s — попытка %d: %s", url, attempt, err)
        if attempt < retries:
            time.sleep(5 * attempt)
    raise RuntimeError(f"не удалось загрузить {url}: {err}")


def get_json(path):
    return json.loads(fetch(SRC + "/api/v1" + path))


# ---------- caprigo.ru: товары в наличии ----------

def load_stock_goods():
    goods = {}
    for gt in GOOD_TYPES:
        page = 1
        while True:
            d = get_json(f"/goods?good_type_id={gt}&only_stock_items=true&page={page}")
            for g in d["data"]:
                if not g.get("is_deleted"):
                    goods[g["id"]] = g
            if not d["pagination"].get("next_page"):
                break
            page += 1
    log.info("caprigo.ru: товаров в наличии — %d", len(goods))
    return list(goods.values())


# ---------- caprigoshop.ru: индекс товаров ----------

TR = dict(zip("абвгдеёзийклмнопрстуфыэ", "abvgdeezijklmnoprstufye"))
TR.update({"ж": "zh", "х": "kh", "ц": "c", "ч": "ch", "ш": "sh", "щ": "shh", "ю": "yu", "я": "ya", "ъ": "", "ь": ""})


def slugify(s):
    """Транслитерация как в ЧПУ PrestaShop: «2212-SF027 ПРМ 800» -> «2212-sf027-prm-800»."""
    s = "".join(TR.get(ch, ch) for ch in s.lower())
    return re.sub(r"[^a-z0-9]+", "-", s).strip("-")


SALE_SECTION = "/rasprodazha-mebeli-dlya-vannoj-iz-nalichiya/"  # распродажа из наличия: полный артикул
STOCK_SECTION = "/skladskaya-programma/"                        # складская программа: артикул + отделка
SLUG_MARKERS = {"super", "supersale", "sklad", "expo", "sale"}

PRODUCT_RE = re.compile(re.escape(SHOP) + r"/[a-z0-9-]+/\d+-[^\"#?]*\.html")


def crawl_category(cat):
    found, page = [], 1
    while page < 100:
        h = fetch(f"{SHOP}/{cat}?p={page}")
        if h is None:
            break
        new = [u for u in dict.fromkeys(PRODUCT_RE.findall(h)) if u not in found]
        if not new:
            break
        found += new
        page += 1
    return found


def load_shop_urls():
    home = fetch(SHOP + "/")
    cats = sorted({c for c in re.findall(re.escape(SHOP) + r"/(\d+-[a-z0-9-]+)\"", home) if not SHOP_SKIP.search(c)})
    urls = set()
    with ThreadPoolExecutor(THREADS) as ex:
        for res in ex.map(crawl_category, cats):
            urls.update(res)
    log.info("caprigoshop.ru: разделов — %d, товаров — %d", len(cats), len(urls))
    return urls


class ShopIndex:
    def __init__(self, urls):
        self.exact, self.sklad = {}, {}
        self.model = collections.defaultdict(set)
        for u in urls:
            slug = re.sub(r"^\d+-", "", u.rsplit("/", 1)[1][:-5])
            sku = self._sku_from_slug(slug)
            # Тип страницы определяем по разделу, артикул — по повтору в адресе:
            # магазин меняет формат ЧПУ («...-supersale-...», «super-...»), а раздел и повтор остаются.
            if sku and SALE_SECTION in u:
                self.exact[sku] = u
            elif sku and STOCK_SECTION in u:
                self.sklad[sku] = u
            else:
                self._add_model(u, slug)

    @staticmethod
    def _sku_from_slug(slug):
        """«super-2221-sf027-ow15-2221-g-2221-sf027-ow15-2221-g» -> «2221-sf027-ow15-2221-g»."""
        toks = slug.split("-")
        for k in range(len(toks) // 2, 0, -1):
            tail, before = toks[-k:], toks[:-k]
            while before and before[-1] in SLUG_MARKERS:
                before = before[:-1]
            if before[-k:] == tail and re.match(r"\d", tail[0]):
                return "-".join(tail)
        return None

    def _add_model(self, u, slug):
        toks = slug.split("-")
        page_side = {"l"} if "levyj" in toks else set()
        if "pravyj" in toks:
            page_side.add("r")
        for i, t in enumerate(toks):
            m = re.fullmatch(r"(\d{3,6})([a-z]{0,3})", t)
            if not m:
                continue
            base, suf = m.groups()
            sides = set(page_side)
            if suf in ("l", "r"):
                sides.add(suf)
            j = i + 1
            while j < len(toks) and toks[j] in ("l", "r"):  # «33450-r-l», «38350r-l»
                sides.add(toks[j])
                j += 1
            if suf and suf not in ("l", "r"):
                self.model[t].add(u)
            self.model[base].add(u)
            for s in sides:
                self.model[base + s].add(u)
            if not sides:
                self.model[base + "*"].add(u)

    @staticmethod
    def _best(urls, name):
        nm = name.lower().strip()
        coll = slugify(nm.split()[0]) if nm else ""

        def score(u):
            s = 0
            if coll and f"/{coll}" in u:
                s -= 20  # страница из той же коллекции
            if "smena-ekspozicii" in u or "-expo-" in u:
                s += 15  # витринные наборы из нескольких предметов
            if "rakovin" in u and not nm.startswith("раковин"):
                s += 10
            if "zerkal" in u and "зеркал" not in nm:
                s += 5
            return s, len(u)
        return sorted(urls, key=score)[0]

    def match(self, g):
        sn = (g.get("stock_number") or "").strip()
        if not sn:
            return None, None
        full, first = slugify(sn), slugify(sn.split()[0])
        if full in self.exact:
            return "exact", self.exact[full]
        if first in self.sklad:
            return "sklad", self.sklad[first]
        m = re.fullmatch(r"(\d{3,6})([a-z]*)", first.split("-")[0])
        if not m:
            return None, None
        base, suf = m.groups()
        side = suf[-1:] if suf[-1:] in ("l", "r") else ""
        keys = ([base + suf] if suf else []) + ([base + side, base + "*"] if side else [base])
        for k in keys:
            if self.model.get(k):
                return "model", self._best(self.model[k], g["name"])
        return None, None


# ---------- caprigoshop.ru: данные страницы товара ----------

def num(rx, h):
    m = re.search(rx, h)
    return float(m.group(1)) if m else None


def parse_shop_page(url):
    h = fetch(url)
    if h is None:
        return None
    name = re.search(r'<h1[^>]*itemprop="name"[^>]*>(.*?)</h1>', h, re.S)
    sku = re.search(r'itemprop="sku" content="([^"]*)"', h)
    img = re.search(r'<meta property="og:image" content="([^"]+)"', h)
    price = num(r"var productPrice = ([\d.]+)", h) or num(r'itemprop="price" content="([\d.]+)"', h)
    old = num(r"var productPriceWithoutReduction = ([\d.]+)", h)
    return {
        "name": html.unescape(re.sub(r"\s+", " ", name.group(1))).strip() if name else None,
        "sku": html.unescape(sku.group(1)).strip() if sku else "",
        "image": img.group(1) if img else None,
        "price": price,
        "oldprice": old if old and price and old > price + 1 else None,
    }


# ---------- сборка ----------

def clean_text(s):
    if not s:
        return ""
    s = s.replace("¶", "\n")
    s = re.sub(r"<[^>]+>", " ", s)
    s = re.sub(r"[ \t]+", " ", s)
    s = re.sub(r"\s*\n\s*", "\n", s).strip()
    return "" if len(s) < 20 or " " not in s else s  # «УК069617» и т.п. — служебные коды, не описание


def category_of(name):
    n = name.lower()
    for key, cat in (("зеркал", "Зеркала"), ("пенал", "Шкафы и пеналы"), ("шкаф", "Шкафы и пеналы"),
                     ("комплект", "Комплекты мебели"), ("тумб", "Тумбы"), ("комод", "Комоды"),
                     ("консол", "Консоли"), ("полк", "Полки")):
        if key in n:
            return cat
    return "Мебель для ванной"


def collect():
    goods = load_stock_goods()
    index = ShopIndex(load_shop_urls())

    matched, unmatched = [], []
    rank = {"exact": 0, "sklad": 1, "model": 2}
    for g in goods:
        how, url = index.match(g)
        (matched if url else unmatched).append((rank.get(how, 9), how, url, g))
    matched.sort(key=lambda m: m[0])
    log.info("Сопоставлено: %d (точно: %d, склад: %d, модель: %d), без пары: %d",
             len(matched), *(sum(1 for m in matched if m[1] == k) for k in ("exact", "sklad", "model")),
             len(unmatched))

    urls = sorted({m[2] for m in matched})
    with ThreadPoolExecutor(THREADS) as ex:
        pages = dict(zip(urls, ex.map(parse_shop_page, urls)))

    offers, report, seen = [], [], set()
    for _, how, url, g in matched:
        p = pages.get(url)
        if not p or not p["price"]:
            status = "нет цены на caprigoshop"
        elif url in seen:
            status = "дубль ссылки"  # несколько отделок одной модели ведут на одну страницу
        elif how != "model" and not slugify(g["stock_number"]).startswith(slugify(p["sku"]) or "-"):
            status = f"артикул не совпал ({p['sku']})"
        else:
            status = "ok"
        report.append([g["stock_number"], g["name"].strip(), how, url, status,
                       p["price"] if p else "", g.get("action_price_min_component") or g.get("price")])
        if status != "ok":
            continue
        seen.add(url)
        pics = ([p["image"]] if p["image"] else []) + \
               [SRC + i["image_path"] for i in sorted(g.get("images") or [], key=lambda i: i.get("order") or 0)
                if i.get("image_path") and not i.get("three_d")]
        if not pics:
            continue
        if how == "model" and p["name"]:
            name = p["name"]  # страница модели: название как на посадочной
        else:
            name = re.sub(r"^модель\s+", "", g["name"].strip(), flags=re.I)
        offers.append({
            "id": hashlib.md5(url.encode()).hexdigest()[:16],
            "name": name,
            "url": url,
            "price": p["price"],
            "oldprice": p["oldprice"],
            "category": category_of(name + " " + g["name"]),
            "pictures": list(dict.fromkeys(pics))[:10],
            "description": clean_text(g.get("description") or g.get("short_description")),
            "params": [(c["name"], c["value"]) for c in (g.get("characteristics") or []) if c.get("name") and c.get("value")],
            "sku": p["sku"] or g["stock_number"],
        })
    for _, how, url, g in unmatched:
        report.append([g["stock_number"], g["name"].strip(), "", "", "нет на caprigoshop", "",
                       g.get("action_price_min_component") or g.get("price")])
    return offers, report


def x(s):
    s = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", str(s))
    return escape(s, {'"': "&quot;"})


def build_yml(offers):
    cats = {c: n for n, c in enumerate(sorted({o["category"] for o in offers}), start=1)}
    now = datetime.now(timezone(timedelta(hours=3))).isoformat(timespec="seconds")  # МСК, даже на серверах GitHub (UTC)
    out = ['<?xml version="1.0" encoding="UTF-8"?>', f'<yml_catalog date="{now}">', "<shop>",
           f"<name>{x(SHOP_NAME)}</name>", f"<company>{x(COMPANY)}</company>", f"<url>{SHOP}/</url>",
           '<currencies><currency id="RUR" rate="1"/></currencies>', "<categories>"]
    out += [f'<category id="{n}">{x(c)}</category>' for c, n in cats.items()]
    out += ["</categories>", "<offers>"]
    for o in offers:
        out.append(f'<offer id="{o["id"]}" available="true">')
        out.append(f"<name>{x(o['name'])}</name>")
        out.append(f"<url>{x(o['url'])}</url>")
        out.append(f"<price>{round(o['price'])}</price>")
        if o["oldprice"]:
            out.append(f"<oldprice>{round(o['oldprice'])}</oldprice>")
        out.append("<currencyId>RUR</currencyId>")
        out.append(f"<categoryId>{cats[o['category']]}</categoryId>")
        out += [f"<picture>{x(p)}</picture>" for p in o["pictures"]]
        out.append(f"<vendor>{x(VENDOR)}</vendor>")
        if o["sku"]:
            out.append(f"<vendorCode>{x(o['sku'])}</vendorCode>")
        if o["description"]:
            out.append(f"<description><![CDATA[{o['description'][:3000].replace(']]>', ']] >')}]]></description>")
        out.append("<sales_notes>В наличии</sales_notes>")
        out += [f'<param name="{x(k)}">{x(v)}</param>' for k, v in o["params"]]
        out.append("</offer>")
    out += ["</offers>", "</shop>", "</yml_catalog>"]
    return "\n".join(out)


def main():
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    out_path = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_OUT
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s",
                        handlers=[logging.FileHandler(LOG_FILE, encoding="utf-8"), logging.StreamHandler(sys.stdout)])
    try:
        offers, report = collect()
    except Exception:
        log.exception("Ошибка сбора данных — старый фид оставлен без изменений")
        return 1
    if len(offers) < MIN_OFFERS:
        log.error("Товаров в фиде: %d — меньше %d, фид не перезаписан", len(offers), MIN_OFFERS)
        return 1

    out_path.parent.mkdir(parents=True, exist_ok=True)
    # Перезаписываем содержимое существующего файла, а не подменяем файл:
    # так на Google Диске у фида сохраняется тот же ID и ссылка для Директа не меняется.
    # Синхронизация Диска заливает файл только после его закрытия, полузаписанным он не уйдёт.
    xml = build_yml(offers).encode("utf-8")
    with open(out_path, "r+b" if out_path.exists() else "wb") as f:
        f.write(xml)
        f.truncate()

    # Отчёт сопоставления: что попало в фид, а что нет и почему (открывается в Excel)
    with open(out_path.with_name("match_report.csv"), "w", encoding="utf-8-sig", newline="") as f:
        w = csv.writer(f, delimiter=";")
        w.writerow(["Артикул caprigo.ru", "Название", "Тип сопоставления", "Ссылка caprigoshop.ru",
                    "Статус", "Цена caprigoshop", "Цена caprigo.ru"])
        w.writerows(report)
    log.info("Готово: %d товаров -> %s", len(offers), out_path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
