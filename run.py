#!/usr/bin/env python3
"""Salle d'enquête - robot d'analyse 100 % déterministe (aucune IA, aucun LLM).

Pipeline : découverte des PDF -> téléchargement -> texte (pdfplumber / OCR) ->
règles (regex, dictionnaires) -> modèle (personnes, relations) -> data/*.json
"""
import hashlib, io, json, os, re, sys, time, unicodedata
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urljoin, urlparse

DATA = Path(os.environ.get("DATA_DIR", "data"))
LISTING_URLS = [u.strip() for u in os.environ.get(
    "LISTING_URLS", "https://www.justice.gov/epstein/doj-disclosures").split(",") if u.strip()]
MAX_DOCS = int(os.environ.get("MAX_DOCS", "25"))          # PDF traités par exécution
MAX_LISTING_PAGES = int(os.environ.get("MAX_LISTING_PAGES", "40"))
TIME_BUDGET = int(os.environ.get("TIME_BUDGET_S", str(35 * 60)))
MAX_PDF_MB = int(os.environ.get("MAX_PDF_MB", "30"))
MAX_OCR_PAGES = int(os.environ.get("MAX_OCR_PAGES", "12"))
DELAY = float(os.environ.get("REQUEST_DELAY_S", "2"))
MIN_MENTIONS = int(os.environ.get("MIN_MENTIONS", "2"))
MAX_NODES = int(os.environ.get("MAX_NODES", "500"))
MASK_SENSITIVE = os.environ.get("MASK_SENSITIVE", "1") == "1"
COOKIE = os.environ.get("SITE_COOKIE", "")               # ex. cookie de l'âge-gate si nécessaire
UA = os.environ.get("BOT_UA", "EpsteinGraphBot/1.0 (analyse citoyenne de documents publics)")

# ----------------------------------------------------------------- règles
TITLES = r"(?:Mr|Mrs|Ms|Dr|Prince|Princess|Judge|Sir|Lord|Lady|Sen|Gov|Rep|Prof)"
NAME = (rf"(?:{TITLES}\.?\s+)?[A-Z][a-z]+(?:\s+[A-Z]\.)?(?:\s+(?:de|von|van|bin|al|del|di))?"
        r"(?:\s+[A-Z][a-zA-Z'\u2019\-]+){1,2}")
NAME_RE = re.compile(NAME)
TITLE_RE = re.compile(rf"^{TITLES}\.?\s+")

STOP = set("""the a an and or of in on at to for from by with without about as is are was were be been this that these
those it its his her their our your my we they he she you i united states state department court district county beach island
islands new york florida street avenue road office bureau federal investigation page exhibit case document division attorney
general southern northern virgin palm times post news university college school hospital bank inc llc corp company foundation
trust airport hotel club grand jury special agent police sheriff senate house committee oversight justice national
international american north south east west january february march april may june july august september october november
december monday tuesday wednesday thursday friday saturday sunday subject sent cc bcc re fw fwd dear thanks thank regards
sincerely best hello hi yesterday today tomorrow then also however according meanwhile later subsequently please see
attached forwarded original message confidential privileged republic kingdom royal government ministry
secretary treasury director manager president chairman mrs mr ms dr miss judge sir lord lady""".split())

ROLE_RULES = [
    ("avocat·e", r"\b(attorney|lawyer|counsel|esq\b|law firm|barrister)"),
    ("pilote / équipage", r"\b(pilot|co-pilot|flight attendant|crew)"),
    ("employé·e / assistant·e", r"\b(assistant|secretary|employee|employed|housekeeper|personal assistant|staff)"),
    ("enquêteur / police", r"\b(fbi|special agent|detective|investigator|police|sheriff)"),
    ("procureur / juge", r"\b(prosecutor|u\.?s\.? attorney|judge|magistrate)"),
    ("témoin", r"\b(testif|witness|deposition|deponent|sworn)"),
    ("victime présumée", r"\b(victim of|alleged victim|jane doe|minor victim|accuser|alleged abuse of)"),
    ("journaliste", r"\b(reporter|journalist|editor|correspondent)"),
    ("politique / diplomatie", r"\b(senator|governor|congress|minister|prince|ambassador|mayor)"),
    ("affaires / finance", r"\b(ceo|founder|investor|financier|hedge fund|chairman|billionaire|banker)"),
    ("science / université", r"\b(professor|scientist|researcher|harvard|mit\b|university)"),
]
ROLE_RES = [(r, re.compile(p, re.I)) for r, p in ROLE_RULES]

REL_VERBS = [
    ("a rencontré", r"met with|met|had dinner with|dined with|lunched with|visited"),
    ("a voyagé avec", r"flew with|traveled with|travelled with|was a passenger with"),
    ("a écrit / appelé", r"emailed|e-mailed|wrote to|messaged|texted|called|telephoned"),
    ("travaille pour", r"worked for|was employed by|reported to|was hired by|worked as an assistant to"),
    ("représente", r"represented|was the attorney for|was the lawyer for"),
    ("a accusé", r"accused"),
]
REL_PATTERNS = [(t, re.compile(rf"(?P<a>{NAME})\s+(?:{v})\s+(?P<b>{NAME})")) for t, v in REL_VERBS]
HEADER_RE = re.compile(r"^\s*(From|To|Cc|CC)\s*:\s*(.+)$", re.M)
ADDR_RE = re.compile(r'"?([^"<>;\n]+?)"?\s*<[^>]+>')

now = lambda: datetime.now(timezone.utc).isoformat(timespec="seconds")


# ------------------------------------------------------------- utilitaires
def norm_key(name: str) -> str:
    n = TITLE_RE.sub("", name.strip())
    n = re.sub(r"\b[A-Z]\.", "", n)
    n = unicodedata.normalize("NFKD", n).encode("ascii", "ignore").decode().lower()
    return re.sub(r"[^a-z' \-]", "", n).replace("'", "").strip()


def clean_name(raw: str):
    """Retire titres et mots-outils aux extrémités ; renvoie None si pas un nom plausible."""
    n = TITLE_RE.sub("", raw.strip())
    toks = n.split()
    while toks and toks[0].lower().strip(".") in STOP:
        toks.pop(0)
    while toks and toks[-1].lower().strip(".") in STOP:
        toks.pop()
    core = [t for t in toks if not re.fullmatch(r"[A-Z]\.", t)]
    if len(core) < 2 or any(t.lower() in STOP for t in core):
        return None
    if any(len(t) < 2 for t in core):
        return None
    return " ".join(toks)


def find_names(sentence: str):
    out = []
    for m in NAME_RE.finditer(sentence):
        nm = clean_name(m.group(0))
        if nm:
            out.append((nm, norm_key(nm), m.start(), m.end()))
    return out


def split_sentences(text: str):
    flat = re.sub(r"\s+", " ", text)
    return [s.strip() for s in re.split(r"(?<=[.!?])\s+(?=[A-Z\"'])", flat) if len(s.strip()) > 20]


def load(path, default):
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"))
    except Exception:
        return default


def save(path, obj):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(json.dumps(obj, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")


# ----------------------------------------------------------------- modèle
class Model:
    def __init__(self, d):
        self.people = d.get("people", {})
        self.edges = d.get("edges", {})

    def person(self, key, display):
        p = self.people.setdefault(key, {"name": display, "forms": {}, "mentions": 0,
                                         "docs": [], "roles": {}, "role_ev": {}})
        p["forms"][display] = p["forms"].get(display, 0) + 1
        return p

    def mention(self, key, display, doc, page, sentence, pos_start, pos_end):
        p = self.person(key, display)
        p["mentions"] += 1
        if doc not in p["docs"]:
            p["docs"].append(doc)
        window = sentence[max(0, pos_start - 100): pos_end + 100]
        for role, rx in ROLE_RES:
            if rx.search(window):
                p["roles"][role] = p["roles"].get(role, 0) + 1
                ev = p["role_ev"].setdefault(role, [])
                if len(ev) < 2:
                    ev.append({"doc": doc, "page": page, "text": sentence[:300]})

    def edge(self, a, b, etype, kind, doc, page, sentence):
        if a == b:
            return
        if kind == "cooccurrence":
            a, b = sorted((a, b))
        k = f"{a}|{b}|{etype}"
        e = self.edges.setdefault(k, {"a": a, "b": b, "type": etype, "kind": kind, "w": 0, "ev": []})
        e["w"] += 1
        if len(e["ev"]) < 3:
            e["ev"].append({"doc": doc, "page": page, "text": sentence[:300]})

    def to_dict(self):
        return {"people": self.people, "edges": self.edges}


# ---------------------------------------------------------------- analyse
def analyze_page(model: Model, text: str, doc: str, page: int, log: list):
    new_before = len(model.people)
    # 1) en-têtes d'e-mails (From / To / Cc)
    sender, recips = None, []
    for m in HEADER_RE.finditer(text):
        field, val = m.group(1).lower(), m.group(2)
        names = []
        for am in ADDR_RE.finditer(val):
            raw = am.group(1).strip().strip('"')
            if "," in raw and raw.count(",") == 1:
                last, first = [x.strip() for x in raw.split(",")]
                raw = f"{first} {last}"
            if raw.islower() or raw.isupper():
                raw = raw.title()
            nm = clean_name(raw)
            if nm:
                names.append(nm)
        if field == "from" and names:
            sender = names[0]
        elif field in ("to", "cc"):
            recips += names
    if sender and recips:
        sk = norm_key(sender)
        model.person(sk, sender)["mentions"] += 1
        for r in recips:
            rk = norm_key(r)
            model.person(rk, r)["mentions"] += 1
            for kk, nm in ((sk, sender), (rk, r)):
                if doc not in model.people[kk]["docs"]:
                    model.people[kk]["docs"].append(doc)
            hdr = f"From: {sender} -> To/Cc: {r}"
            model.edge(sk, rk, "e-mail", "explicit", doc, page, hdr)
            log.append({"t": now(), "kind": "explicit", "doc": doc, "page": page,
                        "msg": f"e-mail détecté : {sender} → {r}"})

    # 2) phrases : noms, rôles, relations explicites, cooccurrences
    for s in split_sentences(text):
        names = find_names(s)
        if not names:
            continue
        for nm, key, a, b in names:
            model.mention(key, nm, doc, page, s, a, b)
        explicit_pairs = set()
        for etype, rx in REL_PATTERNS:
            for m in rx.finditer(s):
                na, nb = clean_name(m.group("a")), clean_name(m.group("b"))
                if na and nb:
                    ka, kb = norm_key(na), norm_key(nb)
                    if ka != kb:
                        model.edge(ka, kb, etype, "explicit", doc, page, s)
                        explicit_pairs.add(frozenset((ka, kb)))
                        log.append({"t": now(), "kind": "explicit", "doc": doc, "page": page,
                                    "msg": f"relation explicite : {na} {etype} {nb}"})
        keys = list(dict.fromkeys(k for _, k, _, _ in names))
        if 2 <= len(keys) <= 8:
            for i in range(len(keys)):
                for j in range(i + 1, len(keys)):
                    if frozenset((keys[i], keys[j])) not in explicit_pairs:
                        model.edge(keys[i], keys[j], "cooccurrence", "cooccurrence", doc, page, s)
    added = len(model.people) - new_before
    if added:
        log.append({"t": now(), "kind": "people", "doc": doc, "page": page,
                    "msg": f"{added} nouvelle(s) personne(s) détectée(s)"})


# ----------------------------------------------------- fusion des doublons
def similar(a: str, b: str) -> float:
    try:
        from rapidfuzz import fuzz
        return fuzz.ratio(a, b)
    except Exception:
        import difflib
        return 100 * difflib.SequenceMatcher(None, a, b).ratio()


def merge_pass(model: Model, review: dict):
    """Fusion auto (score >= 94, même nom de famille) ; 85-94 -> à vérifier."""
    blocks = {}
    for k in model.people:
        blocks.setdefault(k.split()[-1], []).append(k)
    redirect, cands = {}, []
    for last, keys in blocks.items():
        keys.sort(key=lambda x: -model.people[x]["mentions"])
        for i, a in enumerate(keys):
            if a in redirect:
                continue
            for b in keys[i + 1:]:
                if b in redirect:
                    continue
                fa, fb = a.split()[0], b.split()[0]
                sc = similar(a, b)
                same_first = fa == fb or fa.startswith(fb) or fb.startswith(fa)
                if (sc >= 94 and similar(fa, fb) >= 85) or (same_first and len(a.split()) != len(b.split())
                                                              and min(len(fa), len(fb)) >= 4 and sc >= 80):
                    redirect[b] = a
                elif sc >= 85:
                    cands.append({"a": model.people[a]["name"], "b": model.people[b]["name"], "score": round(sc)})
    for b, a in redirect.items():
        pa, pb = model.people[a], model.people.pop(b)
        pa["mentions"] += pb["mentions"]
        pa["docs"] = list(dict.fromkeys(pa["docs"] + pb["docs"]))
        for f, c in pb["forms"].items():
            pa["forms"][f] = pa["forms"].get(f, 0) + c
        for r, c in pb["roles"].items():
            pa["roles"][r] = pa["roles"].get(r, 0) + c
        for r, ev in pb["role_ev"].items():
            pa["role_ev"].setdefault(r, []).extend(ev[:1])
    if redirect:
        new = {}
        for e in model.edges.values():
            a, b = redirect.get(e["a"], e["a"]), redirect.get(e["b"], e["b"])
            if a == b:
                continue
            if e["kind"] == "cooccurrence":
                a, b = sorted((a, b))
            k = f'{a}|{b}|{e["type"]}'
            t = new.setdefault(k, {"a": a, "b": b, "type": e["type"], "kind": e["kind"], "w": 0, "ev": []})
            t["w"] += e["w"]
            t["ev"] = (t["ev"] + e["ev"])[:3]
        model.edges = new
    review["merges_auto"] = review.get("merges_auto", 0) + len(redirect)
    review["merges_to_check"] = cands[:200]


# ------------------------------------------------------------ publication
def top_role(p):
    return max(p["roles"], key=p["roles"].get) if p["roles"] else "non déterminé"


def initials(name):
    return " ".join(t[0] + "." for t in name.split() if t)


def publish(model: Model, docs: dict, state: dict, log: list, review: dict):
    people = {k: p for k, p in model.people.items() if p["mentions"] >= MIN_MENTIONS}
    deg = Counter()
    for e in model.edges.values():
        if e["a"] in people and e["b"] in people and (e["kind"] == "explicit" or e["w"] >= 2):
            deg[e["a"]] += 1
            deg[e["b"]] += 1
    score = {k: p["mentions"] + 3 * deg[k] for k, p in people.items()}
    keep = set(sorted(people, key=lambda k: -score[k])[:MAX_NODES])

    nodes = []
    for k in keep:
        p = people[k]
        sensitive = p["roles"].get("victime présumée", 0) >= 3
        name = max(p["forms"], key=p["forms"].get)
        nodes.append({
            "id": k, "name": initials(name) if (sensitive and MASK_SENSITIVE) else name,
            "masked": bool(sensitive and MASK_SENSITIVE), "sensitive": sensitive,
            "aliases": [] if sensitive else [f for f in p["forms"] if f != name][:5],
            "role": top_role(p),
            "roles": {} if sensitive else dict(sorted(p["roles"].items(), key=lambda x: -x[1])[:4]),
            "role_evidence": {} if sensitive else p["role_ev"],
            "mentions": p["mentions"], "docs": len(p["docs"]), "score": score[k],
        })

    pairs = {}
    for e in model.edges.values():
        if e["a"] not in keep or e["b"] not in keep:
            continue
        if e["kind"] == "cooccurrence" and e["w"] < 2:
            continue
        pk = tuple(sorted((e["a"], e["b"])))
        t = pairs.setdefault(pk, {"source": pk[0], "target": pk[1], "kind": "cooccurrence",
                                  "weight": 0, "types": [], "evidence": []})
        t["weight"] += e["w"]
        if e["kind"] == "explicit":
            t["kind"] = "explicit"
            if e["type"] not in t["types"]:
                t["types"].append(e["type"])
            t["evidence"] = (e["ev"] + t["evidence"])[:3]
        elif len(t["evidence"]) < 3 and not t["types"]:
            t["evidence"] = (t["evidence"] + e["ev"])[:3]
    edges = list(pairs.values())
    masked = {n["id"] for n in nodes if n["masked"]}
    for e in edges:  # pas de texte source pour les personnes masquées
        if e["source"] in masked or e["target"] in masked:
            e["evidence"] = [{"doc": x["doc"], "page": x["page"], "text": "[extrait masqué]"} for x in e["evidence"]]

    used_docs = {x["doc"] for e in edges for x in e["evidence"]}
    used_docs |= {x["doc"] for n in nodes for ev in n["role_evidence"].values() for x in ev}
    meta = {"generated_at": now(), "documents_analyzed": len(state["done"]),
            "documents_failed": len(state["failed"]), "queue_discovered": state.get("discovered", 0),
            "people_total": len(model.people), "people_published": len(nodes),
            "edges_published": len(edges),
            "explicit_edges": sum(1 for e in edges if e["kind"] == "explicit"),
            "disclaimer": "Être cité dans un document ne signifie pas être impliqué. "
                          "Analyse automatique par règles : faux positifs possibles."}
    save(DATA / "graph.json", {"meta": meta, "nodes": nodes, "edges": edges})
    save(DATA / "docs.json", {d: docs[d] for d in used_docs if d in docs})
    save(DATA / "log.json", log[-300:])
    save(DATA / "review.json", review)


# ---------------------------------------------------------- source / PDF
def http():
    import requests
    s = requests.Session()
    s.headers.update({"User-Agent": UA})
    if COOKIE:
        s.headers["Cookie"] = COOKIE
    return s


def discover(sess, state):
    """Parcourt les pages de liste (largeur d'abord) et collecte les liens PDF."""
    from bs4 import BeautifulSoup
    seen, queue, pdfs = set(), list(LISTING_URLS), []
    base_host = urlparse(LISTING_URLS[0]).netloc
    while queue and len(seen) < MAX_LISTING_PAGES:
        url = queue.pop(0)
        if url in seen:
            continue
        seen.add(url)
        try:
            r = sess.get(url, timeout=30)
            time.sleep(DELAY)
            if r.status_code != 200:
                continue
        except Exception as ex:
            print("listing KO", url, ex)
            continue
        soup = BeautifulSoup(r.text, "html.parser")
        for a in soup.find_all("a", href=True):
            link = urljoin(url, a["href"]).split("#")[0]
            host = urlparse(link).netloc
            if link.lower().split("?")[0].endswith(".pdf"):
                pdfs.append(link)
            elif host == base_host and "/epstein" in link and link not in seen:
                queue.append(link)
    pdfs = list(dict.fromkeys(pdfs))
    state["discovered"] = max(state.get("discovered", 0), len(pdfs))
    return pdfs


def download(sess, url):
    r = sess.get(url, timeout=60, stream=True)
    r.raise_for_status()
    size = int(r.headers.get("Content-Length", 0))
    if size > MAX_PDF_MB * 1024 * 1024:
        raise ValueError(f"PDF trop gros ({size // 1024 // 1024} Mo)")
    buf = io.BytesIO()
    for chunk in r.iter_content(1 << 16):
        buf.write(chunk)
        if buf.tell() > MAX_PDF_MB * 1024 * 1024:
            raise ValueError("PDF trop gros")
    return buf.getvalue()


def extract_pages(blob: bytes, review: dict, doc: str):
    """Génère (n° page, texte). OCR en dernier recours."""
    import pdfplumber
    ocr_used = 0
    with pdfplumber.open(io.BytesIO(blob)) as pdf:
        for i, page in enumerate(pdf.pages, 1):
            text = page.extract_text() or ""
            if len(text.strip()) < 30 and ocr_used < MAX_OCR_PAGES:
                try:
                    import pytesseract
                    img = page.to_image(resolution=200).original
                    text = pytesseract.image_to_string(img, lang="eng")
                    ocr_used += 1
                    conf = len(re.findall(r"[A-Za-z]{3,}", text))
                    if conf < 15:
                        review.setdefault("ocr_errors", []).append(
                            {"doc": doc, "page": i, "reason": "OCR peu fiable ou page caviardée"})
                except Exception as ex:
                    review.setdefault("ocr_errors", []).append({"doc": doc, "page": i, "reason": f"OCR KO : {ex}"})
            yield i, text


def process_doc(sess, url, model, docs, state, log, review):
    doc = hashlib.sha1(url.encode()).hexdigest()[:10]
    log.append({"t": now(), "kind": "doc", "doc": doc, "msg": f"ouverture du document {url.rsplit('/', 1)[-1]}"})
    blob = download(sess, url)
    sha = hashlib.sha256(blob).hexdigest()
    if any(v.get("sha") == sha for v in state["done"].values()):
        state["done"][url] = {"sha": sha, "pages": 0, "at": now(), "dup": True}
        return
    pages = 0
    for n, text in extract_pages(blob, review, doc):
        pages += 1
        analyze_page(model, text, doc, n, log)
    docs[doc] = {"url": url, "name": url.rsplit("/", 1)[-1], "pages": pages}
    state["done"][url] = {"sha": sha, "pages": pages, "at": now()}
    log.append({"t": now(), "kind": "doc", "doc": doc, "msg": f"document terminé : {pages} page(s)"})


def main():
    t0 = time.time()
    DATA.mkdir(parents=True, exist_ok=True)
    state = load(DATA / "state.json", {"done": {}, "failed": {}})
    model = Model(load(DATA / "model.json", {}))
    docs_all = load(DATA / "docs_all.json", {})
    log = load(DATA / "log.json", [])
    review = load(DATA / "review.json", {})
    sess = http()

    urls = discover(sess, state)
    todo = [u for u in urls if u not in state["done"] and u not in state["failed"]][:MAX_DOCS]
    print(f"{len(urls)} PDF découverts, {len(todo)} à traiter")
    for u in todo:
        if time.time() - t0 > TIME_BUDGET:
            break
        try:
            process_doc(sess, u, model, docs_all, state, log, review)
        except Exception as ex:
            state["failed"][u] = str(ex)[:200]
            log.append({"t": now(), "kind": "error", "msg": f"échec {u.rsplit('/', 1)[-1]} : {str(ex)[:120]}"})
        time.sleep(DELAY)

    merge_pass(model, review)
    if len(model.edges) > 300_000:  # borne la taille du modèle
        model.edges = {k: e for k, e in model.edges.items() if e["kind"] == "explicit" or e["w"] >= 2}
    publish(model, docs_all, state, log, review)
    save(DATA / "model.json", model.to_dict())
    save(DATA / "docs_all.json", docs_all)
    save(DATA / "state.json", state)
    print("terminé en", round(time.time() - t0), "s")


if __name__ == "__main__":
    main()
