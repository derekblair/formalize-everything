#!/usr/bin/env python3
"""Shard scorer for coincidence mining (pass 2, distributed).

Input in cwd: shard_families.json (list of family dicts from pass 1b).
Fetches each member's OEIS internal-format record from the oeisdata GitHub
mirror, scores families by agreement x definition distance, writes
shard_out.json with {finalists, known, stated, stats}.
Prints SHARD DONE when finished.
"""
import json, os, re, sys, time
import urllib.request
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

RAW = "https://raw.githubusercontent.com/oeis/oeisdata/main/seq/{}/{}.seq"

def fetch_record(a, cache_dir="records"):
    os.makedirs(cache_dir, exist_ok=True)
    path = os.path.join(cache_dir, a + ".seq")
    if os.path.exists(path):
        with open(path, encoding="utf-8", errors="replace") as f:
            return f.read()
    url = RAW.format(a[:4], a)
    for attempt in range(3):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "coincidence-mining/1.0"})
            with urllib.request.urlopen(req, timeout=30) as r:
                text = r.read().decode("utf-8", "replace")
            with open(path, "w") as f:
                f.write(text)
            return text
        except Exception:
            time.sleep(1.5 * (attempt + 1))
    return None

def parse_record(text):
    if text is None:
        return None
    rec = {"name": "", "comments": [], "formulas": [], "xrefs": [],
           "keywords": [], "offset": ""}
    for line in text.splitlines():
        if len(line) < 3 or line[0] != "%":
            continue
        kind, rest = line[1], line[3:].strip()
        rest = re.sub(r"^A\d{6}\s*", "", rest)
        if kind == "N":
            rec["name"] = rest
        elif kind == "C":
            rec["comments"].append(rest)
        elif kind == "F":
            rec["formulas"].append(rest)
        elif kind == "Y":
            rec["xrefs"].append(rest)
        elif kind == "K":
            rec["keywords"] = [k.strip() for k in rest.split(",")]
        elif kind == "O":
            rec["offset"] = rest
    return rec

DOMAIN_PATTERNS = [
    ("digits",        r"decimal expansion|continued fraction expansion|digits of|base-\d"),
    ("partitions",    r"partition"),
    ("modular_forms", r"modular form|dedekind eta|theta function|cusp form"),
    ("graphs",        r"graph|tree|polyomino|poset|lattice path"),
    ("primes",        r"prime"),
    ("divisor_arith", r"divisor|sigma\(|phi\(|euler totient|aliquot|abundance|highly composite"),
    ("recurrence",    r"a\(n\)\s*=\s*[^.]*a\(n\s*-\s*1\)"),
    ("polynomial",    r"polynomial|coefficients of"),
    ("geometry",      r"circle|sphere|lattice points|polygon|polyhed"),
    ("permutations",  r"permutation|involution|derangement"),
    ("fibonacci",     r"fibonacci|lucas|pell"),
    ("binomial",      r"binomial|catalan|bernoulli|eulerian|stirling"),
]

def domains(rec, name):
    if rec is None:
        text, forms, keys = name.lower(), "", []
    else:
        text = (rec["name"] + " " + " ".join(rec["comments"])).lower()
        forms = " ".join(rec["formulas"])
        keys = rec["keywords"]
    tags = set()
    for tag, pat in DOMAIN_PATTERNS:
        if re.search(pat, text) or (tag == "recurrence" and re.search(pat, forms)):
            tags.add(tag)
    if "cons" in keys:
        tags.add("digits")
    return tags

def formula_refs(rec):
    if rec is None:
        return set()
    return set(re.findall(r"A\d{6}", " ".join(rec["formulas"])))

def main():
    families = json.load(open("shard_families.json"))
    anums = sorted({a for fam in families for a in fam["members"]})
    print(f"shard: {len(families)} families, {len(anums)} records", flush=True)
    texts = {}
    with ThreadPoolExecutor(max_workers=10) as ex:
        for a, t in zip(anums, ex.map(fetch_record, anums)):
            texts[a] = t
    recs = {a: parse_record(t) for a, t in texts.items()}
    got = sum(1 for r in recs.values() if r is not None)
    print(f"records fetched: {got}/{len(anums)}", flush=True)

    finalists, known, stated = [], [], []
    stats = Counter()
    for fam in families:
        members = fam["members"]
        sp = fam["sample_pair"]
        a1, a2 = sp["a1"], sp["a2"]
        r1, r2 = recs.get(a1), recs.get(a2)
        pair = {"a1": a1, "a2": a2, "name1": sp["name1"], "name2": sp["name2"],
                "agree": fam["max_agree"], "family_size": fam["size"],
                "members": members, "variant": sp["variant"], "terms": sp["terms"]}
        kw = set()
        for a in members:
            if recs.get(a):
                kw.update(recs[a]["keywords"])
        if "dead" in kw:
            stats["dead"] += 1
            continue
        alltext = {}
        for a in members:
            if recs.get(a):
                alltext[a] = " ".join(recs[a]["xrefs"]) + " " + " ".join(recs[a]["comments"])
        recorded = conjectured = False
        for a in members:
            for b in members:
                if a != b and b in alltext.get(a, ""):
                    recorded = True
                    if re.search(r"conjectur", alltext[a], re.I):
                        conjectured = True
        pair["recorded"], pair["conjectured"] = recorded, conjectured
        d1, d2 = domains(r1, sp["name1"]), domains(r2, sp["name2"])
        pair["domains1"], pair["domains2"] = sorted(d1), sorted(d2)
        if d1 == {"digits"} and d2 == {"digits"}:
            stats["digits_pair"] += 1
            continue
        f1, f2 = formula_refs(r1), formula_refs(r2)
        shared = (f1 & f2) - {a1, a2}
        pair["shared_formula_refs"] = sorted(shared)
        if recorded and not conjectured:
            known.append(pair)
            stats["known"] += 1
            continue
        if conjectured:
            stated.append(pair)
            stats["stated_open"] += 1
        dist = 0.5
        if d1 and d2:
            dist = 1.0 if not (d1 & d2) else 0.35
        elif not d1 or not d2:
            dist = 0.6
        score = fam["max_agree"] * dist
        if shared:
            score *= 0.4
        if fam["size"] >= 3:
            score *= 1.15
        pair["score"] = round(score, 1)
        finalists.append(pair)

    finalists.sort(key=lambda p: -p["score"])
    json.dump({"finalists": finalists, "known": known, "stated": stated,
               "stats": dict(stats)},
              open("shard_out.json", "w"))
    print(f"finalists={len(finalists)} known={len(known)} stated={len(stated)} "
          f"stats={dict(stats)}", flush=True)
    print("SHARD DONE", flush=True)

if __name__ == "__main__":
    main()
