#!/usr/bin/env python3
"""Pass 3 (corrected): index-aware stress test.

Each finalist pair carries a list-alignment relation from pass 1:
  raw:   A(o1+k)     vs B(o2+k),     k >= 0
  drop1: A(o1+k)     vs B(o2+k),     k >= 1   (first listed term ignored)
  drop2: A(o1+k)     vs B(o2+k),     k >= 2
  abs:   |A(o1+k)|   vs |B(o2+k)|,   k >= 0
  stripz:A(o1+z1+k)  vs B(o2+z2+k),  k >= 0
Values come from OEIS b-files (true indices). A pair SURVIVES_EXTENDED only
if it matches on at least one list position beyond the listed agreement
length; BREAKS reports the first mismatching list position with both true
indices and (transformed) values.
"""
import json, sys, time
import urllib.request
from concurrent.futures import ThreadPoolExecutor

BFILE = "https://oeis.org/{}/b{}.txt"

def fetch_bfile(a):
    url = BFILE.format(a, a[1:])
    for attempt in range(3):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "coincidence-mining/1.0"})
            with urllib.request.urlopen(req, timeout=60) as r:
                return r.read().decode("utf-8", "replace")
        except Exception:
            time.sleep(2 * (attempt + 1))
    return None

def parse_bfile(text):
    if text is None:
        return None
    terms = {}
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        if len(parts) >= 2:
            try:
                terms[int(parts[0])] = int(parts[1])
            except ValueError:
                pass
    return terms or None

def check_pair(p):
    t1 = parse_bfile(fetch_bfile(p["a1"]))
    t2 = parse_bfile(fetch_bfile(p["a2"]))
    out = {"a1": p["a1"], "a2": p["a2"], "agree": p["agree"], "score": p["score"],
           "variant": p["variant"], "conjectured": p["conjectured"]}
    if t1 is None or t2 is None or p["o1"] is None or p["o2"] is None:
        out["status"] = "NO_BFILE"
        return out
    v = p["variant"]
    kmin = 1 if v == "drop1" else 2 if v == "drop2" else 0
    s1 = p["z1"] if v == "stripz" else 0
    s2 = p["z2"] if v == "stripz" else 0
    def val(t, idx, side):
        x = t.get(idx)
        if x is None:
            return None
        return abs(x) if v == "abs" else x
    ks = []
    k = kmin
    while True:
        i1, i2 = p["o1"] + s1 + k, p["o2"] + s2 + k
        if i1 not in t1 and i2 not in t2 and k > 10000:
            break
        if i1 in t1 and i2 in t2:
            ks.append(k)
        if i1 not in t1 and i2 not in t2:
            # past both b-files' ranges (b-files are contiguous from offset)
            if k > kmin and (ks and k > ks[-1] + 5):
                break
        k += 1
        if k > 200000:
            break
    out["positions_compared"] = len(ks)
    ext = 0
    for k in ks:
        v1 = val(t1, p["o1"] + s1 + k, 1)
        v2 = val(t2, p["o2"] + s2 + k, 2)
        if v1 != v2:
            out["status"] = "BREAKS"
            out["break_position"] = k
            out["index1"] = p["o1"] + s1 + k
            out["index2"] = p["o2"] + s2 + k
            out["value1"] = v1
            out["value2"] = v2
            out["extended_positions_checked"] = ext
            return out
        if k >= p["agree"]:
            ext += 1
    out["extended_positions_checked"] = ext
    out["status"] = "SURVIVES_EXTENDED" if ext > 0 else "SURVIVES_LISTED_ONLY"
    return out

def main():
    src = sys.argv[1] if len(sys.argv) > 1 else "pass3_enriched.json"
    pairs = json.load(open(src))
    print(f"stress2: {len(pairs)} pairs", flush=True)
    results = []
    with ThreadPoolExecutor(max_workers=6) as ex:
        for r in ex.map(check_pair, pairs):
            results.append(r)
    from collections import Counter
    c = Counter(r["status"] for r in results)
    json.dump(results, open("stress2_out.json", "w"))
    print(f"counts={dict(c)}", flush=True)
    for r in results:
        if r["status"] == "SURVIVES_EXTENDED":
            print(f"EXTENDED {r['a1']} vs {r['a2']} variant={r['variant']} "
                  f"agree={r['agree']} extended={r['extended_positions_checked']}", flush=True)
    print("STRESS2 DONE", flush=True)

if __name__ == "__main__":
    main()
