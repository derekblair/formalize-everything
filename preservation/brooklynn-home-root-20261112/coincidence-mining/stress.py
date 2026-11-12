#!/usr/bin/env python3
"""Pass 3 stress test: extend finalist pairs via OEIS b-files and hunt for
the first term where the two sequences diverge (the Borwein move).

Input: pass3_finalists.json (or a slice). For each pair, fetch both b-files
(oeis.org/A######/b######.txt), parse (index, value) pairs, align by index,
and compare over the union range. Output: stress_out.json with per-pair
{status: SURVIVES(n terms checked) | BREAKS at index i (values) | NO_BFILE}.
Prints STRESS DONE at the end.
"""
import json, os, re, sys, time
import urllib.request
from concurrent.futures import ThreadPoolExecutor

BFILE = "https://oeis.org/{}/b{}.txt"

def anum_digits(a):
    return a[1:]

def fetch_bfile(a):
    url = BFILE.format(a, anum_digits(a))
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

def check_pair(pair):
    t1 = parse_bfile(fetch_bfile(pair["a1"]))
    t2 = parse_bfile(fetch_bfile(pair["a2"]))
    out = {"a1": pair["a1"], "a2": pair["a2"], "agree_listed": pair["agree"],
           "score": pair["score"]}
    if t1 is None or t2 is None:
        out["status"] = "NO_BFILE"
        out["have1"] = t1 is not None
        out["have2"] = t2 is not None
        return out
    common = sorted(set(t1) & set(t2))
    out["bfile_terms_compared"] = len(common)
    for i in common:
        if t1[i] != t2[i]:
            out["status"] = "BREAKS"
            out["break_index"] = i
            out["value1"] = t1[i]
            out["value2"] = t2[i]
            return out
    out["status"] = "SURVIVES"
    out["max_index_checked"] = common[-1] if common else None
    return out

def main():
    src = sys.argv[1] if len(sys.argv) > 1 else "pass3_finalists.json"
    pairs = json.load(open(src))
    print(f"stress: {len(pairs)} pairs", flush=True)
    results = []
    with ThreadPoolExecutor(max_workers=6) as ex:
        for r in ex.map(check_pair, pairs):
            results.append(r)
    breaks = [r for r in results if r["status"] == "BREAKS"]
    survives = [r for r in results if r["status"] == "SURVIVES"]
    json.dump(results, open("stress_out.json", "w"))
    print(f"SURVIVES={len(survives)} BREAKS={len(breaks)} "
          f"NO_BFILE={len(results) - len(survives) - len(breaks)}", flush=True)
    for r in breaks:
        print(f"BREAK {r['a1']} vs {r['a2']} at index {r['break_index']}: "
              f"{r['value1']} != {r['value2']}", flush=True)
    print("STRESS DONE", flush=True)

if __name__ == "__main__":
    main()
