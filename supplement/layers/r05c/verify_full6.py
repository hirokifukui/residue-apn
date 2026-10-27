# Extra full-row exhaustive checks for n = k-j = 6 rows that were verified pair-only by verify_batch.py.
import json, glob
from verify import run
picked = {}
import sys
for fn in (sys.argv[1:] or ['ver1.jsonl', 'ver2.jsonl', 'ver3.jsonl']):
    for l in open(fn):
        r = json.loads(l)
        if r['k'] - r['j'] != 6 or 'brute_row' in r: continue
        key = (fn, r['label'])
        if key in picked: continue
        picked[key] = r
sel = {}
for (fn, lab), r in picked.items():
    sel.setdefault(fn, [])
    if len(sel[fn]) < 4: sel[fn].append(r)
for fn, rs in sel.items():
    for r in rs: run(r['file'], r['k'], r['alpha'], r['label'], 'ver_full6.jsonl', full=True)
