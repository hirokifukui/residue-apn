# Batch verification: python3 verify_batch.py gen.jsonl out.jsonl [start step]
# Policy: full brute-force row if n<=5, or n==6 and (index % 3 == 0); otherwise every open-type pair/class exhaustively.
import sys, json
from verify import run
src, out = sys.argv[1], sys.argv[2]
start = int(sys.argv[3]) if len(sys.argv) > 3 else 0; step = int(sys.argv[4]) if len(sys.argv) > 4 else 1
done = set()
try:
    for l in open(out): done.add(json.loads(l)['file'] + '|' + str(json.loads(l)['k']))
except FileNotFoundError: pass
recs = [json.loads(l) for l in open(src)]
for i in range(start, len(recs), step):
    r = recs[i]
    if r['file'] + '|' + str(r['k']) in done: continue
    n = r['k'] - r['j']
    full = (n <= 5) or (n == 6 and i % 3 == 0)
    lab = r.get('spec') or r.get('mode', '') + '/' + r.get('merge', '')
    run(r['file'], r['k'], r['alpha'], lab, out, full=full)
