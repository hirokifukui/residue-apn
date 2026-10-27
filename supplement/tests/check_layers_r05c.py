# check_layers_r05c.py: fail-closed check of the F6 re-verification (all MATCH) and of the stored R05c tables.
import json, sys, os
d = os.path.join(os.path.dirname(__file__), '..', 'layers', 'r05c')
def load(f): return [json.loads(l) for l in open(os.path.join(d, f)) if l.strip()]
bad = 0; n = 0
for f in ['ver3_replay.jsonl', 'ver1.jsonl', 'ver2.jsonl', 'ver3.jsonl', 'ver3b.jsonl']:
    for r in load(f):
        n += 1
        if not r.get('closed_eq_gr', False): bad += 1; print('closed != GR', f, r.get('label'))
        for key in ('row_closed', 'row_gr'):
            if r.get(key) not in (None, 'MATCH'): bad += 1; print(key, f, r.get('label'), r.get(key))
        for t in r.get('targets', []):
            if t.get('closed') != t.get('brute') or t.get('gr') != t.get('brute'):
                bad += 1; print('target mismatch', f, r.get('label'))
fresh = len(load('ver3_replay.jsonl'))
if fresh != 44: bad += 1; print('expected 44 re-verified sub-case 3 lifts, got', fresh)
if bad: print('LAYERS_R05C FAIL', bad); sys.exit(1)
print('LAYERS_R05C OK', n, 'records (44 re-verified now)')
