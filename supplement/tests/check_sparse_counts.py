# check_sparse_counts.py: fail-closed check of the F7 counts (Theorem sparse).
import sys, os, re
t = open(os.path.join(os.path.dirname(__file__), '..', 'rep_sparse', 'replay_counts.out')).read()
want = {5: 15, 7: 42, 9: 126, 11: 506, 13: 2496}
got = {int(a): int(b) for a, b in re.findall(r'm=(\d+) \|C_m\|=(\d+)', t)}
pts = re.findall(r'm=17 points=(\d+)', t)
ok = got == want and pts == ['125769']
print('counts', got, 'curve', pts)
if not ok: print('SPARSE_COUNTS FAIL'); sys.exit(1)
print('SPARSE_COUNTS OK')
