# Check Lemma A (affine structure of A_F for support-preserving lifts) on arbitrary term files:
#   A_F(a) - A_F(0) = sum_{v>=1} c_{0v} (a rho)^(2^(v-1)) + sum_{v>=2} c_{1v} (a rho^(2^v) + rho a^(2^v))
import sys, json, subprocess
sys.path.insert(0, '/home/claude/w/research/sparse_r06')
from sym import GF, invariants
D = '/home/claude/w/research/sparse_r06'
POLY = {int(l.split()[0]): int(l.split()[1]) for l in open(D + '/polys.txt')}
def check(m, fn):
    F = GF(m, POLY[m]); L = open(fn).read().split('\n'); n = int(L[0])
    c = {}; l = {}; const = 0; maxdig = 0
    for row in L[1:1 + n]:
        v = list(map(int, row.split())); e = v[0]; dig = v[1:1 + m]; maxdig = max(maxdig, max(dig))
        r = sum((d & 1) << i for i, d in enumerate(dig))
        bs = [i for i in range(e.bit_length()) if e >> i & 1]
        if len(bs) > 2: return dict(fn=fn.split('/')[-1], skipped='not support-preserving: exponent %d has binary weight %d' % (e, len(bs)))
        if not r: continue
        if e == 0: const = r
        elif len(bs) == 1: l[bs[0]] = l.get(bs[0], 0) ^ r
        elif len(bs) == 2 and e < (1 << m): c[(bs[0], bs[1])] = c.get((bs[0], bs[1]), 0) ^ r
        else: return dict(fn=fn, skipped='non-quadratic exponent %d' % e)
    iv = invariants(F, c, l)
    if not iv['H']: return dict(fn=fn, skipped='not (H)')
    rho = iv['rho']
    o = json.loads(subprocess.run([D + '/gr', 'aset', str(m), str(POLY[m]), '3', fn, str(rho)], capture_output=True, text=True, check=True).stdout)
    A = o['A']; m1 = m - 1
    def Lp(a):
        s = 0
        for (u, v), cc in c.items():
            if u == 0: s ^= F.mul(cc, F.frob(F.mul(a, rho), v - 1))
            if u == 1 and v >= 2: s ^= F.mul(cc, F.mul(a, F.frob(rho, v)) ^ F.mul(rho, F.frob(a, v)))
        return s
    ok = all(A[a] ^ A[0] == Lp(a) for a in range(F.q))
    return dict(fn=fn.split('/')[-1], m=m, rho=rho, mu=iv['mu'], z=iv['z'], A_zeros=o['zeros'], lemmaA_ok=ok, max_digit=maxdig)
if __name__ == '__main__':
    for arg in sys.argv[1:]:
        m, fn = arg.split(':'); print(json.dumps(check(int(m), fn)))
