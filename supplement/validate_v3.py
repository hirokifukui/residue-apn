# validate_v3.py (Claude, R04-06; from GPT's repaired validate_v2): fail-closed comparison of predicted exceptional/
# penultimate spectra with C rows. R04 changes: empty/unsupported/duplicate scopes rejected; expected record count enforced;
# rows the theorems do not predict are checked against the proven lower bound q^2 (status BOUND_ONLY) and are NOT counted
# as spectrum matches; optional VEXPECT_MATCH / VEXPECT_BOUND pin the exact counts; zero MATCH records is a failure.
# Any failure (child exit, timeout, malformed output, wrong counts, mismatch) -> non-zero exit. Nothing defaults to True.
import subprocess, json, sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from inv import read_terms, invariants
GRDDT = os.environ.get('GRDDT', './grddt3')
FPOLY = {5: '37', 7: '131'}
class Fail(Exception): pass
def run_rows(fn, m, k, rho, mode, per=4, seed=7):
    N = 1 << (m*k)
    env = os.environ.copy(); env['RHO'] = str(rho)
    try:
        proc = subprocess.run([GRDDT, str(m), str(k), FPOLY[m], fn, str(per), str(seed), mode],
                              capture_output=True, text=True, env=env, timeout=int(os.environ.get('VTIMEOUT', '5400')))
    except subprocess.TimeoutExpired:
        raise Fail('timeout')
    if proc.returncode != 0: raise Fail(f'child exit {proc.returncode}: {proc.stderr[-200:]}')
    lines = proc.stdout.splitlines()
    if not lines or lines[0].strip() != 'perm_dups 0': raise Fail('missing/nonzero permutation line: %r' % lines[:1])
    rows = []; seen = set()
    for ln in lines[1:]:
        if not ln.strip(): continue
        parts = ln.split('|')
        if len(parts) != 2: raise Fail('malformed row: ' + ln)
        head = parts[0].split()
        if len(head) != 4 or head[2] != 'max': raise Fail('malformed header: ' + ln)
        cl, a, mx = head[0], int(head[1]), int(head[3])
        if not (0 < a < N): raise Fail('direction out of range')
        if a in seen: raise Fail('repeated direction %d' % a)
        seen.add(a)
        dig = [(a >> (k*i)) & ((1 << k) - 1) for i in range(m)]
        val = min(((d & -d).bit_length() - 1) if d else k for d in dig)
        res = sum((d & 1) << i for i, d in enumerate(dig))
        exp = ('exc' if res == rho else 'ord') if val == 0 else 'v%d' % val
        if cl != exp: raise Fail('class label %s but direction is %s' % (cl, exp))
        hist = {}
        for tok in parts[1].split():
            v, c = map(int, tok.split('x'))
            if v <= 0 or c <= 0 or v in hist: raise Fail('bad histogram token ' + tok)
            hist[v] = c
        if not hist or max(hist) != mx: raise Fail('max mismatch')
        if sum(v*c for v, c in hist.items()) != N: raise Fail('row mass != q^k')
        rows.append((cl, a, hist))
    cnt = collections.Counter(c for c, _, _ in rows)
    if mode == 'exc':
        want = {'exc': (1 << m) ** (k - 1)}
    else:
        want = {c: per for c in ['ord', 'exc'] + ['v%d' % s for s in range(1, k)]}
    if dict(cnt) != want: raise Fail('row counts %r expected %r' % (dict(cnt), want))
    return rows
def predict_exc(iv, m, k):
    q = 1 << m; A = iv['A']; Z = set(iv['Z']); mu = iv['mu']
    s = A.count(0)
    if mu == 0:
        if s: return None                      # singular mu=0 case: not predicted here
        z = len(Z); d = {q: (q - z) * q**(k-2), 2*q: (z//2) * q**(k-2)}
    else:
        if k >= 4 and s: return None           # A-zero at k>=4: only the lower bound q^2 is a theorem
        z0 = sum(1 for a in Z if A[a] == 0)
        nu = sum(1 for a in Z if A[a] != 0 and iv['chi'][a] == 0)
        if k == 3:
            d = {q: (s - z0) * q, 2*q: (q - s + z0 - nu) * q // 2, 4*q: nu * q // 4}
        else:
            d = {2*q: (q - nu) * q**(k-2) // 2, 4*q: nu * q**(k-2) // 4}
    return {v: c for v, c in d.items() if c}
def main(files, m=int(os.environ.get('VM','5')), out=os.environ.get('VOUT','validate_v3.json')):
    if not files:
        raise Fail('no input files: zero-test success is forbidden')
    if m not in FPOLY:
        raise Fail(f'unsupported VM={m}')
    try:
        levels = [int(x) for x in os.environ.get('VK', '3,4').split(',')]
    except ValueError as e:
        raise Fail('VK must be a nonempty subset of 3,4,5') from e
    if not levels or len(levels) != len(set(levels)) or not set(levels) <= {3,4,5}:
        raise Fail('VK must be a nonempty subset of 3,4,5, without duplicates')
    if os.environ.get('VMODE3', 'exc') not in {'exc', 'sample'}:
        raise Fail('VMODE3 must be exc or sample')
    for fn in files:
        if not os.path.isfile(fn):
            raise Fail(f'input file missing: {fn}')
    expected_records = len(files) * len(levels)
    q = 1 << m; recs = []; bad = 0
    for fn in files:
        iv = invariants(read_terms(fn, m), m); rho = iv['rho']; s = iv['A'].count(0)
        KS = levels
        for k, mode in [(3, os.environ.get('VMODE3','exc')), (4, 'sample'), (5, 'sample')]:
            if k not in KS: continue
            rows = run_rows(fn, m, k, rho, mode)
            exc = [h for c, a, h in rows if c == 'exc']
            pred = predict_exc(iv, m, k)
            rec = dict(file=fn, k=k, rho=rho, mu=iv['mu'], z=len(iv['Z']), A_zeros=s,
                       directions=[a for c, a, h in rows], n_exc_rows=len(exc), pred=pred,
                       exc_hists=sorted({tuple(sorted(h.items())) for h in exc}))
            if pred is None:
                # not predicted by the spectrum theorems; every such exceptional row must still satisfy the
                # proven lower bound max >= q^2 (A_F has a zero: ALL_MINIMIZERS M1(iii) for k>=4, M3 proof for k=3, mu=0)
                okb = len(exc) > 0 and all(max(h) >= q * q for h in exc)
                rec['exc_status'] = 'BOUND_ONLY' if okb else 'MISMATCH'; bad += (not okb)
            else:
                ok = len(exc) > 0 and all(h == pred for h in exc)
                rec['exc_status'] = 'MATCH' if ok else 'MISMATCH'; bad += (not ok)
            if k == 4:
                pen = [h for c, a, h in rows if c == 'v2']
                pp = {q**3: q - s}
                if s: pp[2*q**3] = s // 2
                pp = {v: c for v, c in pp.items() if c}
                ok = len(pen) > 0 and all(h == pp for h in pen)
                rec['penult_pred'] = pp; rec['penult_status'] = 'MATCH' if ok else 'MISMATCH'; bad += (not ok)
            recs.append(rec); print(json.dumps({k2: v for k2, v in rec.items() if k2 != 'directions'}), flush=True)
    if len(recs) != expected_records or not recs:
        raise Fail(f'record count {len(recs)} != {expected_records}')
    json.dump(recs, open(out, 'w'), indent=1, default=str)
    if bad: print('MISMATCHES', bad, file=sys.stderr); sys.exit(1)
    n_match = sum(1 for r in recs if r['exc_status'] == 'MATCH')
    n_bound = sum(1 for r in recs if r['exc_status'] == 'BOUND_ONLY')
    if n_match == 0: raise Fail('no record matched a predicted spectrum: zero-test success is forbidden')
    for var, val in (('VEXPECT_MATCH', n_match), ('VEXPECT_BOUND', n_bound)):
        if os.environ.get(var) is not None and int(os.environ[var]) != val:
            raise Fail(f'{var}={os.environ[var]} but observed {val}')
    print('VALIDATE_V3 OK', len(recs), 'records:', n_match, 'MATCH,', n_bound, 'BOUND_ONLY (lower bound only; not counted as spectrum verification)')
if __name__ == '__main__':
    try:
        main(sys.argv[1:])
    except Fail as e:
        print('FAIL', e, file=sys.stderr); sys.exit(2)
