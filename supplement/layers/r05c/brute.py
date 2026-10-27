# Exhaustive (brute-force) spectra: per pair/class via clsspec (C), full rows via redspec2 (C, from r07/layers).
import subprocess, os, tempfile
from collections import Counter
from gr import Ctx, res
HERE = os.path.dirname(os.path.abspath(__file__))
def brute_union(ctx, centers, base, sh=2):
    """Counter N -> multiplicity (zeros omitted), N = (#y mod 2^n)/q, over targets base+2^sh R."""
    C = ctx
    lines = [f"{C.m} {C.k} {37 if C.m==5 else 0} {C.j} {sh}",
             " ".join(map(str, C.alpha)), " ".join(map(str, C.uinv)), " ".join(map(str, base)), str(len(centers))]
    for x in centers:
        for f in C.taylor(x): lines.append(" ".join(map(str, f)))
    fd, fn = tempfile.mkstemp(suffix='.in', dir=HERE); os.close(fd)
    open(fn, 'w').write("\n".join(lines) + "\n")
    o = subprocess.run([os.path.join(HERE, 'clsspec'), fn], capture_output=True, text=True)
    os.unlink(fn)
    if o.returncode: raise RuntimeError(o.stderr)
    out = Counter()
    for l in o.stdout.split('\n'):
        if l.strip():
            c, mlt = map(int, l.split()); assert c % C.q == 0; out[c // C.q] += mlt
    return out
def brute_union2(ctx, centers, base, sh=2):
    """Same as brute_union, via clsspec2 (Taylor data of T)."""
    C = ctx
    lines = [f"{C.m} {C.n} {37 if C.m==5 else 0} {sh}", " ".join(map(str, base)), str(len(centers))]
    for x in centers:
        for t in C.ttaylor(x): lines.append(" ".join(map(str, t)))
    fd, fn = tempfile.mkstemp(suffix='.in', dir=HERE); os.close(fd)
    open(fn, 'w').write("\n".join(lines) + "\n")
    o = subprocess.run([os.path.join(HERE, 'clsspec2'), fn], capture_output=True, text=True)
    os.unlink(fn)
    if o.returncode: raise RuntimeError(o.stderr)
    out = Counter()
    for l in o.stdout.split('\n'):
        if l.strip():
            c, mlt = map(int, l.split()); assert c % C.q == 0; out[c // C.q] += mlt
    return out
def brute_row(ctx, termfile):
    C = ctx
    a = C.R.pack(C.alpha)
    fd, fn = tempfile.mkstemp(suffix='.al', dir=HERE); os.close(fd)
    open(fn, 'w').write(f"{a}\n")
    o = subprocess.run([os.path.join(HERE, 'redspec2'), str(C.m), str(C.k), '37', termfile, fn], capture_output=True, text=True)
    os.unlink(fn)
    if o.returncode: raise RuntimeError(o.stderr)
    return Counter({int(x.split('x')[0]): int(x.split('x')[1]) for x in o.stdout.split('|')[1].split()})

def brute_row_pairs(ctx):
    """Full row by exhaustive enumeration of every pair (both classes), indexing values mod 2^n relative to T(x_a) (sh=1).
    Returns Counter delta-value -> multiplicity.  Uses only: T(y) mod 2 = p'(ybar), so different pairs never collide."""
    C = ctx; out = Counter(); done = set()
    for a in range(C.q):
        if a in done: continue
        b = a ^ C.rho; done |= {a, b}
        xa = C.center(a); xb = C.R.add(xa, C.tau)
        M = brute_union2(C, [xa, xb], C.Tc(xa, C.R.zero), sh=1)
        for N, c in M.items(): out[N * C.q ** (C.j + 1)] += c
    return out
