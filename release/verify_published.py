#!/usr/bin/env python3
"""verify_published.py [ROOT] -- check a copy of this package before anything else is run (standard library only).
V1 every file listed in release/DISTRIBUTION_FILES.tsv exists with the listed size and SHA-256;
V2 no file is present that is not listed (the list itself excepted; macOS .DS_Store files are reported, not fatal);
V3 every path named in README.md, REPRODUCE.md and checks/REPRODUCE_CHECKS.md as a package path exists;
V4 no shipped code or document outside the category `record` depends on a path of the author's working tree
   (home directories, the development folders, a local Mathlib tree); a line may name such a path only as a marked
   fallback (`dev-layout fallback`);
V5 every row has a licence of MIT or CC-BY-4.0.
The list does not contain its own hash (no self-reference); record the hash of the list or of an archive outside it.
Exit 0 and PUBLISHED_CHECK=PASS iff V1-V5 pass."""
import hashlib, re, sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parents[1]
LIST = 'release/DISTRIBUTION_FILES.tsv'
DEV = re.compile(r'/Users/|/home/[a-z]|~/lean|\.\./paper_R5|paper_R5/|re_followup/|mathlib-latest|CloudStorage|gpt_review_R|apnlift_portability_probe')
FROZEN = ('lean/residue_apn_portable/ResidueAPN/', 'lean/residue_apn_portable/ResidueAPN.lean')   # digest-protected math sources: their header comments record provenance; exempt from V4
TEXT = {'.py', '.sh', '.md', '.json', '.tsv', '.tex', '.cff', '.txt', '.lean', '.toml', '.dot'}

def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''): h.update(b)
    return h.hexdigest()

def main():
    fails, notes = [], []
    rows = [l.split('\t') for l in (ROOT / LIST).read_text(encoding='utf-8').splitlines()[1:] if l.strip()]
    listed = {}
    for r in rows:
        path, size, h, lic, cat = r[0], int(r[1]), r[2], r[3], r[4]
        listed[path] = (size, h, lic, cat)
        p = ROOT / path
        if not p.is_file(): fails.append('V1 missing ' + path); continue
        if p.stat().st_size != size or sha(p) != h: fails.append('V1 changed ' + path)
        if lic not in ('MIT', 'CC-BY-4.0'): fails.append('V5 licence ' + path)
    for p in sorted(ROOT.rglob('*')):
        if p.is_file():
            rel = p.relative_to(ROOT).as_posix()
            if rel == LIST or rel in listed: continue
            if p.name == '.DS_Store': notes.append('ignored ' + rel); continue
            fails.append('V2 unlisted ' + rel)
    for doc in ('README.md', 'REPRODUCE.md', 'checks/REPRODUCE_CHECKS.md'):
        d = ROOT / doc
        if not d.is_file(): fails.append('V3 missing ' + doc); continue
        base = d.parent
        for tok in re.findall(r'`([^`\s]+)`|ROOT/([\w./-]+)', d.read_text(encoding='utf-8')):
            t = (tok[0] or tok[1]).rstrip('.,;:)')
            if '/' not in t or t.startswith(('http', '-', '<', '~')) or any(c in t for c in '*{}<>$=:') \
               or t.split('/')[0] in ('WORK', 'WORK2', 'WORK3', 'WORK4', 'LOGS', 'CHECKER', 'repro_runs') \
               or t.startswith('repro_runs/') or re.search(r'\.\.\.|…', t):
                continue
            t2 = t[len('ROOT/'):] if t.startswith('ROOT/') else t
            if not ((ROOT / t2).exists() or (base / t2).exists()):
                fails.append('V3 %s names %s, not in the package' % (doc, t))
    for path, (_, _, _, cat) in listed.items():
        if not (ROOT / path).is_file() or cat == 'record' or path.startswith(FROZEN) or Path(path).suffix not in TEXT or path == 'release/verify_published.py' \
           or path == 'release/tests/test_verify_published.py':
            continue
        for i, line in enumerate((ROOT / path).read_text(encoding='utf-8', errors='replace').splitlines(), 1):
            if DEV.search(line) and 'dev-layout fallback' not in line:
                fails.append('V4 %s:%d depends on a development path' % (path, i))
    for n in notes: print('note:', n)
    print('files listed %d' % len(listed))
    for f in fails[:50]: print(f)
    print('PUBLISHED_CHECK=' + ('PASS' if not fails else 'FAIL (%d)' % len(fails)))
    sys.exit(1 if fails else 0)

if __name__ == '__main__':
    main()
