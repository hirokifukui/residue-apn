#!/usr/bin/env python3
"""verify_published.py [ROOT] -- check a copy of this package before anything else is run (standard library only).
V1 every file listed in release/DISTRIBUTION_FILES.tsv exists with the listed size and SHA-256;
V2 no file is present that is not listed (the list itself excepted; macOS .DS_Store files are reported, not fatal);
V3 every package path named in README.md and REPRODUCE.md exists;
V4 every row has a licence of MIT or CC-BY-4.0.
The list does not contain its own hash. Exit 0 and PUBLISHED_CHECK=PASS iff V1-V4 pass."""
import hashlib, re, sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parents[1]
LIST = 'release/DISTRIBUTION_FILES.tsv'

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
        path, size, h, lic = r[0], int(r[1]), r[2], r[3]
        listed[path] = (size, h, lic)
        p = ROOT / path
        if not p.is_file(): fails.append('V1 missing ' + path); continue
        if p.stat().st_size != size or sha(p) != h: fails.append('V1 changed ' + path)
        if lic not in ('MIT', 'CC-BY-4.0'): fails.append('V4 licence ' + path)
    for p in sorted(ROOT.rglob('*')):
        if p.is_file() and '.git' not in p.relative_to(ROOT).parts:
            rel = p.relative_to(ROOT).as_posix()
            if rel == LIST or rel in listed: continue
            if p.name == '.DS_Store': notes.append('ignored ' + rel); continue
            fails.append('V2 unlisted ' + rel)
    for doc in ('README.md', 'REPRODUCE.md'):
        for tok in re.findall(r'`([^`\s]+)`', (ROOT / doc).read_text(encoding='utf-8')):
            t = tok.rstrip('.,;:)')
            if '/' not in t or t.startswith(('http', '-', '<', '~')) or any(c in t for c in '*{}<>$=:^') or t.startswith('OUT'):
                continue
            if not ((ROOT / t).exists() or (ROOT / 'supplement' / t).exists() or (ROOT / 'supplement/lean' / t).exists()):
                fails.append('V3 %s names %s, not in the package' % (doc, t))
    for n in notes: print('note:', n)
    print('files listed %d' % len(listed))
    for f in fails[:50]: print(f)
    print('PUBLISHED_CHECK=' + ('PASS' if not fails else 'FAIL (%d)' % len(fails)))
    sys.exit(1 if fails else 0)

if __name__ == '__main__':
    main()
