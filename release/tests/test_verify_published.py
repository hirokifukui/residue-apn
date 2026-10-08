#!/usr/bin/env python3
"""test_verify_published.py <work dir> -- positive and negative tests of ../verify_published.py on copies of the
package (the package itself is not changed; nothing is deleted).
Cases: unchanged copy (PASS); a listed file missing (moved aside); a listed file modified; an unlisted file added; a
shipped script given a development path; a README naming a file that is not shipped; a licence column changed.
Last line VERIFY_PUBLISHED_TESTS=PASS n/n (exit 0) or FAIL (exit 1)."""
import shutil, subprocess, sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]

def mv_aside(r, rel):
    (r / rel).rename(r.parent / ((r / rel).name + '.moved_by_test'))

CASES = [
    ('pos_unchanged', None, 0, None),
    ('neg_missing_file', lambda r: mv_aside(r, 'checks/src/gf.py'), 1, 'V1 missing checks/src/gf.py'),
    ('neg_modified_file', lambda r: open(r / 'lean/PINS.json', 'a').write(' '), 1, 'V1 changed lean/PINS.json'),
    ('neg_unlisted_file', lambda r: (r / 'checks/extra.py').write_text('print(1)\n'), 1, 'V2 unlisted checks/extra.py'),
    ('neg_dev_path', lambda r: (r / 'checks/run_quick.sh').write_text((r / 'checks/run_quick.sh').read_text() + '# cd ../paper_R5\n'), 1, 'V4 checks/run_quick.sh'),
    ('neg_readme_names_missing', lambda r: (r / 'README.md').write_text((r / 'README.md').read_text() + '\nSee `release/NOT_SHIPPED.md`.\n'), 1, 'V3 README.md names release/NOT_SHIPPED.md'),
    ('neg_licence_changed', lambda r: (r / 'release/DISTRIBUTION_FILES.tsv').write_text(
        (r / 'release/DISTRIBUTION_FILES.tsv').read_text().replace('\tMIT\t', '\tGPL\t', 1)), 1, 'V5 licence'),
]

def main():
    work = Path(sys.argv[1]).resolve()
    if work.exists() and any(work.iterdir()): print('work dir not empty'); sys.exit(2)
    work.mkdir(parents=True, exist_ok=True)
    ok = 0
    for name, mutate, exp, token in CASES:
        r = work / name / 'pkg'
        shutil.copytree(ROOT, r, ignore=shutil.ignore_patterns('repro_runs', '__pycache__'))
        if mutate: mutate(r)
        p = subprocess.run([sys.executable, '-I', str(r / 'release/verify_published.py'), str(r)], capture_output=True, text=True)
        out = p.stdout
        good = p.returncode == exp and (token is None or token in out) and (exp != 0 or 'PUBLISHED_CHECK=PASS' in out)
        ok += good
        print('%-26s exit=%s %s' % (name, p.returncode, 'ok' if good else 'WRONG\n' + out[-600:]))
    print('VERIFY_PUBLISHED_TESTS=%s %d/%d' % ('PASS' if ok == len(CASES) else 'FAIL', ok, len(CASES)))
    sys.exit(0 if ok == len(CASES) else 1)

if __name__ == '__main__':
    main()
