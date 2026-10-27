#!/usr/bin/env python3
"""make_distribution_list.py ROOT -- write ROOT/release/DISTRIBUTION_FILES.tsv (path, bytes, sha256, licence, role).
Licence rule: prose by the author (Markdown, TeX sources of the paper and blueprint, their PDFs, LICENSE-CC-BY-4.0.txt)
is CC-BY-4.0; everything else (code, machine-readable files, logs, records, LICENSE) is MIT."""
import hashlib, sys
from pathlib import Path
ROOT = Path(sys.argv[1]).resolve()
LIST = 'release/DISTRIBUTION_FILES.tsv'
rows = []
for p in sorted(ROOT.rglob('*')):
    if not p.is_file() or '.git' in p.relative_to(ROOT).parts or p.name == '.DS_Store': continue
    rel = p.relative_to(ROOT).as_posix()
    if rel == LIST: continue
    ccby = rel.endswith('.md') or rel == 'LICENSE-CC-BY-4.0.txt' or rel in ('paper/manuscript.tex', 'paper/manuscript.pdf', 'blueprint/blueprint.tex', 'blueprint/blueprint.pdf')
    role = rel.split('/')[0] if '/' in rel else 'top-level'
    rows.append('\t'.join([rel, str(p.stat().st_size), hashlib.sha256(p.read_bytes()).hexdigest(), 'CC-BY-4.0' if ccby else 'MIT', role]))
(ROOT / LIST).write_text('path\tbytes\tsha256\tlicence\trole\n' + '\n'.join(rows) + '\n', encoding='utf-8')
print('listed', len(rows))
