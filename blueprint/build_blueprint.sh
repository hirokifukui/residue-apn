#!/usr/bin/env bash
# build_blueprint.sh -- regenerate, draw, typeset and gate the blueprint (session R11). Fail-closed: the first failing
# step stops the script with its exit code; BUILD_RECORD.json is written only after a complete build, and the gate runs
# last. Needs: python3, Graphviz `dot`, pdflatex. Build the paper first (its .aux carries the paper's numbers).
#   bash build_blueprint.sh
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-1791331200}" FORCE_SOURCE_DATE=1   # 2026-10-07 00:00 UTC: fixed PDF dates
export PYTHONDONTWRITEBYTECODE=1
python3 gen_blueprint.py
dot -Tpdf dep_graph.dot -o src/dep_graph.pdf
dot -Tpdf lean_imports.dot -o src/lean_imports.pdf
cd src
for i in 1 2 3; do pdflatex -interaction=nonstopmode -halt-on-error print.tex > /dev/null; done
cd ..
cp src/print.pdf blueprint_residue_apn.pdf
python3 - <<'EOF'
import hashlib, json, sys
from pathlib import Path
sys.dont_write_bytecode = True
sys.path.insert(0, '.')
import gen_blueprint as g
import build_record_spec as spec   # the required sets, shared with check_blueprint.py (G7)
h = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
here = Path('.').resolve()
rec = {'_comment': 'written by build_blueprint.sh after a complete build; checked by check_blueprint.py (G7)',
       'inputs': {k: h(spec.path_of(k, here, g)) for k in spec.INPUTS},
       'outputs': {k: h(spec.path_of(k, here, g)) for k in spec.OUTPUTS}}
Path('BUILD_RECORD.json').write_text(json.dumps(rec, indent=1) + '\n')
print('BUILD_RECORD.json written')
EOF
python3 check_blueprint.py
