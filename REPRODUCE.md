# REPRODUCE

1. **Copy check** (seconds): `python3 release/verify_published.py` → `PUBLISHED_CHECK=PASS`.
2. **Finite computations** (needs gcc, Python 3 with SymPy and NumPy): `cd supplement && sh replay_core.sh` (stages
   0–9, about 6 minutes on 2 cores; ends with `CORE REPLAY OK`). The full replay `sh replay_full.sh` takes about
   1.5 hours. Negative controls: `sh tests/replay_negatives.sh rep/m7_search.log` (after the core replay) and
   `sh tests/replay_scope_negatives.sh`. Run them in a copy: the replay deletes and regenerates its outputs.
3. **Lean** (elan; Mathlib is fetched by `lake`): `cd supplement/lean && lake exe cache get && lake build Apn2R03 &&
   lake env lean Audit.lean`. Every `#print axioms` line should show a subset of propext, Classical.choice, Quot.sound.
4. **Paper**: `cd paper && pdflatex manuscript.tex` (three times).
5. **Blueprint** (needs Graphviz): `python3 blueprint/gen_blueprint.py paper/manuscript.aux supplement/lean OUT`, then
   in `OUT`: `dot -Tpdf dep_graph.dot -o dep_graph.pdf`, `dot -Tpdf lean_imports.dot -o lean_imports.pdf`,
   `pdflatex blueprint.tex` (twice).
