# REPRODUCE — commands only, from the root of a copy of this package

`ROOT` is the directory that contains `README.md`, `release/`, `paper/`, `checks/`, `formalization/`, `blueprint/`,
`lean/` and `tools/`. No command below refers to a home directory or to another folder. Run step 0 first.

## 0. The copy itself (Python ≥ 3.9, standard library; seconds)
```
cd ROOT && python3 release/verify_published.py ; echo "exit=$?"
```
Expected `PUBLISHED_CHECK=PASS`, `exit=0`. Its failure cases: `python3 ROOT/release/tests/test_verify_published.py WORK`
(`WORK` a new directory; expected last line `VERIFY_PUBLISHED_TESTS=PASS 7/7`).

## 1. Finite checks (Python 3 + NumPy; about 6–10 minutes, one core)
```
cd ROOT/checks && bash run_quick.sh ; echo "exit=$?"
```
Expected: `OVERALL PASS`, `exit=0`; the new `repro_runs/<timestamp>/STATUS` equals `checks/expected/STATUS`. Scope
and claims per step: `checks/REPRODUCE_CHECKS.md`. These are calibrations on stated ranges and negative controls,
not proofs.

## 2. Maps and generated files (standard library; seconds)
```
cd ROOT && python3 tools/gen_statement_map.py --check && python3 tools/gen_lean_release_meta.py --check
cd ROOT && python3 tools/gen_metadata.py --check
cd ROOT/blueprint && python3 check_blueprint.py
python3 ROOT/blueprint/tests/test_check_blueprint.py WORK2          # expected BLUEPRINT_GATE_TESTS=PASS 26/26
python3 ROOT/tools/tests/test_gen_metadata.py WORK5                # expected METADATA_TESTS=PASS 40/40
```
`gen_metadata.py --check` regenerates `CITATION.cff`, `release/metadata/zenodo_*.json` and the marked blocks of
`README.md` and `CHANGELOG.md` from `release/metadata_source.json` and compares them byte for byte; its tests use
offline test identifiers only.
`check_blueprint.py` compares the blueprint text, node list, both graphs and the label file with what the generator
produces from `paper/` and `formalization/leanmap.json`, checks that each Lean name exists (a name check, not a type
check) and that the shipped PDF was built from these files (`blueprint/BUILD_RECORD.json`, checked against the
required 11 inputs and 2 outputs of `blueprint/build_record_spec.py`).

## 3. PDFs (pdflatex; Graphviz `dot` for the graphs)
```
cd ROOT/paper && pdflatex manuscript && pdflatex manuscript
cd ROOT/paper/elsarticle && python3 make_elsarticle.py && pdflatex manuscript_els && pdflatex manuscript_els
cd ROOT/blueprint && bash build_blueprint.sh
```
With another TeX installation the PDF bytes differ; compare the extracted text (`pdftotext`). Rebuilding changes
files, so run step 0 before this step.

## 4. Lean release check (elan, git, network for Mathlib; about 30 minutes on an Apple M3 Ultra)
Requirements: `elan` (it installs `leanprover/lean4:v4.31.0-rc1` from `lean-toolchain`), `git`, and a `lean4checker`
binary built at revision `91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709` (`lean/PINS.json` has the commands).
```
cp -R ROOT/lean WORK3                                   # WORK3: a new directory
cd WORK3 && bash run_release.sh --checker CHECKER --logs LOGS --cache-get --checker-rev-check ; echo "exit=$?"
```
`CHECKER` is the path of the `lean4checker` binary, `LOGS` a new directory. Expected `RELEASE_CHECK=PASS`, `exit=0` and
`LOGS/PASS.json` with math-source digest `c1844f5479439c4edffbfb4c3c5a7427f13c21b45bb7eef3edc75076889ffdda`. Any failing
gate gives a nonzero exit and `LOGS/FAIL.json`, never `PASS.json`. Its failure cases are tested without Lean by
`python3 ROOT/lean/tests/test_run_release.py WORK4` (expected `RUN_RELEASE_TESTS=PASS 21/21`).
