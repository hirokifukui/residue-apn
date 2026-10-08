# lean/ — the Lean 4 formalization and its release check

| path | role |
|---|---|
| `residue_apn_portable/` | Lean project `ResidueAPN`: 16 math source files (`ResidueAPN/**/*.lean`, `ResidueAPN.lean`; digest `c1844f54…fdda`, stage 3; stage 2 = the same files without `LemmaO.lean`, digest `dad9c6b2…1891`), `audit/` (restated final types, printed definitions, axiom prints), `lakefile.toml` (Mathlib by git revision `d568c8c0…`), `lake-manifest.json` (every dependency pinned, no path dependency), `lean-toolchain` (`leanprover/lean4:v4.31.0-rc1`) |
| `run_release.sh` | the release check, fail-closed: inputs → pins → source digest → (`lake exe cache get`) → `lake build` (+ no `sorry` in the log) → audits → axiom gate (each name of `FINAL_DECLARATIONS.txt` has an axiom line; axioms a subset of propext, Classical.choice, Quot.sound; no `sorryAx`) → `lean4checker --fresh ResidueAPN.All` → source digest again. `PASS.json` only if every gate passes; a non-empty log directory is refused; paths are taken from the script's own position |
| `PINS.json` | toolchain, Mathlib, lean4checker revisions; digest rule |
| `FINAL_DECLARATIONS.txt`, `residue_apn_portable/audit/AuditAxiomsAll.lean` | generated from `../formalization/leanmap.json` by `../tools/gen_lean_release_meta.py` |
| `tests/test_run_release.py` | 21 cases with a mock `lake` and checker (no Lean needed): 3 positive, 18 negative |
| `records/development/` | logs of the development build (b19), audits and the `lean4checker` run, as recorded (they show the author's paths), and the development runners and configuration (`runners/`; they assumed the author's directory layout and did not propagate failures; superseded by `run_release.sh`, kept as the record of what was run) |
| `records/portable_R11/` | the portable release check run from a fresh copy of this folder (when present) |

`ResidueAPN/All.lean` imports every part, so one `lean4checker --fresh ResidueAPN.All` replays the whole development.
The audits check type compatibility of the restated statements; the meaning of the definitions is checked by reading
(`../formalization/MEANING_MAP.md`).
