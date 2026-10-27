# Third-party notices

Nothing third-party is bundled in this package.

| item | role | how it is used | licence | revision |
|---|---|---|---|---|
| Lean 4 | prover | toolchain named in `supplement/lean/lean-toolchain`, installed by elan | Apache-2.0 | `leanprover/lean4:v4.31.0-rc1` |
| Mathlib and its dependencies | library | git dependencies fetched by `lake` (`supplement/lean/lakefile.toml`, `lake-manifest.json`) | Apache-2.0 | https://github.com/leanprover-community/mathlib4 at `d568c8c09630de097a046763c17b9ea99f95f950`; the others at the `rev` of each entry of `lake-manifest.json` |
| gcc, Python 3, SymPy, NumPy | finite computations | `supplement/replay_core.sh`, `replay_full.sh` | GPL-3.0 with runtime exception, PSF, BSD-3-Clause | versions recorded in the replay logs (`supplement/logs/`) |
| Magma | optional cross-check | `supplement/checker_magma_v2.m` (not needed for the replay) | proprietary, not bundled | V2.29-7 |
| pdfTeX / LaTeX, Graphviz | typesetting | to rebuild the PDFs and graphs | LPPL and others; EPL-1.0 | TeX Live; any recent Graphviz |

Cited papers are not included.
