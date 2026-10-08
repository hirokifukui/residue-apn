# Third-party notices and sources of reused material

Nothing third-party is bundled in this package. The items below are used, referenced or (for the author's own earlier
package) copied; each is identified by a full revision.

| item | role | how it is used | licence | revision / source |
|---|---|---|---|---|
| Lean 4 | prover | toolchain named in `lean/residue_apn_portable/lean-toolchain`, installed by elan | Apache-2.0 | `leanprover/lean4:v4.31.0-rc1` |
| Mathlib | library | git dependency fetched by `lake` (`lakefile.toml`, `lake-manifest.json`); its compiled cache is fetched by `lake exe cache get` | Apache-2.0 | https://github.com/leanprover-community/mathlib4 at `d568c8c09630de097a046763c17b9ea99f95f950` |
| Mathlib's dependencies | library | pinned in `lean/residue_apn_portable/lake-manifest.json` (plausible, LeanSearchClient, import-graph, ProofWidgets4, aesop, quote4, batteries, lean4-cli) | Apache-2.0 | the `rev` of each entry of `lake-manifest.json` |
| lean4checker | checker | built by the user; called by `lean/run_release.sh` | Apache-2.0 | https://github.com/leanprover/lean4checker at `91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709` |
| apnlift (the author's earlier package) | 3 Lean files | copied into `lean/residue_apn_portable/ResidueAPN/Shared/` (`Definitions.lean`, `QuadraticAPN.lean`, `ReducedRepresentative.lean`); only the namespace `APNLift → ResidueAPN` and the import paths changed (header of each file) | MIT (same author) | GitHub `hirokifukui/apnlift`, tag `v1.0.4` (commit `a860331e9494a43f3d68247feb848d3d6c30f539`), path `lean/apnlift_R41_portable/APNLift/Core/`; sha256 of the originals `9046c194dec2406803be89216ec1bd8a20d449fddeff4ce0a763e80a5dde8dd5`, `2a9a96541d2db4c706585f7d69b092394381caf0368430d427f3460811b6bdc7`, `175726f4e34d28a794e3b2aed6d8664c00100896e91ab9d36a6e5fcf050de072`; Zenodo software concept DOI 10.5281/zenodo.23053111 |
| apnlift (design) | runner and blueprint | `lean/run_release.sh` and `blueprint/gen_blueprint.py` follow the design of apnlift `release_checks/run_release.sh` and `blueprint/R48/` (rewritten here) | MIT (same author) | as above |
| Python 3, NumPy | finite checks | `checks/run_quick.sh` | PSF, BSD-3-Clause | any recent version (recorded runs: `checks/expected/SOURCE_RUN`) |
| pdfTeX / LaTeX (amsart, elsarticle, hyperref, xr-hyper, amsmath) | typesetting | to rebuild the PDFs; not bundled | LPPL and others | TeX Live 2026 (recorded builds) |
| Graphviz `dot` | graphs | to redraw the two blueprint graphs; not bundled | EPL-1.0 | any recent version |

Cited papers are not included (their PDFs are not redistributed). The publisher's Guide for Authors of the target
journal is not included.
