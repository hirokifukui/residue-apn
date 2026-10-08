# CHANGELOG

<!-- BEGIN gen_metadata:heading -->
## 1.0.1 — released 2026-10-08
<!-- END gen_metadata:heading -->
Corrections after an external read-only review of 1.0.0. No change to the mathematics, the paper text (apart from
the software version DOI in Data availability), the Lean sources (digest unchanged) or the finite checks.
- Blueprint: the title page no longer calls the document an unpublished private draft.
- This changelog, `release/VERSION_MAP.md`, `release/CURRENT_STATE.json` and `release/PUBLICATION_RUNBOOK.md` no longer
  describe 1.0.0 as planned or as a candidate; the runbook records what was observed when 1.0.0 was deposited.
- `tools/gen_metadata.py --readback` accepts `mit-license`, the licence id that the legacy Zenodo API reports for MIT
  (one named alias, with a new test; any other value is still compared exactly). Its tests read the version from
  the source instead of assuming 1.0.0.
- `TRUST.md` states that the blueprint TeX log, like the Lean development logs, shows the author's paths.

## 1.0.0 — released 2026-10-08
First public version. Contents: the paper (amsart source and PDF; generated elsarticle version), the Lean 4
formalization (16 source files, digest `c1844f54…fdda`; Lemma 2.2 added in stage 3) with a fail-closed release check and its tests, the statement
map, meaning map and Galois-ring bridge, the blueprint with its gate and tests, the finite checks with expected
output, licences and citation metadata. Its Zenodo records are the first versions under the same concept DOIs.

Earlier internal rounds are not public versions; their names are listed in `release/VERSION_MAP.md`.
