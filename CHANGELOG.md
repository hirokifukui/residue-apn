# CHANGELOG

## 2.0.1 — released 2026-10-27
Corrections after an external read-only audit of the published 2.0.0. `LICENSE-CC-BY-4.0.txt` named the paper of
1.0.x and its former formats; it now names the paper of 2.0.x and lists exactly the CC BY 4.0 files.
`supplement/mk_manifest.py` no longer lists files of a journal version that are not part of this package, so from
2.0.1 on it differs from the copy in the paper's Online Resource 1.
`supplement/README.txt` and this file explain the paper's name for the supplement; `TRUST.md` states the working
paths and the AI-tool headers as they are. The paper, the blueprint, the Lean sources and the computations are
unchanged; the paper and blueprint PDFs are byte-identical to 2.0.0 and remain in the paper's Zenodo version
doi:10.5281/zenodo.23683495. The paper cites the software as doi:10.5281/zenodo.23683493 (tag `v2.0.0`); that
version stays available.

## 2.0.0 — released 2026-10-27
A new paper replaces the paper of 1.0.x: *Coefficient choice in Galois-ring lifts of APN permutations: sharp
unit-direction spectra and one-term optimal lifts*. It is a substantially revised and extended version of the 1.0.x
paper, from which the residue family `P_{m,r}` and its analysis on ordinary directions and on the top layer are taken.
New: the minimax theorem over all lifts, the classification of minimizers, complete exceptional spectra and their
certification modulo 8, optimality across levels, the intermediate layers, sparse representatives with optimal lifts
obtained by changing one coefficient digit, and layerwise bounds for characteristics and two-round differentials.

The package is rebuilt around the new paper: `paper/` (the paper), `blueprint/` (new blueprint and its generator),
`supplement/` (the Lean 4 development of the new paper — 55 modules, 150 audited declarations — and the finite
computations with replay scripts and negative controls; the paper calls this material Online Resource 1, archive
`ESM_1.zip`). The Lean development, checks, formalization maps and release tools of 1.0.x are not part of 2.0.0; they remain in the tags
`v1.0.0` and `v1.0.1` and in the Zenodo versions of 1.0.x.

## 1.0.1 — released 2026-10-08
Corrections after an external read-only review of 1.0.0 (blueprint title page, release documents, licence alias in
the metadata readback, Data-availability DOI). No change to the mathematics.

## 1.0.0 — released 2026-10-08
First public version: the paper *Explicit reduced APN permutations: ramification and optimal Galois-ring lifts*, its
Lean 4 formalization (16 source files), statement and meaning maps, blueprint and finite checks.
