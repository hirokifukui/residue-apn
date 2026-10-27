# CHANGELOG

## 2.0.0 — released 2026-10-27
A new paper replaces the paper of 1.0.x: *Coefficient choice in Galois-ring lifts of APN permutations: sharp
unit-direction spectra and one-term optimal lifts*. It is a substantially revised and extended version of the 1.0.x
paper, from which the residue family `P_{m,r}` and its analysis on ordinary directions and on the top layer are taken.
New: the minimax theorem over all lifts, the classification of minimizers, complete exceptional spectra and their
certification modulo 8, optimality across levels, the intermediate layers, sparse representatives with optimal lifts
obtained by changing one coefficient digit, and layerwise bounds for characteristics and two-round differentials.

The package is rebuilt around the new paper: `paper/` (the paper), `blueprint/` (new blueprint and its generator),
`supplement/` (the Lean 4 development of the new paper — 55 modules, 150 audited declarations — and the finite
computations with replay scripts and negative controls; the same content as the paper's Online Resource 1). The Lean
development, checks, formalization maps and release tools of 1.0.x are not part of 2.0.0; they remain in the tags
`v1.0.0` and `v1.0.1` and in the Zenodo versions of 1.0.x.

## 1.0.1 — released 2026-10-08
Corrections after an external read-only review of 1.0.0 (blueprint title page, release documents, licence alias in
the metadata readback, Data-availability DOI). No change to the mathematics.

## 1.0.0 — released 2026-10-08
First public version: the paper *Explicit reduced APN permutations: ramification and optimal Galois-ring lifts*, its
Lean 4 formalization (16 source files), statement and meaning maps, blueprint and finite checks.
