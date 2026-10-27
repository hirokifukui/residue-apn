Supplementary material (finite computations and Lean 4 formalization) for
"Coefficient choice in Galois-ring lifts of APN permutations: sharp unit-direction spectra and one-term optimal lifts"
by Hiroki Fukui. This directory has the same content as Online Resource 1 of the paper; only this README differs.
- replay_core.sh: core replay (about 6 min on 2 cores; gcc, Python 3 with SymPy and NumPy). replay_full.sh: full replay
  (about 1.5 h on 2 cores).
- tests/: regression tests and negative controls (tests/replay_negatives.sh, tests/replay_scope_negatives.sh).
- cert/sparse_cert_r06.py: the finite certificate used in the proof of the sparse-family theorem (irreducibility of
  t^17+t^3+1, the 125769 points over F_(2^17), the parameter counts for m <= 13), written independently of the other code.
- lean/: Lean 4 sources (Lean 4.31.0-rc1, Mathlib d568c8c): cd lean && lake build Apn2R03 && lake env lean Audit.lean.
- logs/: author-side build, audit (standard axioms only) and kernel re-check (leanchecker) records, and replay logs.
- LEAN_SCOPE.md / .csv: theorem-level map from the paper to the Lean declarations (LEAN_SCOPE.md is in Japanese;
  the English version is the blueprint, ../blueprint/blueprint.pdf).
- SHA256SUMS of every file of the package: ../release/DISTRIBUTION_FILES.tsv.
