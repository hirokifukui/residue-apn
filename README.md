# Coefficient choice in Galois-ring lifts of APN permutations — paper, Lean 4 formalization, blueprint and finite computations

**Status: version 2.0.0, released 2026-10-27.** Software (this version): doi:10.5281/zenodo.23683493; all versions:
doi:10.5281/zenodo.23232180. Paper (preprint, this version): doi:10.5281/zenodo.23683495; all versions:
doi:10.5281/zenodo.23232182; arXiv:2610.21178 (its replacement by this paper was submitted on 2026-10-27). Source repository: https://github.com/hirokifukui/residue-apn
(tag `v2.0.0`).

Version 2.0.0 replaces the paper of versions 1.0.x ("Explicit reduced APN permutations: ramification and optimal
Galois-ring lifts") by a substantially revised and extended paper; see `CHANGELOG.md`. Versions 1.0.0 and 1.0.1 stay
available under their tags and version DOIs.

Let `m ≥ 5` be odd, `q = 2^m`, `k ≥ 3`, and let `p` be a reduced quadratic APN permutation of `F_q` whose formal
derivative is nowhere zero and two-to-one. Among all polynomials over the Galois ring `GR(2^k, m)` that reduce to `p`
coefficient by coefficient (the lifts of `p`), the paper determines:

- **B** the least possible largest difference-table entry on unit differences: `q` or `2q`, decided by two invariants
  of `p` and the level `k`; **C** every lift attaining it; **D** complete exceptional spectra and a certificate
  modulo 8 that decides optimality at every level; **E** when an optimal lift modulo 8 stays optimal at all levels;
- **A** for the explicit family `P_{m,r}`, one added monomial lowers the maximum from `4q`, or from at least `q^2`, to
  `2q` at every level without raising the degree; for every odd `m ≥ 5`, residue permutations with at most 16 monomials
  attain `q` after one 2-adic digit of one coefficient of the natural lift is changed;
- **G** under a uniform starting state and independent uniform round keys, layerwise bounds for characteristics and
  two-round differentials that distinguish lifts with the same global differential uniformity.

## Ways in
1. **Read the result**: `paper/manuscript.pdf` (source `paper/manuscript.tex`).
2. **What is formalized**: `TRUST.md`, then the blueprint `blueprint/blueprint.pdf` (every result of the paper, its
   Lean declarations, what remains on paper, and the computations that cross-check it).
3. **Reproduce**: `REPRODUCE.md`.
4. **Cite**: `CITATION.cff` (the paper is the preferred citation, version DOI doi:10.5281/zenodo.23683495).

## First command (Python ≥ 3.9, standard library; seconds)
```
python3 release/verify_published.py
```
It checks the size and SHA-256 of every file listed in `release/DISTRIBUTION_FILES.tsv`, that nothing unlisted is
present, and that every package path named in this README and in `REPRODUCE.md` exists.

## Formalization in one paragraph
Lean 4 (`leanprover/lean4:v4.31.0-rc1`) with Mathlib at revision `d568c8c09630de097a046763c17b9ea99f95f950`;
`supplement/lean/` has 55 modules, the root `Apn2R03.lean` and `Audit.lean`. `Audit.lean` prints the axioms of 150
declarations; in the author's clean build all depend only on propext, Classical.choice and Quot.sound, no declaration
uses sorry, and leanchecker re-checks the root and every module. Formalized: Theorems A–D and F, Corollary E, the
results across levels, the intermediate-layer theorem, the residue family, valuation preservation, the product
bounds for characteristics in every layer, the two-round differential bounds, the fixed-key bound and the residue
partition. On paper: operation counts, the coefficient formulas and existence arguments for the representative
families, the digit recursion for the remaining intermediate-layer configurations, the passage from two to N ≥ 2
rounds, and the general case of the low-cost lifts. The blueprint lists the split item by item.

## Licences
Code and machine-readable files: MIT (`LICENSE`). Prose by the author (paper source and PDF, blueprint text and PDF,
Markdown): CC BY 4.0 (`LICENSE-CC-BY-4.0.txt`). The `licence` column of `release/DISTRIBUTION_FILES.tsv` is
authoritative for every file. Dependencies are not bundled: `THIRD_PARTY_NOTICES.md`.

## Relation to other work
The paper cites, and is distinct from, H. Fukui, *Optimal reduced representatives of quadratic APN permutations in
odd dimension* (arXiv:2610.21169). Its use of AI tools is described in Appendix A of the paper.
