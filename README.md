# Explicit reduced APN permutations: ramification and optimal Galois-ring lifts — paper, Lean 4 formalization, blueprint and finite checks

<!-- BEGIN gen_metadata:status -->
**Status: version 1.0.0, released 2026-10-08.** Software (this version): doi:10.5281/zenodo.23232181; all versions: doi:10.5281/zenodo.23232180. Paper (preprint, this version): doi:10.5281/zenodo.23232183; all versions: doi:10.5281/zenodo.23232182. Source repository: https://github.com/hirokifukui/residue-apn (tag `v1.0.0`). Journal: to be submitted; no journal is named as accepting or publishing it.
<!-- END gen_metadata:status -->

For every odd `m ≥ 5` and every odd `r` with `3 ≤ r < m`, `gcd(r, m) = 1`, the reduced polynomial
`P_{m,r} = red((T_r^3)^{2^{m−2}})`, `T_r = Σ_{i<r} X^{2^i}`:

- **A** has coefficients in F_2 and exactly `3r − 2` terms, is an APN permutation of `F_{2^m}`, and is
  derivative-optimal (its formal derivative has no zero and two-element fibres) — Theorem 3.1;
- **B** has a single finite branch value: `P' = g^ℓ`, `P + 1 = g^ℓ E`, `g = X^{2^s} + X + 1`, `s = m − r`,
  `ℓ = 2^{r−2}` — Theorem 4.1;
- **C** satisfies the identity `P̂ = D̂Ê − 1 − 2(Ŷ + Ẑ)` in `Z[X]` for its 0/1 lift (evaluation over every Galois
  ring `GR(2^k, m)` with one general multiplication) — Proposition 5.1;
- **R** every coefficient lift permutes `GR(2^k, m)` and has exact differential rows in two classes of directions —
  Proposition 6.1, Theorem 6.2; **W** an exclusion for two words and two layers — Proposition 7.1.

## Four ways in
1. **Read the result**: `paper/manuscript.pdf` (amsart, canonical source `paper/manuscript.tex`);
   `paper/elsarticle/manuscript_els.pdf` is generated from the same source by `paper/elsarticle/make_elsarticle.py`
   (body copied byte for byte).
2. **What is formalized**: `TRUST.md`, then `formalization/STATEMENT_MAP.md` (statement ↔ Lean declaration),
   `formalization/MEANING_MAP.md` (Lean definitions read against the paper), `formalization/GR_BRIDGE.md`
   (abstract ring → `GR(2^k, m)`), and the blueprint `blueprint/blueprint_residue_apn.pdf`.
3. **Reproduce**: `REPRODUCE.md` — the copy check, the finite checks, the PDFs and blueprint, and the Lean release
   check are separate commands.
<!-- BEGIN gen_metadata:cite -->
4. **Cite**: `CITATION.cff` (software, version DOI doi:10.5281/zenodo.23232181; the paper is the preferred citation, version DOI doi:10.5281/zenodo.23232183).
<!-- END gen_metadata:cite -->

## First command (Python ≥ 3.9, standard library; seconds)
```
python3 release/verify_published.py
```
It checks the size and SHA-256 of every file listed in `release/DISTRIBUTION_FILES.tsv`, that nothing unlisted is
present, that the entry points named in this README and in `REPRODUCE.md` exist, and that no shipped code or
document depends on a path of the author's working tree. Run it before anything else (later steps write files).

## Formalization in one paragraph
Lean 4 (`leanprover/lean4:v4.31.0-rc1`) with Mathlib at revision `d568c8c09630de097a046763c17b9ea99f95f950`; 16 source
files, math-source digest `c1844f5479439c4edffbfb4c3c5a7427f13c21b45bb7eef3edc75076889ffdda`; axioms a subset of
propext, Classical.choice, Quot.sound; no sorry. Formal: Lemma 2.2 (for polynomials over F_2 with quadratic support), Theorem 3.1 (all four items, for all
admissible `m, r`),
Proposition 5.1 (the identity), Theorem 4.1 (items (1)–(3) and the root multiplicities), Proposition 6.1 and
Theorem 6.2 for an abstract finite ring with a surjection onto `F_q` (the Galois-ring instance is in the paper),
Proposition 7.1 after the normalisation. Not formal: Lemma 3.2, Corollary 3.3, Remark 4.2, the operation
count, the ramification reading and the point at infinity, the Galois-ring construction and cardinalities, the
bounds cited from Rønjom–Sandrib. Recorded runs and their status: `lean/records/` and `TRUST.md`.

## Licences
Code and machine-readable files: MIT (`LICENSE`). Prose by the author (paper sources and PDFs, blueprint text,
Markdown): CC BY 4.0 (`LICENSE-CC-BY-4.0.txt`). The `licence` column of `release/DISTRIBUTION_FILES.tsv` is
authoritative for every file. The two licences cover different files; they are not alternatives for the same file.
For this reason `CITATION.cff` has no top-level `license` (CFF reads a list of licences as alternatives); its
preferred citation, the paper, carries CC-BY-4.0. Dependencies are not bundled: `THIRD_PARTY_NOTICES.md`.

## Relation to other work
The paper cites, and is distinct from, H. Fukui, *Optimal reduced representatives of quadratic APN permutations in
odd dimension* (IEEE Trans. Inf. Theory, IT-26-1499, under review; preprint Zenodo doi:10.5281/zenodo.23074611). This
package is not a version of that work. Three Lean files under `lean/residue_apn_portable/ResidueAPN/Shared/` are
copied from its public package (see `THIRD_PARTY_NOTICES.md`). Internal round names (R5.2, R9, R11, …) are explained in
`release/VERSION_MAP.md`.

## Checks are internal
The scripts, the Lean records and the AI-assisted reviews documented here are internal checks, not external peer
review.
