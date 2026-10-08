# TRUST — what is checked by whom, and what is not (status of this copy: `README.md`, `release/CURRENT_STATE.json`)

## Labels
- **F** — a Lean 4 statement, identified by its declaration name, proved and checked by the Lean kernel; logical axioms
  a subset of propext, Classical.choice, Quot.sound; no sorry. "F (…) + M" means only the named part is formal.
- **M** — proved in the paper only (checked by reading, not by the kernel). M is not "unproved": it is mathematics
  whose check is human.
- **L** — a result cited from the literature, with the role stated where it is used.
- **C** — a finite computation over a stated range (calibration, table, negative control); never a proof of a
  general statement.

## Coverage by statement (single source: `formalization/leanmap.json`)
| paper | label | formal part | remains M / L |
|---|---|---|---|
| Definition 2.1 | Def | Lean definitions `IsDerivOptimal`, `IsOptimalAPNPerm`, `IsAPN` (read in `MEANING_MAP.md`) | — |
| Lemma 2.2 | F | `lemma_2_2` for every polynomial over F_2 with quadratic support (`IsQuadSupp`), `m` odd; display (1) for F_2 coefficients (`derivative_quadratic`); the formal proof counts roots instead of using a normal basis | — |
| Theorem 3.1 | F | all four items for every admissible `m, r` (`theorem_3_1`): 0/1 coefficients and support, `3r − 2` terms, degree, `map = rep(…)` (the actual Lagrange reduced representative), evaluation, bijectivity, APN, `P' = D`, optimality, fibres `{x, x+1}`, image `{Tr(y+1) = 0}`, `P + 1 = DE`, `E' = 1` | `Tr` is the explicit Frobenius sum `absTr m y = Σ_{i<m} y^{2^i}`; its identification with `Algebra.trace` is not formalized (standard formula) |
| Lemma 3.2, Corollary 3.3 | L + M, M | — | comparison section; not a dependency of A, B, C, R, W |
| Theorem 4.1 | F (…) + M | `P' = g^ℓ`, `P + 1 = g^ℓ E`, `g` separable with `2^s` roots in `F_{2^{2s}} \ (F_{2^s} ∪ F_q)`, `gcd(g, E) = 1`, `P = 1` at the roots, multiplicity `ℓ` in `P + 1` and `P'` | reading multiplicities as ramification indices / different exponents of `P^1 → P^1`, the point at infinity (Riemann–Hurwitz), the full fibre over 1 |
| Remark 4.2 | Rem | — | remark with a computation (C) |
| Proposition 5.1 | F (identity) + M | the identity in `Z[X]` and its image in every commutative ring | the operation count |
| Proposition 6.1, Theorem 6.2 | F (abstract finite ring) + M | for every finite commutative ring `R` with a surjection `π` onto `F` such that elements outside `ker π` are units (and, in 6.2(2), `α ∈ ker π` with annihilator `ker π`); fibre size `#ker π`; `#R = #F·#ker π` | that `GR(2^k, m)` satisfies these hypotheses, `#ker π = q^{k−1}`, the count `(q−2)q^{k−1}` of directions (`formalization/GR_BRIDGE.md`); bounds cited from Rønjom–Sandrib (L) |
| Proposition 7.1 | F (after the normalisation) + M | the exclusion and `det B ≠ 0`, with the normalisation as a hypothesis | existence of the normalisation |

## Recorded executions (who ran what)
| run | what | result | where |
|---|---|---|---|
| author, development tree (studio, Apple M3 Ultra), 2026-10-07 | stage 2 (15 files): `lake build` (b19), audits stage 1–2, `lean4checker --fresh ResidueAPN.All`; stage 3 (16 files, adds Lemma 2.2): `lake build` (b20), audits stage 1–3 | b19 and b20: 0 errors, 0 `sorry`; every audited statement depends on exactly propext, Classical.choice, Quot.sound; stage-2 checker exit 0 (799 s) | `lean/records/development/` (logs as recorded; they show the author's paths) |
| author, portable release check (`lean/run_release.sh`) from a fresh copy of `lean/`, Mathlib fetched by git revision, 2026-10-07 | all gates: pins, digest before/after, `lake exe cache get`, build, audits incl. `AuditAxiomsAll`, axiom gate, `lean4checker --fresh ResidueAPN.All` (checker at the pinned revision, checked) | stage 2 (digest `dad9c6b2…1891`): PASS, 44 axiom lines; stage 3 (digest `c1844f54…fdda`, the shipped sources): PASS, 33 final declarations, 53 axiom lines, all exactly propext, Classical.choice, Quot.sound; fresh check 799 s | `lean/records/portable_R11_stage2/`, `lean/records/portable_R12_stage3/` |
| author, finite checks (`checks/run_quick.sh`) | 10 steps | see `checks/expected/` | agora (Apple silicon), Python 3 + NumPy |
| independent reviewer (ChatGPT, R7 review) | read the sources and types, re-ran the finite checks in its own environment, wrote independent finite checks; **did not run Lean** | finite checks PASS; Lean: NOT RUN | not part of this package (private review) |

No external party has re-run the Lean build. A static search for missing proof markers is not a kernel check. The
blueprint gate checks that Lean names exist, not their types. A proof of a conditionally stated theorem does not
discharge its hypotheses (the Galois-ring instance, the normalisation of §7).

## Trust boundary
The intended meaning of the definitions (`MEANING_MAP.md`), the Lean logic and kernel, the pinned Mathlib and its
dependencies, lean4checker at the pinned revision and the toolchain are trusted. The finite checks trust Python and
NumPy. The proofs labelled M are checked by reading only. Nothing here is external journal peer review.
