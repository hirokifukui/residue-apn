# GR_BRIDGE — from the abstract ring of the Lean statements to GR(2^k, m) (one page; session R11, GPT R8-03)

The Lean statements of Proposition 6.1 and Theorem 6.2 (`ResidueAPN/Ring.lean`, `ResidueAPN/TheoremR.lean`) are proved
for an **abstract** finite commutative ring `R` with a ring map `π : R →+* F` onto a finite field `F`. Galois rings are
not in Mathlib at the pinned revision, so the step from the abstract ring to `R = GR(2^k, m)`, `k ≥ 2`, `q = 2^m`,
`π` = reduction mod 2, is made in the paper (label **M**, standard facts about Galois rings). It is not unproved
mathematics: it is mathematics checked by reading, not by the Lean kernel.

## The four structural facts used (hypotheses of the Lean statements)

| # | hypothesis in Lean | meaning | holds for GR(2^k, m) because (paper level) |
|---|---|---|---|
| B1 | `hsurj : Function.Surjective π` | π maps onto `F_q` | `GR(2^k,m)/2GR(2^k,m) ≅ F_q`; `ker π = 2R` |
| B2 | `hunit : ∀ u, π u ≠ 0 → IsUnit u` | elements outside `ker π` are units | `R` is local with maximal ideal `2R` |
| B3 | `hα0 : π α = 0`, `hann : ∀ r, α * r = 0 ↔ π r = 0` | `α ∈ ker π` with annihilator `ker π` | for `α ∈ 2^{k−1}R \ {0}`: `α = 2^{k−1}u`, `u` a unit, so `αr = 0 ⇔ r ∈ 2R` (and `π α = 0` as `k ≥ 2`) |
| B4 | — (cardinalities) | `#R = q^k`, `#ker π = q^{k−1}` | `R` is free of rank `m` over `Z/2^k`; `2R ≅ R/2^{k−1}R` has `q^{k−1}` elements |

None of B1–B4 is the differential-uniformity statement being proved; the Lean proofs derive the DDT rows from them by
Taylor expansion and counting (`taylor_diff`, `eq_zero_of_eval_add_eq`, `card_fibre`, `card_roots_in_fibre`,
`card_ker_mul`). The family wrappers (`prop_6_1_family`, `thm_6_2_unit_family`, `thm_6_2_top_family`) connect them to
`P_{m,r}` through Theorem 3.1 (`polP`, `polD`, `ker K = {0,1}`).

## What is formal and what is arithmetic in the paper

| paper statement | formal (Lean) | paper-level step (M) |
|---|---|---|
| Prop. 6.1: every coefficient lift permutes `R` | `prop_6_1`, `prop_6_1_family` (uses B2) | `GR(2^k,m)` satisfies B2 |
| Thm 6.2(1): `δ_F(α,β) = #{y : p(y+ᾱ)+p(y) = β̄} ≤ 2` for `ᾱ ∉ {0, ρ}` | `thm_6_2_unit`, `thm_6_2_unit_family` (B1, B2) | B1, B2 for `GR(2^k,m)` |
| Thm 6.2(1): "there are `(q−2)q^{k−1}` such α" | `card_fibre`: every fibre `π^{-1}(t)` has `#ker π` elements | `#{α : π α ∉ {0,1}} = (q−2)·#ker π` and `#ker π = q^{k−1}` (B4); not a separate Lean theorem |
| Thm 6.2(2): every nonzero entry is `2q^{k−1}` for `α ∈ 2^{k−1}R \ {0}` | `thm_6_2_top`, `thm_6_2_top_family`: nonzero entries equal `2·#ker π`; `card_ker_mul`: `#R = #F · #ker π` | B3 for these α; `#ker π = q^{k−1}` (B4) |
| remaining directions (`ᾱ = ρ`, `α ∈ 2R \ 2^{k−1}R`): bounds `≤ 2q^{k−1}` | — | cited from Rønjom–Sandrib (label L) |

## Not claimed
- No Lean term constructs `GR(2^k, m)` or checks B1–B4 for it.
- The Lean statements do not mention `q^{k−1}`; they state `#ker π`. The identification is B4.
- Nothing about the directions over `ρ` or in `2R \ 2^{k−1}R` is formal.
