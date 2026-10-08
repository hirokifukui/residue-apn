# MEANING_MAP — Lean definitions read against paper_R5 (R5.2), 2026-10-07

Printed definitions: the stage-1 audit log `audit_stage1.log` of `audit/AuditStage1.lean` (in the release: `lean/records/development/`). What the type audit does not catch (a change of a definition propagates to both sides) is checked here by reading.

| Lean (printed) | paper | agreement |
|---|---|---|
| `polV R r = ∑ i ∈ range (r-2), X^(2^i)` | `V = ∑_{i=0}^{r-3} X^{2^i}` (§3) | same |
| `polW R r = X^(2^(r-2))`, `polY R m = X^(2^(m-2))`, `polZ R m = X^(2^(m-1))` | W, Y, Z | same |
| `polD = 1 + W + Y`, `polE = 1 + V + Y + Z` | D, E | same |
| `polP = V + W + WV + WY + WZ + YV + YZ` | Theorem 3.1(1), the displayed form | same; the definition `red((T_r^3)^{2^{m-2}})` is the conjunct `map … = rep (x ↦ (T_r(x)^3)^(2^(m-2)))` of `theorem_3_1` |
| `polT R r = ∑ i ∈ range r, X^(2^i)` | `T_r = ∑_{i<r} X^{2^i}` | same |
| polynomials over `ZMod 2` | "coefficients in F_2" | `(polP (ZMod 2) m r).map castHom` is the image in `F[X]`; `map_polP` shows it equals `polP F m r` |
| `suppP m r = expOf '' supportIdx m r`, `expOf s = ∑_{i∈s} 2^i` | the support listed in the proof of 3.1(1) | same index sets: `{i}` (i ≤ r−2), `{i, r−2}`, `{i, m−2}` (i ≤ r−3), `{r−2, m−2}`, `{r−2, m−1}`, `{m−2, m−1}` |
| `rep f = Lagrange.interpolate univ id f` | `red`: the reduced representative (degree < q) | same (apnlift definition, unchanged) |
| `IsAPN Q := ∀ a ≠ 0, ∀ b, #{x : Q(x+a) + Q x = b} ≤ 2` | APN (§2) | same (apnlift) |
| `IsDerivOptimal p := (∀ x, p'(x) ≠ 0) ∧ ∀ x, #{y : p'(y) = p'(x)} = 2` | Definition 2.1 | same: "every nonempty fibre has two elements" = "the fibre through each point has two elements" |
| `IsOptimalAPNPerm f := IsAPN f ∧ Bijective f ∧ IsDerivOptimal (rep f)` | optimal APN permutation, Definition 2.1 | same |
| `absTr m y = ∑_{i<m} y^(2^i)` | `Tr` (absolute trace) | standard formula of the absolute trace (Mathlib `FiniteField.algebraMap_trace_eq_sum_pow`); the link to `Algebra.trace` is not formalized |
| `polG R s = X^(2^s) + X + 1` | g (§4) with s = m − r | same |
| `rootMultiplicity α (P + 1)`, `rootMultiplicity α P'` | e_α (multiplicity of α as a root of P − P(α)) and d_α = ord_α P' (§4 definitions) | the paper defines e_α, d_α exactly as these multiplicities; their meaning as ramification data of ℙ¹ → ℙ¹ is paper-level |
| `IsCoprime g E` in `(ZMod 2)[X]` | gcd(g, E) = 1 in F_2[X] | same (F_2[X] is a PID) |
| `card (rootSet g (AlgebraicClosure (ZMod 2))) = 2^s` | "its 2^s roots" | same |
| `IsQuadSupp m p` (`p : (ZMod 2)[X]`): every exponent of `p` is `0`, `2^i` (`i < m`) or `2^i + 2^j` (`i < j < m`) | "quadratic with coefficients in `F_2`" (DO + linearised + constant), Lemma 2.2 | same; "reduced" is not assumed (not needed) |
| `kappaOf m p = ∑_{1 ≤ j < m} [X^(1+2^j)]p · t^j` | `κ = ∑_{j≥1}([X^{1+2^j}]p) t^j`, Lemma 2.2 | same (`j < m` covers every exponent of a reduced quadratic) |
| `linMap κ x = ∑_i κ_i x^(2^i)` (`c2 = ZMod.castHom`) | `κ(σ)` | same |
| `derivative_quadratic`: `p' = C([X]p) + ∑_{1≤j<m} C([X^{1+2^j}]p) X^(2^j)` | display (1) with `ε = [X]p`, `K = κ(σ)` | same, for `F_2` coefficients |
| `EuclideanDomain.gcd κ (X^m - 1) = X + 1` | `gcd(κ, t^m-1) = t+1` | same: the only unit of `F_2[t]` is `1`, so the Euclidean gcd is the monic gcd |
| hypotheses `hsurj`, `hunit`, `hann`, `hα0` of `prop_6_1`, `thm_6_2_*` | `π : GR(2^k,m) → F_q`, `k ≥ 2`; `α ∈ 2^{k−1}R \ {0}` in 6.2(2) | structural facts B1–B3 of `GR_BRIDGE.md`, checked in the paper, not in Lean; `#ker π = q^{k−1}` (B4) turns `2·#ker π` into `2q^{k−1}` and `(q−2)·#ker π` into the direction count of 6.2(1) |
| `propW` hypothesis `∀ y, absTr m (p(y+1) + p y) = 1` | normalisation before Prop. 7.1 (`{p(y+1)+p(y)} = {Tr = 1}`) | the hypothesis is the inclusion ⊆, which is all the proof uses; the normalisation argument is paper only |
| `propW` conclusion `¬(β₁ = aγ₁ + bγ₂ ∧ β₂ = bγ₁ + (a+b)γ₂)` | `𝐌β ∉ {0,1}² \ {0}` with `𝐌 = 𝐁⁻¹` (bold in the paper since R12a) | equivalent since B is invertible (`det_B_ne_zero`) |
