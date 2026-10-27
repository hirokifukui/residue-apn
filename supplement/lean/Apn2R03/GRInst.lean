import Apn2R03.Ordinary

/-!
# Galois rings satisfy the abstract axioms `GRS` (Claude, 2026-10-25)

For k ≥ 3 and a monic f ∈ (ℤ/2^k)[X] whose reduction f̄ ∈ F_2[X] is irreducible of degree m,
R = (ℤ/2^k)[X]/(f) (= GR(2^k, m)) and K = F_2[X]/(f̄) (= F_{2^m}) with the reduction map π
satisfy every axiom of `GRS`, and |R| = |K|^k.  Hence all theorems proved for an abstract
`S : GRS R K` apply to GR(2^k, m).
-/

set_option linter.unusedSectionVars false

namespace APN2

open Polynomial

/-- reduction ℤ/2^k → F_2 -/
noncomputable def red (k : ℕ) (hk : 1 ≤ k) : ZMod (2 ^ k) →+* ZMod 2 :=
  ZMod.castHom (dvd_pow_self 2 (by omega)) (ZMod 2)

theorem red_surj (k : ℕ) (hk : 1 ≤ k) : Function.Surjective (red k hk) := ZMod.castHom_surjective _

theorem red_eq_zero_iff (k : ℕ) (hk : 1 ≤ k) (c : ZMod (2 ^ k)) :
    red k hk c = 0 ↔ ∃ d, c = 2 * d := by
  constructor
  · intro h
    have h1 : ((c.val : ℕ) : ZMod 2) = 0 := by
      have : red k hk c = ((c.val : ℕ) : ZMod 2) := by
        unfold red; rw [ZMod.castHom_apply, ZMod.cast_eq_val]
      rw [← this, h]
    rw [ZMod.natCast_eq_zero_iff] at h1
    obtain ⟨d, hd⟩ := h1
    refine ⟨(d : ZMod (2 ^ k)), ?_⟩
    rw [← ZMod.natCast_zmod_val c, hd]; push_cast; ring
  · rintro ⟨d, rfl⟩
    rw [map_mul, map_ofNat]
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]

theorem two_mul_zmod (k : ℕ) (hk : 1 ≤ k) (c : ZMod (2 ^ k)) (h : 2 * c = 0) :
    ∃ d, c = 2 ^ (k - 1) * d := by
  have h1 : (((2 * c.val : ℕ)) : ZMod (2 ^ k)) = 0 := by
    push_cast; rw [ZMod.natCast_zmod_val]; exact h
  rw [ZMod.natCast_eq_zero_iff] at h1
  have h2 : 2 * 2 ^ (k - 1) ∣ 2 * c.val := by
    rw [show 2 * 2 ^ (k - 1) = 2 ^ k by rw [← pow_succ']; congr 1; omega]; exact h1
  obtain ⟨d, hd⟩ := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
  refine ⟨(d : ZMod (2 ^ k)), ?_⟩
  rw [← ZMod.natCast_zmod_val c, hd]; push_cast; ring

theorem poly_even (k : ℕ) (hk : 1 ≤ k) (p : (ZMod (2 ^ k))[X]) (h : p.map (red k hk) = 0) :
    ∃ q, p = C 2 * q := by
  have hmem : p ∈ Ideal.map C (Ideal.span {(2 : ZMod (2 ^ k))}) := by
    rw [Ideal.mem_map_C_iff]
    intro n
    have : red k hk (p.coeff n) = 0 := by
      rw [← coeff_map, h, coeff_zero]
    obtain ⟨d, hd⟩ := (red_eq_zero_iff k hk _).mp this
    rw [hd]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hmem
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, by rw [← hq, mul_comm]⟩

theorem poly_tors (k : ℕ) (hk : 1 ≤ k) (p : (ZMod (2 ^ k))[X]) (h : C 2 * p = 0) :
    ∃ q, p = C (2 ^ (k - 1)) * q := by
  have hmem : p ∈ Ideal.map C (Ideal.span {(2 : ZMod (2 ^ k)) ^ (k - 1)}) := by
    rw [Ideal.mem_map_C_iff]
    intro n
    have : 2 * p.coeff n = 0 := by rw [← coeff_C_mul, h, coeff_zero]
    obtain ⟨d, hd⟩ := two_mul_zmod k hk _ this
    rw [hd]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hmem
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, by rw [← hq, mul_comm, map_pow]⟩

section GR

variable (k : ℕ) (hk : 3 ≤ k) (f : (ZMod (2 ^ k))[X])

/-- the reduction f̄ -/
noncomputable abbrev fbar : (ZMod 2)[X] := f.map (red k (by omega))

theorem eval₂_root_bar :
    f.eval₂ ((AdjoinRoot.of (fbar k hk f)).comp (red k (by omega))) (AdjoinRoot.root (fbar k hk f)) = 0 := by
  rw [← Polynomial.eval₂_map]; exact AdjoinRoot.eval₂_root _

/-- the reduction map GR(2^k, m) → F_{2^m} -/
noncomputable def piGR : AdjoinRoot f →+* AdjoinRoot (fbar k hk f) :=
  AdjoinRoot.lift _ _ (eval₂_root_bar k hk f)

theorem piGR_mk (p : (ZMod (2 ^ k))[X]) :
    piGR k hk f (AdjoinRoot.mk f p) = AdjoinRoot.mk (fbar k hk f) (p.map (red k (by omega))) := by
  unfold piGR
  rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
  rfl

theorem two_bar [Fact (Irreducible (fbar k hk f))] : (2 : AdjoinRoot (fbar k hk f)) = 0 := by
  have : (2 : AdjoinRoot (fbar k hk f)) = AdjoinRoot.of _ (2 : ZMod 2) := (map_ofNat _ 2).symm
  rw [this, show (2 : ZMod 2) = 0 from rfl, map_zero]

/-- **GR(2^k, m) satisfies the axioms `GRS`.** -/
noncomputable def grs (hf : f.Monic) [Fact (Irreducible (fbar k hk f))] :
    GRS (AdjoinRoot f) (AdjoinRoot (fbar k hk f)) where
  π := piGR k hk f
  surj := by
    intro x
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    obtain ⟨p', hp'⟩ := Polynomial.map_surjective _ (red_surj k (by omega)) p
    exact ⟨AdjoinRoot.mk f p', by rw [piGR_mk, hp']⟩
  k := k
  hk := hk
  ker2 := by
    intro x
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    constructor
    · intro h
      rw [piGR_mk, AdjoinRoot.mk_eq_zero] at h
      obtain ⟨gb, hgb⟩ := h
      obtain ⟨g, rfl⟩ := Polynomial.map_surjective _ (red_surj k (by omega)) gb
      have h0 : (p - f * g).map (red k (by omega)) = 0 := by
        rw [Polynomial.map_sub, Polynomial.map_mul, hgb, sub_self]
      obtain ⟨q, hq⟩ := poly_even k (by omega) _ h0
      refine ⟨AdjoinRoot.mk f q, ?_⟩
      have : p = f * g + C 2 * q := by rw [← hq]; ring
      rw [this, map_add, map_mul, AdjoinRoot.mk_self, zero_mul, zero_add, map_mul, AdjoinRoot.mk_C,
        map_ofNat]
    · rintro ⟨y, hy⟩
      rw [hy, map_mul, map_ofNat]
      haveI : Fact (Irreducible (fbar k hk f)) := inferInstance
      rw [two_bar, zero_mul]
  nil := by
    have e : (2 : ZMod (2 ^ k)) ^ k = ((2 ^ k : ℕ) : ZMod (2 ^ k)) := by push_cast; rfl
    calc (2 : AdjoinRoot f) ^ k = AdjoinRoot.of f ((2 : ZMod (2 ^ k)) ^ k) := by
          rw [map_pow, map_ofNat]
      _ = 0 := by rw [e, ZMod.natCast_self, map_zero]
  tors := by
    intro x hx
    haveI : Fact (1 < 2 ^ k) := ⟨Nat.one_lt_two_pow (by omega)⟩
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    set p0 := p %ₘ f with hp0
    have hpp : AdjoinRoot.mk f p = AdjoinRoot.mk f p0 := by
      rw [AdjoinRoot.mk_eq_mk]
      exact ⟨p /ₘ f, by have := modByMonic_add_div p f; rw [hp0]; linear_combination -this⟩
    rw [hpp] at hx ⊢
    have h2 : AdjoinRoot.mk f (C 2 * p0) = 0 := by
      rw [map_mul, AdjoinRoot.mk_C, map_ofNat]; exact hx
    rw [AdjoinRoot.mk_eq_zero] at h2
    have hdeg : (C 2 * p0).degree < f.degree :=
      lt_of_le_of_lt (by rw [C_mul']; exact degree_smul_le _ _) (degree_modByMonic_lt p hf)
    have hz : C 2 * p0 = 0 := by
      rw [← (modByMonic_eq_self_iff hf).mpr hdeg]
      exact (modByMonic_eq_zero_iff_dvd hf).mpr h2
    obtain ⟨q, hq⟩ := poly_tors k (by omega) p0 hz
    refine ⟨AdjoinRoot.mk f q, ?_⟩
    rw [hq, map_mul, AdjoinRoot.mk_C, map_pow, map_ofNat]

theorem grs_k (hf : f.Monic) [Fact (Irreducible (fbar k hk f))] : (grs k hk f hf).k = k := rfl

/-- **|GR(2^k, m)| = |F_{2^m}|^k.** -/
theorem grs_card (hf : f.Monic) [Fact (Irreducible (fbar k hk f))]
    [Fintype (AdjoinRoot f)] [Fintype (AdjoinRoot (fbar k hk f))] :
    Fintype.card (AdjoinRoot f) = Fintype.card (AdjoinRoot (fbar k hk f)) ^ k ∧
      Fintype.card (AdjoinRoot (fbar k hk f)) = 2 ^ f.natDegree := by
  have hR := Module.card_fintype (AdjoinRoot.powerBasis' hf).basis
  have hfb : (fbar k hk f).Monic := hf.map _
  have hK := Module.card_fintype (AdjoinRoot.powerBasis' hfb).basis
  rw [Fintype.card_fin, AdjoinRoot.powerBasis'_dim, ZMod.card] at hR hK
  have hdeg : (fbar k hk f).natDegree = f.natDegree := hf.natDegree_map _
  rw [hdeg] at hK
  refine ⟨?_, hK⟩
  rw [hR, hK, ← pow_mul, ← pow_mul, mul_comm]

end GR

end APN2
