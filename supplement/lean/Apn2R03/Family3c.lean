import Apn2R03.Family3b

/-!
# Theorem A for r = 3 (Claude, 2026-10-25)

For the natural lift F = Fnat3 and the one-term correction F♯ = F + 2·J², J = X^(2+2^(m-2)),
over an abstract Galois ring S : GRS R K with |K| = 2^m, m ≥ 5 odd, gcd(3, m) = 1:
* (H) ⇒ Hyp with ρ = 1, μ = 1, Λ ≡ 0;
* A_F(a) = 1 + a + a^{2^{m-3}} + a^{2^{m-2}} + a^{2^{m-1}}, Tr A_F = 1, so A_F has no zero;
* E_F, E_{F♯} explicit; χ_{F♯} ≡ 1 (φ-identity);
* every exceptional entry of F♯ is ≤ 2q, and every lift has an entry ≥ 2q (optimal);
* the spectrum of F♯ on the exceptional direction: only 0 and 2q;
* the natural lift F has an entry ≥ 4q.
-/

set_option linter.unusedSectionVars false

namespace APN2

open Finset Polynomial APN2R03

section field
variable {K : Type*} [Field K] [CharP K 2]

def A3 (m : ℕ) (a : K) : K := 1 + a + a ^ (2 ^ (m - 3)) + a ^ (2 ^ (m - 2)) + a ^ (2 ^ (m - 1))

def E3n (m : ℕ) (a : K) : K :=
  a + a ^ 2 + a ^ (2 ^ (m - 3)) + a * a ^ (2 ^ (m - 3)) + a ^ 2 * a ^ (2 ^ (m - 3))
    + a ^ 2 * a ^ (2 ^ (m - 2)) + a ^ (2 ^ (m - 1)) + a ^ (2 ^ (m - 3)) * a ^ (2 ^ (m - 1))

def E3s (m : ℕ) (a : K) : K := E3n m a + a ^ 4 + a ^ (2 ^ (m - 1)) + 1

theorem A3_trace [Fintype K] (m : ℕ) (hodd : Odd m) (hcard : Fintype.card K = 2 ^ m) (a : K) :
    absTr m (A3 m a) = 1 := by
  unfold A3
  rw [absTr_add, absTr_add, absTr_add, absTr_add, absTr_one m hodd,
    absTr_pow_two_pow m hcard a, absTr_pow_two_pow m hcard a, absTr_pow_two_pow m hcard a]
  linear_combination (2 * absTr m a) * (two_K : (2 : K) = 0)

theorem A3_ne [Fintype K] (m : ℕ) (hodd : Odd m) (hcard : Fintype.card K = 2 ^ m) (a : K) :
    A3 m a ≠ 0 := by
  intro h
  have := A3_trace m hodd hcard a
  rw [h, absTr_zero] at this
  exact zero_ne_one this

theorem chi3 [Fintype K] [DecidableEq K] (m : ℕ) (hm5 : 5 ≤ m) (hodd : Odd m)
    (hcard : Fintype.card K = 2 ^ m) (a : K) : E3s m a ∉ qimg 1 (A3 m a) := by
  intro hmem
  obtain ⟨y, -, hy⟩ := mem_image.mp hmem
  have hA0 := A3_ne m hodd hcard a
  set φ : K := 1 + a ^ 2 + a * a ^ (2 ^ (m - 1)) + a ^ (2 ^ (m - 3)) * a ^ (2 ^ (m - 1))
    + a ^ (2 ^ (m - 2)) * a ^ (2 ^ (m - 1)) with hφ
  have key : φ ^ 2 + A3 m a * φ = E3s m a + A3 m a ^ 2 := by
    have hU : a ^ (2 ^ (m - 2)) = (a ^ (2 ^ (m - 3))) ^ 2 := (YU_sq m (by omega) a).symm
    have hV : a ^ (2 ^ (m - 1)) = (a ^ (2 ^ (m - 3))) ^ 4 := by
      rw [← UV_sq m (by omega) a, hU]; ring
    have ha : (a ^ (2 ^ (m - 3))) ^ 8 = a := frob_back m (by omega) hcard a
    rw [hφ]
    unfold A3 E3s E3n
    rw [hV, hU]
    generalize a ^ (2 ^ (m - 3)) = t at ha ⊢
    subst ha
    have := phi_identity (R := K) two_K t
    dsimp only at this
    linear_combination this
  have hz : ∃ z : K, 1 * z ^ 2 + A3 m a * z = A3 m a ^ 2 :=
    ⟨φ + y, by linear_combination key + hy + (φ * y + E3s m a) * (two_K : (2 : K) = 0)⟩
  have := (chi_criterion m (by omega) hcard 1 (A3 m a) (A3 m a ^ 2) one_ne_zero hA0).mp hz
  rw [one_mul, div_self (pow_ne_zero 2 hA0), absTr_one m hodd] at this
  exact one_ne_zero this

end field

namespace GRS

variable {R K : Type*} [CommRing R] [Field K] (S : GRS R K)
variable [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

theorem fam3_Lam (m : ℕ) (hm5 : 5 ≤ m) (a : K) : S.Lam (Fnat3 R m) 1 a = 0 := by
  haveI := S.charP2
  unfold Lam; rw [Fnat3_map]; exact p3_Lam m (by omega) a

theorem fam3_hyp (m : ℕ) (hm5 : 5 ≤ m) (hcard : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m) :
    S.Hyp (Fnat3 R m) 1 1 ∧
      (∀ a b : K, ((Fnat3 R m).map S.π).derivative.eval a = ((Fnat3 R m).map S.π).derivative.eval b →
        b = a ∨ b = a + 1) := by
  haveI := S.charP2
  have h := S.hyp_of_H (Fnat3 R m) 1 (by rw [Fnat3_map]; exact p3_quad m hm5) one_ne_zero
    (by rw [Fnat3_map]; exact p3_ker m hm5 hcard h3)
    (by rw [Fnat3_map]; exact p3_apn m hm5 hcard h3)
  have hμ : (hasseDeriv 2 ((Fnat3 R m).map S.π)).eval 1 - (hasseDeriv 2 ((Fnat3 R m).map S.π)).eval 0
      = 1 := by
    rw [Fnat3_map, p3_hasse2 m hm5, p3_hasse2 m hm5, one_pow, one_pow, zero_pow (by positivity),
      zero_pow (by positivity)]
    linear_combination (1 : K) * (two_K : (2 : K) = 0)
  rw [hμ] at h
  exact h

theorem fam3_A (m : ℕ) (hm5 : 5 ≤ m) (hcard : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m)
    (a : K) : S.Afun (Fnat3 R m) 1 a = A3 m a := by
  haveI := S.charP2
  obtain ⟨g, hg, hπ⟩ := S.A_spec (Fnat3 R m) 1 (S.fam3_hyp m hm5 hcard h3).1.hper (S.L a) 1 a
    (S.pi_L a) (map_one _)
  obtain ⟨w, hw⟩ := fnat3_A_R m hm5 (S.L a)
  rw [hw] at hg
  have h2 : S.π g = S.π ((1 + S.L a + S.L a ^ (2 ^ (m - 3)) + S.L a ^ (2 ^ (m - 2))
      + S.L a ^ (2 ^ (m - 1))) + 2 * w) := S.pi_eq_of_two_mul_eq (by linear_combination -hg)
  rw [← hπ, h2, map_add, S.pi_two_mul, add_zero]
  simp only [map_add, map_pow, map_one, S.pi_L, A3]

theorem fam3_E (m : ℕ) (hm5 : 5 ≤ m) (hcard : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m)
    (a : K) : S.Efun (Fnat3 R m) 1 a = E3n m a := by
  haveI := S.charP2
  obtain ⟨c, hc, hπ⟩ := S.E_spec (Fnat3 R m) 1 (S.fam3_hyp m hm5 hcard h3).1.hper (S.L a) 1 a
    (S.pi_L a) (map_one _) (S.fam3_Lam m hm5 a)
  set x := S.L a with hx
  obtain ⟨Q, hQ⟩ := taylor3 (Fnat3 R m) x 2
  obtain ⟨w, hw⟩ := fnat3_E_R m hm5 x
  set N := 1 + x ^ 2 + x ^ (2 ^ (m - 2)) + x ^ (2 ^ (m - 3)) + x * x ^ (2 ^ (m - 3))
        + x ^ 2 * x ^ (2 ^ (m - 3)) + x ^ 2 * x ^ (2 ^ (m - 2))
        + x ^ (2 ^ (m - 3)) * x ^ (2 ^ (m - 1)) with hN
  have h4 : 4 * c = 4 * ((hasseDeriv 2 (Fnat3 R m)).eval x - N - 2 * w + 2 * Q) := by
    rw [← hc]; unfold Sx; rw [mul_one, hQ]; linear_combination (-2) * hw
  have h5 := S.pi_eq_of_four_mul_eq h4
  rw [← hπ, h5, map_add, map_sub, map_sub, S.pi_two_mul, S.pi_two_mul, S.pi_hasse2_eval, Fnat3_map,
    hx, S.pi_L, p3_hasse2 m hm5, hN]
  have hxa : S.π x = a := by rw [hx]; exact S.pi_L a
  simp only [map_add, map_mul, map_pow, map_one, hxa]
  unfold E3n
  linear_combination (-(a ^ 2 + a ^ (2 ^ (m - 3)) + a * a ^ (2 ^ (m - 3)) + a ^ 2 * a ^ (2 ^ (m - 3))
    + a ^ 2 * a ^ (2 ^ (m - 2)) + a ^ (2 ^ (m - 3)) * a ^ (2 ^ (m - 1)))) * (two_K : (2 : K) = 0)

theorem fam3_sh_hyp (m : ℕ) (hm5 : 5 ≤ m) (hcard : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m) :
    S.Hyp (Fsh3 R m) 1 1 := S.hyp_add_two _ _ 1 1 (S.fam3_hyp m hm5 hcard h3).1

theorem fam3_sh_A (m : ℕ) (hm5 : 5 ≤ m) (hcard : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m)
    (a : K) : S.Afun (Fsh3 R m) 1 a = A3 m a := by
  unfold Fsh3
  rw [S.A_add_sq _ _ 1 (S.fam3_hyp m hm5 hcard h3).1.hper, S.fam3_A m hm5 hcard h3]

theorem fam3_sh_Lam (m : ℕ) (hm5 : 5 ≤ m) (a : K) : S.Lam (Fsh3 R m) 1 a = 0 := by
  have := S.fam3_Lam (R := R) m hm5 a
  unfold Lam at this ⊢; unfold Fsh3; rw [S.map_add_two]; exact this

theorem fam3_sh_E (m : ℕ) (hm5 : 5 ≤ m) (hcard : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m)
    (a : K) : S.Efun (Fsh3 R m) 1 a = E3s m a := by
  haveI := S.charP2
  unfold Fsh3
  rw [S.E_control _ _ 1 a (S.fam3_Lam m hm5 a), S.fam3_E m hm5 hcard h3]
  have hJ : ((J3 R m).map S.π).eval (a + 1) - ((J3 R m).map S.π).eval a
      = a ^ 2 + a ^ (2 ^ (m - 2)) + 1 := by
    simp only [J3, Polynomial.map_pow, map_X, eval_pow, eval_X]
    rw [pow_add, pow_add, frob_add (m - 2) a 1, one_pow]
    linear_combination (a * a ^ (2 ^ (m - 2)) + a) * (two_K : (2 : K) = 0)
  rw [hJ]
  unfold E3s
  linear_combination (UV_sq m (by omega) a) +
    (a ^ 2 * a ^ (2 ^ (m - 2)) + a ^ 2 + a ^ (2 ^ (m - 2))) * (two_K : (2 : K) = 0)

/-- **Theorem A (r = 3), upper bound**: every exceptional entry of F♯ is at most 2q, all k ≥ 3. -/
theorem fam3_upper (hcard : Fintype.card R = Fintype.card K ^ S.k) (m : ℕ) (hm5 : 5 ≤ m)
    (hodd : Odd m) (hm : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m) (α β : R)
    (hα : S.π α = 1) : delta (Fsh3 R m) α β ≤ 2 * Fintype.card K := by
  haveI := S.charP2
  exact S.upper_mu_chi1 hcard m hm (Fsh3 R m) 1 1 (S.fam3_sh_hyp m hm5 hm h3) one_ne_zero
    (fun a => by rw [S.fam3_sh_A m hm5 hm h3]; exact A3_ne m hodd hm a)
    (fun a _ => by rw [S.fam3_sh_E m hm5 hm h3, S.fam3_sh_A m hm5 hm h3]; exact chi3 m hm5 hodd hm a)
    α β hα

/-- **Theorem A (r = 3), optimality**: every coefficient lift of the same residue polynomial has an
exceptional entry ≥ 2q. -/
theorem fam3_lower_all (hcard : Fintype.card R = Fintype.card K ^ S.k) (m : ℕ) (hm5 : 5 ≤ m)
    (hm : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m) (g : R[X])
    (hg : g.map S.π = Fnat3 K m) (α : R) (hα : S.π α = 1) :
    ∃ β, 2 * Fintype.card K ≤ delta g α β := by
  have hgm : g.map S.π = (Fnat3 R m).map S.π := by rw [hg, Fnat3_map]
  have H := S.hyp_of_map_eq (Fnat3 R m) g hgm 1 1 (S.fam3_hyp m hm5 hm h3).1
  have hL : S.Lam g 1 0 = 0 := by
    have := S.fam3_Lam (R := R) m hm5 0
    unfold Lam at this ⊢; rw [hgm]; exact this
  exact S.lower_2q hcard g 1 1 H α hα 0 hL

/-- the corrected lift is a lift of the same residue polynomial -/
theorem fam3_sh_map (m : ℕ) : (Fsh3 R m).map S.π = Fnat3 K m := by
  unfold Fsh3; rw [S.map_add_two, Fnat3_map]

/-- **Theorem A (r = 3), spectrum**: on the exceptional direction F♯ takes only the values 0 and 2q,
and 2q is taken q^{k-1}/2 · q / q = q · b times with 2qb = q^{k-1}. -/
theorem fam3_spectrum (hcard : Fintype.card R = Fintype.card K ^ S.k) (m : ℕ) (hm5 : 5 ≤ m)
    (hodd : Odd m) (hm : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m) (α : R)
    (hα : S.π α = 1) :
    ∃ b : ℕ, 2 * Fintype.card K * b = Fintype.card K ^ (S.k - 1) ∧
      (univ.filter (fun β : R => delta (Fsh3 R m) α β = 2 * Fintype.card K)).card =
        Fintype.card K * b ∧
      (univ.filter (fun β : R => delta (Fsh3 R m) α β = 4 * Fintype.card K)).card = 0 ∧
      ∀ β, delta (Fsh3 R m) α β = 0 ∨ delta (Fsh3 R m) α β = 2 * Fintype.card K := by
  haveI := S.charP2
  have hA : ∀ a, S.Afun (Fsh3 R m) 1 a ≠ 0 := fun a => by
    rw [S.fam3_sh_A m hm5 hm h3]; exact A3_ne m hodd hm a
  obtain ⟨b, hb, h4, h2, hall⟩ := S.spectrum_mu hcard m hm (Fsh3 R m) 1 1 (S.fam3_sh_hyp m hm5 hm h3)
    one_ne_zero hA α hα
  have hν : (univ.filter (fun a : K => S.Lam (Fsh3 R m) 1 a = 0 ∧
      S.Efun (Fsh3 R m) 1 a ∈ qimg 1 (S.Afun (Fsh3 R m) 1 a))).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro a - ⟨-, hE⟩
    rw [S.fam3_sh_E m hm5 hm h3, S.fam3_sh_A m hm5 hm h3] at hE
    exact chi3 m hm5 hodd hm a hE
  rw [hν] at h4 h2
  refine ⟨b, hb, by rw [h2, Nat.sub_zero], by omega, fun β => ?_⟩
  have hq : 0 < Fintype.card K := Fintype.card_pos
  have hup := S.fam3_upper hcard m hm5 hodd hm h3 α β hα
  rcases hall β with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · omega

/-- **I8**: the natural lift has an exceptional entry ≥ 4q (so it is not optimal). -/
theorem fam3_natural (hcard : Fintype.card R = Fintype.card K ^ S.k) (m : ℕ) (hm5 : 5 ≤ m)
    (hodd : Odd m) (hm : Fintype.card K = 2 ^ m) (h3 : Nat.Coprime 3 m) (α : R)
    (hα : S.π α = 1) : ∃ β, 4 * Fintype.card K ≤ delta (Fnat3 R m) α β := by
  haveI := S.charP2
  have hA0 : S.Afun (Fnat3 R m) 1 0 ≠ 0 := by
    rw [S.fam3_A m hm5 hm h3]; exact A3_ne m hodd hm 0
  refine S.lower_4q hcard (Fnat3 R m) 1 1 (S.fam3_hyp m hm5 hm h3).1 one_ne_zero α hα 0 hA0
    (S.fam3_Lam m hm5 0) ?_
  rw [S.fam3_E m hm5 hm h3]
  refine mem_image.mpr ⟨0, mem_univ _, ?_⟩
  unfold E3n
  simp [zero_pow (show 2 ^ (m - 3) ≠ 0 by positivity), zero_pow (show 2 ^ (m - 2) ≠ 0 by positivity),
    zero_pow (show 2 ^ (m - 1) ≠ 0 by positivity)]

end GRS

end APN2
