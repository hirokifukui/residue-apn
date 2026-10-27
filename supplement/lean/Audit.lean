import Apn2R03

open APN2 APN2.GRS

-- non-vacuity of the abstract Galois-ring axioms
#check (APN2.zmod8 : APN2.GRS (ZMod 8) (ZMod 2))
#print axioms APN2.zmod8

-- foundations
#print axioms APN2.GRS.card_T
#print axioms APN2.GRS.class_count
#print axioms APN2.GRS.A_spec
#print axioms APN2.GRS.E_spec
#print axioms APN2.GRS.E_transl
#print axioms APN2.GRS.A_control
#print axioms APN2.GRS.E_control
#print axioms APN2.GRS.A_prescribe
#print axioms APN2.GRS.E_prescribe
#print axioms APN2R03.chi_criterion
#print axioms APN2R03.absTr_eq_zero_iff
#print axioms APN2R03.local_pair_count
-- minimax and minimizers
#print axioms APN2.GRS.minimax_k4_lower
#print axioms APN2.GRS.minimax_k4_attain
#print axioms APN2.GRS.minimizers_k4
#print axioms APN2.GRS.minimax_k3_lower
#print axioms APN2.GRS.minimax_k3_attain
#print axioms APN2.GRS.minimizers_k3
-- spectra and layers
#print axioms APN2.GRS.spectrum_mu
#print axioms APN2.GRS.spectrum_mu0
#print axioms APN2.GRS.spectrum_k3
#print axioms APN2.GRS.penultimate
#print axioms APN2.GRS.middle_k3
#print axioms APN2.GRS.O3_iff
#print axioms APN2.GRS.tradeoff
-- (H) ⇒ Hyp
#print axioms APN2.GRS.hyp_of_H
-- explicit families (Theorem A)
#print axioms APN2.F5_eq_paper
#print axioms APN2.GRS.fam3_upper
#print axioms APN2.GRS.fam3_lower_all
#print axioms APN2.GRS.fam3_spectrum
#print axioms APN2.GRS.fam3_natural
#print axioms APN2.GRS.fam5_upper
#print axioms APN2.GRS.fam5_lower_all
#print axioms APN2.GRS.fam5_spectrum
#print axioms APN2.GRS.fam5_natural
#print axioms APN2.GRS.fam3_units
#print axioms APN2.GRS.fam5_units
-- ordinary directions and valuation preservation
#print axioms APN2.GRS.ordinary_eq
#print axioms APN2.GRS.unit_diff
#print axioms APN2.GRS.nonunit_diff
-- concrete Galois rings
#print axioms APN2.grs
#print axioms APN2.grs_card
#print axioms APN2.exists_GR_poly
#print axioms APN2.finite_GR
#print axioms APN2.thmA3_GR
#print axioms APN2.thmA5_GR
-- R04: residue APN property proved, hypothesis removed
#print axioms APN2.resAPN3
#print axioms APN2.resAPN5
#print axioms APN2.GRS.fam3_units'
#print axioms APN2.GRS.fam5_units'
#print axioms APN2.thmA3_GR_units
#print axioms APN2.thmA5_GR_units
-- R04: cross-level optimality (abstract and on GR(2^k,m) -> GR(8,m))
#print axioms APN2.GRS.A_compat
#print axioms APN2.GRS.E_compat
#print axioms APN2.GRS.cross_level_stay
#print axioms APN2.GRS.cross_level_exists
#print axioms APN2.cross_level_stay_GR
#print axioms APN2.cross_level_exists_GR
-- R04 follow-up: literal mod-8 stability (paper Thm S3), Markov product formula (Prop. markov), degree of Theorem A
#print axioms APN2.GRS.cc_stable
#print axioms APN2.GRS.delta_stable_mod8
#print axioms APN2.delta_stable_mod8_GR
#print axioms APN2.Markov.round_diff
#print axioms APN2.Markov.trail_card
#print axioms APN2.Markov.trail_prob
#print axioms APN2.Markov.trail_card_le
#print axioms APN2.Markov.dd_pi
#print axioms APN2.natDegree_Fnat3
#print axioms APN2.natDegree_Fsh3
#print axioms APN2.natDegree_F5
#print axioms APN2.natDegree_Fsh5
#print axioms APN2.Markov.sum_active_ge
#print axioms APN2.Markov.prod_le_pow_of_active
-- R04b: assembled Corollary crypto, residue permutation property of P_{m,r}
#print axioms APN2.Markov.dd_eq_delta
#print axioms APN2.Markov.char_prob_le
#print axioms APN2.Markov.char_prob_le_fam3
#print axioms APN2.Markov.char_prob_le_fam5
#print axioms APN2.cube_inj
#print axioms APN2.resPerm3
#print axioms APN2.resPerm5
#print axioms APN2.Markov.char_prob_le_fam3'
#print axioms APN2.Markov.char_prob_le_fam5'
-- R05: natural-lift benchmarks (exact), coherent family over all levels, residue partition
#print axioms APN2.A5n_zero
#print axioms APN2.GRS.cc_A0_mu0_k3
#print axioms APN2.GRS.fam3_natural_exact
#print axioms APN2.GRS.fam5_natural_q2
#print axioms APN2.GRS.fam5_nat_E0
#print axioms APN2.GRS.fam5_nat_k3
#print axioms APN2.GRS.coherent_family
#print axioms APN2.CongPart.poly_cong
#print axioms APN2.CongPart.round_cong
#print axioms APN2.CongPart.iter_cong
-- R05b: Corollary 7.5 multiplicities; concrete tower Z[X]/(g) -> GR(2^k,m)
#print axioms APN2.GRS.fam5_nat_E01
#print axioms APN2.GRS.fam5_nat_A_iff
#print axioms APN2.GRS.fam5_nat_k3_spectrum
#print axioms APN2.towerGR
#print axioms APN2.towerGR_card
#print axioms APN2.coherent_family_GR
-- R05b: field-level core of Theorem repfamily (mu = 0, Z empty representatives for every odd m)
#print axioms APN2.Ad_inj
#print axioms APN2.Ad_rho
#print axioms APN2.cubeAd_inj
#print axioms APN2.Kd_zero_iff
#print axioms APN2.eps_not_im
#print axioms APN2.Lam_ne_zero
-- R05c: Theorem inter (i)-(iii) with multiplicities, Corollary interfamily (both lifts)
#print axioms APN2.GRS.shift_inv
#print axioms APN2.GRS.inter_dvd
#print axioms APN2.GRS.class_count_gen
#print axioms APN2.GRS.inter_upper
#print axioms APN2.GRS.inter_lower_c3
#print axioms APN2.GRS.inter_lower_deep
#print axioms APN2.GRS.inter_lower_pair
#print axioms APN2.GRS.inter_flat_iff
#print axioms APN2.GRS.inter_row
#print axioms APN2.GRS.inter_count
#print axioms APN2.GRS.inter_mult
#print axioms APN2.GRS.inter_layer_iff
#print axioms APN2.p5_hasse3
#print axioms APN2.GRS.fam5_interfamily
#print axioms APN2.GRS.fam5_nat_inter
-- R05c: characteristics in every layer, two-round differentials, fixed keys
#print axioms APN2.Markov.char_prob_le_digit
#print axioms APN2.GRS.top_layer_le
#print axioms APN2.Markov.char_prob_le_layer
#print axioms APN2.Markov.char_prob_le_fam5_layer
#print axioms APN2.Markov.char_prob_le_top
#print axioms APN2.Markov.hull2_le
#print axioms APN2.Markov.card_out2
#print axioms APN2.Markov.diff2_prob_le
#print axioms APN2.Markov.fixed_key_le
#print axioms APN2.Markov.branch_lift
#print axioms APN2.GRS.fam5_dp_le
#print axioms APN2.GRS.fam5_bij
#print axioms APN2.Markov.fam5_diff2
#print axioms APN2.Markov.fam5_fixed_key
#print axioms APN2.Markov.hull_core
#print axioms APN2.Markov.hull2_unit
#print axioms APN2.Markov.diff2_unit_le
#print axioms APN2.Markov.fam5_diff2_unit
#print axioms APN2.Markov.fam5_fixed_key_unit
-- R05c: coefficient-changed optimal lift of P_{m,r} (no new monomial), sparse family Z = empty
#print axioms APN2.GRS.fam5'_A
#print axioms APN2.GRS.fam5'_A_eq_sharp
#print axioms APN2.GRS.fam5'_upper
#print axioms APN2.sq_add_add_one_ne
#print axioms APN2.sparse_Lam_ne
-- R06: layerwise two-round differentials without the factor 2^n (GPT R05c §4)
#print axioms APN2.Markov.hull2_digit
#print axioms APN2.Markov.diff2_digit
#print axioms APN2.Markov.diff2_layer
#print axioms APN2.Markov.fixed_key_layer
#print axioms APN2.Markov.fam5_diff2_unit_sharp
#print axioms APN2.Markov.fam5_diff2_mid
#print axioms APN2.Markov.diff2_top
