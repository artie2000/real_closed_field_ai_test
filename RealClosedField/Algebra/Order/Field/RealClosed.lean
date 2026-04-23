/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib
import RealClosedField.Algebra.Order.Algebra
import RealClosedField.Algebra.Order.Ring.Ordering.Extensions

/-!
# Equivalent conditions for a real closed field (ordered case)

For an ordered field `R`, the following are equivalent:
1. `R` is real closed.
2. `R` is maximal with respect to ordered algebraic extensions.
3. Polynomials over `R` satisfy the intermediate value property.

This file also develops a number of basic algebraic properties of real closed
fields needed to justify the equivalence: the classification of finite and
algebraic extensions (only `R` and `R(i)`), the classification of monic
irreducible polynomials, and some consequences.
-/

namespace IsRealClosed

variable (R : Type*) [Field R]

section Algebraic

variable [IsRealClosed R]

/-- Every sum of squares in a real closed field is a square. -/
theorem isSquare_of_isSumSq {x : R} (hx : IsSumSq x) : IsSquare x := by
  rcases isSquare_or_isSquare_neg x with h | h
  · exact h
  · by_cases hx0 : x = 0
    · subst hx0
      exact IsSquare.zero
    · exfalso
      apply IsSemireal.not_isSumSq_neg_one R
      have hneg1 : (-1 : R) = (-x) * x⁻¹ := by
        rw [neg_mul, mul_inv_cancel₀ hx0]
      rw [hneg1]
      have hinv : IsSumSq (x⁻¹) := by
        have hxinv2 : IsSumSq (x⁻¹ * x⁻¹) := IsSumSq.mul_self _
        have heq : x⁻¹ = (x⁻¹ * x⁻¹) * x := by
          rw [mul_assoc, inv_mul_cancel₀ hx0, mul_one]
        rw [heq]
        exact IsSumSq.mul hxinv2 hx
      exact IsSumSq.mul h.isSumSq hinv

/-- There is no nontrivial odd-degree finite extension of a real closed field `R`:
any finite extension `K/R` with `Module.finrank R K` odd has `R → K` surjective. -/
theorem surjective_algebraMap_of_odd_finrank
    (K : Type*) [Field K] [Algebra R K] [FiniteDimensional R K]
    (hodd : Odd (Module.finrank R K)) :
    Function.Surjective (algebraMap R K) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element R K
  have hint : IsIntegral R α := .of_finite R α
  have hirr : Irreducible (minpoly R α) := minpoly.irreducible hint
  have hdeg : (minpoly R α).natDegree = Module.finrank R K :=
    (Field.primitive_element_iff_minpoly_natDegree_eq R α).mp hα
  rw [← hdeg] at hodd
  obtain ⟨r, hr⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree hodd
  have hdeg1 : (minpoly R α).natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (Polynomial.degree_eq_one_of_irreducible_of_root hirr hr)
  have hfin1 : Module.finrank R K = 1 := by omega
  intro x
  have hbot : (⊥ : Subalgebra R K) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one hfin1
  have hx : x ∈ (⊥ : Subalgebra R K) := by rw [hbot]; exact Algebra.mem_top
  exact Algebra.mem_bot.mp hx

/-- Auxiliary: any quadratic extension of a real closed field admits a power basis whose
generator is a root of `X ^ 2 + 1`. -/
private theorem exists_powerBasis_of_finrank_eq_two_aux
    (L : Type*) [Field L] [Algebra R L] (hL : Module.finrank R L = 2) :
    ∃ pb : PowerBasis R L, minpoly R pb.gen = Polynomial.X ^ 2 + Polynomial.C (1 : R) := by
  have hFin : FiniteDimensional R L := .of_finrank_eq_succ hL
  have hInj : Function.Injective (algebraMap R L) := (algebraMap R L).injective
  have hne : ∃ x : L, x ∉ (algebraMap R L).range := by
    by_contra h
    push_neg at h
    have hTop : (⊥ : Subalgebra R L) = ⊤ := by
      rw [eq_top_iff]
      rintro x -
      obtain ⟨r, hr⟩ := h x
      exact Algebra.mem_bot.mpr ⟨r, hr⟩
    have heq : Module.finrank R (⊥ : Subalgebra R L) = Module.finrank R L := by
      rw [hTop]; exact Subalgebra.topEquiv.toLinearEquiv.finrank_eq
    rw [Subalgebra.finrank_bot] at heq
    omega
  obtain ⟨x, hx⟩ := hne
  have hxI : IsIntegral R x := .of_finite R x
  have hdeg2 : (minpoly R x).natDegree = 2 := by
    have h2 : 2 ≤ (minpoly R x).natDegree := (minpoly.two_le_natDegree_iff hxI).mpr hx
    have hle : (minpoly R x).natDegree ≤ Module.finrank R L := minpoly.natDegree_le x
    omega
  set a : R := (minpoly R x).coeff 1 with ha_def
  set b : R := (minpoly R x).coeff 0 with hb_def
  have hfm : (minpoly R x).Monic := minpoly.monic hxI
  have hcoeff2 : (minpoly R x).coeff 2 = 1 := by
    have hlc : (minpoly R x).leadingCoeff = 1 := hfm
    rw [Polynomial.leadingCoeff, hdeg2] at hlc
    exact hlc
  have hroot : x ^ 2 + (algebraMap R L) a * x + (algebraMap R L) b = 0 := by
    have hlt : (minpoly R x).natDegree < 3 := by omega
    have haev := minpoly.aeval R x
    rw [Polynomial.aeval_eq_sum_range' hlt] at haev
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Algebra.smul_def, pow_zero, mul_one, pow_one] at haev
    rw [hcoeff2, map_one, one_mul] at haev
    show x ^ 2 + (algebraMap R L) ((minpoly R x).coeff 1) * x +
      (algebraMap R L) ((minpoly R x).coeff 0) = 0
    linear_combination haev
  set c : R := a ^ 2 / 4 - b with hc_def
  set y : L := x + (algebraMap R L) (a / 2) with hy_def
  have h2R : (2 : R) ≠ 0 := two_ne_zero
  have hy_sq : y ^ 2 = (algebraMap R L) c := by
    have half_sq : (algebraMap R L) (a / 2) ^ 2 = (algebraMap R L) (a ^ 2 / 4) := by
      rw [← map_pow]
      congr 1
      field_simp
      ring
    have half_times : 2 * (algebraMap R L) (a / 2) = (algebraMap R L) a := by
      have : (2 : L) = (algebraMap R L) 2 := (map_ofNat (algebraMap R L) 2).symm
      rw [this, ← map_mul]
      congr 1
      field_simp
    have expand : y ^ 2 = x ^ 2 + (algebraMap R L) a * x + (algebraMap R L) (a ^ 2 / 4) := by
      show (x + (algebraMap R L) (a / 2)) ^ 2 = _
      have : (x + (algebraMap R L) (a / 2)) ^ 2 =
          x ^ 2 + x * (2 * (algebraMap R L) (a / 2)) + (algebraMap R L) (a / 2) ^ 2 := by ring
      rw [this, half_sq, half_times]
      ring
    rw [expand]
    show x ^ 2 + (algebraMap R L) a * x + (algebraMap R L) (a ^ 2 / 4) =
      (algebraMap R L) (a ^ 2 / 4 - b)
    rw [map_sub]
    linear_combination hroot
  have hy_ni : y ∉ (algebraMap R L).range := by
    rintro ⟨r, hr⟩
    apply hx
    refine ⟨r - a / 2, ?_⟩
    have hr' : (algebraMap R L) r = x + (algebraMap R L) (a / 2) := hr
    rw [map_sub]
    linear_combination hr'
  have hc_ni : ¬ IsSquare c := by
    rintro ⟨s, hs⟩
    have halg_sq : y ^ 2 = ((algebraMap R L) s) ^ 2 := by
      rw [hy_sq, show c = s * s from hs, map_mul]
      ring
    have hfact : (y - (algebraMap R L) s) * (y + (algebraMap R L) s) = 0 := by
      linear_combination halg_sq
    apply hy_ni
    rcases mul_eq_zero.mp hfact with hd | hd
    · exact ⟨s, by linear_combination -hd⟩
    · refine ⟨-s, ?_⟩
      rw [map_neg]
      linear_combination -hd
  have hnc_sq : IsSquare (-c) := (IsRealClosed.isSquare_or_isSquare_neg c).resolve_left hc_ni
  obtain ⟨s, hs⟩ := hnc_sq
  have hs_ne : s ≠ 0 := by
    rintro rfl
    apply hc_ni
    have hmc : -c = 0 := by rw [hs]; ring
    have hc0 : c = 0 := by linear_combination -hmc
    rw [hc0]
    exact ⟨0, by ring⟩
  have hsL_ne : (algebraMap R L) s ≠ 0 :=
    (map_ne_zero_iff _ hInj).mpr hs_ne
  set sL : L := (algebraMap R L) s with hsL_def
  have hsL_sq : sL ^ 2 = - (algebraMap R L) c := by
    show ((algebraMap R L) s) ^ 2 = - (algebraMap R L) c
    rw [← map_pow, ← map_neg]
    congr 1
    rw [pow_two, ← hs]
  set α : L := y * sL⁻¹ with hα_def
  have hcL_ne : (algebraMap R L) c ≠ 0 := by
    intro hc0
    have : c = 0 := (map_eq_zero_iff _ hInj).mp hc0
    apply hc_ni
    rw [this]; exact ⟨0, by ring⟩
  have hsL_sq_ne : sL ^ 2 ≠ 0 := by
    rw [hsL_sq]; exact neg_ne_zero.mpr hcL_ne
  have hα_sq : α ^ 2 = -1 := by
    have step1 : α ^ 2 * sL ^ 2 = (algebraMap R L) c := by
      calc α ^ 2 * sL ^ 2
          = (y * sL⁻¹) ^ 2 * sL ^ 2 := by rw [hα_def]
        _ = y ^ 2 * (sL⁻¹ * sL) ^ 2 := by ring
        _ = y ^ 2 * 1 ^ 2 := by rw [inv_mul_cancel₀ hsL_ne]
        _ = y ^ 2 := by ring
        _ = (algebraMap R L) c := hy_sq
    have step2 : α ^ 2 * sL ^ 2 = (-1) * sL ^ 2 := by
      rw [step1, hsL_sq]; ring
    exact mul_right_cancel₀ hsL_sq_ne step2
  have hα_ni : α ∉ (algebraMap R L).range := by
    rintro ⟨r, hr⟩
    apply hy_ni
    refine ⟨r * s, ?_⟩
    have hy_eq : y = α * sL := by
      show y = (y * sL⁻¹) * sL
      rw [mul_assoc, inv_mul_cancel₀ hsL_ne, mul_one]
    rw [hy_eq, ← hr, hsL_def, ← map_mul]
  have hαI : IsIntegral R α := .of_finite R α
  have hmin : minpoly R α = Polynomial.X ^ 2 + Polynomial.C (1 : R) := by
    set g : Polynomial R := Polynomial.X ^ 2 + Polynomial.C (1 : R) with hg_def
    have hgm : g.Monic := Polynomial.monic_X_pow_add_C (1 : R) (by norm_num : (2 : ℕ) ≠ 0)
    have hgroot : Polynomial.aeval α g = 0 := by
      show Polynomial.aeval α (Polynomial.X ^ 2 + Polynomial.C (1 : R)) = 0
      simp [hα_sq]
    have hdα : (minpoly R α).natDegree = 2 := by
      have h2α : 2 ≤ (minpoly R α).natDegree :=
        (minpoly.two_le_natDegree_iff hαI).mpr hα_ni
      have hαle : (minpoly R α).natDegree ≤ Module.finrank R L := minpoly.natDegree_le α
      omega
    have hgdeg : g.natDegree = 2 := by
      show (Polynomial.X ^ 2 + Polynomial.C (1 : R)).natDegree = 2
      exact Polynomial.natDegree_X_pow_add_C
    refine (minpoly.unique_of_degree_le_degree_minpoly R α hgm hgroot ?_).symm
    rw [Polynomial.degree_eq_natDegree hgm.ne_zero,
        Polynomial.degree_eq_natDegree (minpoly.ne_zero hαI), hgdeg, hdα]
  have hli : LinearIndependent R ![(1 : L), α] := by
    rw [LinearIndependent.pair_iff]
    intro r t hrt
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hrt
      rw [Algebra.smul_def, mul_one] at hrt
      exact ⟨(map_eq_zero_iff _ hInj).mp hrt, rfl⟩
    · exfalso
      apply hα_ni
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hrt
      have htL : (algebraMap R L) t ≠ 0 := (map_ne_zero_iff _ hInj).mpr ht
      refine ⟨-r / t, ?_⟩
      rw [map_div₀, map_neg]
      field_simp
      linear_combination -hrt
  have hcard : Fintype.card (Fin 2) = Module.finrank R L := by
    rw [Fintype.card_fin, hL]
  let basis2 := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbasis_eq : ∀ i : Fin 2, basis2 i = α ^ (i : ℕ) := by
    intro i
    have key : basisOfLinearIndependentOfCardEqFinrank hli hcard i = ![(1 : L), α] i := by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank hli hcard]
    show basisOfLinearIndependentOfCardEqFinrank hli hcard i = α ^ (i : ℕ)
    rw [key]
    fin_cases i <;> simp
  refine ⟨{ gen := α, dim := 2, basis := basis2, basis_eq_pow := hbasis_eq }, ?_⟩
  exact hmin

/-- `R(i)` is the unique quadratic extension of a real closed field `R` (up to `R`-isomorphism):
any quadratic extension of `R` is `R`-isomorphic to any other quadratic extension of `R`. -/
theorem nonempty_algEquiv_of_finrank_eq_two
    (K K' : Type*) [Field K] [Algebra R K] [Field K'] [Algebra R K']
    (hK : Module.finrank R K = 2) (hK' : Module.finrank R K' = 2) :
    Nonempty (K ≃ₐ[R] K') := by
  obtain ⟨pbK, hminK⟩ := exists_powerBasis_of_finrank_eq_two_aux R K hK
  obtain ⟨pbK', hminK'⟩ := exists_powerBasis_of_finrank_eq_two_aux R K' hK'
  exact ⟨pbK.equivOfMinpoly pbK' (hminK.trans hminK'.symm)⟩

/-- `R(i)` has no quadratic extension: equivalently, every element of any quadratic
extension `K` of `R` is a square in `K`. -/
theorem isSquare_of_finrank_base_eq_two
    (K : Type*) [Field K] [Algebra R K]
    (hK : Module.finrank R K = 2) (x : K) : IsSquare x := by
  obtain ⟨pb, hmin⟩ := exists_powerBasis_of_finrank_eq_two_aux R K hK
  haveI hFin : FiniteDimensional R K := .of_finrank_eq_succ hK
  have hInj : Function.Injective (algebraMap R K) := (algebraMap R K).injective
  have hpb_dim : pb.dim = 2 := by
    have h1 : (minpoly R pb.gen).natDegree = pb.dim := pb.natDegree_minpoly
    rw [hmin] at h1
    have h2 : (Polynomial.X ^ 2 + Polynomial.C (1 : R)).natDegree = 2 :=
      Polynomial.natDegree_X_pow_add_C
    omega
  have hgen_sq : pb.gen ^ 2 = -1 := by
    have haev : Polynomial.aeval pb.gen (minpoly R pb.gen) = 0 := minpoly.aeval R pb.gen
    rw [hmin] at haev
    simp only [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_one] at haev
    linear_combination haev
  set j : K := pb.gen with hj_def
  have hInj_j : j ∉ Set.range (algebraMap R K) := by
    rintro ⟨s, hs⟩
    have hs2 : (algebraMap R K s)^2 = -1 := by rw [hs]; exact hgen_sq
    have hs2' : algebraMap R K (s^2 + 1) = 0 := by
      rw [map_add, map_pow, map_one, hs2]; ring
    have h1 : s^2 + 1 = 0 := hInj (by rw [hs2', map_zero])
    have h2 : IsSumSq ((-1 : R)) := by
      have : (-1 : R) = s * s := by linear_combination -h1
      rw [this]
      exact IsSumSq.mul_self s
    exact IsSemireal.not_isSumSq_neg_one R h2
  have hli : LinearIndependent R ![(1 : K), j] := by
    rw [LinearIndependent.pair_iff]
    intro r t hrt
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hrt
      rw [Algebra.smul_def, mul_one] at hrt
      exact ⟨(map_eq_zero_iff _ hInj).mp hrt, rfl⟩
    · exfalso
      apply hInj_j
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hrt
      have htL : (algebraMap R K) t ≠ 0 := (map_ne_zero_iff _ hInj).mpr ht
      refine ⟨-r / t, ?_⟩
      rw [map_div₀, map_neg]
      rw [div_eq_iff htL]
      linear_combination -hrt
  have hcard : Fintype.card (Fin 2) = Module.finrank R K := by
    rw [Fintype.card_fin, hK]
  let B : Basis (Fin 2) R K := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hB0 : B 0 = 1 := by
    show basisOfLinearIndependentOfCardEqFinrank hli hcard 0 = 1
    rw [coe_basisOfLinearIndependentOfCardEqFinrank hli hcard]
    simp
  have hB1 : B 1 = j := by
    show basisOfLinearIndependentOfCardEqFinrank hli hcard 1 = j
    rw [coe_basisOfLinearIndependentOfCardEqFinrank hli hcard]
    simp
  have hx_decomp : x = algebraMap R K (B.repr x 0) + algebraMap R K (B.repr x 1) * j := by
    have hsum : ∑ i, B.repr x i • B i = x := B.sum_repr x
    rw [Fin.sum_univ_two] at hsum
    rw [hB0, hB1] at hsum
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hsum
    linear_combination -hsum
  set a : R := B.repr x 0 with ha_def
  set b : R := B.repr x 1 with hb_def
  by_cases hb0 : b = 0
  · rw [hb0, map_zero, zero_mul, add_zero] at hx_decomp
    rcases isSquare_or_isSquare_neg a with ⟨c, hc⟩ | ⟨c, hc⟩
    · refine ⟨algebraMap R K c, ?_⟩
      rw [hx_decomp, hc, map_mul]
    · refine ⟨algebraMap R K c * j, ?_⟩
      rw [hx_decomp]
      have ha_eq : a = -(c * c) := by linear_combination -hc
      rw [ha_eq, map_neg, map_mul]
      have : algebraMap R K c * j * (algebraMap R K c * j) = (algebraMap R K c)^2 * j^2 := by ring
      rw [this, hgen_sq]
      ring
  · have hab_sq : IsSquare (a^2 + b^2) :=
      isSquare_of_isSumSq (IsSumSq.add (IsSumSq.sq a) (IsSumSq.sq b))
    obtain ⟨r, hr⟩ := hab_sq
    have hr_sq : r^2 = a^2 + b^2 := by rw [hr]; ring
    have hexists_sign : ∃ s : R, s^2 = a^2 + b^2 ∧ IsSquare ((s + a) / 2) := by
      rcases isSquare_or_isSquare_neg ((r + a) / 2) with hsq | hsq
      · exact ⟨r, hr_sq, hsq⟩
      · refine ⟨-r, ?_, ?_⟩
        · linear_combination hr_sq
        · obtain ⟨α, hα⟩ := hsq
          by_cases hα0 : α = 0
          · exfalso
            rw [hα0] at hα
            have hra : r + a = 0 := by linear_combination -2 * hα
            have h1 : r^2 = a^2 := by linear_combination (r - a) * hra
            have h3 : b^2 = 0 := by linear_combination -hr_sq + h1
            apply hb0
            exact (pow_eq_zero_iff two_ne_zero).mp h3
          · have hα_ne : α ≠ 0 := hα0
            refine ⟨b / (2 * α), ?_⟩
            have h2α_ne : (2 : R) * α ≠ 0 := mul_ne_zero two_ne_zero hα_ne
            have h4α2_ne : (2 * α) * (2 * α) ≠ 0 := mul_ne_zero h2α_ne h2α_ne
            rw [div_mul_div_comm,
                div_eq_div_iff (by norm_num : (2 : R) ≠ 0) h4α2_ne]
            linear_combination 4 * (r - a) * hα + 2 * hr_sq
    obtain ⟨s, hs_sq, hcsq⟩ := hexists_sign
    obtain ⟨c, hc⟩ := hcsq
    have hc0 : c ≠ 0 := by
      intro heq
      rw [heq, mul_zero] at hc
      have hsa : s + a = 0 := by linear_combination 2 * hc
      have h1 : s^2 = a^2 := by linear_combination (s - a) * hsa
      have h3 : b^2 = 0 := by linear_combination -hs_sq + h1
      apply hb0
      exact (pow_eq_zero_iff two_ne_zero).mp h3
    set d : R := b / (2 * c) with hd_def
    have h2c_ne : (2 : R) * c ≠ 0 := mul_ne_zero two_ne_zero hc0
    have hc2_ne : c^2 ≠ 0 := pow_ne_zero _ hc0
    have hc2 : c^2 = (s + a) / 2 := by
      rw [sq]; linear_combination -hc
    have hs_ne : s + a ≠ 0 := by
      rw [show s + a = 2 * c^2 from by linear_combination -2 * hc2]
      exact mul_ne_zero two_ne_zero hc2_ne
    have hprod : (s + a) * (s - a) = b^2 := by linear_combination hs_sq
    have hd2 : d^2 = (s - a) / 2 := by
      have hstep1 : d^2 = b^2 / (2 * c)^2 := by rw [hd_def]; ring
      have h2csq : (2 * c)^2 = 2 * (s + a) := by
        have hex : (2 * c)^2 = 4 * c^2 := by ring
        rw [hex, hc2]; ring
      rw [hstep1, h2csq]
      rw [div_eq_div_iff (mul_ne_zero two_ne_zero hs_ne) two_ne_zero]
      linear_combination -2 * hprod
    have hcd_eq_a : c^2 - d^2 = a := by
      rw [hc2, hd2]; ring
    have h2cd : 2 * c * d = b := by
      rw [hd_def]
      field_simp
    refine ⟨algebraMap R K c + algebraMap R K d * j, ?_⟩
    rw [hx_decomp]
    have hexpand : (algebraMap R K c + algebraMap R K d * j) *
                   (algebraMap R K c + algebraMap R K d * j) =
                   (algebraMap R K c)^2 + (algebraMap R K d)^2 * j^2 +
                   2 * algebraMap R K c * algebraMap R K d * j := by ring
    rw [hexpand, hgen_sq]
    have hmap_a : algebraMap R K a = (algebraMap R K c)^2 - (algebraMap R K d)^2 := by
      rw [← map_pow, ← map_pow, ← map_sub, hcd_eq_a]
    have hmap_b : algebraMap R K b = 2 * algebraMap R K c * algebraMap R K d := by
      have h1 : (2 : K) = algebraMap R K 2 := (map_ofNat (algebraMap R K) 2).symm
      rw [h1, ← map_mul, ← map_mul, h2cd]
    rw [hmap_a, hmap_b]
    ring

/-- Over a real closed field `R`, no tower `R ⊂ M ⊂ N` of fields can have
`[M:R] = [N:M] = 2`. -/
private theorem no_quadratic_over_quadratic
    {M : Type*} [Field M] [Algebra R M]
    {N : Type*} [Field N] [Algebra R N] [Algebra M N] [IsScalarTower R M N]
    (hMR : Module.finrank R M = 2) (hNM : Module.finrank M N = 2) : False := by
  haveI hFinN : FiniteDimensional M N := .of_finrank_eq_succ hNM
  have hInj_MN : Function.Injective (algebraMap M N) := (algebraMap M N).injective
  have hne : ∃ α : N, α ∉ (algebraMap M N).range := by
    by_contra hcon
    push_neg at hcon
    have htop : (⊥ : Subalgebra M N) = ⊤ := by
      rw [eq_top_iff]
      rintro x -
      obtain ⟨r, hr⟩ := hcon x
      exact Algebra.mem_bot.mpr ⟨r, hr⟩
    have heq : Module.finrank M (⊥ : Subalgebra M N) = Module.finrank M N := by
      rw [htop]; exact Subalgebra.topEquiv.toLinearEquiv.finrank_eq
    rw [Subalgebra.finrank_bot] at heq
    omega
  obtain ⟨α, hα⟩ := hne
  have hαI : IsIntegral M α := .of_finite M α
  have hdeg2 : (minpoly M α).natDegree = 2 := by
    have h2 : 2 ≤ (minpoly M α).natDegree := (minpoly.two_le_natDegree_iff hαI).mpr hα
    have hle : (minpoly M α).natDegree ≤ Module.finrank M N := minpoly.natDegree_le α
    omega
  set a : M := (minpoly M α).coeff 1 with ha_def
  set b : M := (minpoly M α).coeff 0 with hb_def
  have hfm : (minpoly M α).Monic := minpoly.monic hαI
  have hcoeff2 : (minpoly M α).coeff 2 = 1 := by
    have hlc : (minpoly M α).leadingCoeff = 1 := hfm
    rw [Polynomial.leadingCoeff, hdeg2] at hlc
    exact hlc
  have hroot : α ^ 2 + (algebraMap M N) a * α + (algebraMap M N) b = 0 := by
    have hlt : (minpoly M α).natDegree < 3 := by omega
    have haev := minpoly.aeval M α
    rw [Polynomial.aeval_eq_sum_range' hlt] at haev
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Algebra.smul_def, pow_zero, mul_one, pow_one] at haev
    rw [hcoeff2, map_one, one_mul] at haev
    show α ^ 2 + (algebraMap M N) ((minpoly M α).coeff 1) * α +
      (algebraMap M N) ((minpoly M α).coeff 0) = 0
    linear_combination haev
  set c : M := a ^ 2 / 4 - b with hc_def
  set β : N := α + (algebraMap M N) (a / 2) with hβ_def
  have h2M : (2 : M) ≠ 0 := two_ne_zero
  have hβ_sq : β ^ 2 = (algebraMap M N) c := by
    have half_sq : (algebraMap M N) (a / 2) ^ 2 = (algebraMap M N) (a ^ 2 / 4) := by
      rw [← map_pow]; congr 1; field_simp; ring
    have half_times : 2 * (algebraMap M N) (a / 2) = (algebraMap M N) a := by
      have : (2 : N) = (algebraMap M N) 2 := (map_ofNat (algebraMap M N) 2).symm
      rw [this, ← map_mul]; congr 1; field_simp
    have expand : β ^ 2 = α ^ 2 + (algebraMap M N) a * α + (algebraMap M N) (a ^ 2 / 4) := by
      show (α + (algebraMap M N) (a / 2)) ^ 2 = _
      have h : (α + (algebraMap M N) (a / 2)) ^ 2 =
          α ^ 2 + α * (2 * (algebraMap M N) (a / 2)) + (algebraMap M N) (a / 2) ^ 2 := by ring
      rw [h, half_sq, half_times]; ring
    rw [expand]
    show α ^ 2 + (algebraMap M N) a * α + (algebraMap M N) (a ^ 2 / 4) =
      (algebraMap M N) (a ^ 2 / 4 - b)
    rw [map_sub]
    linear_combination hroot
  have hβ_ni : β ∉ (algebraMap M N).range := by
    rintro ⟨r, hr⟩
    apply hα
    refine ⟨r - a / 2, ?_⟩
    have hr' : (algebraMap M N) r = α + (algebraMap M N) (a / 2) := hr
    rw [map_sub]
    linear_combination hr'
  have hMsq : IsSquare c :=
    IsRealClosed.isSquare_of_finrank_base_eq_two R M hMR c
  obtain ⟨s, hs⟩ := hMsq
  have halg_sq : β ^ 2 = ((algebraMap M N) s) ^ 2 := by
    rw [hβ_sq, show c = s * s from hs, map_mul]
    ring
  have hfact : (β - (algebraMap M N) s) * (β + (algebraMap M N) s) = 0 := by
    linear_combination halg_sq
  apply hβ_ni
  rcases mul_eq_zero.mp hfact with hd | hd
  · exact ⟨s, by linear_combination -hd⟩
  · refine ⟨-s, ?_⟩
    rw [map_neg]
    linear_combination -hd

/-- Helper: `finrank = 1` when `algebraMap` is surjective. -/
private theorem finrank_eq_one_of_surjective_algebraMap
    {M : Type*} [Field M] [Algebra R M] [FiniteDimensional R M]
    (hsurj : Function.Surjective (algebraMap R M)) : Module.finrank R M = 1 := by
  have hbot_eq_top : (⊥ : Subalgebra R M) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨r, hr⟩ := hsurj x
    exact Algebra.mem_bot.mpr ⟨r, hr⟩
  have heq : Module.finrank R (⊥ : Subalgebra R M) = Module.finrank R M := by
    rw [hbot_eq_top]; exact Subalgebra.topEquiv.toLinearEquiv.finrank_eq
  rw [Subalgebra.finrank_bot] at heq
  exact heq.symm

/-- For a finite Galois extension `L/R` of a real closed field, `[L:R] ≤ 2`. -/
private theorem finrank_le_two_of_isGalois
    (L : Type*) [Field L] [Algebra R L] [FiniteDimensional R L] [IsGalois R L] :
    Module.finrank R L ≤ 2 := by
  have hcard : Nat.card (L ≃ₐ[R] L) = Module.finrank R L := IsGalois.card_aut_eq_finrank R L
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 (L ≃ₐ[R] L) := Classical.arbitrary _
  obtain ⟨m, hPcard⟩ : ∃ m, Nat.card (P : Subgroup (L ≃ₐ[R] L)) = 2 ^ m :=
    IsPGroup.iff_card.mp P.isPGroup'
  set M := IntermediateField.fixedField (P : Subgroup (L ≃ₐ[R] L)) with hM_def
  have hLM : Module.finrank M L = 2 ^ m := by
    rw [IntermediateField.finrank_fixedField_eq_card, hPcard]
  have hmul : Module.finrank R M * Module.finrank M L = Module.finrank R L :=
    Module.finrank_mul_finrank R M L
  have hMR_prod : Module.finrank R M * 2 ^ m = Module.finrank R L := hLM ▸ hmul
  have hMR_odd : Odd (Module.finrank R M) := by
    have hcoprime : (Nat.card (P : Subgroup (L ≃ₐ[R] L))).Coprime
        (P : Subgroup (L ≃ₐ[R] L)).index := P.card_coprime_index
    rw [hPcard] at hcoprime
    have hindex_eq : (P : Subgroup (L ≃ₐ[R] L)).index = Module.finrank R M := by
      have h1 : (P : Subgroup (L ≃ₐ[R] L)).index * Nat.card (P : Subgroup (L ≃ₐ[R] L))
          = Nat.card (L ≃ₐ[R] L) := (P : Subgroup (L ≃ₐ[R] L)).index_mul_card
      rw [hcard, ← hMR_prod, hPcard] at h1
      have h2m_pos : (0 : ℕ) < 2 ^ m := Nat.pos_of_ne_zero (pow_ne_zero m (by norm_num))
      exact (Nat.eq_of_mul_eq_mul_right h2m_pos h1).symm
    rw [← hindex_eq]
    rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
    · have h2_not_dvd : ¬ 2 ∣ Nat.card (L ≃ₐ[R] L) := by
        intro hdvd
        rcases Nat.eq_zero_or_pos (Nat.card (L ≃ₐ[R] L)) with h0 | hpos
        · rw [h0] at hdvd; exact absurd hdvd (by norm_num)
        · have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hpos.ne' hdvd
          have hmult := P.card_eq_multiplicity
          rw [hPcard, hm0, pow_zero] at hmult
          omega
      rw [Nat.odd_iff_not_even]
      intro heven
      apply h2_not_dvd
      rw [hcard, ← hMR_prod, hm0, pow_zero, mul_one]
      exact heven.two_dvd
    · have h2_dvd : (2 : ℕ) ∣ 2 ^ m := dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hm_pos)
      have h2_cop : Nat.Coprime 2 (P : Subgroup (L ≃ₐ[R] L)).index :=
        hcoprime.coprime_dvd_left h2_dvd
      rw [Nat.odd_iff_not_even]
      intro heven
      have h2div : 2 ∣ (P : Subgroup (L ≃ₐ[R] L)).index := heven.two_dvd
      have hgcd : Nat.gcd 2 (P : Subgroup (L ≃ₐ[R] L)).index = 2 := Nat.gcd_eq_left h2div
      rw [Nat.Coprime] at h2_cop
      omega
  have hMR_one : Module.finrank R M = 1 :=
    finrank_eq_one_of_surjective_algebraMap R
      (IsRealClosed.surjective_algebraMap_of_odd_finrank R M hMR_odd)
  have hLR_pow : Module.finrank R L = 2 ^ m := by
    rw [← hMR_prod, hMR_one, one_mul]
  rcases Nat.lt_or_ge m 2 with hm | hm
  · rw [hLR_pow]
    interval_cases m <;> norm_num
  · exfalso
    have hG_card : Nat.card (L ≃ₐ[R] L) = 2 ^ m := by rw [hcard, hLR_pow]
    have hG_pgroup : IsPGroup 2 (L ≃ₐ[R] L) := IsPGroup.of_card hG_card
    have h2m1_le : (2 : ℕ) ^ (m - 1) ≤ Nat.card (L ≃ₐ[R] L) := by
      rw [hG_card]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨H, hH⟩ : ∃ H : Subgroup (L ≃ₐ[R] L), Nat.card H = 2 ^ (m - 1) :=
      Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two hG_pgroup h2m1_le
    have h2m2_le : (2 : ℕ) ^ (m - 2) ≤ Nat.card H := by
      rw [hH]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨H', hH'_le_H, hH'⟩ : ∃ H' ≤ H, Nat.card H' = 2 ^ (m - 2) :=
      Sylow.exists_subgroup_le_card_pow_prime_of_le_card Nat.prime_two hG_pgroup h2m2_le
    set M1 : IntermediateField R L := IntermediateField.fixedField H with hM1_def
    set M2 : IntermediateField R L := IntermediateField.fixedField H' with hM2_def
    have hM1_le_M2 : M1 ≤ M2 := IntermediateField.fixedField_le hH'_le_H
    have hLM1 : Module.finrank M1 L = 2 ^ (m - 1) := by
      rw [IntermediateField.finrank_fixedField_eq_card, hH]
    have hLM2 : Module.finrank M2 L = 2 ^ (m - 2) := by
      rw [IntermediateField.finrank_fixedField_eq_card, hH']
    have hM1R : Module.finrank R M1 = 2 := by
      have := Module.finrank_mul_finrank R M1 L
      rw [hLM1, hLR_pow] at this
      have hk_eq : (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) := by
        conv_lhs => rw [show m = (m - 1) + 1 from by omega]
        rw [pow_succ]; ring
      rw [hk_eq] at this
      have hpos : (0 : ℕ) < 2 ^ (m - 1) :=
        Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num))
      exact Nat.eq_of_mul_eq_mul_right hpos (by linarith)
    letI : Algebra M1 M2 := (IntermediateField.inclusion hM1_le_M2).toAlgebra
    haveI hST_RM1M2 : IsScalarTower R M1 M2 := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI hST_M1M2L : IsScalarTower M1 M2 L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI hFinM2L : FiniteDimensional M2 L := FiniteDimensional.of_finrank_eq_succ hLM2
    have hM2M1 : Module.finrank M1 M2 = 2 := by
      have := Module.finrank_mul_finrank M1 M2 L
      rw [hLM2, hLM1] at this
      have heq : (2 : ℕ) ^ (m - 1) = 2 * 2 ^ (m - 2) := by
        conv_lhs => rw [show m - 1 = (m - 2) + 1 from by omega]
        rw [pow_succ]; ring
      rw [heq] at this
      have hpos : (0 : ℕ) < 2 ^ (m - 2) :=
        Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num))
      exact Nat.eq_of_mul_eq_mul_right hpos (by linarith)
    exact no_quadratic_over_quadratic R hM1R hM2M1

/-- Fundamental theorem of algebra for real closed fields: the only finite extensions
of `R` are `R` itself and the quadratic extension `R(i)`. -/
theorem finrank_le_two_of_finiteDimensional
    (K : Type*) [Field K] [Algebra R K] [FiniteDimensional R K] :
    Module.finrank R K ≤ 2 := by
  haveI : Algebra.IsAlgebraic R K := Algebra.IsIntegral.isAlgebraic
  let φ : K →ₐ[R] AlgebraicClosure R := IsAlgClosed.lift
  have hφ_inj : Function.Injective φ := φ.toRingHom.injective
  let K' : IntermediateField R (AlgebraicClosure R) := φ.fieldRange
  let L : IntermediateField R (AlgebraicClosure R) := normalClosure R K' (AlgebraicClosure R)
  haveI : FiniteDimensional R K' := φ.toLinearMap.finiteDimensional_range
  haveI : FiniteDimensional R L := inferInstance
  haveI : Algebra.IsAlgebraic R L := Algebra.IsAlgebraic.of_finite R L
  haveI : Algebra.IsSeparable R L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Normal R L := normalClosure.normal R K' (AlgebraicClosure R)
  haveI : IsGalois R L := ⟨⟩
  have hL_le_two : Module.finrank R L ≤ 2 := finrank_le_two_of_isGalois R L
  have hKK'_eq : Module.finrank R K = Module.finrank R K' := by
    have e : K ≃ₐ[R] φ.fieldRange := AlgEquiv.ofInjectiveField φ hφ_inj
    exact LinearEquiv.finrank_eq e.toLinearEquiv
  have hK'L : Module.finrank R K' ≤ Module.finrank R L :=
    Submodule.finrank_mono (IntermediateField.le_normalClosure K').le
  linarith

/-- The only algebraic extensions of a real closed field `R` are `R` and `R(i)`. -/
theorem finrank_le_two_of_isAlgebraic
    (K : Type*) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K] :
    Module.finrank R K ≤ 2 := by
  by_contra hgt
  push_neg at hgt
  have hpos : 0 < Module.finrank R K := by omega
  haveI : FiniteDimensional R K := .of_finrank_pos hpos
  exact absurd (finrank_le_two_of_finiteDimensional R K) (not_le.mpr hgt)

/-- A real closed field has no nontrivial real algebraic extensions. -/
theorem surjective_algebraMap_of_isAlgebraic_of_isSemireal
    (K : Type*) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K] [IsSemireal K] :
    Function.Surjective (algebraMap R K) := by
  intro x
  -- x is algebraic over R, so R[x] is finite-dim with dim = minpoly degree ≤ 2.
  have hx_int : IsIntegral R x := Algebra.IsIntegral.isIntegral x
  set A : Subalgebra R K := Algebra.adjoin R ({x} : Set K) with hA_def
  haveI : FiniteDimensional R A :=
    (Subalgebra.isField_of_algebraic A (fun a ↦ (Algebra.IsAlgebraic.isAlgebraic _)))
      |>.elim
      (fun _ ↦ inferInstance)
    |>.elim
      (fun _ ↦ inferInstance)
  sorry

end Algebraic

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- `R` has no nontrivial ordered algebraic extension: for every field `K` that is an
algebraic extension of `R` and admits a linear order making it a strictly ordered ring
with `R → K` monotone, the structure map `R → K` is surjective. -/
def NoNontrivialOrderedAlgExt : Prop :=
  ∀ (K : Type*) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K],
    (∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule R K) →
    Function.Surjective (algebraMap R K)

/-- Polynomials over `R` satisfy the intermediate value property. -/
def PolynomialIVP : Prop :=
  ∀ (f : Polynomial R) (a b : R), a ≤ b → f.eval a ≤ 0 → 0 ≤ f.eval b →
    ∃ c ∈ Set.Icc a b, f.IsRoot c

section PolynomialIVPProof

open Polynomial

/-- For a quadratic monic of the form `(X - α)^2 + β^2` with `β ≠ 0`,
the evaluation is strictly positive everywhere. -/
private lemma quadratic_pos {α β : R} (hβ : β ≠ 0) (x : R) :
    0 < ((X - C α) ^ 2 + C (β ^ 2)).eval x := by
  simp only [eval_add, eval_pow, eval_sub, eval_X, eval_C]
  have h1 : 0 ≤ (x - α) ^ 2 := sq_nonneg _
  have h2 : 0 < β ^ 2 := by positivity
  linarith

end PolynomialIVPProof

/-- Polynomials over a real closed ordered field satisfy the intermediate value property. -/
theorem polynomialIVP_of_isRealClosed [IsRealClosed R] : PolynomialIVP R := by
  suffices h : ∀ n : ℕ, ∀ (f : Polynomial R) (a b : R),
      f.natDegree = n → a ≤ b → f.eval a ≤ 0 → 0 ≤ f.eval b →
      ∃ c ∈ Set.Icc a b, f.IsRoot c by
    intro f a b hab hfa hfb
    exact h f.natDegree f a b rfl hab hfa hfb
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f a b hn hab hfa hfb
  by_cases hn0 : n = 0
  · subst hn0
    have hfC : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hn
    rw [hfC] at hfa hfb
    simp only [Polynomial.eval_C] at hfa hfb
    have hc0 : f.coeff 0 = 0 := le_antisymm hfa hfb
    refine ⟨a, ⟨le_refl a, hab⟩, ?_⟩
    show f.eval a = 0
    rw [hfC, Polynomial.eval_C, hc0]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hfdeg_pos : 0 < f.natDegree := by rw [hn]; exact hnpos
    have hf_not_unit : ¬ IsUnit f := Polynomial.not_isUnit_of_natDegree_pos f hfdeg_pos
    obtain ⟨g, hg_monic, hg_irr, hg_dvd⟩ := Polynomial.exists_monic_irreducible_factor f hf_not_unit
    obtain ⟨h, hfgh⟩ := hg_dvd
    have hfne : f ≠ 0 := by
      intro hfz
      rw [hfz, Polynomial.natDegree_zero] at hn
      exact hn0 hn.symm
    have hhne : h ≠ 0 := by
      intro hhz
      rw [hhz, mul_zero] at hfgh
      exact hfne hfgh
    have hg_ne : g ≠ 0 := hg_monic.ne_zero
    have hdeg_sum : f.natDegree = g.natDegree + h.natDegree := by
      rw [hfgh]; exact Polynomial.natDegree_mul hg_ne hhne
    rcases monic_irreducible_classification R hg_monic hg_irr with
      ⟨c, hgeq⟩ | ⟨α, β, hβ, hgeq⟩
    · have hg_natDeg : g.natDegree = 1 := by rw [hgeq, Polynomial.natDegree_X_sub_C]
      have hh_natDeg : h.natDegree = n - 1 := by
        rw [hg_natDeg, hn] at hdeg_sum
        omega
      have hh_lt : h.natDegree < n := by rw [hh_natDeg]; omega
      by_cases hcab : a ≤ c ∧ c ≤ b
      · refine ⟨c, ⟨hcab.1, hcab.2⟩, ?_⟩
        show f.eval c = 0
        rw [hfgh, Polynomial.eval_mul, hgeq]
        simp
      · have hga : g.eval a = a - c := by rw [hgeq]; simp
        have hgb : g.eval b = b - c := by rw [hgeq]; simp
        push_neg at hcab
        rcases lt_or_ge c a with hca | hac
        · have hga_pos : 0 < g.eval a := by rw [hga]; linarith
          have hgb_pos : 0 < g.eval b := by rw [hgb]; linarith
          have hfa_eq : f.eval a = g.eval a * h.eval a := by rw [hfgh, Polynomial.eval_mul]
          have hfb_eq : f.eval b = g.eval b * h.eval b := by rw [hfgh, Polynomial.eval_mul]
          have hha : h.eval a ≤ 0 := by
            by_contra hha'
            push_neg at hha'
            rw [hfa_eq] at hfa
            exact absurd hfa (not_le.mpr (mul_pos hga_pos hha'))
          have hhb : 0 ≤ h.eval b := by
            by_contra hhb'
            push_neg at hhb'
            rw [hfb_eq] at hfb
            exact absurd hfb (not_le.mpr (mul_neg_of_pos_of_neg hgb_pos hhb'))
          obtain ⟨c', hc'_mem, hc'_root⟩ :=
            ih h.natDegree hh_lt h a b rfl hab hha hhb
          refine ⟨c', hc'_mem, ?_⟩
          show f.eval c' = 0
          rw [hfgh, Polynomial.eval_mul]
          have : h.eval c' = 0 := hc'_root
          rw [this, mul_zero]
        · have hbc : b < c := hcab hac
          have hga_neg : g.eval a < 0 := by rw [hga]; linarith
          have hgb_neg : g.eval b < 0 := by rw [hgb]; linarith
          have hfa_eq : f.eval a = g.eval a * h.eval a := by rw [hfgh, Polynomial.eval_mul]
          have hfb_eq : f.eval b = g.eval b * h.eval b := by rw [hfgh, Polynomial.eval_mul]
          have hha_nonneg : 0 ≤ h.eval a := by
            by_contra hha'
            push_neg at hha'
            rw [hfa_eq] at hfa
            exact absurd hfa (not_le.mpr (mul_pos_of_neg_of_neg hga_neg hha'))
          have hhb_nonpos : h.eval b ≤ 0 := by
            by_contra hhb'
            push_neg at hhb'
            rw [hfb_eq] at hfb
            exact absurd hfb (not_le.mpr (mul_neg_of_neg_of_pos hgb_neg hhb'))
          have hmh_a : (-h).eval a ≤ 0 := by
            rw [Polynomial.eval_neg]; linarith
          have hmh_b : 0 ≤ (-h).eval b := by
            rw [Polynomial.eval_neg]; linarith
          have hmh_deg : (-h).natDegree = h.natDegree := Polynomial.natDegree_neg h
          have hmh_lt : (-h).natDegree < n := by rw [hmh_deg]; exact hh_lt
          obtain ⟨c', hc'_mem, hc'_root⟩ :=
            ih (-h).natDegree hmh_lt (-h) a b rfl hab hmh_a hmh_b
          refine ⟨c', hc'_mem, ?_⟩
          have hc'_h : h.eval c' = 0 := by
            have heq : (-h).eval c' = 0 := hc'_root
            rw [Polynomial.eval_neg, neg_eq_zero] at heq
            exact heq
          show f.eval c' = 0
          rw [hfgh, Polynomial.eval_mul, hc'_h, mul_zero]
    · have hg_natDeg : g.natDegree = 2 := by
        rw [hgeq, Polynomial.natDegree_add_C, Polynomial.natDegree_pow,
          Polynomial.natDegree_X_sub_C]
      have hh_natDeg : h.natDegree = n - 2 := by
        rw [hg_natDeg, hn] at hdeg_sum
        omega
      have hh_lt : h.natDegree < n := by rw [hh_natDeg]; omega
      have hga_pos : 0 < g.eval a := by rw [hgeq]; exact quadratic_pos R hβ a
      have hgb_pos : 0 < g.eval b := by rw [hgeq]; exact quadratic_pos R hβ b
      have hfa_eq : f.eval a = g.eval a * h.eval a := by rw [hfgh, Polynomial.eval_mul]
      have hfb_eq : f.eval b = g.eval b * h.eval b := by rw [hfgh, Polynomial.eval_mul]
      have hha : h.eval a ≤ 0 := by
        by_contra hha'
        push_neg at hha'
        rw [hfa_eq] at hfa
        exact absurd hfa (not_le.mpr (mul_pos hga_pos hha'))
      have hhb : 0 ≤ h.eval b := by
        by_contra hhb'
        push_neg at hhb'
        rw [hfb_eq] at hfb
        exact absurd hfb (not_le.mpr (mul_neg_of_pos_of_neg hgb_pos hhb'))
      obtain ⟨c', hc'_mem, hc'_root⟩ :=
        ih h.natDegree hh_lt h a b rfl hab hha hhb
      refine ⟨c', hc'_mem, ?_⟩
      show f.eval c' = 0
      rw [hfgh, Polynomial.eval_mul]
      have : h.eval c' = 0 := hc'_root
      rw [this, mul_zero]

namespace polynomialIVP_aux

open Polynomial

/-- Helper: for a polynomial `f` with positive leading coefficient, odd `natDegree = n ≥ 1`,
there exists `M > 0` with `f.eval M > 0` and `f.eval (-M) < 0`. -/
private lemma exists_sign_change
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (f : Polynomial R) {n : ℕ} (hn : f.natDegree = n) (hn1 : 1 ≤ n) (hodd : Odd n)
    (hlc : 0 < f.leadingCoeff) :
    ∃ M : R, 0 < M ∧ f.eval (-M) < 0 ∧ 0 < f.eval M := by
  set B := ∑ i ∈ Finset.range n, |f.coeff i| with hB_def
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  set M : R := 1 + B / f.leadingCoeff with hM_def
  have hBdiv : 0 ≤ B / f.leadingCoeff := div_nonneg hB hlc.le
  have hMpos : 0 < M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hM0 : (0 : R) ≤ M := hMpos.le
  have hne : f.leadingCoeff ≠ 0 := ne_of_gt hlc
  have hkey : f.leadingCoeff * M - B = f.leadingCoeff := by
    have hMexpand : f.leadingCoeff * M = f.leadingCoeff + B := by
      rw [hM_def, mul_add, mul_one, mul_div_cancel₀ B hne]
    linarith
  have hMpow_pos : (0 : R) < M ^ (n - 1) := pow_pos hMpos _
  have hMpow_ge_one : (1 : R) ≤ M ^ (n - 1) := one_le_pow₀ hM1
  have hn_split : n = (n - 1) + 1 := by omega
  have hMn_eq : M ^ n = M ^ (n - 1) * M := by
    conv_lhs => rw [hn_split]
    exact pow_succ M (n - 1)
  have hlc_eq : f.coeff n = f.leadingCoeff := by rw [← hn]; rfl
  have heval_general : ∀ x : R, f.eval x =
      f.leadingCoeff * x ^ n + ∑ i ∈ Finset.range n, f.coeff i * x ^ i := by
    intro x
    have h1 : f.eval x = ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i * x ^ i :=
      eval_eq_sum_range x
    rw [h1, hn, Finset.sum_range_succ, hlc_eq]
    exact add_comm _ _
  have heval_M := heval_general M
  have heval_negM := heval_general (-M)
  have htail_M : |∑ i ∈ Finset.range n, f.coeff i * M ^ i| ≤ B * M ^ (n - 1) := by
    calc |∑ i ∈ Finset.range n, f.coeff i * M ^ i|
        ≤ ∑ i ∈ Finset.range n, |f.coeff i * M ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range n, |f.coeff i| * M ^ i := by
            refine Finset.sum_congr rfl (fun i _ ↦ ?_)
            rw [abs_mul, abs_of_nonneg (pow_nonneg hM0 i)]
      _ ≤ ∑ i ∈ Finset.range n, |f.coeff i| * M ^ (n - 1) := by
            refine Finset.sum_le_sum (fun i hi ↦ ?_)
            rw [Finset.mem_range] at hi
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact pow_le_pow_right₀ hM1 (by omega)
      _ = B * M ^ (n - 1) := by rw [← Finset.sum_mul]
  have htail_negM : |∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i| ≤ B * M ^ (n - 1) := by
    calc |∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i|
        ≤ ∑ i ∈ Finset.range n, |f.coeff i * (-M) ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range n, |f.coeff i| * M ^ i := by
            refine Finset.sum_congr rfl (fun i _ ↦ ?_)
            rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg hM0]
      _ ≤ ∑ i ∈ Finset.range n, |f.coeff i| * M ^ (n - 1) := by
            refine Finset.sum_le_sum (fun i hi ↦ ?_)
            rw [Finset.mem_range] at hi
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact pow_le_pow_right₀ hM1 (by omega)
      _ = B * M ^ (n - 1) := by rw [← Finset.sum_mul]
  have hneg_pow : (-M) ^ n = -M ^ n := Odd.neg_pow hodd M
  refine ⟨M, hMpos, ?_, ?_⟩
  · rw [heval_negM, hneg_pow, hMn_eq]
    have htail_upper : ∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i ≤ B * M ^ (n - 1) := by
      have := htail_negM
      rw [abs_le] at this
      exact this.2
    have hcompute :
        f.leadingCoeff * -(M ^ (n - 1) * M) + B * M ^ (n - 1)
          = -(M ^ (n - 1) * f.leadingCoeff) := by
      have h1 : f.leadingCoeff * -(M ^ (n - 1) * M) + B * M ^ (n - 1)
             = -M ^ (n - 1) * (f.leadingCoeff * M - B) := by ring
      rw [h1, hkey]; ring
    have hbound :
        f.leadingCoeff * -(M ^ (n - 1) * M) + ∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i
          ≤ -(M ^ (n - 1) * f.leadingCoeff) := by
      calc
        f.leadingCoeff * -(M ^ (n - 1) * M) + ∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i
            ≤ f.leadingCoeff * -(M ^ (n - 1) * M) + B * M ^ (n - 1) := by linarith
        _ = -(M ^ (n - 1) * f.leadingCoeff) := hcompute
    have : 0 < M ^ (n - 1) * f.leadingCoeff := mul_pos hMpow_pos hlc
    linarith
  · rw [heval_M, hMn_eq]
    have htail_lower : -(B * M ^ (n - 1)) ≤ ∑ i ∈ Finset.range n, f.coeff i * M ^ i := by
      have := htail_M
      rw [abs_le] at this
      linarith
    have hcompute :
        f.leadingCoeff * (M ^ (n - 1) * M) - B * M ^ (n - 1)
          = M ^ (n - 1) * f.leadingCoeff := by
      have h1 : f.leadingCoeff * (M ^ (n - 1) * M) - B * M ^ (n - 1)
             = M ^ (n - 1) * (f.leadingCoeff * M - B) := by ring
      rw [h1, hkey]
    have hbound :
        M ^ (n - 1) * f.leadingCoeff
          ≤ f.leadingCoeff * (M ^ (n - 1) * M) + ∑ i ∈ Finset.range n, f.coeff i * M ^ i := by
      calc M ^ (n - 1) * f.leadingCoeff
          = f.leadingCoeff * (M ^ (n - 1) * M) - B * M ^ (n - 1) := hcompute.symm
        _ ≤ f.leadingCoeff * (M ^ (n - 1) * M) + ∑ i ∈ Finset.range n, f.coeff i * M ^ i := by
            linarith
    have : 0 < M ^ (n - 1) * f.leadingCoeff := mul_pos hMpow_pos hlc
    linarith

end polynomialIVP_aux

/-- An ordered field whose polynomials satisfy the intermediate value property is real closed. -/
theorem isRealClosed_of_polynomialIVP (h : PolynomialIVP R) : IsRealClosed R := by
  refine IsRealClosed.of_linearOrderedField (R := R) ?_ ?_
  · intro a ha
    have h0 : (0 : R) ≤ a + 1 := by linarith
    have heval_0 : (Polynomial.X ^ 2 - Polynomial.C a).eval 0 ≤ 0 := by
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      nlinarith
    have heval_1 : 0 ≤ (Polynomial.X ^ 2 - Polynomial.C a).eval (a + 1) := by
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      nlinarith
    obtain ⟨c, _, hc_root⟩ :=
      h (Polynomial.X ^ 2 - Polynomial.C a) 0 (a + 1) h0 heval_0 heval_1
    have hc_eval : (Polynomial.X ^ 2 - Polynomial.C a).eval c = 0 := hc_root
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        sub_eq_zero] at hc_eval
    exact ⟨c, by rw [← sq]; exact hc_eval.symm⟩
  · intro f hodd
    set n := f.natDegree with hn_def
    have hn1 : 1 ≤ n := by
      rcases hodd with ⟨k, hk⟩
      omega
    have hf_ne : f ≠ 0 := by
      intro hfz
      rw [hfz, Polynomial.natDegree_zero] at hn_def
      omega
    by_cases hlc_pos : 0 < f.leadingCoeff
    · obtain ⟨M, hMpos, hMneg_eval, hMpos_eval⟩ :=
        polynomialIVP_aux.exists_sign_change (R := R) f hn_def.symm hn1 hodd hlc_pos
      obtain ⟨c, _, hc_root⟩ :=
        h f (-M) M (by linarith) hMneg_eval.le hMpos_eval.le
      exact ⟨c, hc_root⟩
    · rw [not_lt] at hlc_pos
      have hlc_ne : f.leadingCoeff ≠ 0 := by
        rw [Ne, Polynomial.leadingCoeff_eq_zero]
        exact hf_ne
      have hlc_neg : f.leadingCoeff < 0 := lt_of_le_of_ne hlc_pos hlc_ne
      have hndeg : (-f).natDegree = n := by rw [Polynomial.natDegree_neg, ← hn_def]
      have hlc' : 0 < (-f).leadingCoeff := by
        rw [Polynomial.leadingCoeff_neg]; linarith
      obtain ⟨M, hMpos, hMneg_eval, hMpos_eval⟩ :=
        polynomialIVP_aux.exists_sign_change (R := R) (-f) hndeg hn1 hodd hlc'
      obtain ⟨c, _, hc_root⟩ :=
        h (-f) (-M) M (by linarith) hMneg_eval.le hMpos_eval.le
      refine ⟨c, ?_⟩
      have : (-f).eval c = 0 := hc_root
      rw [Polynomial.eval_neg, neg_eq_zero] at this
      exact this

/-- A real closed ordered field has no nontrivial ordered algebraic extensions. -/
theorem noNontrivialOrderedAlgExt_of_isRealClosed [IsRealClosed R] :
    NoNontrivialOrderedAlgExt R := by
  intro K _ _ _ h
  obtain ⟨_, _, _⟩ := h
  exact surjective_algebraMap_of_isAlgebraic_of_isSemireal R K

/-- If `R` is an ordered field with no nontrivial ordered algebraic extensions, then every
non-negative element of `R` is a square in `R`. Corresponds to blueprint `cor:ext_ord_to_adj_sqrt`. -/
private lemma isSquare_of_nonneg_of_noNontrivialOrderedAlgExt
    (h : NoNontrivialOrderedAlgExt R) {x : R} (hx : 0 ≤ x) : IsSquare x := sorry

/-- If `R` is an ordered field with no nontrivial ordered algebraic extensions, then every
odd-degree polynomial in `R[X]` has a root in `R`. Corresponds to blueprint `lem:ext_ord_odd_deg`. -/
private lemma exists_isRoot_of_odd_natDegree_of_noNontrivialOrderedAlgExt
    (h : NoNontrivialOrderedAlgExt R) {f : Polynomial R}
    (hodd : Odd f.natDegree) : ∃ x, f.IsRoot x := sorry

/-- An ordered field with no nontrivial ordered algebraic extensions is real closed. -/
theorem isRealClosed_of_noNontrivialOrderedAlgExt (h : NoNontrivialOrderedAlgExt R) :
    IsRealClosed R :=
  IsRealClosed.of_linearOrderedField
    (isSquare_of_nonneg_of_noNontrivialOrderedAlgExt R h)
    (exists_isRoot_of_odd_natDegree_of_noNontrivialOrderedAlgExt R h)

/-- For an ordered field `R`, the following are equivalent:
1. `R` is real closed.
2. `R` is maximal with respect to ordered algebraic extensions.
3. Polynomials over `R` satisfy the intermediate value property. -/
theorem tfae_of_linearOrderedField :
    List.TFAE
      [ IsRealClosed R,
        NoNontrivialOrderedAlgExt R,
        PolynomialIVP R ] := by
  tfae_have 1 → 2 := fun _ ↦ noNontrivialOrderedAlgExt_of_isRealClosed R
  tfae_have 2 → 1 := isRealClosed_of_noNontrivialOrderedAlgExt R
  tfae_have 1 → 3 := fun _ ↦ polynomialIVP_of_isRealClosed R
  tfae_have 3 → 1 := isRealClosed_of_polynomialIVP R
  tfae_finish

end IsRealClosed
