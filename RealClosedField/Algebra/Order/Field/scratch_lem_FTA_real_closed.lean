/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib
import RealClosedField.Algebra.Order.Field.RealClosed

namespace IsRealClosed

variable (R : Type*) [Field R] [IsRealClosed R]

open scoped IntermediateField
open IntermediateField Module

/-- Over a real closed field R, no tower R ⊂ M ⊂ N of fields can have [M:R] = [N:M] = 2. -/
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

-- Helper: finrank = 1 when algebraMap is surjective.
private theorem finrank_eq_one_of_surjective_algebraMap
    {R : Type*} [Field R] {M : Type*} [Field M] [Algebra R M] [FiniteDimensional R M]
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

/-- For a finite Galois extension L/R of a real closed field, [L:R] ≤ 2. -/
private theorem finrank_le_two_of_isGalois
    (L : Type*) [Field L] [Algebra R L] [FiniteDimensional R L] [IsGalois R L] :
    Module.finrank R L ≤ 2 := by
  have hcard : Nat.card (L ≃ₐ[R] L) = Module.finrank R L := IsGalois.card_aut_eq_finrank R L
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Pick a Sylow 2-subgroup P of Gal(L/R).
  let P : Sylow 2 (L ≃ₐ[R] L) := Classical.arbitrary _
  obtain ⟨m, hPcard⟩ : ∃ m, Nat.card (P : Subgroup (L ≃ₐ[R] L)) = 2 ^ m :=
    IsPGroup.iff_card.mp P.isPGroup'
  -- [L:fixedField P] = |P| = 2^m
  set M := fixedField (P : Subgroup (L ≃ₐ[R] L)) with hM_def
  have hLM : Module.finrank M L = 2 ^ m := by
    rw [finrank_fixedField_eq_card, hPcard]
  have hmul : Module.finrank R M * Module.finrank M L = Module.finrank R L :=
    Module.finrank_mul_finrank R M L
  have hMR_prod : Module.finrank R M * 2 ^ m = Module.finrank R L := hLM ▸ hmul
  -- [M:R] is odd, so [M:R] = 1 by surjective_algebraMap_of_odd_finrank.
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
    · have hmult := P.card_eq_multiplicity
      rw [hPcard, hm0, pow_zero] at hmult
      have hfact_zero : Nat.factorization (Nat.card (L ≃ₐ[R] L)) 2 = 0 := by
        by_contra hne
        have hge : 2 ^ Nat.factorization (Nat.card (L ≃ₐ[R] L)) 2 ≥ 2 :=
          Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hne)
        omega
      have h2_not_dvd : ¬ 2 ∣ Nat.card (L ≃ₐ[R] L) := by
        intro hdvd
        rcases Nat.eq_zero_or_pos (Nat.card (L ≃ₐ[R] L)) with h0 | hpos
        · rw [h0] at hdvd; exact absurd hdvd (by norm_num)
        · have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hpos.ne' hdvd
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
    finrank_eq_one_of_surjective_algebraMap
      (IsRealClosed.surjective_algebraMap_of_odd_finrank R M hMR_odd)
  have hLR_pow : Module.finrank R L = 2 ^ m := by
    rw [← hMR_prod, hMR_one, one_mul]
  rcases Nat.lt_or_ge m 2 with hm | hm
  · rw [hLR_pow]
    interval_cases m <;> norm_num
  · -- m ≥ 2: derive contradiction by finding tower of dim-2 extensions.
    exfalso
    -- |G| = 2^m, so G is a 2-group.
    have hG_card : Nat.card (L ≃ₐ[R] L) = 2 ^ m := by rw [hcard, hLR_pow]
    have hG_pgroup : IsPGroup 2 (L ≃ₐ[R] L) := IsPGroup.of_card hG_card
    -- Find H subgroup of G with |H| = 2^(m-1).
    have h2m1_le : (2 : ℕ) ^ (m - 1) ≤ Nat.card (L ≃ₐ[R] L) := by
      rw [hG_card]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨H, hH⟩ : ∃ H : Subgroup (L ≃ₐ[R] L), Nat.card H = 2 ^ (m - 1) :=
      Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two hG_pgroup h2m1_le
    -- Find H' ≤ H with |H'| = 2^(m-2).
    have h2m2_le : (2 : ℕ) ^ (m - 2) ≤ Nat.card H := by
      rw [hH]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨H', hH'_le_H, hH'⟩ : ∃ H' ≤ H, Nat.card H' = 2 ^ (m - 2) :=
      Sylow.exists_subgroup_le_card_pow_prime_of_le_card Nat.prime_two hG_pgroup h2m2_le
    -- M1 = fixedField H, M2 = fixedField H'. M1 ≤ M2 (contravariant).
    set M1 : IntermediateField R L := fixedField H with hM1_def
    set M2 : IntermediateField R L := fixedField H' with hM2_def
    have hM1_le_M2 : M1 ≤ M2 := fixedField_le hH'_le_H
    have hLM1 : Module.finrank M1 L = 2 ^ (m - 1) := by
      rw [finrank_fixedField_eq_card, hH]
    have hLM2 : Module.finrank M2 L = 2 ^ (m - 2) := by
      rw [finrank_fixedField_eq_card, hH']
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
    -- Algebra M1 M2 via inclusion.
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

/-- FTA for real closed fields: any finite extension of R has dimension at most 2. -/
theorem finrank_le_two_of_finiteDimensional'
    (K : Type*) [Field K] [Algebra R K] [FiniteDimensional R K] :
    Module.finrank R K ≤ 2 := by
  haveI : Algebra.IsAlgebraic R K := Algebra.IsIntegral.isAlgebraic
  let φ : K →ₐ[R] AlgebraicClosure R := IsAlgClosed.lift
  let K' : IntermediateField R (AlgebraicClosure R) := φ.fieldRange
  let L : IntermediateField R (AlgebraicClosure R) := normalClosure R K' (AlgebraicClosure R)
  haveI : FiniteDimensional R K' := φ.toLinearMap.finiteDimensional_range
  -- FiniteDimensional R L is an instance.
  haveI : FiniteDimensional R L := inferInstance
  haveI : Algebra.IsAlgebraic R L := Algebra.IsAlgebraic.of_finite R L
  haveI : Algebra.IsSeparable R L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Normal R L := inferInstance
  haveI : IsGalois R L := ⟨⟩
  have hL_le_two : Module.finrank R L ≤ 2 := finrank_le_two_of_isGalois R L
  have hKK'_eq : Module.finrank R K = Module.finrank R K' := by
    have e : K ≃ₐ[R] φ.range := AlgEquiv.ofInjectiveField φ
    have h1 : Module.finrank R K = Module.finrank R φ.range := LinearEquiv.finrank_eq e.toLinearEquiv
    have h2 : Module.finrank R (φ.range : Subalgebra R (AlgebraicClosure R)) = Module.finrank R K' := by
      -- φ.range and K'.toSubalgebra have the same carrier and same finrank.
      -- Actually φ.fieldRange.toSubalgebra = φ.range (by @[simps toSubalgebra]).
      rfl
    exact h1.trans h2
  have hK'L : Module.finrank R K' ≤ Module.finrank R L :=
    IntermediateField.finrank_le_of_le_right (IntermediateField.le_normalClosure K')
  linarith

end IsRealClosed
