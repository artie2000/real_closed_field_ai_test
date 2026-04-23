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

-- Helper: over a real closed field R, there is no tower R ⊂ M ⊂ N of fields
-- with [M:R] = 2 and [N:M] = 2.
private theorem no_quadratic_over_quadratic
    (M : Type*) [Field M] [Algebra R M]
    (N : Type*) [Field N] [Algebra R N] [Algebra M N] [IsScalarTower R M N]
    (hMR : Module.finrank R M = 2) (hNM : Module.finrank M N = 2) : False := by
  haveI hFinN : FiniteDimensional M N := .of_finrank_eq_succ hNM
  haveI hInj_MN : Function.Injective (algebraMap M N) := (algebraMap M N).injective
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

/-- Auxiliary: over a real closed field, any finite Galois extension has dimension at most 2. -/
private theorem finrank_le_two_of_isGalois
    (L : Type*) [Field L] [Algebra R L] [FiniteDimensional R L] [IsGalois R L] :
    Module.finrank R L ≤ 2 := by
  have hcard : Nat.card (L ≃ₐ[R] L) = Module.finrank R L := IsGalois.card_aut_eq_finrank R L
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Take Sylow 2-subgroup P.
  let P : Sylow 2 (L ≃ₐ[R] L) := Classical.arbitrary _
  -- |P| = 2^m for some m.
  obtain ⟨m, hPcard⟩ : ∃ m, Nat.card (P : Subgroup (L ≃ₐ[R] L)) = 2 ^ m :=
    IsPGroup.iff_card.mp P.isPGroup'
  -- Set M = fixedField P. [L:M] = |P| = 2^m.
  set M := fixedField (P : Subgroup (L ≃ₐ[R] L)) with hM_def
  have hLM : Module.finrank M L = 2 ^ m := by
    rw [finrank_fixedField_eq_card, hPcard]
  have hmul : Module.finrank R M * Module.finrank M L = Module.finrank R L :=
    Module.finrank_mul_finrank R M L
  -- [M:R] equals the Sylow index, which is coprime to 2.
  have hMR_prod : Module.finrank R M * 2 ^ m = Module.finrank R L := by
    rw [← hLM]; exact hmul
  -- [M:R] is odd:
  have hMR_odd : Odd (Module.finrank R M) := by
    have hcoprime : (Nat.card (P : Subgroup (L ≃ₐ[R] L))).Coprime
        (P : Subgroup (L ≃ₐ[R] L)).index := P.card_coprime_index
    -- (P.index) equals [M:R]
    have hindex_eq : (P : Subgroup (L ≃ₐ[R] L)).index = Module.finrank R M := by
      have h1 : (P : Subgroup (L ≃ₐ[R] L)).index * Nat.card (P : Subgroup (L ≃ₐ[R] L))
          = Nat.card (L ≃ₐ[R] L) := (P : Subgroup (L ≃ₐ[R] L)).index_mul_card
      rw [hcard, ← hMR_prod, hPcard] at h1
      have h2m_pos : (0 : ℕ) < 2 ^ m := Nat.pos_of_ne_zero (pow_ne_zero m (by norm_num))
      exact (Nat.eq_of_mul_eq_mul_right h2m_pos h1).symm
    rw [← hindex_eq]
    rw [hPcard] at hcoprime
    -- Coprime (2^m) index.
    rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
    · -- m = 0, so |P| = 1. But from card_eq_multiplicity, 2 doesn't divide |G|.
      have hmult := P.card_eq_multiplicity
      rw [hPcard, hm0, pow_zero] at hmult
      have hfact_zero : Nat.factorization (Nat.card (L ≃ₐ[R] L)) 2 = 0 := by
        by_contra hne
        have : 2 ^ Nat.factorization (Nat.card (L ≃ₐ[R] L)) 2 ≥ 2 :=
          Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hne)
        omega
      -- 2 doesn't divide |G|
      have h2_not_dvd : ¬ 2 ∣ Nat.card (L ≃ₐ[R] L) := by
        intro hdvd
        rcases Nat.eq_zero_or_pos (Nat.card (L ≃ₐ[R] L)) with h0 | hpos
        · rw [h0] at hdvd; omega
        · have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hpos.ne' hdvd
          omega
      rw [Nat.odd_iff_not_even]
      intro heven
      apply h2_not_dvd
      rw [hcard, ← hMR_prod, hm0, pow_zero, mul_one]
      exact heven.two_dvd
    · -- m ≥ 1: use hcoprime
      have h2_dvd : (2 : ℕ) ∣ 2 ^ m := dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hm_pos)
      have h2_cop : Nat.Coprime 2 (P : Subgroup (L ≃ₐ[R] L)).index :=
        hcoprime.coprime_dvd_left h2_dvd
      rw [Nat.odd_iff_not_even]
      intro heven
      have h2div : 2 ∣ (P : Subgroup (L ≃ₐ[R] L)).index := heven.two_dvd
      have : Nat.gcd 2 (P : Subgroup (L ≃ₐ[R] L)).index = 2 := Nat.gcd_eq_left h2div
      rw [Nat.Coprime] at h2_cop
      omega
  -- By surjective_algebraMap_of_odd_finrank, [M:R] = 1.
  have hMR_one : Module.finrank R M = 1 := by
    have hsurj := IsRealClosed.surjective_algebraMap_of_odd_finrank R (M := M) M hMR_odd
    have hbot_eq_top : (⊥ : Subalgebra R M) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨r, hr⟩ := hsurj x
      exact Algebra.mem_bot.mpr ⟨r, hr⟩
    have : Module.finrank R (⊥ : Subalgebra R M) = Module.finrank R M := by
      rw [hbot_eq_top]
      exact Subalgebra.topEquiv.toLinearEquiv.finrank_eq
    rw [Subalgebra.finrank_bot] at this
    exact this.symm
  -- Now [L:R] = 2^m.
  have hLR_pow : Module.finrank R L = 2 ^ m := by
    rw [← hMR_prod, hMR_one, one_mul]
  -- Show m ≤ 1.
  rcases Nat.lt_or_ge m 2 with hm | hm
  · -- m ∈ {0, 1}, so 2^m ∈ {1, 2}.
    rw [hLR_pow]
    interval_cases m <;> norm_num
  · -- m ≥ 2: derive contradiction via no_quadratic_over_quadratic.
    -- Build tower: Sylow of order 2^(k-1) gives M with [M:R] = 2.
    -- Sylow in Gal(L/M) of order 2^(k-2) gives N with [N:M] = 2.
    exfalso
    -- Here k := m. [L:R] = 2^m. Use as G = Gal(L/R).
    set k := m with hk_def
    -- Get subgroup H of order 2^(k-1).
    have h2km1_dvd : (2 : ℕ) ^ (k - 1) ∣ Nat.card (L ≃ₐ[R] L) := by
      rw [hcard, hLR_pow]; exact pow_dvd_pow 2 (by omega)
    obtain ⟨H, hH⟩ : ∃ H : Subgroup (L ≃ₐ[R] L), Nat.card H = 2 ^ (k - 1) :=
      Sylow.exists_subgroup_card_pow_prime 2 h2km1_dvd
    set M' := fixedField H with hM'_def
    have hLM' : Module.finrank M' L = 2 ^ (k - 1) := by
      rw [finrank_fixedField_eq_card, hH]
    have hM'R : Module.finrank R M' = 2 := by
      have hmul' := Module.finrank_mul_finrank R M' L
      rw [hLM', hLR_pow] at hmul'
      have : Module.finrank R M' * 2 ^ (k - 1) = 2 ^ k := hmul'
      have hk_eq : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
        conv_lhs => rw [show k = (k - 1) + 1 from by omega]
        rw [pow_succ]; ring
      rw [hk_eq] at this
      have hpos : (0 : ℕ) < 2 ^ (k - 1) := Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num))
      exact Nat.eq_of_mul_eq_mul_right hpos (by linarith)
    -- L/M' is Galois.
    haveI : IsGalois M' L := IsGalois.tower_top_of_isGalois R M' L
    haveI hfd : FiniteDimensional M' L := .of_finrank_eq_succ hLM' |>.elim (fun _ => inferInstance)
      -- Actually simpler: it's a subfield tower.
    sorry

/-- FTA for real closed fields: any finite extension of R has dimension at most 2. -/
theorem finrank_le_two_of_finiteDimensional'
    (K : Type*) [Field K] [Algebra R K] [FiniteDimensional R K] :
    Module.finrank R K ≤ 2 := by
  sorry

end IsRealClosed
