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

/-- Key lemma: over a real closed field, no finite Galois extension has dimension a power of 2
that is at least 4. -/
private theorem not_finrank_eq_pow_two_of_isGalois
    (L : Type*) [Field L] [Algebra R L] [FiniteDimensional R L] [IsGalois R L]
    {k : ℕ} (hk : 2 ≤ k) (hLR : Module.finrank R L = 2 ^ k) : False := by
  -- Gal(L/R) has order 2^k ≥ 4.
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (L ≃ₐ[R] L) = 2 ^ k := by
    rw [IsGalois.card_aut_eq_finrank, hLR]
  -- There exists a subgroup H of order 2^(k-1).
  have h2km1_dvd : (2 : ℕ) ^ (k - 1) ∣ Nat.card (L ≃ₐ[R] L) := by
    rw [hcard]
    exact pow_dvd_pow 2 (by omega)
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (L ≃ₐ[R] L), Nat.card H = 2 ^ (k - 1) :=
    Sylow.exists_subgroup_card_pow_prime 2 h2km1_dvd
  -- M := fixedField H. Then [L:M] = |H| = 2^(k-1), [M:R] = 2.
  set M := fixedField H with hM_def
  haveI : FiniteDimensional R M := inferInstance
  have hLM : Module.finrank M L = 2 ^ (k - 1) := by
    rw [show (Module.finrank M L) = _ from finrank_fixedField_eq_card H]
    rw [hH]
  have hMR : Module.finrank R M = 2 := by
    have h := Module.finrank_mul_finrank R M L
    rw [hLM, hLR] at h
    have : Module.finrank R M * 2 ^ (k - 1) = 2 ^ k := h
    have hk_eq : 2 ^ k = 2 * 2 ^ (k - 1) := by
      have : k = (k - 1) + 1 := by omega
      rw [this, pow_succ]; ring
    rw [hk_eq] at this
    have hpos : 0 < (2 : ℕ) ^ (k - 1) := Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num))
    have hcancel : Module.finrank R M = 2 := by
      have := Nat.eq_of_mul_eq_mul_right hpos (a := Module.finrank R M) (b := 2)
        (by linarith)
      exact this
    exact hcancel
  -- Since [L:M] ≥ 2, Gal(L/M) has order ≥ 2. Find a subgroup H' of Gal(L/M) of index 2.
  haveI : IsGalois M L := IsGalois.tower_top_of_isGalois R M L
  -- Nat.card Gal(L/M) = 2^(k-1)
  have hcardGM : Nat.card (L ≃ₐ[M] L) = 2 ^ (k - 1) := by
    rw [IsGalois.card_aut_eq_finrank, hLM]
  -- Sylow: exists subgroup H' of Gal(L/M) with |H'| = 2^(k-2).
  have h2km2_dvd : (2 : ℕ) ^ (k - 2) ∣ Nat.card (L ≃ₐ[M] L) := by
    rw [hcardGM]
    exact pow_dvd_pow 2 (by omega)
  obtain ⟨H', hH'⟩ : ∃ H' : Subgroup (L ≃ₐ[M] L), Nat.card H' = 2 ^ (k - 2) :=
    Sylow.exists_subgroup_card_pow_prime 2 h2km2_dvd
  -- N := fixedField H' (as intermediate field of L/M)
  set N : IntermediateField M L := fixedField H' with hN_def
  -- [L:N] = |H'| = 2^(k-2), so [N:M] = [L:M]/[L:N] = 2^(k-1)/2^(k-2) = 2.
  have hLN : Module.finrank N L = 2 ^ (k - 2) := by
    rw [show Module.finrank N L = _ from finrank_fixedField_eq_card H']
    rw [hH']
  have hNM : Module.finrank M N = 2 := by
    have h := Module.finrank_mul_finrank M N L
    rw [hLN, hLM] at h
    have : Module.finrank M N * 2 ^ (k - 2) = 2 ^ (k - 1) := h
    have hk1_eq : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
      have : k - 1 = (k - 2) + 1 := by omega
      rw [this, pow_succ]; ring
    rw [hk1_eq] at this
    have hpos : 0 < (2 : ℕ) ^ (k - 2) := Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num))
    have hcancel : Module.finrank M N = 2 :=
      Nat.eq_of_mul_eq_mul_right hpos (a := Module.finrank M N) (b := 2) (by linarith)
    exact hcancel
  -- Now apply isSquare_of_finrank_base_eq_two: every element of M is a square in M.
  -- But N/M is quadratic, so there's some α ∈ N \ M with α² ∈ M.
  -- α² is a square in M, so α² = s². Then α = ±s ∈ M, contradiction.
  -- Let's construct α.
  have hinj_MN : Function.Injective (algebraMap M N) := (algebraMap M N).injective
  -- Find α ∈ N \ range(algebraMap M N).
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
  -- α is integral over M with minpoly of degree 2.
  have hαI : IsIntegral M α := .of_finite M α
  have hdeg2 : (minpoly M α).natDegree = 2 := by
    have h2 : 2 ≤ (minpoly M α).natDegree := (minpoly.two_le_natDegree_iff hαI).mpr hα
    have hle : (minpoly M α).natDegree ≤ Module.finrank M N := minpoly.natDegree_le α
    omega
  -- minpoly M α = X^2 + aX + b for some a, b in M.
  set a : M := (minpoly M α).coeff 1 with ha_def
  set b : M := (minpoly M α).coeff 0 with hb_def
  have hfm : (minpoly M α).Monic := minpoly.monic hαI
  have hcoeff2 : (minpoly M α).coeff 2 = 1 := by
    have hlc : (minpoly M α).leadingCoeff = 1 := hfm
    rw [Polynomial.leadingCoeff, hdeg2] at hlc
    exact hlc
  -- α² + a α + b = 0.
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
  -- Let β := α + a/2 (completing the square). Then β² = a²/4 - b ∈ M.
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
      have : (α + (algebraMap M N) (a / 2)) ^ 2 =
          α ^ 2 + α * (2 * (algebraMap M N) (a / 2)) + (algebraMap M N) (a / 2) ^ 2 := by ring
      rw [this, half_sq, half_times]; ring
    rw [expand]
    show α ^ 2 + (algebraMap M N) a * α + (algebraMap M N) (a ^ 2 / 4) =
      (algebraMap M N) (a ^ 2 / 4 - b)
    rw [map_sub]
    linear_combination hroot
  -- β ∉ M (else α ∈ M)
  have hβ_ni : β ∉ (algebraMap M N).range := by
    rintro ⟨r, hr⟩
    apply hα
    refine ⟨r - a / 2, ?_⟩
    have hr' : (algebraMap M N) r = α + (algebraMap M N) (a / 2) := hr
    rw [map_sub]
    linear_combination hr'
  -- Now apply isSquare_of_finrank_base_eq_two to M (as a quadratic extension of R).
  -- Wait: isSquare_of_finrank_base_eq_two takes (K : Type*) with [Algebra R K] [finrank R K = 2].
  -- Here K = M, which is IntermediateField R L coerced.
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
  -- |Gal(L/R)| = [L:R]
  have hcard : Nat.card (L ≃ₐ[R] L) = Module.finrank R L := IsGalois.card_aut_eq_finrank R L
  -- 2 is prime
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Take a Sylow 2-subgroup P.
  let P : Sylow 2 (L ≃ₐ[R] L) := Classical.arbitrary _
  -- P is a 2-group, |P| = 2^m for some m.
  obtain ⟨m, hPcard⟩ : ∃ m, Nat.card (P : Subgroup (L ≃ₐ[R] L)) = 2 ^ m :=
    IsPGroup.iff_card.mp P.isPGroup'
  -- [L : fixedField P] = |P| = 2^m.
  have hLFK : Module.finrank (fixedField (P : Subgroup (L ≃ₐ[R] L))) L = 2 ^ m := by
    rw [finrank_fixedField_eq_card, hPcard]
  set M := fixedField (P : Subgroup (L ≃ₐ[R] L)) with hM_def
  -- [M:R] * [L:M] = [L:R]
  have hmul : Module.finrank R M * Module.finrank M L = Module.finrank R L :=
    Module.finrank_mul_finrank R M L
  -- [M:R] = [L:R] / 2^m. It's the index.
  -- Claim: [M:R] is coprime to 2, so odd.
  have hindex_eq : (P : Subgroup (L ≃ₐ[R] L)).index = Module.finrank R M := by
    -- index * card = |G|; |G| = [L:R] = [M:R] * 2^m.
    have h1 : (P : Subgroup (L ≃ₐ[R] L)).index * Nat.card (P : Subgroup (L ≃ₐ[R] L))
        = Nat.card (L ≃ₐ[R] L) := (P : Subgroup (L ≃ₐ[R] L)).index_mul_card
    rw [hcard, ← hmul, hLFK, hPcard] at h1
    have h2m_pos : (0 : ℕ) < 2 ^ m := Nat.pos_of_ne_zero (pow_ne_zero m (by norm_num))
    exact (Nat.eq_of_mul_eq_mul_right h2m_pos h1).symm
  have hMR_odd : Odd (Module.finrank R M) := by
    rw [← hindex_eq]
    have hcoprime : (Nat.card (P : Subgroup (L ≃ₐ[R] L))).Coprime (P : Subgroup (L ≃ₐ[R] L)).index :=
      P.card_coprime_index
    rw [hPcard] at hcoprime
    -- Need: (P.index).Coprime 2, i.e., Odd P.index.
    rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
    · -- m = 0: 2^0 = 1, so coprime is trivial. But 2 may still divide P.index. Use hcard more.
      -- Actually if m = 0, |P| = 1, so P = ⊥, so index = |G| = 2^0 * ... wait.
      -- Actually we know from hindex_eq and hcard that index = finrank R M = |G|/1 = |G|.
      -- Need |G| to be odd. But m is the 2-adic multiplicity in |G|, so m = 0 means 2 ∤ |G|, i.e. |G| odd.
      -- Actually we can't assume multiplicity here. P is just some Sylow, and |P| = 2^0 = 1 means... hmm.
      -- Sylow subgroup of order 1 means 2 doesn't divide |G|. Let's prove this.
      rw [hm0] at hPcard
      simp at hPcard
      -- |P| = 1, so P = ⊥, but P is a Sylow, so 2 ∤ |G|.
      -- Use card_eq_multiplicity to show 2^m = 2^(v_2(|G|)).
      have hmult := P.card_eq_multiplicity
      rw [hm0, pow_zero] at hmult
      -- 1 = 2^factorization(|G|) 2
      have hfact_zero : Nat.factorization (Nat.card (L ≃ₐ[R] L)) 2 = 0 := by
        have := hmult.symm
        -- 2^(factorization |G| 2) = 1
        by_contra hne
        have : 2 ^ Nat.factorization (Nat.card (L ≃ₐ[R] L)) 2 ≥ 2 := by
          calc 2 ^ Nat.factorization (Nat.card (L ≃ₐ[R] L)) 2
              ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hne)
            _ = 2 := by norm_num
        omega
      -- 2 ∤ |G|
      have h2_not_dvd : ¬ 2 ∣ Nat.card (L ≃ₐ[R] L) := by
        rcases Nat.eq_zero_or_pos (Nat.card (L ≃ₐ[R] L)) with h0 | hpos
        · rw [h0]; omega
        · intro hdvd
          have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hpos.ne' hdvd
          omega
      rw [Nat.odd_iff_not_even]
      intro heven
      apply h2_not_dvd
      rw [hindex_eq, hcard]
      exact heven.two_dvd
    · -- m ≥ 1: 2 ∣ 2^m = Nat.card P, and Nat.card P coprime to P.index, so 2 coprime to P.index.
      have h2_dvd_2m : (2 : ℕ) ∣ 2 ^ m := by
        rw [show m = (m - 1) + 1 from by omega, pow_succ]
        exact dvd_mul_left 2 _
      have h2_cop : Nat.Coprime 2 (P : Subgroup (L ≃ₐ[R] L)).index :=
        hcoprime.coprime_dvd_left h2_dvd_2m
      rw [Nat.odd_iff_not_even]
      intro heven
      have : ¬ Nat.Coprime 2 (P : Subgroup (L ≃ₐ[R] L)).index := by
        intro h
        have := h.eq_of_mul_eq_zero_left
        -- Even means 2 ∣ index
        have h2div : 2 ∣ (P : Subgroup (L ≃ₐ[R] L)).index := heven.two_dvd
        rw [Nat.Coprime, Nat.gcd_comm] at h
        have : Nat.gcd (P : Subgroup (L ≃ₐ[R] L)).index 2 = 2 := by
          exact Nat.gcd_eq_right h2div
        omega
      exact this h2_cop
  -- By surjective_algebraMap_of_odd_finrank, [M:R] = 1.
  have hMR_one : Module.finrank R M = 1 := by
    have hsurj := IsRealClosed.surjective_algebraMap_of_odd_finrank R M hMR_odd
    -- If algebraMap R M is surjective, then M = R as algebras, so finrank = 1.
    -- Use the fact that algebraMap bijective implies finrank = 1.
    have hinj := (algebraMap R M).injective
    have hbij : Function.Bijective (algebraMap R M) := ⟨hinj, hsurj⟩
    -- finrank R M = finrank R R = 1
    exact Subalgebra.finrank_eq_one_of_eq_bot (by
      rw [eq_bot_iff]
      intro x _
      obtain ⟨r, hr⟩ := hsurj x
      exact Algebra.mem_bot.mpr ⟨r, hr⟩)
  -- So |G| = 2^m. And Module.finrank R L = 2^m.
  have hLR_pow : Module.finrank R L = 2 ^ m := by
    rw [← hmul, hMR_one, one_mul, hLFK]
  -- Now use the key lemma.
  rcases Nat.lt_or_ge m 2 with hm | hm
  · rcases m with _ | _ | _ <;> rw [hLR_pow] <;> omega
  · exact absurd (not_finrank_eq_pow_two_of_isGalois R L hm hLR_pow).elim (fun h => h.elim)

/-- FTA for real closed fields: any finite extension of R has dimension at most 2. -/
theorem finrank_le_two_of_finiteDimensional'
    (K : Type*) [Field K] [Algebra R K] [FiniteDimensional R K] :
    Module.finrank R K ≤ 2 := by
  -- Embed K into AlgebraicClosure R.
  -- Take L = normal closure of K's image. L/R is Galois. [K:R] ≤ [L:R] ≤ 2.
  have : Algebra.IsAlgebraic R K := Algebra.IsIntegral.isAlgebraic
  -- Get K →ₐ[R] AlgebraicClosure R.
  let φ : K →ₐ[R] AlgebraicClosure R := IsAlgClosed.lift
  have hφ_inj : Function.Injective φ := φ.injective
  -- Image K' = φ.fieldRange
  set K' : IntermediateField R (AlgebraicClosure R) := φ.fieldRange with hK'_def
  -- Normal closure of K' in AlgebraicClosure R.
  set L : IntermediateField R (AlgebraicClosure R) := normalClosure R K' (AlgebraicClosure R) with hL_def
  -- L is finite dimensional
  haveI : FiniteDimensional R K' := φ.toLinearMap.finiteDimensional_range
  haveI : FiniteDimensional R L := normalClosure.is_finiteDimensional R K' (AlgebraicClosure R)
  -- L/R is Galois (char 0 → separable; and normal by construction).
  haveI : CharZero R := inferInstance
  haveI : CharZero (AlgebraicClosure R) := charZero_of_injective_algebraMap (algebraMap R _).injective
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap R L).injective
  haveI : Algebra.IsSeparable R L := by
    -- L is a subfield of AlgebraicClosure R, so is algebraic over R.
    have : Algebra.IsAlgebraic R L := Algebra.IsAlgebraic.of_isIntegral
    infer_instance
  haveI : Normal R L := normalClosure.normal R K' (AlgebraicClosure R)
  haveI : IsGalois R L := ⟨⟩
  -- K is R-alg isomorphic to K' ⊆ L, so [K:R] = [K':R] ≤ [L:R].
  have hKK' : Module.finrank R K = Module.finrank R K' := by
    -- Use AlgEquiv from AlgHom injective
    have e : K ≃ₐ[R] K' := AlgEquiv.ofInjectiveField φ
    exact (LinearEquiv.finrank_eq e.toLinearEquiv)
  have hK'_le_L : K' ≤ L := IntermediateField.le_normalClosure K'
  have hKpL : Module.finrank R K ≤ Module.finrank R L := by
    rw [hKK']
    -- K' ⊆ L, so finrank R K' ≤ finrank R L.
    have := Submodule.finrank_mono (M := L.toSubalgebra.toSubmodule)
      (N := K'.toSubalgebra.toSubmodule)
    sorry
  sorry

end IsRealClosed
