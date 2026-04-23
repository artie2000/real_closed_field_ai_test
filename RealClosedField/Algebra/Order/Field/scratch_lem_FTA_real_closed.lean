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

/-- Auxiliary: over a real closed field, any finite Galois extension has dimension at most 2. -/
private theorem finrank_le_two_of_isGalois
    (L : Type*) [Field L] [Algebra R L] [FiniteDimensional R L] [IsGalois R L] :
    Module.finrank R L ≤ 2 := by
  -- |Gal(L/R)| = [L:R]
  have hcard : Nat.card (L ≃ₐ[R] L) = Module.finrank R L := IsGalois.card_aut_eq_finrank R L
  -- 2 is prime
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Take a Sylow 2-subgroup
  let P : Sylow 2 (L ≃ₐ[R] L) := Classical.arbitrary _
  -- P is a 2-group, so |P| = 2^m
  obtain ⟨m, hPcard⟩ : ∃ m, Nat.card (P : Subgroup (L ≃ₐ[R] L)) = 2 ^ m :=
    IsPGroup.iff_card.mp P.isPGroup'
  -- The fixed field of P has dimension equal to the index [G : P] which is odd.
  have hFK_finrank : Module.finrank R (fixedField (P : Subgroup (L ≃ₐ[R] L))) * (2 ^ m) =
      Module.finrank R L := by
    rw [← hPcard]
    rw [show Nat.card (P : Subgroup (L ≃ₐ[R] L)) = Nat.card (↥(P : Subgroup (L ≃ₐ[R] L))) from rfl]
    rw [← finrank_fixedField_eq_card (P : Subgroup (L ≃ₐ[R] L))]
    exact Module.finrank_mul_finrank R _ L
  -- The index is odd (coprime to 2).
  have hP_index_odd : Odd (Module.finrank R (fixedField (P : Subgroup (L ≃ₐ[R] L)))) := by
    have hcoprime : (Nat.card (P : Subgroup (L ≃ₐ[R] L))).Coprime (P : Subgroup (L ≃ₐ[R] L)).index :=
      P.card_coprime_index
    -- index * card = card G (= finrank R L = 2^m * (index))
    have hindex_eq :
        (P : Subgroup (L ≃ₐ[R] L)).index = Module.finrank R (fixedField (P : Subgroup (L ≃ₐ[R] L))) := by
      have h1 : (P : Subgroup (L ≃ₐ[R] L)).index * Nat.card (P : Subgroup (L ≃ₐ[R] L)) = Nat.card (L ≃ₐ[R] L) :=
        (P : Subgroup (L ≃ₐ[R] L)).index_mul_card
      rw [hcard, ← hFK_finrank, hPcard] at h1
      have h2m_pos : (0 : ℕ) < 2 ^ m := Nat.pos_of_ne_zero (pow_ne_zero m (by norm_num))
      -- a * 2^m = b * 2^m implies a = b
      exact Nat.eq_of_mul_eq_mul_right h2m_pos h1
    rw [← hindex_eq]
    -- coprime to 2 implies not divisible by 2, but index is a natural number, so odd.
    rw [hPcard] at hcoprime
    -- Nat.Coprime (2^m) n → ¬(2 ∣ n)  hence Odd n (for n positive)
    rw [Nat.Coprime, Nat.gcd_comm] at hcoprime
    -- hmm need odd.
    have hne2 : ¬ (2 ∣ (P : Subgroup (L ≃ₐ[R] L)).index) := by
      intro hdvd
      have : Nat.gcd (P : Subgroup (L ≃ₐ[R] L)).index (2 ^ m) = 2 ^ m * _ := sorry
      sorry
    exact Nat.odd_iff_not_even.mpr (fun heven => hne2 heven.two_dvd)
  sorry

/-- FTA for real closed fields: any finite extension of R has dimension at most 2. -/
theorem finrank_le_two_of_finiteDimensional'
    (K : Type*) [Field K] [Algebra R K] [FiniteDimensional R K] :
    Module.finrank R K ≤ 2 := by
  sorry

end IsRealClosed
