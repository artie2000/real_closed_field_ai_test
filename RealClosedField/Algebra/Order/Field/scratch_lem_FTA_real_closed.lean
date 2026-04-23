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
  -- G = Gal(L/R)
  set G := (L ≃ₐ[R] L)
  -- |G| = [L:R]
  have hcard : Nat.card G = Module.finrank R L := IsGalois.card_aut_eq_finrank R L
  -- Find a Sylow 2-subgroup; its index is odd.
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Finite G
  have hfin : Finite G := AlgEquiv.fintype R L |>.finite
  -- Sylow 2-subgroup
  let P : Sylow 2 G := Classical.arbitrary _
  have hPindex_coprime : (Nat.card P).Coprime P.1.index := P.card_coprime_index
  -- P is a 2-group, so Nat.card P = 2^m for some m
  obtain ⟨m, hPcard⟩ : ∃ m, Nat.card (P : Subgroup G) = 2 ^ m := IsPGroup.iff_card.mp P.isPGroup'
  -- P.index is coprime to 2, hence odd
  have hP_index_odd : Odd P.1.index := by
    rw [Nat.odd_iff_not_even, ← Nat.Prime.dvd_iff_not_coprime Nat.prime_two]
    · intro hdvd
      have : (Nat.card P).Coprime P.1.index := hPindex_coprime
      rw [hPcard] at this
      have hdvd' : 2 ∣ 2 ^ m := by
        rcases m with _ | m
        · simp at hPcard
          -- Nat.card P = 1, but P is a Sylow subgroup of a nontrivial group? Could be trivial.
          -- Actually we don't need this.
          exact hdvd.elim (fun _ => False.elim (by omega))
        · exact ⟨2 ^ m, by ring⟩
      exact absurd (Nat.Coprime.symm this).eq_of_mul_eq_zero_left sorry
    · exact hdvd
  sorry

/-- FTA for real closed fields: any finite extension of R has dimension at most 2. -/
theorem finrank_le_two_of_finiteDimensional'
    (K : Type*) [Field K] [Algebra R K] [FiniteDimensional R K] :
    Module.finrank R K ≤ 2 := by
  sorry

end IsRealClosed
