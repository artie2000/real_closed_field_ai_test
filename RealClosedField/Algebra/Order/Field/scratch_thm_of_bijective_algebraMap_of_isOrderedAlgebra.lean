/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.Algebra.Order.Algebra
import RealClosedField.Algebra.Order.Field.IsSemireal
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.TFAE

open Polynomial

namespace IsRealClosed

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A polynomial of the form `X^2 - C a` with `a` non-negative and not a square
is irreducible in `R[X]`. -/
private lemma irreducible_X_sq_sub_C_of_not_isSquare
    {a : R} (hsq : ¬ IsSquare a) : Irreducible (X ^ 2 - C a : R[X]) := by
  have hmonic : (X ^ 2 - C a : R[X]).Monic := monic_X_pow_sub_C a (by decide)
  refine (Polynomial.Monic.irreducible_iff_natDegree' hmonic).mpr ⟨?_, ?_⟩
  · rw [natDegree_X_pow_sub_C]; decide
  · rintro g₁ g₂ hg_prod ⟨hg1_pos, hg1_le⟩
    -- g1.natDegree > 0 and g1.natDegree ≤ 1
    rw [natDegree_X_pow_sub_C] at hg1_le
    -- Thus g1.natDegree = 1
    interval_cases g₁.natDegree
    -- So g1 is of degree 1, has a root, contradicting non-square
    have hne : (X ^ 2 - C a : R[X]) ≠ 0 := hmonic.ne_zero
    have hg1_ne : g₁ ≠ 0 := fun he => by rw [he, zero_mul] at hg_prod; exact hne hg_prod.symm
    set b := g₁.coeff 1
    set c := g₁.coeff 0
    have hb_ne : b ≠ 0 := by
      intro he
      have : g₁.leadingCoeff = 0 := by
        show g₁.coeff g₁.natDegree = 0
        rw [show g₁.natDegree = 1 by assumption]; exact he
      exact hg1_ne (leadingCoeff_eq_zero.mp this)
    have hg1_eq : g₁ = C b * X + C c := by
      conv_lhs => rw [g₁.as_sum_range_C_mul_X_pow, show g₁.natDegree = 1 by assumption]
      simp [Finset.sum_range_succ]
      ring
    -- So -c/b is a root of g₁, hence of p
    have hroot : (X ^ 2 - C a : R[X]).IsRoot (-c / b) := by
      rw [hg_prod]
      simp [IsRoot, hg1_eq, hb_ne]
      field_simp
    simp [IsRoot, sub_eq_zero] at hroot
    exact hsq ⟨-c / b, by linear_combination hroot.symm⟩

/-- If an ordered field `R` has no nontrivial ordered algebraic extension, then it is
real closed. -/
theorem of_bijective_algebraMap_of_isOrderedAlgebra
    (h : ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
         [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K],
         Function.Bijective (algebraMap R K)) :
    IsRealClosed R := by
  sorry

end IsRealClosed
