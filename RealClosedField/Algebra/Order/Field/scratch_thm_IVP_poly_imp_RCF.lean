/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.Algebra.Order.Algebra
import RealClosedField.Algebra.Order.Field.IsSemireal
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Tactic.TFAE

open Polynomial

/-!
# TFAE characterisation of real closed fields among ordered fields

This file records the equivalence between three characterisations of real closed fields
over an ordered field `R`:

1. `R` is real closed.
2. `R` is maximal among ordered algebraic extensions: every algebraic extension of `R`
   which is itself an ordered algebra over `R` is isomorphic to `R`.
3. Polynomials over `R` satisfy the intermediate value property.

The main result is `IsRealClosed.tfae_ord`.
-/

namespace IsRealClosed

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Polynomials over a real closed field satisfy the intermediate value property. -/
theorem exists_isRoot_of_nonpos_of_nonneg [IsRealClosed R]
    {f : R[X]} {a b : R} (hab : a ≤ b) (ha : f.eval a ≤ 0) (hb : 0 ≤ f.eval b) :
    ∃ c ∈ Set.Icc a b, f.IsRoot c := by
  sorry

/-- If polynomials over an ordered field `R` satisfy the intermediate value property,
then `R` is real closed. -/
theorem of_ivp
    (h : ∀ (f : R[X]) (a b : R), a ≤ b → f.eval a ≤ 0 → 0 ≤ f.eval b →
         ∃ c ∈ Set.Icc a b, f.IsRoot c) :
    IsRealClosed R := by
  refine IsRealClosed.of_linearOrderedField ?_ ?_
  · -- isSquare_of_nonneg
    intro x hx
    have ha : (X^2 - C x).eval 0 ≤ 0 := by simp
    have hb : 0 ≤ (X^2 - C x).eval (x + 1) := by
      simp only [eval_sub, eval_pow, eval_X, eval_C]
      nlinarith [sq_nonneg x, sq_nonneg (x+1), hx]
    have hab : (0 : R) ≤ x + 1 := by linarith
    obtain ⟨c, _, hc⟩ := h (X^2 - C x) 0 (x + 1) hab ha hb
    have : c^2 = x := by
      have := hc
      simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at this
      linarith
    exact ⟨c, by linarith [sq c, this]⟩
  · -- exists_isRoot_of_odd_natDegree
    sorry

/-- A real closed field has no nontrivial ordered algebraic extension: if `K` is an
algebraic extension of the real closed field `R` and `K` can be ordered compatibly with
the order on `R`, then the embedding `R → K` is a bijection. -/
theorem bijective_algebraMap_of_isOrderedAlgebra [IsRealClosed R]
    (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
    [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K] :
    Function.Bijective (algebraMap R K) := by
  sorry

/-- If an ordered field `R` has no nontrivial ordered algebraic extension, then it is
real closed. -/
theorem of_bijective_algebraMap_of_isOrderedAlgebra
    (h : ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
         [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K],
         Function.Bijective (algebraMap R K)) :
    IsRealClosed R := by
  sorry

variable (R) in
/-- Characterisation of real closed fields among ordered fields. -/
theorem tfae_ord :
    List.TFAE [
      IsRealClosed R,
      ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
        [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K],
        Function.Bijective (algebraMap R K),
      ∀ (f : R[X]) (a b : R), a ≤ b → f.eval a ≤ 0 → 0 ≤ f.eval b →
        ∃ c ∈ Set.Icc a b, f.IsRoot c] := by
  tfae_have 1 → 2 := by
    intro _ K _ _ _ _ _ _
    exact bijective_algebraMap_of_isOrderedAlgebra K
  tfae_have 2 → 1 := of_bijective_algebraMap_of_isOrderedAlgebra
  tfae_have 1 → 3 := by
    intro _ f a b hab ha hb
    exact exists_isRoot_of_nonpos_of_nonneg hab ha hb
  tfae_have 3 → 1 := of_ivp
  tfae_finish

end IsRealClosed
