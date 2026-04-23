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

/-- If an ordered field `R` has no nontrivial ordered algebraic extension, then it is
real closed. -/
theorem of_bijective_algebraMap_of_isOrderedAlgebra
    (h : ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
         [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K],
         Function.Bijective (algebraMap R K)) :
    IsRealClosed R := by
  sorry

end IsRealClosed
