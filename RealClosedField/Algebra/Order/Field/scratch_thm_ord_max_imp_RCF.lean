/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.TFAE
import RealClosedField.Algebra.Order.Algebra

/-!
# Scratch: thm:ord_max_imp_RCF
-/

namespace IsRealClosed

variable (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `R` has no nontrivial ordered algebraic extension: for every field `K` that is an
algebraic extension of `R` and admits a linear order making it a strictly ordered ring
with `R → K` monotone, the structure map `R → K` is surjective. -/
def NoNontrivialOrderedAlgExt : Prop :=
  ∀ (K : Type*) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K],
    (∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule R K) →
    Function.Surjective (algebraMap R K)

/-- If `R` is an ordered field with no nontrivial ordered algebraic extensions, then every
non-negative element of `R` is a square in `R`. -/
private lemma isSquare_of_nonneg_of_noNontrivialOrderedAlgExt
    (h : NoNontrivialOrderedAlgExt R) {x : R} (hx : 0 ≤ x) : IsSquare x := sorry

/-- If `R` is an ordered field with no nontrivial ordered algebraic extensions, then every
odd-degree polynomial in `R[X]` has a root in `R`. -/
private lemma exists_isRoot_of_odd_natDegree_of_noNontrivialOrderedAlgExt
    (h : NoNontrivialOrderedAlgExt R) {f : Polynomial R}
    (hodd : Odd f.natDegree) : ∃ x, f.IsRoot x := sorry

/-- An ordered field with no nontrivial ordered algebraic extensions is real closed. -/
theorem isRealClosed_of_noNontrivialOrderedAlgExt (h : NoNontrivialOrderedAlgExt R) :
    IsRealClosed R :=
  IsRealClosed.of_linearOrderedField
    (isSquare_of_nonneg_of_noNontrivialOrderedAlgExt R h)
    (exists_isRoot_of_odd_natDegree_of_noNontrivialOrderedAlgExt R h)

end IsRealClosed
