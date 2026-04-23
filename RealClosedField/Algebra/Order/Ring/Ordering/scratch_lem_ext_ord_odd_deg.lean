/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import RealClosedField.Algebra.Order.Algebra

/-!
# Sufficient conditions for an ordered field extension

Let `F` be an ordered field and `K/F` a field extension. We give sufficient
conditions for `K` to admit a linear order making `K/F` ordered.

## Main results

* `Field.exists_isOrderedAlgebra_of_linearProj_nonneg_sq`: if there is an
  `F`-linear functional `π : K → F` sending every square to a nonneg value, then
  `K` admits an ordering making `K/F` ordered.
* `Field.exists_isOrderedAlgebra_of_adjoin_sqrt`: if `a ∈ F` is nonneg and not a
  square, then `F(√a)` admits an ordering making `F(√a)/F` ordered.
* `Field.exists_isOrderedAlgebra_of_odd_finrank`: any odd-degree finite field
  extension of an ordered field admits an ordering making it ordered.
-/

variable {F K : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [Field K] [Algebra F K]

namespace Field

/-- If there is an `F`-linear functional `π : K → F` with `π(x^2) ≥ 0` for all `x`, then
`K` admits an ordering making `K/F` ordered. -/
theorem exists_isOrderedAlgebra_of_linearProj_nonneg_sq
    (π : K →ₗ[F] F) (hπ : ∀ x : K, 0 ≤ π (x ^ 2)) :
    ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K := sorry

/-- If `a ∈ F` is nonneg (and not a square), then `F(√a)` admits an ordering making
`F(√a)/F` ordered. We state this abstractly: for any quadratic extension `K/F` whose
defining element `α` satisfies `α^2 = algebraMap F K a`, with `a ≥ 0`, there is an
ordering on `K` making `K/F` ordered. -/
theorem exists_isOrderedAlgebra_of_adjoin_sqrt
    {a : F} (ha : 0 ≤ a) {α : K} (hα : α ^ 2 = algebraMap F K a)
    (hspan : Submodule.span F {(1 : K), α} = ⊤) :
    ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K := sorry

/-- Any odd-degree finite field extension `K/F` of an ordered field `F` admits an ordering
making it ordered. -/
theorem exists_isOrderedAlgebra_of_odd_finrank
    [FiniteDimensional F K] (hodd : Odd (Module.finrank F K)) :
    ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K := sorry

end Field
