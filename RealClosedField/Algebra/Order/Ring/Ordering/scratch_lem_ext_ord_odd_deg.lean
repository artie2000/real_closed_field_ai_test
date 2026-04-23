/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib
import RealClosedField.Algebra.Order.Algebra

/-!
# Sufficient conditions for an ordered field extension
-/

variable {F K : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [Field K] [Algebra F K]

namespace Field

theorem exists_isOrderedAlgebra_of_linearProj_nonneg_sq
    (π : K →ₗ[F] F) (hπ1 : π 1 = 1) (hπ : ∀ x : K, 0 ≤ π (x ^ 2)) :
    ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K := by
  rw [Field.exists_isOrderedAlgebra_iff_neg_one_notMem_span_nonneg_isSquare]
  intro h
  have key : ∀ y ∈ Submodule.span (Subsemiring.nonneg F) {x : K | IsSquare x}, 0 ≤ π y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      have hww : w * w = w ^ 2 := by ring
      rw [hww]
      exact hπ w
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; linarith
    | smul r x _ hx =>
      rw [LinearMap.map_smul_of_tower, Subsemiring.smul_def, smul_eq_mul]
      exact mul_nonneg r.2 hx
  have h1 := key (-1) h
  rw [map_neg, hπ1] at h1
  linarith

/-!
## Odd-degree extension

We now prove that any odd-degree finite field extension `K/F` of an ordered field `F`
admits an ordering making it ordered. The idea is to prove by strong induction on the
degree that `-1` is not in the span of squares of `K` over the non-negative cone in `F`.
-/

/-- Helper: the statement we'll prove by strong induction on `n`. -/
private def OddDegreeStatement (n : ℕ) : Prop :=
    ∀ (F K : Type) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
      [Field K] [Algebra F K] [FiniteDimensional F K],
      Module.finrank F K = n → Odd n →
      ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K

-- The key polynomial-theoretic lemma we will use.
-- Setting: F is an ordered field, and suppose -1 ∈ span_{F≥0}(squares(K)) where
-- K = F(α) with minpoly f of degree n (odd, > 1). We derive a polynomial h of odd degree
-- strictly less than n such that the same property holds in F[X]/(h).

/-- Any odd-degree finite field extension `K/F` of an ordered field `F` admits an ordering
making it ordered. -/
theorem exists_isOrderedAlgebra_of_odd_finrank
    [FiniteDimensional F K] (hodd : Odd (Module.finrank F K)) :
    ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K := by
  sorry

end Field
