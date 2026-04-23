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

theorem exists_isOrderedAlgebra_of_adjoin_sqrt
    {a : F} (ha : 0 ≤ a) {α : K} (hα : α ^ 2 = algebraMap F K a)
    (hspan : Submodule.span F {(1 : K), α} = ⊤) :
    ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K := by
  sorry

/-- Any odd-degree finite field extension `K/F` of an ordered field `F` admits an ordering
making it ordered.

The proof idea: by `Field.exists_isOrderedAlgebra_iff_neg_one_notMem_span_nonneg_isSquare`, we
need to show `-1` is not in the span of squares of `K` over the non-negative cone in `F`.
By the primitive element theorem (applicable because ordered fields have characteristic 0, so
the extension is separable), we may write `K = F(α)` with minpoly `f` of degree `n = [K:F]`
odd. Identifying `K ≃ F[X]/(f)`, the congruence `∑ aᵢ gᵢ² ≡ -1 (mod f)` would need to hold
for some non-negative `aᵢ ∈ F` and polynomials `gᵢ ∈ F[X]`. Strong induction on `n`: if the
congruence holds, rearranging gives `∑ aᵢ gᵢ² + 1 = h·f` for some `h ∈ F[X]`. Counting the
`(2d)`-th coefficient (where `d = maxᵢ deg gᵢ`) shows `deg h = 2d - deg f` is odd, so `h`
has an odd-degree irreducible factor `h̃` with `deg h̃ ≤ deg h < deg f`. Then
`∑ aᵢ gᵢ² ≡ -1 (mod h̃)` would contradict the inductive hypothesis applied to `F[X]/(h̃)`.
-/
theorem exists_isOrderedAlgebra_of_odd_finrank
    [FiniteDimensional F K] (hodd : Odd (Module.finrank F K)) :
    ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K := by
  sorry

end Field
