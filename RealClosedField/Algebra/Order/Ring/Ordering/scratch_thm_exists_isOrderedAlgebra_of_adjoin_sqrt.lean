/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import RealClosedField.Algebra.Order.Algebra

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
  -- Case split on whether α is in the range of `algebraMap F K`.
  by_cases hα_range : ∃ c : F, algebraMap F K c = α
  · -- Degenerate case: α = algebraMap F K c for some c.
    -- Then algebraMap is surjective (since span {1, α} = ⊤ and both are in the range).
    -- Use `Algebra.linearMap`⁻¹ as π.
    obtain ⟨c, hc⟩ := hα_range
    have hsurj : Function.Surjective (algebraMap F K) := by
      intro x
      have hx : x ∈ (⊤ : Submodule F K) := Submodule.mem_top
      rw [← hspan, Submodule.mem_span_pair] at hx
      obtain ⟨r, s, hrs⟩ := hx
      refine ⟨r + s * c, ?_⟩
      rw [map_add, map_mul, hc, ← hrs, Algebra.smul_def, Algebra.smul_def, mul_one]
    have hbij : Function.Bijective (algebraMap F K) :=
      ⟨(algebraMap F K).injective, hsurj⟩
    let e : F ≃ₗ[F] K := LinearEquiv.ofBijective (Algebra.linearMap F K) hbij
    refine exists_isOrderedAlgebra_of_linearProj_nonneg_sq e.symm.toLinearMap ?_ ?_
    · -- e.symm 1 = 1
      have h_e1 : e 1 = 1 := by
        show Algebra.linearMap F K 1 = 1
        simp
      calc e.symm.toLinearMap 1 = e.symm 1 := rfl
        _ = e.symm (e 1) := by rw [h_e1]
        _ = 1 := e.left_inv 1
    · intro x
      -- Let r = e.symm x. Then x = e r = algebraMap F K r, so x^2 = algebraMap F K (r^2).
      set r := e.symm x with hr_def
      have hxr : x = algebraMap F K r := by
        have : x = e r := (e.right_inv x).symm
        rw [this]; rfl
      have : e.symm (x^2) = r^2 := by
        have hx2 : x^2 = e (r^2) := by
          show x^2 = Algebra.linearMap F K (r^2)
          rw [hxr, ← map_pow]; rfl
        rw [hx2, e.left_inv]
      show 0 ≤ e.symm (x^2)
      rw [this]
      exact sq_nonneg _
  · -- Non-degenerate case: {1, α} is linearly independent.
    push_neg at hα_range
    have hv : LinearIndependent F ![(1 : K), α] := by
      rw [LinearIndependent.pair_iff' one_ne_zero]
      intro t
      rw [Algebra.smul_def, mul_one]
      exact hα_range t
    have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : K), α]) := by
      rw [show Set.range ![(1 : K), α] = {(1 : K), α} by
        rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
          Set.union_singleton]]
      rw [hspan]
    let b : Basis (Fin 2) F K := Basis.mk hv hsp
    have hb0 : b 0 = 1 := by simp [b]
    have hb1 : b 1 = α := by simp [b]
    refine exists_isOrderedAlgebra_of_linearProj_nonneg_sq (b.coord 0) ?_ ?_
    · rw [← hb0]
      exact Basis.mk_coord_apply_eq 0
    · intro x
      set c := b.coord 0 x with hc_def
      set d := b.coord 1 x with hd_def
      -- Expand x in the basis.
      have hx_eq : x = c • (1 : K) + d • α := by
        have : ∑ i, b.repr x i • b i = x := Basis.sum_repr b x
        rw [Fin.sum_univ_two] at this
        rw [hb0, hb1] at this
        have hc_eq : c = b.repr x 0 := rfl
        have hd_eq : d = b.repr x 1 := rfl
        rw [hc_eq, hd_eq]
        exact this.symm
      -- Compute x^2.
      have hx_sq : x^2 = (c^2 + d^2 * a) • (1 : K) + (2 * c * d) • α := by
        rw [hx_eq]
        have h_sm : ∀ (r : F) (y : K), r • y = algebraMap F K r * y :=
          fun r y ↦ Algebra.smul_def r y
        have h_am : algebraMap F K a = a • (1 : K) := (Algebra.algebraMap_eq_smul_one a)
        have expand : (c • (1 : K) + d • α)^2
            = c^2 • (1 : K) + (2 * c * d) • α + d^2 • α^2 := by
          simp_rw [h_sm]
          ring
        rw [expand, hα, h_am]
        rw [show (d^2 • (a • (1 : K)) : K) = (d^2 * a) • (1 : K) from by rw [smul_smul]]
        rw [add_assoc, add_comm ((2 * c * d) • α) _, ← add_assoc]
        congr 1
        rw [← add_smul]
      -- Compute π(x^2).
      have hπ_x_sq : b.coord 0 (x^2) = c^2 + d^2 * a := by
        rw [hx_sq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        rw [show (1 : K) = b 0 from hb0.symm, show α = b 1 from hb1.symm]
        rw [Basis.mk_coord_apply_eq 0]
        rw [Basis.mk_coord_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
        ring
      show 0 ≤ b.coord 0 (x^2)
      rw [hπ_x_sq]
      have h1 : 0 ≤ c^2 := sq_nonneg c
      have h2 : 0 ≤ d^2 * a := mul_nonneg (sq_nonneg d) ha
      linarith

theorem exists_isOrderedAlgebra_of_odd_finrank
    [FiniteDimensional F K] (hodd : Odd (Module.finrank F K)) :
    ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K := sorry

end Field
