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
    -- Then span {1, α} = span {1} = range algebraMap = ⊤, so algebraMap is surjective.
    -- Since algebraMap is also injective (field hom from F to nonzero ring), it is bijective.
    -- Use the inverse as π.
    obtain ⟨c, hc⟩ := hα_range
    have hspan1 : Submodule.span F ({1} : Set K) = ⊤ := by
      have : (1 : K) ∈ Submodule.span F ({1, α} : Set K) := by
        apply Submodule.subset_span
        simp
      have hα_in : α ∈ Submodule.span F ({1} : Set K) := by
        rw [Submodule.mem_span_singleton]
        refine ⟨c, ?_⟩
        rw [← hc, Algebra.smul_def, mul_one]
      rw [← hspan]
      apply le_antisymm
      · exact Submodule.span_mono (by simp)
      · rw [Submodule.span_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact Submodule.subset_span rfl
        · exact hα_in
    -- Every element of K is a scalar multiple of 1.
    have hsurj : Function.Surjective (algebraMap F K) := by
      intro x
      have hx : x ∈ Submodule.span F ({1} : Set K) := hspan1 ▸ Submodule.mem_top
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨r, hr⟩ := hx
      exact ⟨r, by rw [Algebra.algebraMap_eq_smul_one]; exact hr⟩
    have hinj : Function.Injective (algebraMap F K) :=
      (algebraMap F K).injective
    have hbij : Function.Bijective (algebraMap F K) := ⟨hinj, hsurj⟩
    -- The linear map `F → K` via `algebraMap` is a linear equiv; take its inverse.
    let e : F ≃ₗ[F] K := LinearEquiv.ofBijective (Algebra.linearMap F K) hbij
    refine exists_isOrderedAlgebra_of_linearProj_nonneg_sq e.symm.toLinearMap ?_ ?_
    · -- e.symm 1 = 1
      have : e 1 = 1 := by
        show Algebra.linearMap F K 1 = 1
        simp
      rw [← this, LinearEquiv.symm_apply_apply]
    · -- e.symm (x^2) ≥ 0
      intro x
      -- Let r = e.symm x, so x = e r = algebraMap F K r.
      set r := e.symm x with hr
      have hxr : x = algebraMap F K r := by
        show x = Algebra.linearMap F K r
        rw [hr]
        exact (LinearEquiv.apply_symm_apply e x).symm
      -- Then x^2 = algebraMap F K (r^2), so e.symm (x^2) = r^2 ≥ 0.
      have hx2 : x^2 = algebraMap F K (r^2) := by
        rw [hxr, ← map_pow]
      have : e.symm (x^2) = r^2 := by
        rw [hx2]
        show e.symm (Algebra.linearMap F K (r^2)) = r^2
        change e.symm (e (r^2)) = r^2
        exact LinearEquiv.symm_apply_apply e _
      rw [LinearEquiv.coe_coe, this]
      exact sq_nonneg _
  · -- Non-degenerate case: {1, α} is linearly independent.
    push_neg at hα_range
    -- hα_range : ∀ c : F, algebraMap F K c ≠ α
    have hli_smul : ∀ c : F, c • (1 : K) ≠ α := by
      intro c
      rw [Algebra.smul_def, mul_one]
      exact hα_range c
    have hv : LinearIndependent F ![(1 : K), α] := by
      rw [LinearIndependent.pair_iff' one_ne_zero]
      exact hli_smul
    have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : K), α]) := by
      rw [show Set.range ![(1 : K), α] = {(1 : K), α} by
        rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
          Set.union_singleton]]
      rw [hspan]
    let b : Basis (Fin 2) F K := Basis.mk hv hsp
    have hb0 : b 0 = 1 := by simp [b]
    have hb1 : b 1 = α := by simp [b]
    refine exists_isOrderedAlgebra_of_linearProj_nonneg_sq (b.coord 0) ?_ ?_
    · -- π 1 = 1
      rw [← hb0]
      simp [Basis.coord_apply, Basis.repr_self]
    · intro x
      -- Expand x in the basis.
      have hx_eq : x = b.coord 0 x • (b 0 : K) + b.coord 1 x • (b 1 : K) := by
        conv_lhs => rw [← Basis.sum_repr b x]
        rw [Fin.sum_univ_two]
        simp [Basis.coord_apply]
      rw [hb0, hb1] at hx_eq
      set c := b.coord 0 x with hc_def
      set d := b.coord 1 x with hd_def
      -- x = c • 1 + d • α = c + d·α (via algebraMap)
      -- x² = c² + 2cd·α + d²·α² = (c² + d²·a) + 2cd·α
      have hx_sq : x^2 = (c^2 + d^2 * a) • (1 : K) + (2 * c * d) • α := by
        have h_am : ∀ r : F, r • (1 : K) = algebraMap F K r := fun r ↦ by
          rw [Algebra.algebraMap_eq_smul_one]
        have h_smul_eq : ∀ (r : F) (y : K), r • y = algebraMap F K r * y := fun r y ↦
          (Algebra.smul_def r y)
        rw [show x = c • (1 : K) + d • α from hx_eq]
        have : (c • (1 : K) + d • α)^2 = c^2 • (1 : K) + 2 • (c * d) • α + d^2 • α^2 := by
          simp_rw [h_smul_eq]
          ring
        rw [this, hα]
        rw [show algebraMap F K a = a • (1 : K) from (h_am a).symm]
        rw [show (d^2 • (a • (1 : K)) : K) = (d^2 * a) • (1 : K) from by rw [smul_smul]]
        rw [show (2 • (c * d) • α : K) = (2 * c * d) • α from by
          rw [smul_smul]; congr 1; simp [two_smul, two_mul]]
        rw [add_assoc]
        rw [show (d^2 * a) • (1 : K) + (2 * c * d) • α
              = (2 * c * d) • α + (d^2 * a) • (1 : K) from add_comm _ _]
        rw [← add_assoc]
        rw [show c^2 • (1 : K) + (d^2 * a) • (1 : K) = (c^2 + d^2 * a) • (1 : K) from
          (add_smul _ _ _).symm]
      -- Now compute (b.coord 0) (x^2) = c^2 + d^2 * a
      have hπ_x_sq : b.coord 0 (x^2) = c^2 + d^2 * a := by
        rw [hx_sq]
        rw [map_add]
        rw [map_smul, map_smul]
        rw [show (1 : K) = b 0 from hb0.symm, show α = b 1 from hb1.symm]
        rw [Basis.mk_coord_apply_eq]
        rw [Basis.mk_coord_apply_ne (show (1 : Fin 2) ≠ 0 from by decide)]
        simp
      rw [hπ_x_sq]
      have h1 : 0 ≤ c^2 := sq_nonneg c
      have h2 : 0 ≤ d^2 * a := mul_nonneg (sq_nonneg d) ha
      linarith

theorem exists_isOrderedAlgebra_of_odd_finrank
    [FiniteDimensional F K] (hodd : Odd (Module.finrank F K)) :
    ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K := sorry

end Field
