/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Module.Basis.Basic
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

/-- If there is an `F`-linear functional `π : K → F` with `π 1 = 1` and `π(x^2) ≥ 0` for all `x`,
then `K` admits an ordering making `K/F` ordered. -/
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

/-- If `a ∈ F` is nonneg (and not a square), then `F(√a)` admits an ordering making
`F(√a)/F` ordered. We state this abstractly: for any quadratic extension `K/F` whose
defining element `α` satisfies `α^2 = algebraMap F K a`, with `a ≥ 0`, there is an
ordering on `K` making `K/F` ordered. -/
theorem exists_isOrderedAlgebra_of_adjoin_sqrt
    {a : F} (ha : 0 ≤ a) {α : K} (hα : α ^ 2 = algebraMap F K a)
    (hspan : Submodule.span F {(1 : K), α} = ⊤) :
    ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K := by
  by_cases hα_range : ∃ c : F, algebraMap F K c = α
  · obtain ⟨c, hc⟩ := hα_range
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
    have he_apply : ∀ r : F, e r = algebraMap F K r := fun _ => rfl
    refine exists_isOrderedAlgebra_of_linearProj_nonneg_sq e.symm.toLinearMap ?_ ?_
    · show e.symm 1 = 1
      have h1 : e 1 = 1 := by rw [he_apply]; exact map_one _
      rw [← h1, e.symm_apply_apply]
    · intro x
      show 0 ≤ e.symm (x ^ 2)
      set r := e.symm x with hr
      have hxr : x = algebraMap F K r := by
        have h_er : e r = x := e.apply_symm_apply x
        rw [he_apply] at h_er
        exact h_er.symm
      have hx2 : x ^ 2 = algebraMap F K (r ^ 2) := by rw [hxr, ← map_pow]
      have hesx : e.symm (x ^ 2) = r ^ 2 := by
        rw [hx2, ← he_apply, e.symm_apply_apply]
      rw [hesx]
      exact sq_nonneg _
  · push_neg at hα_range
    have hv : LinearIndependent F ![(1 : K), α] := by
      rw [LinearIndependent.pair_iff' one_ne_zero]
      intro t
      rw [Algebra.smul_def, mul_one]
      exact hα_range t
    have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : K), α]) := by
      rw [← hspan]
      refine Submodule.span_mono ?_
      rintro x (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    let b : Module.Basis (Fin 2) F K := Module.Basis.mk hv hsp
    have hb0 : b 0 = 1 := by simp [b]
    have hb1 : b 1 = α := by simp [b]
    have hcoord00 : b.coord 0 (b 0) = 1 := by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
    have hcoord01 : b.coord 0 (b 1) = 0 := by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
    refine exists_isOrderedAlgebra_of_linearProj_nonneg_sq (b.coord 0) ?_ ?_
    · show b.coord 0 1 = 1
      rw [← hb0]; exact hcoord00
    · intro x
      show 0 ≤ b.coord 0 (x ^ 2)
      have hx_eq : x = b.repr x 0 • (1 : K) + b.repr x 1 • α := by
        have hsum : ∑ i, b.repr x i • b i = x := Module.Basis.sum_repr b x
        rw [Fin.sum_univ_two, hb0, hb1] at hsum
        exact hsum.symm
      set c := b.repr x 0 with hc_def
      set d := b.repr x 1 with hd_def
      have hx_sq : x ^ 2 = (c ^ 2 + d ^ 2 * a) • (1 : K) + (2 * c * d) • α := by
        have expand : (c • (1 : K) + d • α) ^ 2
            = c ^ 2 • (1 : K) + (2 * c * d) • α + d ^ 2 • α ^ 2 := by
          simp only [Algebra.smul_def, map_pow, map_mul, map_ofNat, mul_one]
          ring
        have h_am : algebraMap F K a = a • (1 : K) := Algebra.algebraMap_eq_smul_one a
        calc x ^ 2
            = (c • (1 : K) + d • α) ^ 2 := by rw [hx_eq]
          _ = c ^ 2 • (1 : K) + (2 * c * d) • α + d ^ 2 • α ^ 2 := expand
          _ = c ^ 2 • (1 : K) + (2 * c * d) • α + d ^ 2 • (a • (1 : K)) := by rw [hα, h_am]
          _ = c ^ 2 • (1 : K) + (2 * c * d) • α + (d ^ 2 * a) • (1 : K) := by rw [smul_smul]
          _ = c ^ 2 • (1 : K) + (d ^ 2 * a) • (1 : K) + (2 * c * d) • α := by
              rw [add_assoc, add_comm ((2 * c * d) • α) _, ← add_assoc]
          _ = (c ^ 2 + d ^ 2 * a) • (1 : K) + (2 * c * d) • α := by rw [← add_smul]
      have hπ_x_sq : b.coord 0 (x ^ 2) = c ^ 2 + d ^ 2 * a := by
        rw [hx_sq, map_add, map_smul, map_smul]
        rw [show (1 : K) = b 0 from hb0.symm, show α = b 1 from hb1.symm]
        rw [hcoord00, hcoord01]
        simp [smul_eq_mul]
      rw [hπ_x_sq]
      have h1 : 0 ≤ c ^ 2 := sq_nonneg c
      have h2 : 0 ≤ d ^ 2 * a := mul_nonneg (sq_nonneg d) ha
      linarith

/-- Any odd-degree finite field extension `K/F` of an ordered field `F` admits an ordering
making it ordered. -/
theorem exists_isOrderedAlgebra_of_odd_finrank
    [FiniteDimensional F K] (hodd : Odd (Module.finrank F K)) :
    ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K := sorry

end Field
