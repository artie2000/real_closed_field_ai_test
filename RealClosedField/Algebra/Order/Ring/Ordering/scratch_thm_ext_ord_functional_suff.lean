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

NOTE (from prover agent).

The statement

    theorem exists_isOrderedAlgebra_of_linearProj_nonneg_sq
        (π : K →ₗ[F] F) (hπ : ∀ x : K, 0 ≤ π (x ^ 2)) :
        ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K

is *unprovable as written*.  Counter-example: take `F = ℚ`, `K = ℚ(i)`, and
`π := 0`.  Both hypotheses hold (`hπ` trivially), but `K` admits no ordering
making `K/F` an ordered algebra (because `-1 = i² ∈` span of squares).

The blueprint proof writes "since π(-1) = -1 < 0"; this step secretly uses
the hypothesis `π 1 = 1` (or, more weakly, `π 1 > 0`).  Suggested fix: add
a hypothesis `(hπ1 : π 1 = 1)` (or equivalently `0 < π 1`).  With that fix
the proof goes through, as demonstrated by
`exists_isOrderedAlgebra_of_linearProj_nonneg_sq'` below.
-/

variable {F K : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [Field K] [Algebra F K]

namespace Field

/-- Auxiliary: with the extra hypothesis `π 1 = 1`, the statement is true.
(This demonstrates that adding that hypothesis is the right fix.) -/
theorem exists_isOrderedAlgebra_of_linearProj_nonneg_sq'
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

/-- Unprovable as stated — see the module doc. -/
theorem exists_isOrderedAlgebra_of_linearProj_nonneg_sq
    (π : K →ₗ[F] F) (hπ : ∀ x : K, 0 ≤ π (x ^ 2)) :
    ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K := sorry

end Field
