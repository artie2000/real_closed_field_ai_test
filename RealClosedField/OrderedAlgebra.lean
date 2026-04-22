/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.Algebra.Order.Ring.Ordering.Adjoin
import RealClosedField.Algebra.Order.Ring.Ordering.Order
import Mathlib.Algebra.Order.Algebra

attribute [-simp] AdjoinRoot.algebraMap_eq

variable {F K : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [Field K] [Algebra F K]

namespace Field

-- TODO : generalise to ordered extensions of rings :
--        correspondence between `Subalgebra (.nonneg R) S` (with `IsPointed`)
--        and `IsOrderedModule R S`

variable (F K) in
open Classical in
open scoped algebraMap in
noncomputable def isOrderingOrderedAlgebraEquiv :
    Equiv {O : Subsemiring K // O.IsOrdering ∧ (Subsemiring.nonneg F).map (algebraMap F K) ≤ O}
          {l : LinearOrder K // IsStrictOrderedRing K ∧ IsOrderedModule F K} where
  toFun := fun ⟨O, hO, hO₂⟩ =>
    letI l := (isOrderingLinearOrderEquiv K ⟨O, hO⟩).1
    letI hl := (isOrderingLinearOrderEquiv K ⟨O, hO⟩).2
    ⟨l, ⟨inferInstance, .of_algebraMap_mono <| by
      rw [monotone_iff_map_nonneg]
      intro a ha
      apply_fun (fun s ↦ s.carrier : Subsemiring K → Set K) at hO₂
      · simpa [l] using (show Set.Ici (0 : F) ⊆ _ by simpa using hO₂) ha
      · exact fun _ _ h ↦ h⟩⟩
  invFun := fun ⟨l, hl⟩ =>
    let O := (isOrderingLinearOrderEquiv K).symm ⟨l, hl.1⟩
    ⟨O, O.property, fun x hx => by
    rcases hl with ⟨hl, hl₂⟩
    have : ∀ b : F, 0 ≤ b → 0 ≤ (b : K) := fun _ h ↦ by
      simpa using algebraMap_mono (β := K) h
    aesop⟩
  left_inv := fun ⟨_, _, _⟩ => by ext; simp
  right_inv := fun ⟨_, _, _⟩ => by ext; simp

@[simp]
theorem isOrderingOrderedAlgebraEquiv_apply_coe
    (O : Subsemiring K) (hO : O.IsOrdering)
    (hO₂ : Subsemiring.map (algebraMap F K) (Subsemiring.nonneg F) ≤ O) :
    (isOrderingOrderedAlgebraEquiv F K ⟨O, hO, hO₂⟩ : LinearOrder K) =
    isOrderingLinearOrderEquiv K ⟨O, hO⟩ := rfl

@[simp]
theorem isOrderingOrderedAlgebraEquiv_symm_apply_coe
    (l : LinearOrder K) (hl : IsStrictOrderedRing K) (hl₂ : IsOrderedModule F K) :
    ((isOrderingOrderedAlgebraEquiv F K).symm ⟨l, hl, hl₂⟩ : Subsemiring K) =
    (isOrderingLinearOrderEquiv K).symm ⟨l, hl⟩ := rfl

open Classical Subsemiring in
theorem exists_isOrderedAlgebra_iff_neg_one_notMem_sup :
    (∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K) ↔
    -1 ∉ ((Subsemiring.nonneg F).map (algebraMap F K) ⊔ Subsemiring.sumSq K) := by
  rw [Equiv.exists_subtype_congr (isOrderingOrderedAlgebraEquiv F K).symm]
  set P := (Subsemiring.nonneg F).map (algebraMap F K) ⊔ Subsemiring.sumSq K with hP
  refine ⟨fun ⟨O, hO, hO₂⟩ hc => ?_, fun h => ?_⟩
  · suffices P ≤ O from IsPreordering.neg_one_notMem _ (this hc)
    rw [sup_le_iff]
    exact ⟨hO₂, fun _ ↦ by aesop⟩
  · have : P.IsPreordering := { }
    rcases IsPreordering.exists_le_isOrdering P with ⟨O, hO, hO₂⟩
    exact ⟨O, ⟨inferInstance, by simp_all⟩⟩

end Field

open scoped Pointwise in
theorem sup_map_nonneg_sumSq_eq_addSubmonoid_closure_set_mul :
    ↑((Subsemiring.nonneg F).map (algebraMap F K) ⊔ Subsemiring.sumSq K) =
    (Submodule.span (Subsemiring.nonneg F) {x : K | IsSquare x} : Set K) := by
  rw [← Subsemiring.closure_isSquare, ← Subsemiring.closure_eq <| Subsemiring.map ..,
      ← Subsemiring.closure_union, ← Subsemiring.closure_submonoid_closure,
      ← Submonoid.subsemiringClosure_eq_closure, Submonoid.subsemiringClosure_coe,
      ← Submodule.coe_toAddSubmonoid, Submodule.span_eq_closure]
  congr
  rw [← Subsemiring.coe_toSubmonoid, ← Submonoid.coe_square, ← Submonoid.sup_eq_closure,
      Submonoid.coe_sup, Subsemiring.coe_toSubmonoid]
  ext x
  simp [Set.mem_mul, Set.mem_smul, Subsemiring.smul_def, ← Algebra.smul_def]

open scoped Pointwise in
theorem Field.exists_isOrderedAlgebra_iff_neg_one_notMem_span_nonneg_isSquare :
    (∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K) ↔
    -1 ∉ Submodule.span (Subsemiring.nonneg F) {x : K | IsSquare x} := by
  rw [← SetLike.mem_coe, ← sup_map_nonneg_sumSq_eq_addSubmonoid_closure_set_mul, SetLike.mem_coe,
    Field.exists_isOrderedAlgebra_iff_neg_one_notMem_sup]
