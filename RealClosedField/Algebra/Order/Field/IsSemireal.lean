/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Algebra.Ring.Semireal.Defs
import RealClosedField.Algebra.Order.Ring.Ordering.Adjoin
import RealClosedField.Algebra.Order.Ring.Ordering.Order

section CommRing

variable {R : Type*} [CommRing R]

instance [IsSemireal R] : (Subsemiring.sumSq R).IsPreordering where
  neg_one_notMem := by simpa using IsSemireal.not_isSumSq_neg_one R

theorem isSemireal_ofIsPreordering (P : Subsemiring R) [P.IsPreordering] : IsSemireal R :=
  .of_not_isSumSq_neg_one (P.neg_one_notMem <| P.mem_of_isSumSq ·)

theorem exists_isPreordering_iff_isSemireal :
    (∃ P : Subsemiring R, P.IsPreordering) ↔ IsSemireal R where
  mp | ⟨P, _⟩ => isSemireal_ofIsPreordering P
  mpr _ := ⟨Subsemiring.sumSq R, inferInstance⟩

end CommRing

variable {F : Type*} [Field F]

open Classical in
theorem Field.exists_isStrictOrderedRing_iff_isSemireal :
    (∃ _ : LinearOrder F, IsStrictOrderedRing F) ↔ IsSemireal F := by
  rw [Equiv.exists_subtype_congr (isOrderingLinearOrderEquiv F).symm]
  exact ⟨fun ⟨O, hO⟩ => ⟨fun {s} hs h => Subsemiring.IsPreordering.neg_one_notMem O <|
            Subsemiring.mem_of_isSumSq O (by simp_all [show s = -1 by linear_combination h])⟩,
          fun _ =>
            letI exO := Subsemiring.IsPreordering.exists_le_isOrdering (Subsemiring.sumSq F)
            letI inst := (choose_spec exO).2
            ⟨choose exO, inferInstance⟩⟩

variable (F) in
noncomputable abbrev LinearOrder.ofIsSemireal [IsSemireal F] : LinearOrder F :=
  (Field.exists_isStrictOrderedRing_iff_isSemireal.mpr inferInstance).choose

variable (F) in
instance IsStrictOrderedRing.ofIsSemireal [IsSemireal F] :
    letI := LinearOrder.ofIsSemireal F
    IsStrictOrderedRing F :=
  (Field.exists_isStrictOrderedRing_iff_isSemireal.mpr inferInstance).choose_spec

set_option backward.isDefEq.respectTransparency false in
noncomputable abbrev IsSemireal.unique_isStrictOrderedRing [IsSemireal F]
    (h : ∀ x : F, IsSumSq x ∨ IsSumSq (-x)) :
    Unique {l : LinearOrder F // IsStrictOrderedRing F} where
  default := Field.isOrderingLinearOrderEquiv F
    ⟨Subsemiring.sumSq F, .mk' (by aesop) inferInstance⟩
  uniq l' := by
    rcases l' with ⟨l', hl'⟩
    generalize_proofs
    ext x y
    suffices x ≤ y ↔ IsSumSq (y - x) by simp [this]
    refine ⟨fun hxy => ?_, fun hxy => by linarith [IsSumSq.nonneg hxy]⟩
    · cases h (y - x) with | inl => assumption | inr h =>
      simp_all [show x = y by linarith [IsSumSq.nonneg h]]

theorem IsSemireal.isSumSq_or_isSumSq_neg [IsSemireal F]
    (h : ∃! _ : LinearOrder F, IsStrictOrderedRing F) :
    ∀ x : F, IsSumSq x ∨ IsSumSq (-x) := by
  rw [Equiv.existsUnique_subtype_congr (Field.isOrderingLinearOrderEquiv F).symm] at h
  by_contra! hc
  rcases hc with ⟨x, _⟩
  rcases Subsemiring.IsPreordering.exists_le_isOrdering_and_mem <|
    Subsemiring.IsPreordering.neg_one_notMem_closure_insert_of_neg_notMem
      (by simp_all : -x ∉ (Subsemiring.sumSq F)) with ⟨O₁, hle₁, hO₁, hx₁⟩
  rcases Subsemiring.IsPreordering.exists_le_isOrdering_and_mem <|
    Subsemiring.IsPreordering.neg_one_notMem_closure_insert_of_neg_notMem
      (by simp_all : -(-x) ∉ (Subsemiring.sumSq F)) with ⟨O₂, hle₂, hO₂, hx₂⟩
  exact (show O₁ ≠ O₂ from fun h => show x ≠ 0 by aesop <|
    (Subsemiring.IsPreordering.isPointed O₁).eq_zero_of_mem_of_neg_mem hx₁ (by simp_all)) <|
      h.unique inferInstance inferInstance

theorem IsSemireal.existsUnique_isStrictOrderedRing_iff [IsSemireal F] :
    (∃! _ : LinearOrder F, IsStrictOrderedRing F) ↔ ∀ x : F, IsSumSq x ∨ IsSumSq (-x) where
  mp := IsSemireal.isSumSq_or_isSumSq_neg
  mpr h := by
    rw [← unique_subtype_iff_existsUnique]
    exact .intro <| IsSemireal.unique_isStrictOrderedRing h

theorem IsStrictOrderedRing.unique_isStrictOrderedRing_iff [LinearOrder F] [IsStrictOrderedRing F] :
    (∃! _ : LinearOrder F, IsStrictOrderedRing F) ↔ ∀ x : F, 0 ≤ x → IsSumSq x := by
  rw [IsSemireal.existsUnique_isStrictOrderedRing_iff]
  refine ⟨fun h x hx => ?_, fun h x => ?_⟩
  · cases h x with | inl => assumption | inr ssnx =>
    aesop (add norm (show  x = 0 by linarith [IsSumSq.nonneg ssnx]))
  · by_cases hx : 0 ≤ x
    · simp [h x hx]
    · simp [h (-x) (by linarith)]

set_option backward.isDefEq.respectTransparency false in
theorem Rat.existsUnique_isStrictOrderedRing :
    ∃! _ : LinearOrder ℚ, IsStrictOrderedRing ℚ := by
  have aux : ∀ (n : ℕ) (y : ℚ), IsSumSq (n * y^2) := by
    intro n y
    induction n with
    | zero => simp [IsSumSq.zero]
    | succ k ih =>
        have : ((k + 1 : ℕ) : ℚ) * y^2 = y * y + k * y^2 := by push_cast; ring
        rw [this]
        exact IsSumSq.sq_add y ih
  have key : ∀ x : ℚ, 0 ≤ x → IsSumSq x := by
    intro x hx
    have hnum : x.num ≥ 0 := Rat.num_nonneg.mpr hx
    set p : ℕ := x.num.toNat with hp
    set q : ℕ := x.den with hq
    have hqpos : (q : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
    have hnumcast : (x.num : ℚ) = (p : ℚ) := by
      have : (x.num.toNat : ℤ) = x.num := Int.toNat_of_nonneg hnum
      exact_mod_cast this.symm
    have hpq : x = (p * q : ℕ) * ((1 : ℚ) / q)^2 := by
      rw [← Rat.num_div_den x, hnumcast]
      push_cast
      field_simp
      ring
    rw [hpq]
    exact aux (p * q) (1 / q)
  convert IsStrictOrderedRing.unique_isStrictOrderedRing_iff.mpr key using 0
  rfl
