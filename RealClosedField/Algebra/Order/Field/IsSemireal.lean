/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Ring.Semireal.Defs
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
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

theorem Rat.existsUnique_isStrictOrderedRing :
    ∃! l : LinearOrder ℚ, @IsStrictOrderedRing ℚ _ l.toPartialOrder := by
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
  exact IsStrictOrderedRing.unique_isStrictOrderedRing_iff.mpr key

open Polynomial in
/-- If `-1` is not a square in a field `F`, and every element of `F(i) := AdjoinRoot (X^2 + 1)`
is a square in `F(i)`, then every sum of squares in `F` is a square in `F`. -/
theorem IsSquare.of_isSumSq_of_forall_isSquare_adjoinRoot
    {F : Type*} [Field F] (hF : ¬ IsSquare (-1 : F))
    (hsq : ∀ z : AdjoinRoot (X^2 + 1 : F[X]), IsSquare z)
    {s : F} (hs : IsSumSq s) : IsSquare s := by
  -- Key step: for any `x u : F`, `x^2 + u^2` is a square in `F`.
  have hkey : ∀ x u : F, IsSquare (x ^ 2 + u ^ 2) := by
    intro x u
    -- Setup: use IsAdjoinRootMonic for X^2+1
    have hmonic : (X ^ 2 + 1 : F[X]).Monic := by
      have heq : (X ^ 2 + 1 : F[X]) = X ^ 2 - C (-1 : F) := by simp [sub_neg_eq_add]
      rw [heq]; exact monic_X_pow_sub_C _ (by decide)
    have hdeg2 : (X ^ 2 + 1 : F[X]).natDegree = 2 := by
      have heq : (X ^ 2 + 1 : F[X]) = X ^ 2 - C (-1 : F) := by simp [sub_neg_eq_add]
      rw [heq]; exact natDegree_X_pow_sub_C
    set hm : IsAdjoinRootMonic (AdjoinRoot (X ^ 2 + 1 : F[X])) (X ^ 2 + 1 : F[X]) :=
      AdjoinRoot.isAdjoinRootMonic (X ^ 2 + 1 : F[X]) hmonic
    have hroot_sq : hm.root ^ 2 = -1 := by
      have heq : hm.root = AdjoinRoot.root (X ^ 2 + 1 : F[X]) := rfl
      have h0 : aeval (AdjoinRoot.root (X ^ 2 + 1 : F[X])) (X ^ 2 + 1 : F[X]) = 0 :=
        AdjoinRoot.eval₂_root _
      simp [aeval_def, eval₂_add, eval₂_pow, eval₂_X, eval₂_one,
            add_eq_zero_iff_eq_neg] at h0
      rw [heq]; exact h0
    -- Representation: every element of F(i) is `c + d * root` for `c, d : F`.
    have hrepr : ∀ y : AdjoinRoot (X ^ 2 + 1 : F[X]),
        y = algebraMap F _ (hm.coeff y 0) +
            algebraMap F _ (hm.coeff y 1) * hm.root := by
      intro y
      apply hm.ext_elem
      intro i hi
      rw [hdeg2] at hi
      have hroot_coeff : hm.coeff hm.root = Pi.single 1 1 :=
        hm.coeff_root (by rw [hdeg2]; decide)
      have hcoeff_aM_mul_root : ∀ (c : F) (j : ℕ),
          hm.coeff (algebraMap F _ c * hm.root) j =
            c • (Pi.single (M := fun _ : ℕ => F) 1 1) j := by
        intro c j
        rw [show algebraMap F _ c * hm.root = c • hm.root from by rw [Algebra.smul_def],
            LinearMap.map_smul hm.coeff]
        show c • hm.coeff hm.root j = _
        rw [hroot_coeff]
      interval_cases i
      · rw [LinearMap.map_add hm.coeff, hm.coeff_algebraMap]
        show hm.coeff y 0 = (Pi.single 0 (hm.coeff y 0) : ℕ → F) 0
            + hm.coeff (algebraMap F _ (hm.coeff y 1) * hm.root) 0
        rw [hcoeff_aM_mul_root]; simp
      · rw [LinearMap.map_add hm.coeff, hm.coeff_algebraMap]
        show hm.coeff y 1 = (Pi.single 0 (hm.coeff y 0) : ℕ → F) 1
            + hm.coeff (algebraMap F _ (hm.coeff y 1) * hm.root) 1
        rw [hcoeff_aM_mul_root]; simp
    -- Apply hsq to `x + u * root`
    set z : AdjoinRoot (X ^ 2 + 1 : F[X]) :=
      algebraMap F _ x + algebraMap F _ u * hm.root with hz_def
    obtain ⟨w, hw⟩ := hsq z
    set c : F := hm.coeff w 0
    set d : F := hm.coeff w 1
    have hw_repr : w = algebraMap F _ c + algebraMap F _ d * hm.root := hrepr w
    -- Compute w*w = (c^2 - d^2) + (2cd) * root (using root^2 = -1)
    have hi2 : hm.root * hm.root = -1 := by rw [← sq]; exact hroot_sq
    have hw_sq :
        w * w = algebraMap F _ (c ^ 2 - d ^ 2) +
                algebraMap F _ (2 * c * d) * hm.root := by
      rw [hw_repr]
      set i : AdjoinRoot (X ^ 2 + 1 : F[X]) := hm.root
      set A : AdjoinRoot (X ^ 2 + 1 : F[X]) := algebraMap F _ c
      set B : AdjoinRoot (X ^ 2 + 1 : F[X]) := algebraMap F _ d
      have hstep :
          (A + B * i) * (A + B * i)
            = (A * A - B * B) + (A * B + A * B) * i := by
        have h1 : B * i * (B * i) = -(B * B) := by
          calc B * i * (B * i) = (B * B) * (i * i) := by ring
            _ = (B * B) * (-1) := by rw [hi2]
            _ = -(B * B) := by ring
        calc (A + B * i) * (A + B * i)
            = A * A + A * (B * i) + B * i * A + B * i * (B * i) := by ring
          _ = A * A + A * B * i + A * B * i + (-(B * B)) := by rw [h1]; ring
          _ = (A * A - B * B) + (A * B + A * B) * i := by ring
      rw [hstep]
      congr 1
      · rw [map_sub, map_pow, map_pow]; ring
      · rw [show A * B + A * B = algebraMap F _ (2 * c * d) from ?_]
        · rw [map_mul, map_mul, map_ofNat]; ring
    -- From hw: z = w^2 = w*w
    have hz_wsq : z = w * w := by rw [hw, sq]
    have hz_wsq' :
        algebraMap F _ x + algebraMap F _ u * hm.root =
          algebraMap F _ (c ^ 2 - d ^ 2) +
          algebraMap F _ (2 * c * d) * hm.root := by
      rw [← hz_def, hz_wsq, hw_sq]
    -- Match coefficients: x = c^2 - d^2 and u = 2cd
    have hxc : x = c ^ 2 - d ^ 2 := by
      have hcoeff := congr_arg (hm.coeff · 0) hz_wsq'
      simp only at hcoeff
      rw [LinearMap.map_add hm.coeff, LinearMap.map_add hm.coeff] at hcoeff
      rw [hm.coeff_algebraMap, hm.coeff_algebraMap] at hcoeff
      have hcoeff_aM_mul_root : ∀ (e : F),
          hm.coeff (algebraMap F _ e * hm.root) 0 = 0 := by
        intro e
        have : hm.coeff (algebraMap F _ e * hm.root) =
            e • (Pi.single (M := fun _ : ℕ => F) 1 1) := by
          rw [show algebraMap F _ e * hm.root = e • hm.root from by rw [Algebra.smul_def],
              LinearMap.map_smul hm.coeff,
              hm.coeff_root (by rw [hdeg2]; decide)]
        rw [this]; simp
      rw [hcoeff_aM_mul_root, hcoeff_aM_mul_root] at hcoeff
      have h1 : (Pi.single 0 x : ℕ → F) 0 = x := by simp
      have h2 : (Pi.single 0 (c^2 - d^2) : ℕ → F) 0 = c^2 - d^2 := by simp
      rw [show (Pi.single 0 x + 0 : ℕ → F) 0 = x from by rw [Pi.add_apply, h1]; ring,
          show (Pi.single 0 (c^2 - d^2) + 0 : ℕ → F) 0 = c^2 - d^2 from by
            rw [Pi.add_apply, h2]; ring] at hcoeff
      exact hcoeff
    have hud : u = 2 * c * d := by
      have hcoeff := congr_arg (hm.coeff · 1) hz_wsq'
      simp only at hcoeff
      rw [LinearMap.map_add hm.coeff, LinearMap.map_add hm.coeff] at hcoeff
      rw [hm.coeff_algebraMap, hm.coeff_algebraMap] at hcoeff
      have hcoeff_aM_mul_root : ∀ (e : F),
          hm.coeff (algebraMap F _ e * hm.root) 1 = e := by
        intro e
        have : hm.coeff (algebraMap F _ e * hm.root) =
            e • (Pi.single (M := fun _ : ℕ => F) 1 1) := by
          rw [show algebraMap F _ e * hm.root = e • hm.root from by rw [Algebra.smul_def],
              LinearMap.map_smul hm.coeff,
              hm.coeff_root (by rw [hdeg2]; decide)]
        rw [this]; simp
      rw [hcoeff_aM_mul_root, hcoeff_aM_mul_root] at hcoeff
      have h1 : (Pi.single 0 x : ℕ → F) 1 = 0 := by simp
      have h2 : (Pi.single 0 (c^2 - d^2) : ℕ → F) 1 = 0 := by simp
      rw [show (Pi.single 0 x + u : ℕ → F) 1 = u from by rw [Pi.add_apply, h1]; ring,
          show (Pi.single 0 (c^2-d^2) + (2*c*d) : ℕ → F) 1 = 2*c*d from by
            rw [Pi.add_apply, h2]; ring] at hcoeff
      exact hcoeff
    -- Conclude: x^2 + u^2 = (c^2 + d^2)^2
    refine ⟨c ^ 2 + d ^ 2, ?_⟩
    rw [hxc, hud]; ring
  -- Now induct on hs
  induction hs with
  | zero => exact ⟨0, by simp⟩
  | sq_add a _ ih =>
    obtain ⟨u, hu⟩ := ih
    -- hs is a * a + t, t = u * u
    -- Rewrite: a*a + t = a^2 + u^2, then apply hkey
    have h1 : a * a + _ = a ^ 2 + u ^ 2 := by rw [hu]; ring
    rw [h1]
    exact hkey a u
