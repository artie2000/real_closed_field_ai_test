/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Fundamental theorem of algebra for real closed fields

This file collects the key consequences of `IsRealClosed R` that together yield FTA
for an RCF: every finite extension of `R` is either `R` itself or `R[i]`.

The main applications are the two remaining sorries in
`RealClosedField/Algebra/Order/Field/IsRealClosed.lean`:

* `IsRealClosed.bijective_algebraMap_of_isOrderedAlgebra`:
  a real closed field has no nontrivial ordered algebraic extension.
* `IsRealClosed.exists_isRoot_of_nonpos_of_nonneg`:
  polynomials over a real closed field satisfy the intermediate value property.
-/

open Polynomial

namespace IsRealClosed

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `X^2 + 1` has no root in an RCF because `-1` is not a square. -/
private lemma not_isSquare_neg_one [IsRealClosed R] : ¬ IsSquare (-1 : R) := by
  intro hsq
  have h : (0 : R) ≤ -1 := (IsRealClosed.nonneg_iff_isSquare (R := R) (x := -1)).mpr hsq
  linarith

private lemma irreducible_X_sq_add_one [IsRealClosed R] :
    Irreducible (X ^ 2 + 1 : R[X]) := by
  have h : (X ^ 2 + 1 : R[X]) = X ^ 2 - C (-1) := by simp [map_neg, map_one, sub_neg_eq_add]
  have hmonic : (X ^ 2 - C (-1 : R)).Monic := monic_X_pow_sub_C _ (by decide)
  have hdeg : (X ^ 2 - C (-1 : R)).natDegree = 2 := natDegree_X_pow_sub_C
  rw [h]
  rw [Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hmonic
        (by rw [hdeg]) (by rw [hdeg]; decide),
      Multiset.eq_zero_iff_forall_notMem]
  intro c hc
  rw [mem_roots hmonic.ne_zero] at hc
  simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_neg_eq_add] at hc
  have hsq : IsSquare (-1 : R) := ⟨c, by linear_combination hc.symm - sq c⟩
  exact not_isSquare_neg_one hsq

/-- `Ri R` is the adjoinment of a square root of `-1` to `R`, i.e. `R[i]`.
It is modelled as `AdjoinRoot (X^2 + 1)`. Marked `abbrev` so instance resolution
fires automatically via `AdjoinRoot`. -/
private abbrev Ri (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] : Type u := AdjoinRoot (X ^ 2 + 1 : R[X])

private instance [IsRealClosed R] : Fact (Irreducible (X ^ 2 + 1 : R[X])) :=
  ⟨irreducible_X_sq_add_one⟩

private noncomputable instance [IsRealClosed R] : Module.Finite R (Ri R) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis (irreducible_X_sq_add_one).ne_zero).basis

section FTA

variable [IsRealClosed R]

/-- **S1.** In a real closed linearly ordered field, a sum of squares is a square. -/
theorem isSquare_of_isSumSq {s : R} (hs : IsSumSq s) : IsSquare s :=
  (IsRealClosed.nonneg_iff_isSquare).mp hs.nonneg

/-- **S2.** No proper odd-degree finite extension of a real closed field. -/
theorem finrank_eq_one_of_odd_finrank
    (K : Type u) [Field K] [Algebra R K] [Module.Finite R K]
    (h : Odd (Module.finrank R K)) : Module.finrank R K = 1 := by
  sorry

/-- **S4.** Every element of `R[i]` is a square. -/
theorem Ri_isSquare (z : Ri R) : IsSquare z := by
  have hpoly : (X ^ 2 + 1 : R[X]) = X ^ 2 - C (-1) := by
    simp [map_neg, map_one, sub_neg_eq_add]
  have hmonic : (X ^ 2 + 1 : R[X]).Monic := by
    rw [hpoly]; exact monic_X_pow_sub_C _ (by decide)
  have hdeg2 : (X ^ 2 + 1 : R[X]).natDegree = 2 := by
    rw [hpoly]; exact natDegree_X_pow_sub_C
  set hm : IsAdjoinRootMonic (Ri R) (X ^ 2 + 1 : R[X]) :=
    AdjoinRoot.isAdjoinRootMonic (X ^ 2 + 1 : R[X]) hmonic
  -- `i^2 = -1`
  have hroot_sq : hm.root ^ 2 = -1 := by
    have heq : hm.root = AdjoinRoot.root (X ^ 2 + 1 : R[X]) := rfl
    have h0 : aeval (AdjoinRoot.root (X ^ 2 + 1 : R[X])) (X ^ 2 + 1 : R[X]) = 0 :=
      AdjoinRoot.eval₂_root _
    simp [aeval_def, eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at h0
    rw [heq]; linear_combination h0
  -- Every element decomposes as `u + v · root`
  have hrepr : ∀ x : Ri R,
      x = algebraMap R (Ri R) (hm.coeff x 0) + algebraMap R (Ri R) (hm.coeff x 1) * hm.root := by
    intro x
    apply hm.ext_elem
    intro i hi
    rw [hdeg2] at hi
    have hroot_coeff : hm.coeff hm.root = Pi.single 1 1 := hm.coeff_root (by rw [hdeg2]; decide)
    have hcoeff_aM_mul_root : ∀ (c : R) (j : ℕ),
        hm.coeff (algebraMap R (Ri R) c * hm.root) j
          = c • (Pi.single (M := fun _ : ℕ => R) 1 1) j := by
      intro c j
      rw [show algebraMap R (Ri R) c * hm.root = c • hm.root from by rw [Algebra.smul_def],
          LinearMap.map_smul hm.coeff]
      show c • hm.coeff hm.root j = _
      rw [hroot_coeff]
    interval_cases i
    · rw [LinearMap.map_add hm.coeff, hm.coeff_algebraMap]
      show hm.coeff x 0 = (Pi.single 0 (hm.coeff x 0) : ℕ → R) 0
          + hm.coeff (algebraMap R (Ri R) (hm.coeff x 1) * hm.root) 0
      rw [hcoeff_aM_mul_root]; simp
    · rw [LinearMap.map_add hm.coeff, hm.coeff_algebraMap]
      show hm.coeff x 1 = (Pi.single 0 (hm.coeff x 0) : ℕ → R) 1
          + hm.coeff (algebraMap R (Ri R) (hm.coeff x 1) * hm.root) 1
      rw [hcoeff_aM_mul_root]; simp
  set a := hm.coeff z 0
  set b := hm.coeff z 1
  -- Helper: exhibit a square root of `z` given `u v : R` satisfying the arithmetic identities
  suffices h : ∃ u v : R, u ^ 2 - v ^ 2 = a ∧ 2 * u * v = b by
    obtain ⟨u, v, huv1, huv2⟩ := h
    refine ⟨algebraMap R (Ri R) u + algebraMap R (Ri R) v * hm.root, ?_⟩
    rw [hrepr z]
    have hmid : (2 : Ri R) * algebraMap R (Ri R) u * algebraMap R (Ri R) v
              = algebraMap R (Ri R) (2 * u * v) := by
      rw [map_mul, map_mul, map_ofNat]
    have h1 : (algebraMap R (Ri R) u)^2 + (algebraMap R (Ri R) v)^2 * (-1 : Ri R)
            = algebraMap R (Ri R) (u^2 - v^2) := by
      rw [map_sub, map_pow, map_pow]; ring
    have key : (algebraMap R (Ri R) u + algebraMap R (Ri R) v * hm.root) *
               (algebraMap R (Ri R) u + algebraMap R (Ri R) v * hm.root)
             = algebraMap R (Ri R) (u ^ 2 - v ^ 2)
               + algebraMap R (Ri R) (2 * u * v) * hm.root := by
      have hsq : (algebraMap R (Ri R) u + algebraMap R (Ri R) v * hm.root) *
                 (algebraMap R (Ri R) u + algebraMap R (Ri R) v * hm.root)
               = (algebraMap R (Ri R) u)^2 + (algebraMap R (Ri R) v)^2 * hm.root^2
                 + (2 * algebraMap R (Ri R) u * algebraMap R (Ri R) v) * hm.root := by ring
      rw [hsq, hroot_sq, hmid, h1]
    rw [key, huv1, huv2]
  -- Now solve the arithmetic system
  by_cases hb : b = 0
  · -- b = 0 case
    rcases le_or_lt 0 a with ha | ha
    · obtain ⟨u, hu⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R) (x := a)).mp ha
      refine ⟨u, 0, ?_, ?_⟩
      · rw [hu]; ring
      · rw [hb]; ring
    · have hna : 0 ≤ -a := by linarith
      obtain ⟨v, hv⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R) (x := -a)).mp hna
      refine ⟨0, v, ?_, ?_⟩
      · linarith [hv]
      · rw [hb]; ring
  · -- b ≠ 0 case
    have hab_nn : 0 ≤ a^2 + b^2 := by positivity
    obtain ⟨s0, hs0⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R) (x := a^2 + b^2)).mp hab_nn
    -- Use |s0| as the nonneg root
    set s := |s0| with hs_def
    have hs : a^2 + b^2 = s^2 := by rw [hs_def, sq_abs]; exact hs0
    have hs_nn : 0 ≤ s := abs_nonneg _
    -- s ≥ |a|, so a + s ≥ 0
    have hs_sq_ge : a ^ 2 ≤ s ^ 2 := by nlinarith [sq_nonneg b]
    have hs_ge_abs : |a| ≤ s := by
      rw [abs_le]
      constructor
      · nlinarith [sq_nonneg (a + s), sq_nonneg (a - s)]
      · nlinarith [sq_nonneg (a + s), sq_nonneg (a - s)]
    have ha_plus_s_nn : 0 ≤ a + s := by
      have := neg_abs_le a
      linarith
    have hhalf_nn : 0 ≤ (a + s) / 2 := by linarith
    obtain ⟨u, hu⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R) (x := (a + s) / 2)).mp hhalf_nn
    have hu_sq : u ^ 2 = (a + s) / 2 := by rw [← hu]; ring
    -- u ≠ 0: if u = 0 then (a+s)/2 = 0 so s = -a, so s² = a², so b² = 0, contradiction
    have hu_ne : u ≠ 0 := by
      intro hu0
      apply hb
      have hsa : s = -a := by
        have h1 : (a + s) / 2 = 0 := by rw [← hu_sq, hu0]; ring
        linarith
      have hbsq : b ^ 2 = 0 := by nlinarith [hs, hsa]
      exact pow_eq_zero_iff (two_ne_zero).mpr hbsq
    -- Choose v := b / (2u)
    refine ⟨u, b / (2 * u), ?_, ?_⟩
    · -- u^2 - (b/(2u))^2 = a
      have h2u : (2 * u) ≠ 0 := mul_ne_zero two_ne_zero hu_ne
      field_simp
      nlinarith [hs, hu_sq, sq_nonneg u]
    · field_simp

/-- **S3.** Every degree-2 extension of an RCF is isomorphic to `R[i]`. -/
theorem nonempty_algEquiv_Ri_of_finrank_eq_two
    (K : Type u) [Field K] [Algebra R K] (h : Module.finrank R K = 2) :
    Nonempty (K ≃ₐ[R] Ri R) := by
  sorry

/-- Auxiliary: no proper quadratic extension of `R[i]`. -/
theorem no_quadratic_ext_Ri
    (M : Type u) [Field M] [Algebra (Ri R) M] (h : Module.finrank (Ri R) M = 2) : False := by
  sorry

/-- **S5.** FTA for RCF: every finite extension has degree 1 or 2. -/
theorem finrank_eq_one_or_two_of_finite
    (K : Type u) [Field K] [Algebra R K] [Module.Finite R K] [Nontrivial K] :
    Module.finrank R K = 1 ∨ Module.finrank R K = 2 := by
  sorry

/-- **S6.** An algebraic extension of an RCF is finite. -/
theorem finite_of_isAlgebraic
    (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K] :
    Module.Finite R K := by
  sorry

/-- **S9** (for IVP use). Every monic irreducible polynomial over an RCF is either
linear or is everywhere positive. -/
theorem natDegree_eq_one_or_forall_eval_pos_of_irreducible
    {g : R[X]} (hmonic : g.Monic) (hirred : Irreducible g) :
    g.natDegree = 1 ∨ ∀ x : R, 0 < g.eval x := by
  sorry

/-- **S10.** IVP for polynomials over an RCF. -/
theorem ivp_poly
    {f : R[X]} {a b : R} (hab : a ≤ b) (ha : f.eval a ≤ 0) (hb : 0 ≤ f.eval b) :
    ∃ c ∈ Set.Icc a b, f.IsRoot c := by
  sorry

/-- **S8.** An RCF has no nontrivial ordered algebraic extension. -/
theorem bijective_algebraMap_of_isOrderedAlgebra'
    (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
    [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K] :
    Function.Bijective (algebraMap R K) := by
  sorry

end FTA

end IsRealClosed
