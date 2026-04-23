/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.TFAE
import RealClosedField.Algebra.Order.Algebra

namespace IsRealClosed

variable (R : Type*) [Field R]

section Algebraic

variable [IsRealClosed R]

/-- Every sum of squares in a real closed field is a square. -/
theorem isSquare_of_isSumSq {x : R} (hx : IsSumSq x) : IsSquare x := by
  rcases isSquare_or_isSquare_neg x with h | h
  · exact h
  · by_cases hx0 : x = 0
    · subst hx0
      exact IsSquare.zero
    · exfalso
      apply IsSemireal.not_isSumSq_neg_one R
      have hneg1 : (-1 : R) = (-x) * x⁻¹ := by
        rw [neg_mul, mul_inv_cancel₀ hx0]
      rw [hneg1]
      have hinv : IsSumSq (x⁻¹) := by
        have hxinv2 : IsSumSq (x⁻¹ * x⁻¹) := IsSumSq.mul_self _
        have heq : x⁻¹ = (x⁻¹ * x⁻¹) * x := by
          rw [mul_assoc, inv_mul_cancel₀ hx0, mul_one]
        rw [heq]
        exact IsSumSq.mul hxinv2 hx
      exact IsSumSq.mul h.isSumSq hinv

/-- In a quadratic extension of a real closed field, there is a square root of `-1`. -/
theorem exists_sq_neg_one_of_finrank_eq_two
    (K : Type*) [Field K] [Algebra R K]
    (hK : Module.finrank R K = 2) : ∃ j : K, j ^ 2 = -1 := by
  haveI : FiniteDimensional R K := FiniteDimensional.of_finrank_eq_succ hK
  -- Find an element e of K that is not in the image of the algebraMap.
  have hbot_ne_top : (⊥ : Subalgebra R K) ≠ ⊤ := by
    intro h
    have h1 : Module.finrank R K = 1 :=
      Subalgebra.bot_eq_top_iff_finrank_eq_one.mp h
    omega
  have hexists : ∃ e : K, e ∉ Set.range (algebraMap R K) := by
    by_contra hall
    push_neg at hall
    apply hbot_ne_top
    apply eq_top_iff.mpr
    intro e _
    rw [Algebra.mem_bot]
    exact hall e
  obtain ⟨e, he⟩ := hexists
  -- The minimal polynomial of e has natDegree exactly 2
  have hint : IsIntegral R e := Algebra.IsIntegral.isIntegral e
  have hdeg : (minpoly R e).natDegree = 2 := by
    have h1 : 2 ≤ (minpoly R e).natDegree :=
      (minpoly.two_le_natDegree_iff hint).mpr he
    have h2 : (minpoly R e).natDegree ≤ Module.finrank R K :=
      minpoly.natDegree_le _
    omega
  -- Extract coefficients c₁ = coeff 1, c₀ = coeff 0 (monic so coeff 2 = 1)
  set c₁ := (minpoly R e).coeff 1 with hc₁
  set c₀ := (minpoly R e).coeff 0 with hc₀
  have hmonic : (minpoly R e).Monic := minpoly.monic hint
  have hleadcoeff : (minpoly R e).coeff 2 = 1 := by
    have := hmonic
    rw [Polynomial.Monic, Polynomial.leadingCoeff] at this
    rw [hdeg] at this
    exact this
  have haeval : (Polynomial.aeval e) (minpoly R e) = 0 := minpoly.aeval R e
  -- Expand aeval using the formula aeval = sum of coeff i • e^i
  have hsum : (Polynomial.aeval e) (minpoly R e) =
      (minpoly R e).coeff 0 • (e^0) +
      (minpoly R e).coeff 1 • (e^1) +
      (minpoly R e).coeff 2 • (e^2) := by
    rw [Polynomial.aeval_eq_sum_range' (n := 3) (by omega)]
    simp [Finset.sum_range_succ]
    ring
  -- So e² + c₁ e + c₀ = 0, meaning e² = -c₁ e - c₀
  have hesq : e^2 = -(algebraMap R K c₁) * e - (algebraMap R K c₀) := by
    have h0 := haeval
    rw [hsum] at h0
    rw [hleadcoeff, ← hc₁, ← hc₀, pow_zero, pow_one, one_smul] at h0
    simp only [Algebra.smul_def] at h0
    linear_combination h0
  -- Let β = e + c₁/2 (in K).
  -- Then β² = -c₀ + c₁²/4 = d.
  set d : R := c₁^2 / 4 - c₀ with hd
  set β : K := e + (algebraMap R K) (c₁ / 2) with hβ
  have hβsq : β^2 = (algebraMap R K) d := by
    rw [hβ, hd]
    have h2ne : (2 : R) ≠ 0 := two_ne_zero
    have : (algebraMap R K (c₁ / 2))^2 = algebraMap R K (c₁^2 / 4) := by
      rw [← map_pow]
      congr 1
      field_simp
      ring
    rw [add_pow_two, this, hesq]
    rw [map_sub, map_pow]
    push_cast
    have hmul2 : (2 : K) * e * (algebraMap R K (c₁ / 2)) = algebraMap R K c₁ * e := by
      have : (algebraMap R K (c₁ / 2)) * 2 = algebraMap R K c₁ := by
        rw [← map_ofNat (algebraMap R K) 2, ← map_mul]
        congr 1
        field_simp
      linarith [this]
    sorry
  sorry

theorem isSquare_of_finrank_base_eq_two
    (K : Type*) [Field K] [Algebra R K]
    (hK : Module.finrank R K = 2) (x : K) : IsSquare x := sorry

end Algebraic

end IsRealClosed
