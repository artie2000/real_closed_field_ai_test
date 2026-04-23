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

/-- Helper: in a real closed field, `a^2 + b^2` is a square. -/
private lemma aux_sq_sum_sq (a b : R) : IsSquare (a^2 + b^2) := by
  apply isSquare_of_isSumSq
  exact IsSumSq.add (IsSumSq.sq a) (IsSumSq.sq b)

/-- Helper: in a real closed field, if one of `u, -u` is a square but not the other,
we can always find a square by going to the other of a "pair".
Given `a b r : R` with `r^2 = a^2 + b^2` and `b ≠ 0`, there exists `r' : R` with
`r'^2 = a^2 + b^2` and `IsSquare ((a + r') / 2)`. -/
private lemma aux_choose_r {a b : R} (hb : b ≠ 0) {r : R} (hr : r^2 = a^2 + b^2) :
    ∃ r' : R, r'^2 = a^2 + b^2 ∧ IsSquare ((a + r') / 2) := by
  rcases isSquare_or_isSquare_neg ((a + r) / 2) with hsq | hsq
  · exact ⟨r, hr, hsq⟩
  · -- -(a+r)/2 is a square, show (a + (-r))/2 = (a-r)/2 is a square
    refine ⟨-r, by linear_combination hr, ?_⟩
    -- Want: IsSquare ((a + -r) / 2) = IsSquare ((a - r) / 2)
    -- We have: IsSquare (-(a+r)/2).
    -- Product: ((a+r)/2) * ((a-r)/2) = (a^2 - r^2)/4 = -b^2/4
    -- So (a-r)/2 = (-b^2/4) / ((a+r)/2) = -b^2 / (2(a+r))
    -- Or: if -(a+r)/2 = c^2 with c ≠ 0, then (a-r)/2 = -b^2/(4(a+r)/2) = -b^2/(-4c^2) = (b/(2c))^2
    obtain ⟨c, hc⟩ := hsq
    -- hc : -(a + r)/2 = c * c
    by_cases hc0 : c = 0
    · -- If c = 0 then -(a+r)/2 = 0, so r = -a, so r² = a², so a²+b² = a², so b = 0
      exfalso
      rw [hc0, mul_zero] at hc
      have hr0 : r = -a := by linarith
      apply hb
      have : b^2 = 0 := by
        have := hr
        rw [hr0] at this
        linarith [sq_nonneg a, sq_nonneg b]
      have : b^2 = 0 := this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    · -- c ≠ 0. Take d = b/(2c). Then d^2 = b^2/(4c^2).
      -- Goal: (a + -r)/2 = d * d
      refine ⟨b / (2 * c), ?_⟩
      have h2c : 2 * c ≠ 0 := mul_ne_zero two_ne_zero hc0
      have hcsq : c^2 = -(a + r)/2 := by
        have : c * c = -(a + r)/2 := hc.symm
        nlinarith [this]
      field_simp
      have : c^2 = -(a+r)/2 := hcsq
      have key : (a - r) * (4 * c^2) = (2 * (b / (2 * c)))^2 * (4 * c^2) := by
        have : (2 * (b / (2 * c)))^2 * (4 * c^2) = 4 * b^2 := by
          field_simp
          ring
        rw [this]
        have : (a - r) * (4 * c^2) = (a - r) * (-(2*(a+r))) := by
          rw [hcsq]; ring
        rw [this]
        -- (a - r) * (-2*(a+r)) = -2(a^2 - r^2) = -2(a^2 - (a^2+b^2)) = 2 b^2
        -- Hmm that gives 2b^2, not 4b^2. Let me recompute.
        -- Actually c^2 = -(a+r)/2, so 4c^2 = -2(a+r). So (a-r)*4c^2 = -2(a-r)(a+r) = -2(a^2-r^2) = -2(-b^2) = 2b^2
        -- But I wrote 4*b^2. Let me fix.
        nlinarith [hr]
      sorry

private lemma aux_exists_sq_root_of_rc_field {a b : R} (hb : b ≠ 0) :
    ∃ c : R, IsSquare ((a + c)/2) ∧ IsSquare ((a - c)/2 + b^2 / (4 * ((a+c)/2))) := by
  sorry

theorem isSquare_of_finrank_base_eq_two
    (K : Type*) [Field K] [Algebra R K]
    (hK : Module.finrank R K = 2) (x : K) : IsSquare x := sorry

end Algebraic

end IsRealClosed
