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

/-- Helper: in a real closed field, every element of the form `a^2 + b^2` is a square. -/
private lemma aux_isSquare_sum_two_sq (a b : R) : IsSquare (a^2 + b^2) :=
  isSquare_of_isSumSq (IsSumSq.add (IsSumSq.sq a) (IsSumSq.sq b))

/-- Given `a b : R` with `b ≠ 0` and `r` a square root of `a^2 + b^2`, there exists
`r' : R` which is also a square root of `a^2 + b^2` and for which `(a + r')/2` is a
square in `R`. -/
private lemma aux_choose_sqrt
    {a b r : R} (hb : b ≠ 0) (hr : r^2 = a^2 + b^2) :
    ∃ r' : R, r'^2 = a^2 + b^2 ∧ IsSquare ((a + r') / 2) := by
  rcases isSquare_or_isSquare_neg ((a + r) / 2) with h | h
  · exact ⟨r, hr, h⟩
  · refine ⟨-r, by linear_combination hr, ?_⟩
    -- Need IsSquare ((a + -r)/2) = IsSquare ((a - r)/2)
    -- We have IsSquare (-(a+r)/2).
    -- (a+r)/2 * (a-r)/2 = (a² - r²)/4 = -b²/4
    -- So if (a+r)/2 = -c^2 with c ≠ 0 (c=0 would make (a+r)/2 = 0, which combined with
    -- product -b²/4 forces b=0), then (a-r)/2 = -b²/(4·(a+r)/2) = -b²/(-4c²) = (b/(2c))²
    obtain ⟨c, hc⟩ := h
    have hc_eq : -((a + r) / 2) = c * c := hc
    by_cases hc0 : c = 0
    · exfalso
      rw [hc0, mul_zero] at hc_eq
      have har : a + r = 0 := by linarith
      -- r = -a, r² = a²
      have hr2 : r^2 = a^2 := by
        have : r = -a := by linarith
        rw [this]; ring
      -- a² + b² = a², so b² = 0
      have : b^2 = 0 := by linarith [hr, hr2]
      apply hb
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    · -- c ≠ 0. (a - r)/2 = (b/(2c))²
      refine ⟨b / (2 * c), ?_⟩
      have h2c : (2 * c) ≠ 0 := mul_ne_zero two_ne_zero hc0
      have hcsq : c * c = -((a + r) / 2) := hc_eq.symm
      have key : (a + -r) / 2 = (b / (2 * c)) * (b / (2 * c)) := by
        have h_prod : ((a + r) / 2) * ((a - r) / 2) = -b^2 / 4 := by
          have : a^2 - r^2 = -b^2 := by linarith [hr]
          field_simp
          linarith [this]
        -- (a + -r)/2 = (a-r)/2
        have h_rewrite : (a + -r) / 2 = (a - r) / 2 := by ring
        rw [h_rewrite]
        -- (a-r)/2 = (-b²/4) / ((a+r)/2)
        -- (a+r)/2 = -c², so (a-r)/2 = -b²/(4·(-c²)) = b²/(4c²)
        have hh : (a - r) / 2 = b^2 / (4 * c^2) := by
          have hnn : (a + r) / 2 ≠ 0 := by
            intro heq
            rw [heq, mul_zero] at hcsq
            exact hc0 (by
              have : c^2 = 0 := by rw [sq]; linarith [hcsq]
              exact pow_eq_zero_iff (two_ne_zero) |>.mp this)
          have : (a + r) / 2 = -c^2 := by rw [sq]; linarith [hcsq]
          rw [← h_prod, this] at *
          field_simp
          nlinarith [hr]
        rw [hh]
        field_simp
        ring
      exact key

/-- In a quadratic extension `K` of a real closed field `R`, there exists
`j : K` with `j^2 = -1`. -/
theorem exists_sq_neg_one_of_finrank_eq_two
    (K : Type*) [Field K] [Algebra R K]
    (hK : Module.finrank R K = 2) : ∃ j : K, j ^ 2 = -1 := by
  haveI : FiniteDimensional R K := FiniteDimensional.of_finrank_eq_succ hK
  -- Step 1: find e ∈ K not in range of algebraMap
  have hbot_ne_top : (⊥ : Subalgebra R K) ≠ ⊤ := by
    intro h
    have : Module.finrank R K = 1 :=
      Subalgebra.bot_eq_top_iff_finrank_eq_one.mp h
    omega
  obtain ⟨e, he⟩ : ∃ e : K, e ∉ Set.range (algebraMap R K) := by
    by_contra hall
    push_neg at hall
    apply hbot_ne_top
    apply eq_top_iff.mpr
    intro e _
    rw [Algebra.mem_bot]
    exact hall e
  -- Step 2: minpoly e has natDegree exactly 2
  have hint : IsIntegral R e := Algebra.IsIntegral.isIntegral e
  have hdeg : (minpoly R e).natDegree = 2 := by
    have h1 : 2 ≤ (minpoly R e).natDegree :=
      (minpoly.two_le_natDegree_iff hint).mpr he
    have h2 : (minpoly R e).natDegree ≤ Module.finrank R K :=
      minpoly.natDegree_le _
    omega
  set c₁ := (minpoly R e).coeff 1
  set c₀ := (minpoly R e).coeff 0
  have hmonic : (minpoly R e).Monic := minpoly.monic hint
  have hleadcoeff : (minpoly R e).coeff 2 = 1 := by
    rw [← hdeg]; exact hmonic.coeff_natDegree
  have haeval : (Polynomial.aeval e) (minpoly R e) = 0 := minpoly.aeval R e
  -- Expand: aeval e p = c₀•1 + c₁•e + 1•e^2
  have hsum : (minpoly R e).coeff 0 • (1 : K) + (minpoly R e).coeff 1 • e +
              (minpoly R e).coeff 2 • e^2 = 0 := by
    have := haeval
    rw [Polynomial.aeval_eq_sum_range' (n := 3) (by omega)] at this
    simp [Finset.sum_range_succ] at this
    have helper : ∀ r : R, r • (1 : K) = r • (1 : K) := fun _ => rfl
    linarith [this]
  sorry

theorem isSquare_of_finrank_base_eq_two
    (K : Type*) [Field K] [Algebra R K]
    (hK : Module.finrank R K = 2) (x : K) : IsSquare x := sorry

end Algebraic

end IsRealClosed
