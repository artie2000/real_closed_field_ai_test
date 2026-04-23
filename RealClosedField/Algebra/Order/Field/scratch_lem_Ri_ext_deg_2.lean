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

/-- In a real closed field, every element of the form `a^2 + b^2` is a square. -/
private lemma aux_isSquare_sum_two_sq (a b : R) : IsSquare (a^2 + b^2) :=
  isSquare_of_isSumSq (IsSumSq.add (IsSumSq.sq a) (IsSumSq.sq b))

/-- In a real closed field, given `a b : R` with `b ≠ 0` and `r^2 = a^2 + b^2`,
there exists `r' : R` with `r'^2 = a^2 + b^2` and `(a + r')/2` is a square. -/
private lemma aux_choose_sqrt
    {a b r : R} (hb : b ≠ 0) (hr : r^2 = a^2 + b^2) :
    ∃ r' : R, r'^2 = a^2 + b^2 ∧ IsSquare ((a + r') / 2) := by
  rcases isSquare_or_isSquare_neg ((a + r) / 2) with h | h
  · exact ⟨r, hr, h⟩
  · refine ⟨-r, by linear_combination hr, ?_⟩
    obtain ⟨c, hc⟩ := h  -- hc : -((a+r)/2) = c * c
    by_cases hc0 : c = 0
    · exfalso
      rw [hc0, mul_zero] at hc
      have har : a + r = 0 := by linarith
      have hr_eq : r = -a := by linarith
      have h1 : r^2 = a^2 := by rw [hr_eq]; ring
      have hab : a^2 + b^2 = a^2 := by linarith [hr]
      have hb0 : b^2 = 0 := by linarith
      exact hb ((pow_eq_zero_iff two_ne_zero).mp hb0)
    · refine ⟨b / (2 * c), ?_⟩
      have h2c_ne : (2 * c) ≠ 0 := mul_ne_zero two_ne_zero hc0
      have hc2_ne : c^2 ≠ 0 := pow_ne_zero _ hc0
      have har_eq : a + r = -(2 * c^2) := by
        have hcsq : c * c = c^2 := (sq c).symm
        have hcc : -((a + r) / 2) = c^2 := by rw [hc, hcsq]
        linarith
      have h_ar_ne : a + r ≠ 0 := by
        rw [har_eq]
        intro heq
        have hc0' : c^2 = 0 := by linarith
        exact hc2_ne hc0'
      have h_prod : (a + r) * (a - r) = -(b^2) := by
        linear_combination -hr
      have h_amr : a - r = -(b^2) / (a + r) := by
        field_simp
        linear_combination h_prod
      have h_amr' : a + -r = b^2 / (2 * c^2) := by
        have heq : a + -r = a - r := by ring
        rw [heq, h_amr, har_eq]
        field_simp
      rw [h_amr']
      field_simp
      ring

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
  -- Step 2: minpoly e has natDegree = 2, extract coefficients
  have hint : IsIntegral R e := Algebra.IsIntegral.isIntegral e
  have hdeg : (minpoly R e).natDegree = 2 := by
    have h1 : 2 ≤ (minpoly R e).natDegree :=
      (minpoly.two_le_natDegree_iff hint).mpr he
    have h2 : (minpoly R e).natDegree ≤ Module.finrank R K :=
      minpoly.natDegree_le _
    omega
  have hmonic : (minpoly R e).Monic := minpoly.monic hint
  have hleadcoeff : (minpoly R e).coeff 2 = 1 := by
    rw [← hdeg]; exact hmonic.coeff_natDegree
  have haeval : (Polynomial.aeval e) (minpoly R e) = 0 := minpoly.aeval R e
  -- Let c₀ = coeff 0, c₁ = coeff 1 (as concrete nums).
  -- Derive: e² + c₁·e + c₀ = 0 (with scalar-algebraMap).
  have hesq_eq :
      e^2 + algebraMap R K ((minpoly R e).coeff 1) * e
        + algebraMap R K ((minpoly R e).coeff 0) = 0 := by
    have hexpand :
        (Polynomial.aeval e) (minpoly R e) =
          ∑ i ∈ Finset.range 3, (minpoly R e).coeff i • e^i :=
      Polynomial.aeval_eq_sum_range' (by omega) e
    rw [haeval] at hexpand
    rw [show (3 : ℕ) = 2 + 1 from rfl, Finset.sum_range_succ,
        show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ,
        Finset.sum_range_one] at hexpand
    rw [hleadcoeff, pow_zero, pow_one, one_smul,
        Algebra.smul_def, Algebra.smul_def, mul_one] at hexpand
    linear_combination -hexpand
  -- Set d := c₁²/4 - c₀ and β := e + algebraMap(c₁/2).
  -- We will prove β² = algebraMap d.
  set c₁ : R := (minpoly R e).coeff 1 with hc₁_def
  set c₀ : R := (minpoly R e).coeff 0 with hc₀_def
  -- hesq_eq is now: e^2 + algebraMap c₁ * e + algebraMap c₀ = 0
  have hfour : (algebraMap R K (4 : R)) = (4 : K) := map_ofNat _ 4
  have htwo : (algebraMap R K (2 : R)) = (2 : K) := map_ofNat _ 2
  -- d = c₁²/4 - c₀
  have hβ_sq : (e + algebraMap R K c₁ / 2)^2 = algebraMap R K (c₁^2 / 4 - c₀) := by
    have he2 : e^2 = -(algebraMap R K c₁ * e) - algebraMap R K c₀ := by
      linear_combination hesq_eq
    have hexpand : (e + algebraMap R K c₁ / 2)^2 =
        e^2 + algebraMap R K c₁ * e + (algebraMap R K c₁)^2 / 4 := by
      field_simp; ring
    rw [hexpand, he2]
    rw [map_sub, map_div₀, hfour, map_pow]
    ring
  -- d is not a square in R: if so, β = ±algebraMap s, putting e ∈ R.
  have hd_not_sq : ¬ IsSquare (c₁^2 / 4 - c₀) := by
    rintro ⟨s, hs⟩
    apply he
    have hβ2' : (e + algebraMap R K c₁ / 2)^2 = (algebraMap R K s)^2 := by
      rw [hβ_sq]
      have hseq : c₁^2 / 4 - c₀ = s^2 := by rw [hs]; ring
      rw [hseq, map_pow]
    have hfac :
        ((e + algebraMap R K c₁ / 2) - algebraMap R K s) *
        ((e + algebraMap R K c₁ / 2) + algebraMap R K s) = 0 := by
      have h_expand :
          ((e + algebraMap R K c₁ / 2) - algebraMap R K s) *
          ((e + algebraMap R K c₁ / 2) + algebraMap R K s) =
          (e + algebraMap R K c₁ / 2)^2 - (algebraMap R K s)^2 := by ring
      rw [h_expand, hβ2', sub_self]
    rcases mul_eq_zero.mp hfac with h1 | h1
    · have hβs : e + algebraMap R K c₁ / 2 = algebraMap R K s := by
        linear_combination h1
      refine ⟨s - c₁/2, ?_⟩
      show algebraMap R K (s - c₁/2) = e
      rw [map_sub, map_div₀, htwo]
      linear_combination -hβs
    · have hβs : e + algebraMap R K c₁ / 2 = -algebraMap R K s := by
        linear_combination h1
      refine ⟨-s - c₁/2, ?_⟩
      show algebraMap R K (-s - c₁/2) = e
      rw [map_sub, map_neg, map_div₀, htwo]
      linear_combination -hβs
  -- Apply isSquare_or_isSquare_neg to d; get u with -d = u²
  have hneg_d_sq : IsSquare (-(c₁^2 / 4 - c₀)) := by
    rcases isSquare_or_isSquare_neg (c₁^2 / 4 - c₀) with h | h
    · exact absurd h hd_not_sq
    · exact h
  obtain ⟨u, hu⟩ := hneg_d_sq  -- hu : -(c₁²/4 - c₀) = u*u
  have hu_ne : u ≠ 0 := by
    intro heq
    rw [heq, mul_zero] at hu
    have hd_zero : c₁^2 / 4 - c₀ = 0 := by linarith
    apply hd_not_sq
    exact ⟨0, by rw [hd_zero]; ring⟩
  refine ⟨(e + algebraMap R K c₁ / 2) / (algebraMap R K u), ?_⟩
  have hu_ne_K : algebraMap R K u ≠ 0 := by
    intro heq
    exact hu_ne (FaithfulSMul.algebraMap_injective R K (by rw [heq]; simp))
  rw [div_pow, hβ_sq,
      show (algebraMap R K u)^2 = algebraMap R K (u^2) from (map_pow _ _ _).symm]
  have hu2 : u^2 = -(c₁^2 / 4 - c₀) := by
    have huu : u * u = -(c₁^2 / 4 - c₀) := hu.symm
    linear_combination -huu
  rw [hu2, ← map_div₀]
  have hd_ne : c₁^2 / 4 - c₀ ≠ 0 := by
    intro heq
    apply hd_not_sq
    exact ⟨0, by rw [heq]; ring⟩
  have hdd : (c₁^2 / 4 - c₀) / (-(c₁^2 / 4 - c₀)) = (-1 : R) := by field_simp
  rw [hdd, map_neg, map_one]

theorem isSquare_of_finrank_base_eq_two
    (K : Type*) [Field K] [Algebra R K]
    (hK : Module.finrank R K = 2) (x : K) : IsSquare x := sorry

end Algebraic

end IsRealClosed
