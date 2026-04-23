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
    -- Goal: IsSquare ((a + -r) / 2). We have: -(a+r)/2 = c*c for some c.
    obtain ⟨c, hc⟩ := h
    by_cases hc0 : c = 0
    · -- c = 0 gives a contradiction with b ≠ 0.
      exfalso
      rw [hc0, mul_zero] at hc
      -- hc : -((a+r)/2) = 0
      have har : a + r = 0 := by linarith
      have hr_eq : r = -a := by linarith
      have hab : a^2 + b^2 = a^2 := by
        calc a^2 + b^2 = r^2 := hr.symm
          _ = (-a)^2 := by rw [hr_eq]
          _ = a^2 := by ring
      have hb0 : b^2 = 0 := by linarith
      exact hb ((pow_eq_zero_iff two_ne_zero).mp hb0)
    · refine ⟨b / (2 * c), ?_⟩
      -- Goal: (a + -r)/2 = (b/(2c)) * (b/(2c))
      have h2c : (2 * c) ≠ 0 := mul_ne_zero two_ne_zero hc0
      have hc_sq : c^2 = -((a + r) / 2) := by
        have hcc : c * c = -((a + r) / 2) := hc.symm
        linear_combination hcc
      -- From hc_sq: a + r = -2c²
      have har_eq : a + r = -2 * c^2 := by linarith
      -- b² = r² - a² = (r-a)(r+a), and r+a = -2c², so r - a = -b²/(2c²) (or a - r = b²/(2c²))
      have hc2_ne : c^2 ≠ 0 := pow_ne_zero _ hc0
      have h_prod : (a + r) * (a - r) = -(b^2) := by
        have : a^2 - r^2 = -(b^2) := by linarith [hr]
        linear_combination this
      have h_amr : a - r = b^2 / (2 * c^2) := by
        have h1 : a + r ≠ 0 := by
          rw [har_eq]
          intro heq
          have : c^2 = 0 := by linarith
          exact hc2_ne this
        have h2 : a - r = -(b^2) / (a + r) := by
          field_simp
          linear_combination h_prod
        rw [h2, har_eq]
        field_simp
      have h_amr' : a + -r = b^2 / (2 * c^2) := by
        have : a + -r = a - r := by ring
        rw [this, h_amr]
      -- Goal: (a + -r)/2 = (b/(2c))*(b/(2c))
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
  -- Step 2: minpoly e has natDegree = 2
  have hint : IsIntegral R e := Algebra.IsIntegral.isIntegral e
  have hdeg : (minpoly R e).natDegree = 2 := by
    have h1 : 2 ≤ (minpoly R e).natDegree :=
      (minpoly.two_le_natDegree_iff hint).mpr he
    have h2 : (minpoly R e).natDegree ≤ Module.finrank R K :=
      minpoly.natDegree_le _
    omega
  set c₁ : R := (minpoly R e).coeff 1 with hc₁_def
  set c₀ : R := (minpoly R e).coeff 0 with hc₀_def
  have hmonic : (minpoly R e).Monic := minpoly.monic hint
  have hleadcoeff : (minpoly R e).coeff 2 = 1 := by
    rw [← hdeg]; exact hmonic.coeff_natDegree
  have haeval : (Polynomial.aeval e) (minpoly R e) = 0 := minpoly.aeval R e
  -- Get the equation: e² + (algebraMap c₁) * e + (algebraMap c₀) = 0
  have hesq_eq : e^2 + (algebraMap R K c₁) * e + (algebraMap R K c₀) = 0 := by
    have hexpand :
        (Polynomial.aeval e) (minpoly R e) =
          ∑ i ∈ Finset.range 3, (minpoly R e).coeff i • e^i :=
      Polynomial.aeval_eq_sum_range' (by omega) e
    rw [haeval] at hexpand
    -- hexpand : 0 = ∑ i ∈ range 3, coeff i • e^i
    rw [show (3 : ℕ) = 2 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one] at hexpand
    -- hexpand : 0 = coeff 0 • e^0 + coeff 1 • e^1 + coeff 2 • e^2
    rw [hleadcoeff, ← hc₁_def, ← hc₀_def, pow_zero, pow_one, one_smul,
        Algebra.smul_def, Algebra.smul_def, mul_one] at hexpand
    -- hexpand : 0 = algebraMap c₀ + algebraMap c₁ * e + e^2
    linear_combination -hexpand
  -- Define A = algebraMap c₁, B = algebraMap c₀ in K.
  set A : K := algebraMap R K c₁ with hA_def
  set B : K := algebraMap R K c₀ with hB_def
  -- β² = A²/4 - B = algebraMap(c₁²/4 - c₀) = algebraMap d
  set d : R := c₁^2 / 4 - c₀ with hd_def
  set β : K := e + A / 2 with hβ_def
  have h2K : (2 : K) ≠ 0 := two_ne_zero
  have h4K : (4 : K) ≠ 0 := four_ne_zero
  have hβsq : β^2 = algebraMap R K d := by
    rw [hβ_def]
    -- β² = e² + 2·e·(A/2) + (A/2)² = e² + A·e + A²/4
    have h_exp : (e + A / 2)^2 = e^2 + A*e + A^2/4 := by
      field_simp
      ring
    rw [h_exp]
    -- Substitute e² = -A·e - B
    have he2 : e^2 = -(A * e) - B := by
      have := hesq_eq
      rw [hA_def, hB_def] at this ⊢
      linear_combination this
    rw [he2]
    -- -A·e - B + A·e + A²/4 = A²/4 - B
    have hsimp : -(A * e) - B + A * e + A^2/4 = A^2/4 - B := by ring
    rw [hsimp]
    -- A²/4 = algebraMap (c₁²/4), B = algebraMap c₀, so A²/4 - B = algebraMap(c₁²/4 - c₀) = algebraMap d
    rw [hA_def, hB_def, hd_def]
    rw [map_sub, map_div₀, map_pow]
    congr 1
    -- Goal: algebraMap R K (c₁^2) / algebraMap R K 4 = (algebraMap R K c₁)^2 / 4
    · rw [map_pow]
    · rw [show (4 : K) = algebraMap R K 4 from (map_ofNat _ 4).symm]
  -- d is not a square
  have hd_not_sq : ¬ IsSquare d := by
    rintro ⟨s, hs⟩
    apply he
    -- β² = (algebraMap s)²
    have hβ2' : β^2 = (algebraMap R K s)^2 := by
      rw [hβsq, hs]
      rw [← map_mul, sq]
    -- (β - algebraMap s)(β + algebraMap s) = 0
    have hfac : (β - algebraMap R K s) * (β + algebraMap R K s) = 0 := by
      have : (β - algebraMap R K s) * (β + algebraMap R K s) =
          β^2 - (algebraMap R K s)^2 := by ring
      rw [this, hβ2', sub_self]
    rcases mul_eq_zero.mp hfac with h1 | h1
    · have hβs : β = algebraMap R K s := by
        have := h1
        linear_combination this
      refine ⟨s - c₁/2, ?_⟩
      have he_eq : e = β - A/2 := by rw [hβ_def]; ring
      rw [he_eq, hβs]
      rw [hA_def, map_sub, map_div₀]
      rw [show (2 : K) = algebraMap R K 2 from (map_ofNat _ 2).symm]
    · have hβs : β = -algebraMap R K s := by
        have := h1
        linear_combination this
      refine ⟨-s - c₁/2, ?_⟩
      have he_eq : e = β - A/2 := by rw [hβ_def]; ring
      rw [he_eq, hβs]
      rw [hA_def, map_sub, map_neg, map_div₀]
      rw [show (2 : K) = algebraMap R K 2 from (map_ofNat _ 2).symm]
  -- -d is a square
  have hneg_d_sq : IsSquare (-d) := by
    rcases isSquare_or_isSquare_neg d with h | h
    · exact absurd h hd_not_sq
    · exact h
  obtain ⟨u, hu⟩ := hneg_d_sq  -- hu : -d = u * u
  have hu_ne : u ≠ 0 := by
    intro heq
    rw [heq, mul_zero] at hu
    -- hu : -d = 0
    have hd_zero : d = 0 := by linarith
    apply hd_not_sq
    exact ⟨0, by rw [hd_zero]; ring⟩
  -- j = β / algebraMap u
  refine ⟨β / (algebraMap R K u), ?_⟩
  have hu_ne_K : algebraMap R K u ≠ 0 := by
    intro heq
    exact hu_ne (FaithfulSMul.algebraMap_injective R K (by rw [heq]; simp))
  rw [div_pow]
  rw [hβsq]
  rw [show (algebraMap R K u)^2 = algebraMap R K (u^2) from (map_pow _ _ _).symm]
  have hu2 : u^2 = -d := by rw [sq]; linarith [hu]
  rw [hu2]
  -- Goal: algebraMap R K d / algebraMap R K (-d) = -1
  rw [← map_div₀]
  have hd_ne : d ≠ 0 := by
    intro heq
    apply hd_not_sq
    exact ⟨0, by rw [heq]; ring⟩
  have hdd : d / (-d) = -1 := by field_simp
  rw [hdd]
  rw [map_neg, map_one]

theorem isSquare_of_finrank_base_eq_two
    (K : Type*) [Field K] [Algebra R K]
    (hK : Module.finrank R K = 2) (x : K) : IsSquare x := sorry

end Algebraic

end IsRealClosed
