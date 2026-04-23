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

/-- In a real closed field, given `a b : R` with `b ≠ 0` and `r^2 = a^2 + b^2`,
there exists `r' : R` with `r'^2 = a^2 + b^2` and `(a + r')/2` is a square. -/
private lemma aux_choose_sqrt
    {a b r : R} (hb : b ≠ 0) (hr : r^2 = a^2 + b^2) :
    ∃ r' : R, r'^2 = a^2 + b^2 ∧ IsSquare ((a + r') / 2) := by
  rcases isSquare_or_isSquare_neg ((a + r) / 2) with h | h
  · exact ⟨r, hr, h⟩
  · -- Use -r instead of r
    refine ⟨-r, ?_, ?_⟩
    · linear_combination hr
    · -- Need: IsSquare ((a + -r) / 2).
      -- We have: (a+r)/2 + (a-r)/2 = a and ((a+r)/2)·((a-r)/2) = (a²-r²)/4 = -b²/4.
      -- If -(a+r)/2 = c² with c ≠ 0, then (a-r)/2 = -b²/(4·(a+r)/2) = -b²/(-4c²) = (b/(2c))²
      obtain ⟨c, hc⟩ := h  -- hc : -(a+r)/2 = c * c
      -- First handle c = 0 case: then a = -r, so r² = a², so b² = 0, contradicting b ≠ 0.
      by_cases hc0 : c = 0
      · exfalso
        rw [hc0, mul_zero] at hc
        have har : a + r = 0 := by linarith
        have hr_eq : r = -a := by linarith
        have : a^2 + b^2 = a^2 := by
          rw [← hr, hr_eq]; ring
        have hb0 : b^2 = 0 := by linarith
        exact hb (pow_eq_zero_iff (two_ne_zero)).mp hb0
      · -- c ≠ 0
        refine ⟨b / (2 * c), ?_⟩
        have h2c_ne : (2 * c) ≠ 0 := mul_ne_zero two_ne_zero hc0
        have h2c2_ne : (2 * c)^2 ≠ 0 := pow_ne_zero _ h2c_ne
        -- Goal: (a + -r) / 2 = (b / (2c)) * (b / (2c))
        -- From hc: -(a+r)/2 = c*c, i.e., a+r = -2c²
        have har_eq : a + r = -(2 * c^2) := by
          have : c * c = c^2 := by ring
          rw [this] at hc
          linarith
        -- From hr: r² = a²+b², so b² = r² - a² = (r-a)(r+a) = -(a+r)(a-r)
        -- Wait: r² - a² = (r-a)(r+a). So b² = (r-a)(r+a) = (-(a-r))(a+r) = -(a-r)(a+r)
        -- Hmm let me recompute: b² = r² - a² = (r-a)(r+a).
        -- So (a-r) = -(r-a), so b² = -(a-r)(r+a) = -(a-r)(a+r). Yes.
        -- Now a-r = a+(-r), and a+r = -2c². So b² = -(a-r)·(-2c²) = 2c²·(a-r).
        -- So (a + -r) = a - r = b²/(2c²).
        -- Goal: (a + -r)/2 = b²/(4c²) = b²/(2c)².
        have hkey : a + -r = b^2 / c^2 - 0 := by
          -- (a-r)(a+r) = a² - r² = -b². So (a-r) = -b²/(a+r) = -b²/(-2c²) = b²/(2c²).
          -- Hmm wait: we'd need a ≠ r for this. a+r = -2c² ≠ 0 (since c ≠ 0).
          have hc2_ne : c^2 ≠ 0 := pow_ne_zero _ hc0
          have h_prod : (a - r) * (a + r) = -(b^2) := by
            have : a^2 - r^2 = -(b^2) := by linarith [hr]
            linear_combination this
          have : a + r ≠ 0 := by
            intro heq
            rw [heq] at har_eq
            have : c^2 = 0 := by linarith
            exact hc0 ((pow_eq_zero_iff two_ne_zero).mp this)
          have h_amr : a - r = -(b^2) / (a + r) := by
            field_simp
            linear_combination h_prod
          rw [har_eq] at h_amr
          have : a - r = b^2 / (2 * c^2) := by
            rw [h_amr]
            field_simp
            ring
          have : a + -r = b^2 / (2 * c^2) := by linarith [this]
          rw [this]
          field_simp
          ring
        -- Now goal: (a + -r)/2 = (b/(2c)) * (b/(2c))
        rw [hkey]
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
  -- Step 2: minpoly e has natDegree exactly 2
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
  -- Convert aeval to explicit form
  have hesq_eq : e^2 + (algebraMap R K c₁) * e + (algebraMap R K c₀) = 0 := by
    have hexpand :
        (Polynomial.aeval e) (minpoly R e) =
          ∑ i ∈ Finset.range 3, (minpoly R e).coeff i • e^i :=
      Polynomial.aeval_eq_sum_range' (by omega) e
    rw [haeval] at hexpand
    -- hexpand : 0 = sum_{i=0..2} coeff i • e^i
    simp [Finset.sum_range_succ, Finset.sum_range_zero] at hexpand
    rw [hleadcoeff, ← hc₁_def, ← hc₀_def] at hexpand
    -- hexpand now: c₀ • 1 + c₁ • e + 1 • e^2 = 0 (or 0 = ... depending on direction)
    -- Convert scalar actions
    have h_e0 : e^0 = (1 : K) := pow_zero e
    have h_e1 : e^1 = e := pow_one e
    -- Let me use Algebra.smul_def: r • x = algebraMap r * x
    have : c₀ • (1 : K) + c₁ • e + (1 : R) • (e^2) = 0 := by
      convert hexpand using 1
      simp [h_e0, h_e1]
      ring
    rw [one_smul] at this
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at this
    linear_combination this
  -- Define β = e + algebraMap(c₁/2), d = c₁²/4 - c₀
  set d : R := c₁^2 / 4 - c₀ with hd_def
  set β : K := e + (algebraMap R K) (c₁ / 2) with hβ_def
  have hβsq : β^2 = (algebraMap R K) d := by
    rw [hβ_def, hd_def, add_pow_two]
    -- β^2 = e^2 + 2·e·(c₁/2) + (c₁/2)^2
    -- Substitute e² = -algebraMap c₁ · e - algebraMap c₀
    have he2 : e^2 = -(algebraMap R K c₁) * e - (algebraMap R K c₀) := by
      linear_combination hesq_eq
    rw [he2]
    rw [map_sub, map_pow]
    have h2c : (2 : K) * e * (algebraMap R K (c₁ / 2)) = (algebraMap R K c₁) * e := by
      have : (2 : K) * (algebraMap R K (c₁ / 2)) = algebraMap R K c₁ := by
        rw [show (2 : K) = algebraMap R K 2 from (map_ofNat (algebraMap R K) 2).symm,
            ← map_mul]
        congr 1
        field_simp
      ring_nf
      rw [mul_assoc, this]
    rw [h2c]
    have hquarter : (algebraMap R K (c₁ / 2))^2 = algebraMap R K (c₁^2 / 4) := by
      rw [← map_pow]
      congr 1
      field_simp
      ring
    rw [hquarter]
    have : (algebraMap R K (c₁^2)) / 4 = algebraMap R K (c₁^2 / 4) := by
      rw [show (4 : K) = algebraMap R K 4 from (map_ofNat (algebraMap R K) 4).symm,
          ← map_div₀]
    rw [this]
    ring
  -- d is not a square: if d = s², then β = ±algebraMap s, so e ∈ R, contradiction.
  have hd_not_sq : ¬ IsSquare d := by
    rintro ⟨s, hs⟩
    apply he
    -- From hβsq and hs: β² = algebraMap(s²) = (algebraMap s)²
    have hβ2 : β^2 = (algebraMap R K s)^2 := by
      rw [hβsq, hs]
      push_cast
      rw [← map_mul]
      congr 1
      rw [sq]
    -- So (β - algebraMap s)(β + algebraMap s) = 0
    have hfac : (β - algebraMap R K s) * (β + algebraMap R K s) = 0 := by
      have : (β - algebraMap R K s) * (β + algebraMap R K s) = β^2 - (algebraMap R K s)^2 := by
        ring
      rw [this, hβ2]
      ring
    -- In a field, either β = algebraMap s or β = -algebraMap s
    rcases mul_eq_zero.mp hfac with h1 | h1
    · have hβs : β = algebraMap R K s := by linarith
      -- e = β - algebraMap(c₁/2) = algebraMap(s - c₁/2)
      refine ⟨s - c₁/2, ?_⟩
      have : e = β - (algebraMap R K) (c₁ / 2) := by rw [hβ_def]; ring
      rw [this, hβs, map_sub]
    · have hβs : β = -algebraMap R K s := by linarith
      refine ⟨-s - c₁/2, ?_⟩
      have : e = β - (algebraMap R K) (c₁ / 2) := by rw [hβ_def]; ring
      rw [this, hβs]
      push_cast
      rw [map_sub]
      ring
  -- So -d is a square: -d = u²
  have hneg_d_sq : IsSquare (-d) := by
    rcases isSquare_or_isSquare_neg d with h | h
    · exact absurd h hd_not_sq
    · exact h
  obtain ⟨u, hu⟩ := hneg_d_sq  -- hu : -d = u * u
  have hu_ne : u ≠ 0 := by
    intro heq
    rw [heq, mul_zero] at hu
    have hd_zero : d = 0 := by linarith
    apply hd_not_sq
    exact ⟨0, by rw [hd_zero]; ring⟩
  -- j = β / algebraMap u. Then j² = β² / (algebraMap u)² = algebraMap d / algebraMap(u²)
  -- = algebraMap(d/u²) = algebraMap(d/-d) = algebraMap(-1) = -1.
  refine ⟨β / (algebraMap R K u), ?_⟩
  rw [div_pow, hβsq]
  have hu_ne_K : algebraMap R K u ≠ 0 := by
    intro heq
    exact hu_ne ((FaithfulSMul.algebraMap_injective R K) (by simpa using heq))
  have hu2_K : (algebraMap R K u)^2 = algebraMap R K (u^2) := (map_pow _ _ _).symm
  rw [hu2_K]
  have hdu2 : d / u^2 = -1 := by
    have hu2_ne : u^2 ≠ 0 := pow_ne_zero _ hu_ne
    have : u^2 = -d := by rw [sq]; linarith [hu]
    rw [this]
    field_simp
  rw [← map_div₀, hdu2]
  push_cast
  rfl

theorem isSquare_of_finrank_base_eq_two
    (K : Type*) [Field K] [Algebra R K]
    (hK : Module.finrank R K = 2) (x : K) : IsSquare x := sorry

end Algebraic

end IsRealClosed
