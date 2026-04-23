/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.PowerBasis
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.TFAE
import Mathlib.Tactic.FinCases
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

/-- There is no nontrivial odd-degree finite extension of a real closed field `R`:
any finite extension `K/R` with `Module.finrank R K` odd has `R → K` surjective. -/
theorem surjective_algebraMap_of_odd_finrank
    (K : Type*) [Field K] [Algebra R K] [FiniteDimensional R K]
    (hodd : Odd (Module.finrank R K)) :
    Function.Surjective (algebraMap R K) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element R K
  have hint : IsIntegral R α := .of_finite R α
  have hirr : Irreducible (minpoly R α) := minpoly.irreducible hint
  have hdeg : (minpoly R α).natDegree = Module.finrank R K :=
    (Field.primitive_element_iff_minpoly_natDegree_eq R α).mp hα
  rw [← hdeg] at hodd
  obtain ⟨r, hr⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree hodd
  have hdeg1 : (minpoly R α).natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (Polynomial.degree_eq_one_of_irreducible_of_root hirr hr)
  have hfin1 : Module.finrank R K = 1 := by omega
  intro x
  have hbot : (⊥ : Subalgebra R K) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one hfin1
  have hx : x ∈ (⊥ : Subalgebra R K) := by rw [hbot]; exact Algebra.mem_top
  exact Algebra.mem_bot.mp hx

/-- Auxiliary: any quadratic extension of a real closed field admits a power basis whose
generator is a root of `X ^ 2 + 1`. -/
private theorem exists_powerBasis_of_finrank_eq_two_aux
    (L : Type*) [Field L] [Algebra R L] (hL : Module.finrank R L = 2) :
    ∃ pb : PowerBasis R L, minpoly R pb.gen = Polynomial.X ^ 2 + Polynomial.C (1 : R) := by
  have hFin : FiniteDimensional R L := .of_finrank_eq_succ hL
  have hInj : Function.Injective (algebraMap R L) := (algebraMap R L).injective
  have hne : ∃ x : L, x ∉ (algebraMap R L).range := by
    by_contra h
    push_neg at h
    have hTop : (⊥ : Subalgebra R L) = ⊤ := by
      rw [eq_top_iff]
      rintro x -
      obtain ⟨r, hr⟩ := h x
      exact Algebra.mem_bot.mpr ⟨r, hr⟩
    have heq : Module.finrank R (⊥ : Subalgebra R L) = Module.finrank R L := by
      rw [hTop]; exact Subalgebra.topEquiv.toLinearEquiv.finrank_eq
    rw [Subalgebra.finrank_bot] at heq
    omega
  obtain ⟨x, hx⟩ := hne
  have hxI : IsIntegral R x := .of_finite R x
  have hdeg2 : (minpoly R x).natDegree = 2 := by
    have h2 : 2 ≤ (minpoly R x).natDegree := (minpoly.two_le_natDegree_iff hxI).mpr hx
    have hle : (minpoly R x).natDegree ≤ Module.finrank R L := minpoly.natDegree_le x
    omega
  set a : R := (minpoly R x).coeff 1 with ha_def
  set b : R := (minpoly R x).coeff 0 with hb_def
  have hfm : (minpoly R x).Monic := minpoly.monic hxI
  have hcoeff2 : (minpoly R x).coeff 2 = 1 := by
    have hlc : (minpoly R x).leadingCoeff = 1 := hfm
    rw [Polynomial.leadingCoeff, hdeg2] at hlc
    exact hlc
  have hroot : x ^ 2 + (algebraMap R L) a * x + (algebraMap R L) b = 0 := by
    have hlt : (minpoly R x).natDegree < 3 := by omega
    have haev := minpoly.aeval R x
    rw [Polynomial.aeval_eq_sum_range' hlt] at haev
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Algebra.smul_def, pow_zero, mul_one, pow_one] at haev
    rw [hcoeff2, map_one, one_mul] at haev
    show x ^ 2 + (algebraMap R L) ((minpoly R x).coeff 1) * x +
      (algebraMap R L) ((minpoly R x).coeff 0) = 0
    linear_combination haev
  set c : R := a ^ 2 / 4 - b with hc_def
  set y : L := x + (algebraMap R L) (a / 2) with hy_def
  have h2R : (2 : R) ≠ 0 := two_ne_zero
  have hy_sq : y ^ 2 = (algebraMap R L) c := by
    have half_sq : (algebraMap R L) (a / 2) ^ 2 = (algebraMap R L) (a ^ 2 / 4) := by
      rw [← map_pow]
      congr 1
      field_simp
      ring
    have half_times : 2 * (algebraMap R L) (a / 2) = (algebraMap R L) a := by
      have : (2 : L) = (algebraMap R L) 2 := (map_ofNat (algebraMap R L) 2).symm
      rw [this, ← map_mul]
      congr 1
      field_simp
    have expand : y ^ 2 = x ^ 2 + (algebraMap R L) a * x + (algebraMap R L) (a ^ 2 / 4) := by
      show (x + (algebraMap R L) (a / 2)) ^ 2 = _
      have : (x + (algebraMap R L) (a / 2)) ^ 2 =
          x ^ 2 + x * (2 * (algebraMap R L) (a / 2)) + (algebraMap R L) (a / 2) ^ 2 := by ring
      rw [this, half_sq, half_times]
      ring
    rw [expand]
    show x ^ 2 + (algebraMap R L) a * x + (algebraMap R L) (a ^ 2 / 4) =
      (algebraMap R L) (a ^ 2 / 4 - b)
    rw [map_sub]
    linear_combination hroot
  have hy_ni : y ∉ (algebraMap R L).range := by
    rintro ⟨r, hr⟩
    apply hx
    refine ⟨r - a / 2, ?_⟩
    have hr' : (algebraMap R L) r = x + (algebraMap R L) (a / 2) := hr
    rw [map_sub]
    linear_combination hr'
  have hc_ni : ¬ IsSquare c := by
    rintro ⟨s, hs⟩
    have halg_sq : y ^ 2 = ((algebraMap R L) s) ^ 2 := by
      rw [hy_sq, show c = s * s from hs, map_mul]
      ring
    have hfact : (y - (algebraMap R L) s) * (y + (algebraMap R L) s) = 0 := by
      linear_combination halg_sq
    apply hy_ni
    rcases mul_eq_zero.mp hfact with hd | hd
    · exact ⟨s, by linear_combination -hd⟩
    · refine ⟨-s, ?_⟩
      rw [map_neg]
      linear_combination -hd
  have hnc_sq : IsSquare (-c) := (IsRealClosed.isSquare_or_isSquare_neg c).resolve_left hc_ni
  obtain ⟨s, hs⟩ := hnc_sq
  have hs_ne : s ≠ 0 := by
    rintro rfl
    apply hc_ni
    have hmc : -c = 0 := by rw [hs]; ring
    have hc0 : c = 0 := by linear_combination -hmc
    rw [hc0]
    exact ⟨0, by ring⟩
  have hsL_ne : (algebraMap R L) s ≠ 0 :=
    (map_ne_zero_iff _ hInj).mpr hs_ne
  set sL : L := (algebraMap R L) s with hsL_def
  have hsL_sq : sL ^ 2 = - (algebraMap R L) c := by
    show ((algebraMap R L) s) ^ 2 = - (algebraMap R L) c
    rw [← map_pow, ← map_neg]
    congr 1
    rw [pow_two, ← hs]
  set α : L := y * sL⁻¹ with hα_def
  have hcL_ne : (algebraMap R L) c ≠ 0 := by
    intro hc0
    have : c = 0 := (map_eq_zero_iff _ hInj).mp hc0
    apply hc_ni
    rw [this]; exact ⟨0, by ring⟩
  have hsL_sq_ne : sL ^ 2 ≠ 0 := by
    rw [hsL_sq]; exact neg_ne_zero.mpr hcL_ne
  have hα_sq : α ^ 2 = -1 := by
    have step1 : α ^ 2 * sL ^ 2 = (algebraMap R L) c := by
      calc α ^ 2 * sL ^ 2
          = (y * sL⁻¹) ^ 2 * sL ^ 2 := by rw [hα_def]
        _ = y ^ 2 * (sL⁻¹ * sL) ^ 2 := by ring
        _ = y ^ 2 * 1 ^ 2 := by rw [inv_mul_cancel₀ hsL_ne]
        _ = y ^ 2 := by ring
        _ = (algebraMap R L) c := hy_sq
    have step2 : α ^ 2 * sL ^ 2 = (-1) * sL ^ 2 := by
      rw [step1, hsL_sq]; ring
    exact mul_right_cancel₀ hsL_sq_ne step2
  have hα_ni : α ∉ (algebraMap R L).range := by
    rintro ⟨r, hr⟩
    apply hy_ni
    refine ⟨r * s, ?_⟩
    have hy_eq : y = α * sL := by
      show y = (y * sL⁻¹) * sL
      rw [mul_assoc, inv_mul_cancel₀ hsL_ne, mul_one]
    rw [hy_eq, ← hr, hsL_def, ← map_mul]
  have hαI : IsIntegral R α := .of_finite R α
  have hmin : minpoly R α = Polynomial.X ^ 2 + Polynomial.C (1 : R) := by
    set g : Polynomial R := Polynomial.X ^ 2 + Polynomial.C (1 : R) with hg_def
    have hgm : g.Monic := Polynomial.monic_X_pow_add_C (1 : R) (by norm_num : (2 : ℕ) ≠ 0)
    have hgroot : Polynomial.aeval α g = 0 := by
      show Polynomial.aeval α (Polynomial.X ^ 2 + Polynomial.C (1 : R)) = 0
      simp [hα_sq]
    have hdα : (minpoly R α).natDegree = 2 := by
      have h2α : 2 ≤ (minpoly R α).natDegree :=
        (minpoly.two_le_natDegree_iff hαI).mpr hα_ni
      have hαle : (minpoly R α).natDegree ≤ Module.finrank R L := minpoly.natDegree_le α
      omega
    have hgdeg : g.natDegree = 2 := by
      show (Polynomial.X ^ 2 + Polynomial.C (1 : R)).natDegree = 2
      exact Polynomial.natDegree_X_pow_add_C
    refine (minpoly.unique_of_degree_le_degree_minpoly R α hgm hgroot ?_).symm
    rw [Polynomial.degree_eq_natDegree hgm.ne_zero,
        Polynomial.degree_eq_natDegree (minpoly.ne_zero hαI), hgdeg, hdα]
  have hli : LinearIndependent R ![(1 : L), α] := by
    rw [LinearIndependent.pair_iff]
    intro r t hrt
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hrt
      rw [Algebra.smul_def, mul_one] at hrt
      exact ⟨(map_eq_zero_iff _ hInj).mp hrt, rfl⟩
    · exfalso
      apply hα_ni
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hrt
      have htL : (algebraMap R L) t ≠ 0 := (map_ne_zero_iff _ hInj).mpr ht
      refine ⟨-r / t, ?_⟩
      rw [map_div₀, map_neg]
      field_simp
      linear_combination -hrt
  have hcard : Fintype.card (Fin 2) = Module.finrank R L := by
    rw [Fintype.card_fin, hL]
  let basis2 := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbasis_eq : ∀ i : Fin 2, basis2 i = α ^ (i : ℕ) := by
    intro i
    have key : basisOfLinearIndependentOfCardEqFinrank hli hcard i = ![(1 : L), α] i := by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank hli hcard]
    show basisOfLinearIndependentOfCardEqFinrank hli hcard i = α ^ (i : ℕ)
    rw [key]
    fin_cases i <;> simp
  refine ⟨{ gen := α, dim := 2, basis := basis2, basis_eq_pow := hbasis_eq }, ?_⟩
  exact hmin

/-- `R(i)` has no quadratic extension: equivalently, every element of any quadratic
extension `K` of `R` is a square in `K`. -/
theorem isSquare_of_finrank_base_eq_two
    (K : Type*) [Field K] [Algebra R K]
    (hK : Module.finrank R K = 2) (x : K) : IsSquare x := by
  obtain ⟨pb, hmin⟩ := exists_powerBasis_of_finrank_eq_two_aux R K hK
  -- pb.dim = 2 and pb.gen satisfies X^2 + 1 = 0, i.e., pb.gen^2 = -1
  haveI hFin : FiniteDimensional R K := .of_finrank_eq_succ hK
  have hInj : Function.Injective (algebraMap R K) := (algebraMap R K).injective
  -- Derive pb.dim = 2
  have hpb_dim : pb.dim = 2 := by
    have h1 : (minpoly R pb.gen).natDegree = pb.dim := pb.natDegree_minpoly
    rw [hmin] at h1
    have h2 : (Polynomial.X ^ 2 + Polynomial.C (1 : R)).natDegree = 2 :=
      Polynomial.natDegree_X_pow_add_C
    omega
  -- Derive pb.gen^2 = -1
  have hgen_sq : pb.gen ^ 2 = -1 := by
    have haev : Polynomial.aeval pb.gen (minpoly R pb.gen) = 0 := minpoly.aeval R pb.gen
    rw [hmin] at haev
    simp at haev
    linear_combination haev
  set j : K := pb.gen with hj_def
  -- Decompose x via pb.basis
  -- pb.basis is Basis (Fin pb.dim) R K
  -- We have pb.basis 0 = pb.gen ^ 0 = 1, pb.basis 1 = pb.gen ^ 1 = j
  set a : R := pb.basis.repr x ⟨0, by rw [hpb_dim]; omega⟩ with ha_def
  set b : R := pb.basis.repr x ⟨1, by rw [hpb_dim]; omega⟩ with hb_def
  have hx_decomp : x = algebraMap R K a + algebraMap R K b * j := by
    have hsum : ∑ i, pb.basis.repr x i • pb.basis i = x := pb.basis.sum_repr x
    have hbasis0 : pb.basis ⟨0, by rw [hpb_dim]; omega⟩ = 1 := by
      rw [pb.basis_eq_pow]
      simp
    have hbasis1 : pb.basis ⟨1, by rw [hpb_dim]; omega⟩ = j := by
      rw [pb.basis_eq_pow]
      simp [hj_def]
    -- Rewrite sum over Fin pb.dim = Fin 2
    have hsum2 : pb.basis.repr x ⟨0, by rw [hpb_dim]; omega⟩ • pb.basis ⟨0, by rw [hpb_dim]; omega⟩ +
                 pb.basis.repr x ⟨1, by rw [hpb_dim]; omega⟩ • pb.basis ⟨1, by rw [hpb_dim]; omega⟩ = x := by
      rw [← hsum]
      have : (Finset.univ : Finset (Fin pb.dim)) =
        {⟨0, by rw [hpb_dim]; omega⟩, ⟨1, by rw [hpb_dim]; omega⟩} := by
        ext ⟨i, hi⟩
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        rw [hpb_dim] at hi
        interval_cases i
        · left; rfl
        · right; rfl
      rw [this, Finset.sum_insert (by simp), Finset.sum_singleton]
    rw [hbasis0, hbasis1] at hsum2
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hsum2
    linear_combination -hsum2
  -- Goal: IsSquare x, where x = algebraMap a + algebraMap b * j
  by_cases hb0 : b = 0
  · -- Case b = 0: x = algebraMap a; split by isSquare_or_isSquare_neg a
    rw [hb0, map_zero, zero_mul, add_zero] at hx_decomp
    rcases isSquare_or_isSquare_neg a with ⟨c, hc⟩ | ⟨c, hc⟩
    · -- a = c * c, so x = algebraMap a = (algebraMap c)^2
      refine ⟨algebraMap R K c, ?_⟩
      rw [hx_decomp, hc, map_mul]
    · -- -a = c * c, so a = -c^2, x = algebraMap a = -(algebraMap c)^2 = (algebraMap c * j)^2
      refine ⟨algebraMap R K c * j, ?_⟩
      rw [hx_decomp]
      have ha_eq : a = -(c * c) := by linear_combination -hc
      rw [ha_eq, map_neg, map_mul]
      have : algebraMap R K c * j * (algebraMap R K c * j) = (algebraMap R K c)^2 * j^2 := by ring
      rw [this, hgen_sq]
      ring
  · -- Case b ≠ 0: find c, d with (c + d*j)^2 = algebraMap a + algebraMap b * j
    -- We want c² - d² = a, 2cd = b
    -- a² + b² is a sum of squares, so a square: let r² = a² + b²
    have hab_sq : IsSquare (a^2 + b^2) :=
      isSquare_of_isSumSq (IsSumSq.add (IsSumSq.sq a) (IsSumSq.sq b))
    obtain ⟨r, hr⟩ := hab_sq
    have hr_sq : r^2 = a^2 + b^2 := by rw [hr]; ring
    -- We want to pick sign of r so that (r + a)/2 is a square
    -- The two cases: either (r+a)/2 is a square, or -(r+a)/2 is a square
    -- In the second case, we switch r to -r: (-r + a)/2 = (a - r)/2
    -- and we need (a-r)/2 to be a square
    -- Key: (r+a)/2 * (r-a)/2 = (r² - a²)/4 = b²/4 = (b/2)²
    -- So if P := (r+a)/2 isn't a square, -P is a square, and also -Q = -(r-a)/2 = (a-r)/2 is a square
    -- because Q = (b/2)² / P and if P = -α², then Q = (b/2)² / -α² = -(b/2α)², so -Q is a square
    -- Formally: choose s := r or s := -r so that (s + a)/2 is a square
    have hexists_sign : ∃ s : R, s^2 = a^2 + b^2 ∧ IsSquare ((s + a) / 2) := by
      rcases isSquare_or_isSquare_neg ((r + a) / 2) with hsq | hsq
      · exact ⟨r, hr_sq, hsq⟩
      · refine ⟨-r, ?_, ?_⟩
        · linear_combination hr_sq
        · -- Need (a-r)/2 is a square
          -- hsq : IsSquare (-((r+a)/2))
          obtain ⟨α, hα⟩ := hsq
          -- hα : -((r+a)/2) = α * α
          have hα0_or : α = 0 ∨ α ≠ 0 := em _
          rcases hα0_or with hα0 | hα_ne
          · -- Then -(r+a)/2 = 0, so r = -a, then r² = a², a² + b² = a², b² = 0, b = 0, contra
            exfalso
            rw [hα0] at hα
            -- hα : -((r+a)/2) = 0 * 0
            have hra : r + a = 0 := by linear_combination -2 * hα
            have h1 : r^2 = a^2 := by linear_combination (r - a) * hra
            have h3 : b^2 = 0 := by linear_combination -hr_sq + h1
            apply hb0
            exact (pow_eq_zero_iff two_ne_zero).mp h3
          · -- Set β := b / (2α); claim (a - r)/2 = β²
            refine ⟨b / (2 * α), ?_⟩
            have h2α_ne : (2 : R) * α ≠ 0 := mul_ne_zero two_ne_zero hα_ne
            have h2_ne : (2 : R) ≠ 0 := two_ne_zero
            -- Goal: (-r + a) / 2 = b / (2 * α) * (b / (2 * α))
            have := mul_ne_zero h2α_ne h2α_ne
            field_simp
            linear_combination 4 * (r - a) * hα + 2 * hr_sq

    obtain ⟨s, hs_sq, hcsq⟩ := hexists_sign
    obtain ⟨c, hc⟩ := hcsq
    -- hc : (s + a) / 2 = c * c
    -- c² = (s+a)/2. Need c ≠ 0 (else s = -a, then s² = a², so b² = 0, so b = 0, contra)
    have hc0 : c ≠ 0 := by
      intro heq
      rw [heq, mul_zero] at hc
      have hsa : s + a = 0 := by linear_combination -2 * hc
      have hs_eq : s = -a := by linear_combination hsa
      have h1 : s^2 = a^2 := by rw [hs_eq]; ring
      have h2 : a^2 = a^2 + b^2 := by linear_combination -hs_sq + h1
      have h3 : b^2 = 0 := by linear_combination -h2
      apply hb0
      exact (pow_eq_zero_iff two_ne_zero).mp h3
    -- Let d := b / (2c)
    set d : R := b / (2 * c) with hd_def
    -- Verify: c² - d² = a
    have h2c_ne : (2 : R) * c ≠ 0 := mul_ne_zero two_ne_zero hc0
    have hc2_ne : c^2 ≠ 0 := pow_ne_zero _ hc0
    -- c² = (s+a)/2
    have hc2 : c^2 = (s + a) / 2 := by
      rw [sq]; linear_combination -hc
    -- d² = b² / (4c²) = b² / (4 * (s+a)/2) = b² / (2(s+a))
    -- Using (s+a)(s-a) = b², we get d² = (s-a)/2
    -- so c² - d² = (s+a)/2 - (s-a)/2 = a
    have hs_ne : s + a ≠ 0 := by
      rw [show s + a = 2 * c^2 from by linear_combination 2 * hc2]
      exact mul_ne_zero two_ne_zero hc2_ne
    have hprod : (s + a) * (s - a) = b^2 := by linear_combination hs_sq
    have hd2 : d^2 = (s - a) / 2 := by
      have : d^2 = b^2 / (2 * c)^2 := by rw [hd_def]; ring
      rw [this]
      have h2csq : (2 * c)^2 = 2 * (s + a) := by
        have : (2 * c)^2 = 4 * c^2 := by ring
        rw [this, hc2]; ring
      rw [h2csq]
      -- b² / (2 * (s+a)) = (s-a) / 2
      field_simp
      linear_combination hprod
    have hcd_eq_a : c^2 - d^2 = a := by
      rw [hc2, hd2]; ring
    -- 2cd = b
    have h2cd : 2 * c * d = b := by
      rw [hd_def]
      field_simp
    -- Define y := algebraMap c + algebraMap d * j
    refine ⟨algebraMap R K c + algebraMap R K d * j, ?_⟩
    rw [hx_decomp]
    -- Goal: algebraMap a + algebraMap b * j =
    --       (algebraMap c + algebraMap d * j) * (algebraMap c + algebraMap d * j)
    have hexpand : (algebraMap R K c + algebraMap R K d * j) *
                   (algebraMap R K c + algebraMap R K d * j) =
                   (algebraMap R K c)^2 + (algebraMap R K d)^2 * j^2 +
                   2 * algebraMap R K c * algebraMap R K d * j := by ring
    rw [hexpand, hgen_sq]
    have hmap_a : algebraMap R K a = (algebraMap R K c)^2 - (algebraMap R K d)^2 := by
      rw [← map_pow, ← map_pow, ← map_sub, hcd_eq_a]
    have hmap_b : algebraMap R K b = 2 * algebraMap R K c * algebraMap R K d := by
      have h1 : (2 : K) = algebraMap R K 2 := (map_ofNat (algebraMap R K) 2).symm
      rw [h1, ← map_mul, ← map_mul, h2cd]
    rw [hmap_a, hmap_b]
    ring

end Algebraic

end IsRealClosed
