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
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.TFAE
import RealClosedField.Algebra.Order.Algebra

/-!
# Equivalent conditions for a real closed field (ordered case)

For an ordered field `R`, the following are equivalent:
1. `R` is real closed.
2. `R` is maximal with respect to ordered algebraic extensions.
3. Polynomials over `R` satisfy the intermediate value property.

This file also develops a number of basic algebraic properties of real closed
fields needed to justify the equivalence: the classification of finite and
algebraic extensions (only `R` and `R(i)`), the classification of monic
irreducible polynomials, and some consequences.
-/

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

/-- Auxiliary: any quadratic extension `L/R` of a real closed field has a power basis
whose minimal polynomial is `X^2 + 1`. -/
private theorem powerBasis_X_sq_add_one_of_finrank_eq_two
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
      rw [← map_pow]; congr 1; field_simp; ring
    have half_times : 2 * (algebraMap R L) (a / 2) = (algebraMap R L) a := by
      have : (2 : L) = (algebraMap R L) 2 := (map_ofNat (algebraMap R L) 2).symm
      rw [this, ← map_mul]; congr 1; field_simp
    have expand : y ^ 2 = x ^ 2 + (algebraMap R L) a * x + (algebraMap R L) (a ^ 2 / 4) := by
      show (x + (algebraMap R L) (a / 2)) ^ 2 = _
      have : (x + (algebraMap R L) (a / 2)) ^ 2 =
          x ^ 2 + x * (2 * (algebraMap R L) (a / 2)) + (algebraMap R L) (a / 2) ^ 2 := by ring
      rw [this, half_sq, half_times]; ring
    rw [expand]
    show x ^ 2 + (algebraMap R L) a * x + (algebraMap R L) (a ^ 2 / 4) =
      (algebraMap R L) (a ^ 2 / 4 - b)
    rw [map_sub]; linear_combination hroot
  have hy_ni : y ∉ (algebraMap R L).range := by
    rintro ⟨r, hr⟩
    apply hx
    refine ⟨r - a / 2, ?_⟩
    have hr' : (algebraMap R L) r = x + (algebraMap R L) (a / 2) := hr
    rw [map_sub]; linear_combination hr'
  have hc_ni : ¬ IsSquare c := by
    rintro ⟨s, hs⟩
    have halg_sq : y ^ 2 = ((algebraMap R L) s) ^ 2 := by
      rw [hy_sq, show c = s * s from hs, map_mul]; ring
    have hfact : (y - (algebraMap R L) s) * (y + (algebraMap R L) s) = 0 := by
      linear_combination halg_sq
    apply hy_ni
    rcases mul_eq_zero.mp hfact with hd | hd
    · exact ⟨s, by linear_combination -hd⟩
    · refine ⟨-s, ?_⟩
      rw [map_neg]; linear_combination -hd
  have hnc_sq : IsSquare (-c) := (IsRealClosed.isSquare_or_isSquare_neg c).resolve_left hc_ni
  obtain ⟨s, hs⟩ := hnc_sq
  have hs_ne : s ≠ 0 := by
    rintro rfl
    apply hc_ni
    have hmc : -c = 0 := by rw [hs]; ring
    have hc0 : c = 0 := by linear_combination -hmc
    rw [hc0]; exact ⟨0, by ring⟩
  have hsL_ne : (algebraMap R L) s ≠ 0 := (map_ne_zero_iff _ hInj).mpr hs_ne
  set sL : L := (algebraMap R L) s with hsL_def
  have hsL_sq : sL ^ 2 = - (algebraMap R L) c := by
    show ((algebraMap R L) s) ^ 2 = - (algebraMap R L) c
    rw [← map_pow, ← map_neg]; congr 1
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
  let basis2 : Module.Basis (Fin 2) R L := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbasis_eq : ∀ i : Fin 2, basis2 i = α ^ (i : ℕ) := by
    intro i
    have key : basisOfLinearIndependentOfCardEqFinrank hli hcard i = ![(1 : L), α] i := by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank hli hcard]
    show basisOfLinearIndependentOfCardEqFinrank hli hcard i = α ^ (i : ℕ)
    rw [key]
    fin_cases i <;> simp
  exact ⟨{ gen := α, dim := 2, basis := basis2, basis_eq_pow := hbasis_eq }, hmin⟩

/-- `R(i)` is the unique quadratic extension of a real closed field `R` (up to `R`-isomorphism):
any quadratic extension of `R` is `R`-isomorphic to any other quadratic extension of `R`. -/
theorem nonempty_algEquiv_of_finrank_eq_two
    (K K' : Type*) [Field K] [Algebra R K] [Field K'] [Algebra R K']
    (hK : Module.finrank R K = 2) (hK' : Module.finrank R K' = 2) :
    Nonempty (K ≃ₐ[R] K') := by
  obtain ⟨pbK, hminK⟩ := powerBasis_X_sq_add_one_of_finrank_eq_two R K hK
  obtain ⟨pbK', hminK'⟩ := powerBasis_X_sq_add_one_of_finrank_eq_two R K' hK'
  exact ⟨pbK.equivOfMinpoly pbK' (hminK.trans hminK'.symm)⟩

/-- `R(i)` has no quadratic extension: equivalently, every element of any quadratic
extension `K` of `R` is a square in `K`. -/
theorem isSquare_of_finrank_base_eq_two
    (K : Type*) [Field K] [Algebra R K]
    (hK : Module.finrank R K = 2) (x : K) : IsSquare x := sorry

/-- Fundamental theorem of algebra for real closed fields: the only finite extensions
of `R` are `R` itself and the quadratic extension `R(i)`. -/
theorem finrank_le_two_of_finiteDimensional
    (K : Type*) [Field K] [Algebra R K] [FiniteDimensional R K] :
    Module.finrank R K ≤ 2 := sorry

/-- The only algebraic extensions of a real closed field `R` are `R` and `R(i)`. -/
theorem finrank_le_two_of_isAlgebraic
    (K : Type*) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K] :
    Module.finrank R K ≤ 2 := sorry

/-- A real closed field has no nontrivial real algebraic extensions. -/
theorem surjective_algebraMap_of_isAlgebraic_of_isSemireal
    (K : Type*) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K] [IsSemireal K] :
    Function.Surjective (algebraMap R K) := sorry

/-- Classification of monic irreducible polynomials over a real closed field `R`:
they are linear (`X - c`) or quadratic of the form `(X - a)^2 + b^2` with `b ≠ 0`. -/
theorem monic_irreducible_classification {f : Polynomial R} (hf : f.Monic) (hf' : Irreducible f) :
    (∃ c : R, f = Polynomial.X - Polynomial.C c) ∨
    (∃ a b : R, b ≠ 0 ∧
      f = (Polynomial.X - Polynomial.C a) ^ 2 + Polynomial.C (b ^ 2)) := sorry

end Algebraic

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- `R` has no nontrivial ordered algebraic extension: for every field `K` that is an
algebraic extension of `R` and admits a linear order making it a strictly ordered ring
with `R → K` monotone, the structure map `R → K` is surjective. -/
def NoNontrivialOrderedAlgExt : Prop :=
  ∀ (K : Type*) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K],
    (∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule R K) →
    Function.Surjective (algebraMap R K)

/-- Polynomials over `R` satisfy the intermediate value property. -/
def PolynomialIVP : Prop :=
  ∀ (f : Polynomial R) (a b : R), a ≤ b → f.eval a ≤ 0 → 0 ≤ f.eval b →
    ∃ c ∈ Set.Icc a b, f.IsRoot c

/-- Polynomials over a real closed ordered field satisfy the intermediate value property. -/
theorem polynomialIVP_of_isRealClosed [IsRealClosed R] : PolynomialIVP R := sorry

namespace polynomialIVP_aux

open Polynomial

/-- Helper: for a polynomial `f` with positive leading coefficient, odd `natDegree = n ≥ 1`,
there exists `M > 0` with `f.eval M > 0` and `f.eval (-M) < 0`. -/
private lemma exists_sign_change
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (f : Polynomial R) {n : ℕ} (hn : f.natDegree = n) (hn1 : 1 ≤ n) (hodd : Odd n)
    (hlc : 0 < f.leadingCoeff) :
    ∃ M : R, 0 < M ∧ f.eval (-M) < 0 ∧ 0 < f.eval M := by
  set B := ∑ i ∈ Finset.range n, |f.coeff i| with hB_def
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  set M : R := 1 + B / f.leadingCoeff with hM_def
  have hBdiv : 0 ≤ B / f.leadingCoeff := div_nonneg hB hlc.le
  have hMpos : 0 < M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hM0 : (0 : R) ≤ M := hMpos.le
  have hne : f.leadingCoeff ≠ 0 := ne_of_gt hlc
  have hkey : f.leadingCoeff * M - B = f.leadingCoeff := by
    have hMexpand : f.leadingCoeff * M = f.leadingCoeff + B := by
      rw [hM_def, mul_add, mul_one, mul_div_cancel₀ B hne]
    linarith
  have hMpow_pos : (0 : R) < M ^ (n - 1) := pow_pos hMpos _
  have hMpow_ge_one : (1 : R) ≤ M ^ (n - 1) := one_le_pow₀ hM1
  have hn_split : n = (n - 1) + 1 := by omega
  have hMn_eq : M ^ n = M ^ (n - 1) * M := by
    conv_lhs => rw [hn_split]
    exact pow_succ M (n - 1)
  have hlc_eq : f.coeff n = f.leadingCoeff := by rw [← hn]; rfl
  have heval_general : ∀ x : R, f.eval x =
      f.leadingCoeff * x ^ n + ∑ i ∈ Finset.range n, f.coeff i * x ^ i := by
    intro x
    have h1 : f.eval x = ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i * x ^ i :=
      eval_eq_sum_range x
    rw [h1, hn, Finset.sum_range_succ, hlc_eq]
    exact add_comm _ _
  have heval_M := heval_general M
  have heval_negM := heval_general (-M)
  have htail_M : |∑ i ∈ Finset.range n, f.coeff i * M ^ i| ≤ B * M ^ (n - 1) := by
    calc |∑ i ∈ Finset.range n, f.coeff i * M ^ i|
        ≤ ∑ i ∈ Finset.range n, |f.coeff i * M ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range n, |f.coeff i| * M ^ i := by
            refine Finset.sum_congr rfl (fun i _ ↦ ?_)
            rw [abs_mul, abs_of_nonneg (pow_nonneg hM0 i)]
      _ ≤ ∑ i ∈ Finset.range n, |f.coeff i| * M ^ (n - 1) := by
            refine Finset.sum_le_sum (fun i hi ↦ ?_)
            rw [Finset.mem_range] at hi
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact pow_le_pow_right₀ hM1 (by omega)
      _ = B * M ^ (n - 1) := by rw [← Finset.sum_mul]
  have htail_negM : |∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i| ≤ B * M ^ (n - 1) := by
    calc |∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i|
        ≤ ∑ i ∈ Finset.range n, |f.coeff i * (-M) ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range n, |f.coeff i| * M ^ i := by
            refine Finset.sum_congr rfl (fun i _ ↦ ?_)
            rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg hM0]
      _ ≤ ∑ i ∈ Finset.range n, |f.coeff i| * M ^ (n - 1) := by
            refine Finset.sum_le_sum (fun i hi ↦ ?_)
            rw [Finset.mem_range] at hi
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact pow_le_pow_right₀ hM1 (by omega)
      _ = B * M ^ (n - 1) := by rw [← Finset.sum_mul]
  have hneg_pow : (-M) ^ n = -M ^ n := Odd.neg_pow hodd M
  refine ⟨M, hMpos, ?_, ?_⟩
  · rw [heval_negM, hneg_pow, hMn_eq]
    have htail_upper : ∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i ≤ B * M ^ (n - 1) := by
      have := htail_negM
      rw [abs_le] at this
      exact this.2
    have hcompute :
        f.leadingCoeff * -(M ^ (n - 1) * M) + B * M ^ (n - 1)
          = -(M ^ (n - 1) * f.leadingCoeff) := by
      have h1 : f.leadingCoeff * -(M ^ (n - 1) * M) + B * M ^ (n - 1)
             = -M ^ (n - 1) * (f.leadingCoeff * M - B) := by ring
      rw [h1, hkey]; ring
    have hbound :
        f.leadingCoeff * -(M ^ (n - 1) * M) + ∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i
          ≤ -(M ^ (n - 1) * f.leadingCoeff) := by
      calc
        f.leadingCoeff * -(M ^ (n - 1) * M) + ∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i
            ≤ f.leadingCoeff * -(M ^ (n - 1) * M) + B * M ^ (n - 1) := by linarith
        _ = -(M ^ (n - 1) * f.leadingCoeff) := hcompute
    have : 0 < M ^ (n - 1) * f.leadingCoeff := mul_pos hMpow_pos hlc
    linarith
  · rw [heval_M, hMn_eq]
    have htail_lower : -(B * M ^ (n - 1)) ≤ ∑ i ∈ Finset.range n, f.coeff i * M ^ i := by
      have := htail_M
      rw [abs_le] at this
      linarith
    have hcompute :
        f.leadingCoeff * (M ^ (n - 1) * M) - B * M ^ (n - 1)
          = M ^ (n - 1) * f.leadingCoeff := by
      have h1 : f.leadingCoeff * (M ^ (n - 1) * M) - B * M ^ (n - 1)
             = M ^ (n - 1) * (f.leadingCoeff * M - B) := by ring
      rw [h1, hkey]
    have hbound :
        M ^ (n - 1) * f.leadingCoeff
          ≤ f.leadingCoeff * (M ^ (n - 1) * M) + ∑ i ∈ Finset.range n, f.coeff i * M ^ i := by
      calc M ^ (n - 1) * f.leadingCoeff
          = f.leadingCoeff * (M ^ (n - 1) * M) - B * M ^ (n - 1) := hcompute.symm
        _ ≤ f.leadingCoeff * (M ^ (n - 1) * M) + ∑ i ∈ Finset.range n, f.coeff i * M ^ i := by
            linarith
    have : 0 < M ^ (n - 1) * f.leadingCoeff := mul_pos hMpow_pos hlc
    linarith

end polynomialIVP_aux

/-- An ordered field whose polynomials satisfy the intermediate value property is real closed. -/
theorem isRealClosed_of_polynomialIVP (h : PolynomialIVP R) : IsRealClosed R := by
  refine IsRealClosed.of_linearOrderedField (R := R) ?_ ?_
  · intro a ha
    have h0 : (0 : R) ≤ a + 1 := by linarith
    have heval_0 : (Polynomial.X ^ 2 - Polynomial.C a).eval 0 ≤ 0 := by
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      nlinarith
    have heval_1 : 0 ≤ (Polynomial.X ^ 2 - Polynomial.C a).eval (a + 1) := by
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      nlinarith
    obtain ⟨c, _, hc_root⟩ :=
      h (Polynomial.X ^ 2 - Polynomial.C a) 0 (a + 1) h0 heval_0 heval_1
    have hc_eval : (Polynomial.X ^ 2 - Polynomial.C a).eval c = 0 := hc_root
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        sub_eq_zero] at hc_eval
    exact ⟨c, by rw [← sq]; exact hc_eval.symm⟩
  · intro f hodd
    set n := f.natDegree with hn_def
    have hn1 : 1 ≤ n := by
      rcases hodd with ⟨k, hk⟩
      omega
    have hf_ne : f ≠ 0 := by
      intro hfz
      rw [hfz, Polynomial.natDegree_zero] at hn_def
      omega
    by_cases hlc_pos : 0 < f.leadingCoeff
    · obtain ⟨M, hMpos, hMneg_eval, hMpos_eval⟩ :=
        polynomialIVP_aux.exists_sign_change (R := R) f hn_def.symm hn1 hodd hlc_pos
      obtain ⟨c, _, hc_root⟩ :=
        h f (-M) M (by linarith) hMneg_eval.le hMpos_eval.le
      exact ⟨c, hc_root⟩
    · rw [not_lt] at hlc_pos
      have hlc_ne : f.leadingCoeff ≠ 0 := by
        rw [Ne, Polynomial.leadingCoeff_eq_zero]
        exact hf_ne
      have hlc_neg : f.leadingCoeff < 0 := lt_of_le_of_ne hlc_pos hlc_ne
      have hndeg : (-f).natDegree = n := by rw [Polynomial.natDegree_neg, ← hn_def]
      have hlc' : 0 < (-f).leadingCoeff := by
        rw [Polynomial.leadingCoeff_neg]; linarith
      obtain ⟨M, hMpos, hMneg_eval, hMpos_eval⟩ :=
        polynomialIVP_aux.exists_sign_change (R := R) (-f) hndeg hn1 hodd hlc'
      obtain ⟨c, _, hc_root⟩ :=
        h (-f) (-M) M (by linarith) hMneg_eval.le hMpos_eval.le
      refine ⟨c, ?_⟩
      have : (-f).eval c = 0 := hc_root
      rw [Polynomial.eval_neg, neg_eq_zero] at this
      exact this

/-- A real closed ordered field has no nontrivial ordered algebraic extensions. -/
theorem noNontrivialOrderedAlgExt_of_isRealClosed [IsRealClosed R] :
    NoNontrivialOrderedAlgExt R := sorry

/-- An ordered field with no nontrivial ordered algebraic extensions is real closed. -/
theorem isRealClosed_of_noNontrivialOrderedAlgExt (h : NoNontrivialOrderedAlgExt R) :
    IsRealClosed R := by
  sorry

/-- For an ordered field `R`, the following are equivalent:
1. `R` is real closed.
2. `R` is maximal with respect to ordered algebraic extensions.
3. Polynomials over `R` satisfy the intermediate value property. -/
theorem tfae_of_linearOrderedField :
    List.TFAE
      [ IsRealClosed R,
        NoNontrivialOrderedAlgExt R,
        PolynomialIVP R ] := by
  tfae_have 1 → 2 := fun _ ↦ noNontrivialOrderedAlgExt_of_isRealClosed R
  tfae_have 2 → 1 := isRealClosed_of_noNontrivialOrderedAlgExt R
  tfae_have 1 → 3 := fun _ ↦ polynomialIVP_of_isRealClosed R
  tfae_have 3 → 1 := isRealClosed_of_polynomialIVP R
  tfae_finish

end IsRealClosed
