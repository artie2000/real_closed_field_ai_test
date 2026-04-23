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
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.RingTheory.Algebraic.Basic
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

/-- `R(i)` is the unique quadratic extension of a real closed field `R` (up to `R`-isomorphism):
any quadratic extension of `R` is `R`-isomorphic to any other quadratic extension of `R`. -/
theorem nonempty_algEquiv_of_finrank_eq_two
    (K K' : Type*) [Field K] [Algebra R K] [Field K'] [Algebra R K']
    (hK : Module.finrank R K = 2) (hK' : Module.finrank R K' = 2) :
    Nonempty (K ≃ₐ[R] K') := sorry

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
    IsRealClosed R := sorry

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
