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
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
theorem isSquare_of_isSumSq {x : R} (hx : IsSumSq x) : IsSquare x := sorry

/-- There is no nontrivial odd-degree finite extension of a real closed field `R`:
any finite extension `K/R` with `Module.finrank R K` odd has `R → K` surjective. -/
theorem surjective_algebraMap_of_odd_finrank
    (K : Type*) [Field K] [Algebra R K] [FiniteDimensional R K]
    (hodd : Odd (Module.finrank R K)) :
    Function.Surjective (algebraMap R K) := sorry

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

namespace _root_.IsRealClosed.polynomialIVP_aux

open Polynomial Finset

/-- For any `M ≥ 1` in an ordered ring, and any polynomial `f` with `f.natDegree = n`,
the tail sum `∑_{i < n} f.coeff i * x^i` evaluated at `x = M` has absolute value
bounded by `(∑_{i < n} |f.coeff i|) * M^(n-1)`, provided `n ≥ 1`. -/
private lemma tail_abs_le
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (f : Polynomial R) (n : ℕ) (hn : 1 ≤ n) {M : R} (hM : 1 ≤ M) :
    |∑ i ∈ Finset.range n, f.coeff i * M ^ i|
      ≤ (∑ i ∈ Finset.range n, |f.coeff i|) * M ^ (n - 1) := by
  have hM0 : (0 : R) ≤ M := le_trans zero_le_one hM
  -- Each term |f.coeff i * M^i| ≤ |f.coeff i| * M^{n-1}
  calc
    |∑ i ∈ Finset.range n, f.coeff i * M ^ i|
        ≤ ∑ i ∈ Finset.range n, |f.coeff i * M ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range n, |f.coeff i| * M ^ i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul, abs_of_nonneg (pow_nonneg hM0 i)]
    _ ≤ ∑ i ∈ Finset.range n, |f.coeff i| * M ^ (n - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_range] at hi
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply pow_le_pow_right₀ hM
          omega
    _ = (∑ i ∈ Finset.range n, |f.coeff i|) * M ^ (n - 1) := by
          rw [← Finset.sum_mul]

/-- Key computation: for polynomial `f` with positive leading coefficient and `natDegree = n ≥ 1`,
taking `M := 1 + B / f.leadingCoeff` (where `B = ∑_{i<n} |f.coeff i|`), we have
`f.eval M ≥ f.leadingCoeff * M^(n-1) > 0`. -/
private lemma eval_pos_at_large
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (f : Polynomial R) {n : ℕ} (hn : f.natDegree = n) (hn1 : 1 ≤ n)
    (hlc : 0 < f.leadingCoeff) :
    ∃ M : R, 1 ≤ M ∧ 0 < f.eval M := by
  set B := ∑ i ∈ Finset.range n, |f.coeff i| with hB_def
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  set M : R := 1 + B / f.leadingCoeff with hM_def
  have hMpos : 0 < M := by
    have : 0 ≤ B / f.leadingCoeff := div_nonneg hB hlc.le
    linarith
  have hM1 : 1 ≤ M := by
    have : 0 ≤ B / f.leadingCoeff := div_nonneg hB hlc.le
    linarith
  -- Key: a_n * M - B = a_n (since M = 1 + B/a_n)
  have hkey : f.leadingCoeff * M - B = f.leadingCoeff := by
    field_simp [hM_def]
    ring
  refine ⟨M, hM1, ?_⟩
  -- Express f.eval M = f.leadingCoeff * M^n + (tail)
  have heval : f.eval M =
      f.leadingCoeff * M ^ n + ∑ i ∈ Finset.range n, f.coeff i * M ^ i := by
    rw [eval_eq_sum_range, hn, Finset.sum_range_succ]
    congr 1
    · rw [add_comm]
    · rw [Polynomial.coeff_natDegree, hn]
  -- Bound the tail
  have htail := tail_abs_le (R := R) f n hn1 hM1
  -- Combine: f.eval M ≥ a_n * M^n - B * M^{n-1} = M^{n-1} * (a_n * M - B) = a_n * M^{n-1}
  have hM0 : (0 : R) ≤ M := hMpos.le
  have hMpow : (0 : R) < M ^ (n - 1) := pow_pos hMpos _
  have hMpow_ge : (1 : R) ≤ M ^ (n - 1) := one_le_pow₀ hM1
  -- Split M^n as M * M^{n-1}
  have hn_split : n = (n - 1) + 1 := by omega
  have hMn : M ^ n = M ^ (n - 1) * M := by
    rw [hn_split, pow_succ]
  rw [heval, hMn]
  have habs : ∑ i ∈ Finset.range n, f.coeff i * M ^ i ≥
      -(B * M ^ (n - 1)) := by
    have := htail
    rw [abs_le] at this
    linarith
  have : f.leadingCoeff * (M ^ (n - 1) * M) +
      ∑ i ∈ Finset.range n, f.coeff i * M ^ i
      ≥ f.leadingCoeff * (M ^ (n - 1) * M) - B * M ^ (n - 1) := by linarith
  have hrhs : f.leadingCoeff * (M ^ (n - 1) * M) - B * M ^ (n - 1)
      = M ^ (n - 1) * (f.leadingCoeff * M - B) := by ring
  rw [hrhs, hkey] at this
  have : M ^ (n - 1) * f.leadingCoeff ≤
      f.leadingCoeff * (M ^ (n - 1) * M) + ∑ i ∈ Finset.range n, f.coeff i * M ^ i := this
  have hpos : 0 < M ^ (n - 1) * f.leadingCoeff := mul_pos hMpow hlc
  linarith

/-- Key computation (negative side): for polynomial `f` with positive leading coefficient,
odd `natDegree = n ≥ 1`, and `M` as above, `f.eval (-M) < 0`. -/
private lemma eval_neg_at_neg_large
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (f : Polynomial R) {n : ℕ} (hn : f.natDegree = n) (hn1 : 1 ≤ n) (hodd : Odd n)
    (hlc : 0 < f.leadingCoeff) :
    ∃ M : R, 1 ≤ M ∧ f.eval (-M) < 0 := by
  set B := ∑ i ∈ Finset.range n, |f.coeff i| with hB_def
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  set M : R := 1 + B / f.leadingCoeff with hM_def
  have hMpos : 0 < M := by
    have : 0 ≤ B / f.leadingCoeff := div_nonneg hB hlc.le
    linarith
  have hM1 : 1 ≤ M := by
    have : 0 ≤ B / f.leadingCoeff := div_nonneg hB hlc.le
    linarith
  have hkey : f.leadingCoeff * M - B = f.leadingCoeff := by
    field_simp [hM_def]
    ring
  refine ⟨M, hM1, ?_⟩
  -- Express f.eval (-M) = f.leadingCoeff * (-M)^n + tail at (-M).
  have heval : f.eval (-M) =
      f.leadingCoeff * (-M) ^ n + ∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i := by
    rw [eval_eq_sum_range, hn, Finset.sum_range_succ]
    congr 1
    · rw [add_comm]
    · rw [Polynomial.coeff_natDegree, hn]
  -- Since n is odd, (-M)^n = -M^n.
  have hnegn : (-M) ^ n = -M ^ n := Odd.neg_pow hodd M
  -- Bound |tail| using tail_abs_le applied with -M in place of M? No, the lemma uses M.
  -- Instead bound the sum directly.
  have hMneg0 : (0 : R) ≤ M := hMpos.le
  -- Compute the sum at -M.
  -- ∑ f.coeff i * (-M)^i ≤ ∑ |f.coeff i| * M^i ≤ B * M^{n-1}
  have htail_upper : ∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i ≤ B * M ^ (n - 1) := by
    calc ∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i
        ≤ |∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i| := le_abs_self _
      _ ≤ ∑ i ∈ Finset.range n, |f.coeff i * (-M) ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range n, |f.coeff i| * M ^ i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg hMneg0]
      _ ≤ ∑ i ∈ Finset.range n, |f.coeff i| * M ^ (n - 1) := by
            apply Finset.sum_le_sum
            intro i hi
            rw [Finset.mem_range] at hi
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            apply pow_le_pow_right₀ hM1
            omega
      _ = B * M ^ (n - 1) := by rw [← Finset.sum_mul]
  -- Split M^n
  have hn_split : n = (n - 1) + 1 := by omega
  have hMn : M ^ n = M ^ (n - 1) * M := by
    rw [hn_split, pow_succ]
  have hMpow : (0 : R) < M ^ (n - 1) := pow_pos hMpos _
  rw [heval, hnegn, hMn]
  -- Now goal: f.leadingCoeff * -(M^{n-1} * M) + tail < 0
  -- tail ≤ B * M^{n-1}
  -- f.leadingCoeff * -(M^{n-1} * M) = -(f.leadingCoeff * M * M^{n-1})
  -- So LHS ≤ -a_n * M * M^{n-1} + B * M^{n-1} = M^{n-1} * (B - a_n * M) = -a_n * M^{n-1}
  have hgoal : f.leadingCoeff * -(M ^ (n - 1) * M) + B * M ^ (n - 1)
             = -(M ^ (n - 1) * f.leadingCoeff) := by
    have : f.leadingCoeff * -(M ^ (n - 1) * M) + B * M ^ (n - 1) =
      -M ^ (n - 1) * (f.leadingCoeff * M - B) := by ring
    rw [this, hkey]
    ring
  have : f.leadingCoeff * -(M ^ (n - 1) * M) +
      ∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i ≤
      f.leadingCoeff * -(M ^ (n - 1) * M) + B * M ^ (n - 1) := by
    linarith
  have hneg : -(M ^ (n - 1) * f.leadingCoeff) < 0 := by
    have : 0 < M ^ (n - 1) * f.leadingCoeff := mul_pos hMpow hlc
    linarith
  linarith [hgoal]

end _root_.IsRealClosed.polynomialIVP_aux

/-- An ordered field whose polynomials satisfy the intermediate value property is real closed. -/
theorem isRealClosed_of_polynomialIVP (h : PolynomialIVP R) : IsRealClosed R := by
  refine IsRealClosed.of_linearOrderedField (R := R) ?_ ?_
  · -- Every nonneg is a square
    intro a ha
    have h0 : (0 : R) ≤ a + 1 := by linarith
    have heval_0 : (Polynomial.X ^ 2 - Polynomial.C a).eval 0 ≤ 0 := by
      simp
      exact ha
    have heval_1 : 0 ≤ (Polynomial.X ^ 2 - Polynomial.C a).eval (a + 1) := by
      simp
      nlinarith
    obtain ⟨c, hc_mem, hc_root⟩ :=
      h (Polynomial.X ^ 2 - Polynomial.C a) 0 (a + 1) h0 heval_0 heval_1
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, sub_eq_zero] at hc_root
    exact ⟨c, by rw [← sq]; exact hc_root.symm⟩
  · -- Every odd-degree polynomial has a root
    intro f hodd
    -- natDegree is odd so ≥ 1
    set n := f.natDegree with hn_def
    have hn1 : 1 ≤ n := by
      rcases hodd with ⟨k, hk⟩
      omega
    -- f ≠ 0
    have hf_ne : f ≠ 0 := by
      intro hf
      rw [hf, Polynomial.natDegree_zero] at hn_def
      omega
    -- Case on sign of leading coefficient
    by_cases hlc_pos : 0 < f.leadingCoeff
    · -- Positive leading coefficient
      obtain ⟨M, hM1, hMpos⟩ :=
        _root_.IsRealClosed.polynomialIVP_aux.eval_pos_at_large f rfl hn1 hlc_pos
      obtain ⟨_, hM1', hMneg⟩ :=
        _root_.IsRealClosed.polynomialIVP_aux.eval_neg_at_neg_large f rfl hn1 hodd hlc_pos
      -- Find root between -M and M. But for eval_pos_at_large and eval_neg_at_neg_large
      -- we produced the same M (they're defined the same), but we need same M.
      -- Let's redo: use same definition.
      sorry
    · -- Negative (or zero, but not zero) leading coefficient
      push_neg at hlc_pos
      have hlc_ne : f.leadingCoeff ≠ 0 := by
        rwa [Ne, Polynomial.leadingCoeff_eq_zero]
      have hlc_neg : f.leadingCoeff < 0 := lt_of_le_of_ne hlc_pos hlc_ne
      -- Consider -f
      have hndeg_neg : (-f).natDegree = n := by rw [Polynomial.natDegree_neg, hn_def]
      have hlc_neg_f : 0 < (-f).leadingCoeff := by
        rw [Polynomial.leadingCoeff_neg]; linarith
      sorry

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
