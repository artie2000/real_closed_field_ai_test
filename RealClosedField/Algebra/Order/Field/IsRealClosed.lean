/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.Algebra.Order.Algebra
import RealClosedField.Algebra.Order.Field.IsSemireal
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Tactic.TFAE

open Polynomial

/-!
# TFAE characterisation of real closed fields among ordered fields

This file records the equivalence between three characterisations of real closed fields
over an ordered field `R`:

1. `R` is real closed.
2. `R` is maximal among ordered algebraic extensions: every algebraic extension of `R`
   which is itself an ordered algebra over `R` is isomorphic to `R`.
3. Polynomials over `R` satisfy the intermediate value property.

The main result is `IsRealClosed.tfae_ord`.
-/

namespace IsRealClosed

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Polynomials over a real closed field satisfy the intermediate value property. -/
theorem exists_isRoot_of_nonpos_of_nonneg [IsRealClosed R]
    {f : R[X]} {a b : R} (hab : a ≤ b) (ha : f.eval a ≤ 0) (hb : 0 ≤ f.eval b) :
    ∃ c ∈ Set.Icc a b, f.IsRoot c := by
  sorry

/-- If polynomials over an ordered field `R` satisfy the intermediate value property,
then `R` is real closed. -/
theorem of_ivp
    (h : ∀ (f : R[X]) (a b : R), a ≤ b → f.eval a ≤ 0 → 0 ≤ f.eval b →
         ∃ c ∈ Set.Icc a b, f.IsRoot c) :
    IsRealClosed R := by
  refine IsRealClosed.of_linearOrderedField ?_ ?_
  · -- every non-negative element is a square
    intro x hx
    have ha : (X ^ 2 - C x).eval 0 ≤ 0 := by
      simp only [eval_sub, eval_pow, eval_X, eval_C]; linarith
    have hb : 0 ≤ (X ^ 2 - C x).eval (x + 1) := by
      simp only [eval_sub, eval_pow, eval_X, eval_C]; nlinarith [sq_nonneg x]
    obtain ⟨c, _, hc⟩ := h (X ^ 2 - C x) 0 (x + 1) (by linarith) ha hb
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at hc
    exact ⟨c, by linarith [sq c]⟩
  · -- every odd-natDegree polynomial has a root
    intro f hodd
    have hn : 1 ≤ f.natDegree := hodd.pos
    -- reduce to the case where the leading coefficient is positive
    have key : ∀ (g : R[X]), g.natDegree = f.natDegree → 0 < g.leadingCoeff →
        ∃ c, g.IsRoot c := by
      intro g hgdeg hlc
      set n := f.natDegree
      have hgn : g.natDegree = n := hgdeg
      set B : R := ∑ i ∈ Finset.range n, |g.coeff i| with hB
      have hB_nonneg : 0 ≤ B := Finset.sum_nonneg (fun i _ => abs_nonneg _)
      set aₙ := g.leadingCoeff with haₙ
      set M : R := (B + 1) / aₙ + 1 with hM
      have hM_pos : (0 : R) < M := by
        have : 0 < (B + 1) / aₙ := div_pos (by linarith) hlc; linarith
      have hM_ge : (1 : R) ≤ M := by
        have : 0 ≤ (B + 1) / aₙ := (div_pos (by linarith) hlc).le; linarith
      have hkey : aₙ * M - B ≥ 1 := by
        rw [hM]
        have heq : aₙ * ((B + 1) / aₙ + 1) = (B + 1) + aₙ := by field_simp
        linarith
      -- tail bound at M
      have tail_bound :
          ∀ x : R, 1 ≤ x → |∑ i ∈ Finset.range n, g.coeff i * x ^ i| ≤ x ^ (n - 1) * B := by
        intro x hx
        calc |∑ i ∈ Finset.range n, g.coeff i * x ^ i|
            ≤ ∑ i ∈ Finset.range n, |g.coeff i * x ^ i| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i ∈ Finset.range n, |g.coeff i| * x ^ i := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : R) ≤ x) i)]
          _ ≤ ∑ i ∈ Finset.range n, |g.coeff i| * x ^ (n - 1) := by
              refine Finset.sum_le_sum fun i hi => ?_
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              exact pow_le_pow_right₀ hx (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi))
          _ = x ^ (n - 1) * B := by rw [← Finset.sum_mul]; ring
      -- tail bound at -M (using (-x)^i)
      have tail_bound_neg :
          ∀ x : R, 1 ≤ x →
            |∑ i ∈ Finset.range n, g.coeff i * (-x) ^ i| ≤ x ^ (n - 1) * B := by
        intro x hx
        calc |∑ i ∈ Finset.range n, g.coeff i * (-x) ^ i|
            ≤ ∑ i ∈ Finset.range n, |g.coeff i * (-x) ^ i| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i ∈ Finset.range n, |g.coeff i| * x ^ i := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg (by linarith : (0 : R) ≤ x)]
          _ ≤ ∑ i ∈ Finset.range n, |g.coeff i| * x ^ (n - 1) := by
              refine Finset.sum_le_sum fun i hi => ?_
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              exact pow_le_pow_right₀ hx (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi))
          _ = x ^ (n - 1) * B := by rw [← Finset.sum_mul]; ring
      -- g.eval M > 0
      have hg_pos : 0 < g.eval M := by
        have hexp : g.eval M = aₙ * M ^ n + ∑ i ∈ Finset.range n, g.coeff i * M ^ i := by
          have := eval_eq_sum_range (p := g) M
          rw [hgn] at this
          rw [this, Finset.sum_range_succ,
              show g.coeff n = aₙ from by rw [haₙ, leadingCoeff, hgn]]
          ring
        rw [hexp]
        have htb := tail_bound M hM_ge
        have hMn_pos : 0 < M ^ (n - 1) := pow_pos hM_pos _
        have hpow : M ^ n = M * M ^ (n - 1) := by
          conv_lhs => rw [show n = (n - 1) + 1 from by omega, pow_succ]; ring
        rw [hpow]
        have hlb : ∑ i ∈ Finset.range n, g.coeff i * M ^ i ≥ -(M ^ (n - 1) * B) := by
          have := abs_le.mp htb; linarith [this.1]
        have hpos : 0 < M ^ (n - 1) * (aₙ * M - B) := by positivity
        nlinarith
      -- g.eval (-M) < 0
      have hg_neg : g.eval (-M) < 0 := by
        have hexp :
            g.eval (-M) = aₙ * (-M) ^ n + ∑ i ∈ Finset.range n, g.coeff i * (-M) ^ i := by
          have := eval_eq_sum_range (p := g) (-M)
          rw [hgn] at this
          rw [this, Finset.sum_range_succ,
              show g.coeff n = aₙ from by rw [haₙ, leadingCoeff, hgn]]
          ring
        rw [hexp, Odd.neg_pow (hgdeg ▸ hodd : Odd n) M]
        have htb := tail_bound_neg M hM_ge
        have hMn_pos : 0 < M ^ (n - 1) := pow_pos hM_pos _
        have hpow : M ^ n = M * M ^ (n - 1) := by
          conv_lhs => rw [show n = (n - 1) + 1 from by omega, pow_succ]; ring
        rw [hpow]
        have hub : ∑ i ∈ Finset.range n, g.coeff i * (-M) ^ i ≤ M ^ (n - 1) * B := by
          have := abs_le.mp htb; linarith [this.2]
        have hpos : 0 < M ^ (n - 1) * (aₙ * M - B) := by positivity
        nlinarith
      obtain ⟨c, _, hc⟩ := h g (-M) M (by linarith) hg_neg.le hg_pos.le
      exact ⟨c, hc⟩
    by_cases hlc : 0 < f.leadingCoeff
    · exact key f rfl hlc
    · have hne : f.leadingCoeff ≠ 0 := fun he => by
        rw [leadingCoeff_eq_zero] at he; subst he; simp at hn
      have hlc' : 0 < (-f).leadingCoeff := by
        rw [leadingCoeff_neg, neg_pos]; exact lt_of_le_of_ne (not_lt.mp hlc) hne
      obtain ⟨c, hc⟩ := key (-f) (natDegree_neg f) hlc'
      refine ⟨c, ?_⟩
      simp only [IsRoot, eval_neg, neg_eq_zero] at hc
      exact hc

/-- A real closed field has no nontrivial ordered algebraic extension: if `K` is an
algebraic extension of the real closed field `R` and `K` can be ordered compatibly with
the order on `R`, then the embedding `R → K` is a bijection. -/
theorem bijective_algebraMap_of_isOrderedAlgebra [IsRealClosed R]
    (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
    [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K] :
    Function.Bijective (algebraMap R K) := by
  sorry

/-- If an ordered field `R` has no nontrivial ordered algebraic extension, then it is
real closed. -/
theorem of_bijective_algebraMap_of_isOrderedAlgebra
    (h : ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
         [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K],
         Function.Bijective (algebraMap R K)) :
    IsRealClosed R := by
  sorry

variable (R) in
/-- Characterisation of real closed fields among ordered fields. -/
theorem tfae_ord :
    List.TFAE [
      IsRealClosed R,
      ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
        [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K],
        Function.Bijective (algebraMap R K),
      ∀ (f : R[X]) (a b : R), a ≤ b → f.eval a ≤ 0 → 0 ≤ f.eval b →
        ∃ c ∈ Set.Icc a b, f.IsRoot c] := by
  tfae_have 1 → 2 := by
    intro _ K _ _ _ _ _ _
    exact bijective_algebraMap_of_isOrderedAlgebra K
  tfae_have 2 → 1 := of_bijective_algebraMap_of_isOrderedAlgebra
  tfae_have 1 → 3 := by
    intro _ f a b hab ha hb
    exact exists_isRoot_of_nonpos_of_nonneg hab ha hb
  tfae_have 3 → 1 := of_ivp
  tfae_finish

end IsRealClosed
