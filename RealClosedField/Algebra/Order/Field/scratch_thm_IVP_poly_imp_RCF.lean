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
  · -- isSquare_of_nonneg
    intro x hx
    have ha : (X^2 - C x).eval 0 ≤ 0 := by
      simp only [eval_sub, eval_pow, eval_X, eval_C]
      linarith
    have hb : 0 ≤ (X^2 - C x).eval (x + 1) := by
      simp only [eval_sub, eval_pow, eval_X, eval_C]
      nlinarith [sq_nonneg x, hx]
    have hab : (0 : R) ≤ x + 1 := by linarith
    obtain ⟨c, _, hc⟩ := h (X^2 - C x) 0 (x + 1) hab ha hb
    have hcsq : c ^ 2 = x := by
      have := hc
      simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at this
      linarith
    exact ⟨c, by rw [← hcsq, sq]⟩
  · -- exists_isRoot_of_odd_natDegree
    intro f hodd
    -- Key lemma: for polynomial g with positive leading coefficient, we can find
    -- M > 0 with g.eval M > 0 and, if natDegree is odd, g.eval (-M) < 0.
    -- Strategy: Replace f by (f / aₙ) — actually easier: bound via coefficients directly.
    -- For large x, f(x) ≈ aₙ x^n. Since n is odd, sign of f(-x) and f(x) differ.
    have hn : 1 ≤ f.natDegree := hodd.pos
    -- reduce to the case where leading coeff > 0
    have key : ∀ (g : R[X]), g.natDegree = f.natDegree → 0 < g.leadingCoeff →
        ∃ c, g.IsRoot c := by
      intro g hgdeg hlc
      set n := f.natDegree
      have hgn : g.natDegree = n := hgdeg
      -- Define B = ∑ |coeff_i| for i < n
      set B : R := ∑ i ∈ Finset.range n, |g.coeff i| with hB
      have hB_nonneg : 0 ≤ B := Finset.sum_nonneg (fun i _ => abs_nonneg _)
      -- Define M = (B+1)/aₙ + 1
      set aₙ := g.leadingCoeff with haₙ
      set M : R := (B + 1) / aₙ + 1 with hM
      have hM_pos : (0 : R) < M := by
        have h1 : 0 < B + 1 := by linarith
        have : 0 < (B + 1) / aₙ := div_pos h1 hlc
        linarith
      have hM_ge : (1 : R) ≤ M := by
        have : 0 ≤ (B + 1) / aₙ := le_of_lt (div_pos (by linarith) hlc)
        linarith
      -- Key inequality: aₙ * M - B ≥ 1
      have hkey : aₙ * M - B ≥ 1 := by
        rw [hM]
        have : aₙ * ((B + 1) / aₙ + 1) = (B + 1) + aₙ := by
          field_simp
      -- aux bound: for |x| ≤ M with |x| ≥ 1, x^i ≤ x^(n-1) for i < n
        linarith [hlc]
      -- Tail bound: for x ≥ 1, |∑ i ∈ range n, g.coeff i * x^i| ≤ x^(n-1) * B
      have tail_bound : ∀ x : R, 1 ≤ x → |∑ i ∈ Finset.range n, g.coeff i * x^i| ≤ x^(n-1) * B := by
        intro x hx
        calc |∑ i ∈ Finset.range n, g.coeff i * x^i|
            ≤ ∑ i ∈ Finset.range n, |g.coeff i * x^i| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i ∈ Finset.range n, |g.coeff i| * x^i := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : R) ≤ x) i)]
          _ ≤ ∑ i ∈ Finset.range n, |g.coeff i| * x^(n-1) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hx0 : (0 : R) ≤ x := by linarith
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              exact pow_le_pow_right₀ hx (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi))
          _ = x^(n-1) * B := by rw [← Finset.sum_mul]; ring
      -- Tail bound for negative x: for x ≥ 1, |∑ i ∈ range n, g.coeff i * (-x)^i| ≤ x^(n-1) * B
      have tail_bound_neg : ∀ x : R, 1 ≤ x → |∑ i ∈ Finset.range n, g.coeff i * (-x)^i| ≤ x^(n-1) * B := by
        intro x hx
        calc |∑ i ∈ Finset.range n, g.coeff i * (-x)^i|
            ≤ ∑ i ∈ Finset.range n, |g.coeff i * (-x)^i| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i ∈ Finset.range n, |g.coeff i| * x^i := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg (by linarith : (0 : R) ≤ x)]
          _ ≤ ∑ i ∈ Finset.range n, |g.coeff i| * x^(n-1) := by
              refine Finset.sum_le_sum fun i hi => ?_
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              exact pow_le_pow_right₀ hx (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi))
          _ = x^(n-1) * B := by rw [← Finset.sum_mul]; ring
      -- Now: g.eval M > 0
      have hg_pos : 0 < g.eval M := by
        have hexp : g.eval M = aₙ * M^n + ∑ i ∈ Finset.range n, g.coeff i * M^i := by
          have := eval_eq_sum_range (p := g) M
          rw [hgn] at this
          rw [this, Finset.sum_range_succ]
          rw [show g.coeff n = aₙ from by rw [haₙ, leadingCoeff, hgn]]
          ring
        rw [hexp]
        have htb := tail_bound M hM_ge
        have hMn_pos : 0 < M^(n-1) := pow_pos hM_pos _
        -- aₙ * M^n = aₙ * M * M^(n-1)
        have hn_pos : 1 ≤ n := hn
        have hpow : M^n = M * M^(n-1) := by
          conv_lhs => rw [show n = (n-1) + 1 from by omega, pow_succ]
          ring
        rw [hpow]
        have : ∑ i ∈ Finset.range n, g.coeff i * M^i ≥ -(M^(n-1) * B) := by
          have := abs_le.mp htb
          linarith [this.1]
        have : aₙ * (M * M^(n-1)) + ∑ i ∈ Finset.range n, g.coeff i * M^i
             ≥ M^(n-1) * (aₙ * M - B) := by nlinarith [this]
        have hpos : 0 < M^(n-1) * (aₙ * M - B) := by positivity
        linarith
      -- g.eval (-M) < 0
      have hg_neg : g.eval (-M) < 0 := by
        have hexp : g.eval (-M) = aₙ * (-M)^n + ∑ i ∈ Finset.range n, g.coeff i * (-M)^i := by
          have := eval_eq_sum_range (p := g) (-M)
          rw [hgn] at this
          rw [this, Finset.sum_range_succ]
          rw [show g.coeff n = aₙ from by rw [haₙ, leadingCoeff, hgn]]
          ring
        rw [hexp]
        have hnegM : (-M)^n = -M^n := Odd.neg_pow (hgdeg ▸ hodd : Odd n) M
        rw [hnegM]
        have htb := tail_bound_neg M hM_ge
        have hMn_pos : 0 < M^(n-1) := pow_pos hM_pos _
        have hn_pos : 1 ≤ n := hn
        have hpow : M^n = M * M^(n-1) := by
          conv_lhs => rw [show n = (n-1) + 1 from by omega, pow_succ]
          ring
        rw [hpow]
        have : ∑ i ∈ Finset.range n, g.coeff i * (-M)^i ≤ M^(n-1) * B := by
          have := abs_le.mp htb
          linarith [this.2]
        have hpos : 0 < M^(n-1) * (aₙ * M - B) := by positivity
        nlinarith
      -- Apply IVP
      have hle : -M ≤ M := by linarith
      obtain ⟨c, _, hc⟩ := h g (-M) M hle hg_neg.le hg_pos.le
      exact ⟨c, hc⟩
    by_cases hlc : 0 < f.leadingCoeff
    · exact key f rfl hlc
    · have hlc' : 0 < (-f).leadingCoeff := by
        rw [leadingCoeff_neg, neg_pos]
        have hne : f.leadingCoeff ≠ 0 := by
          intro he
          rw [leadingCoeff_eq_zero] at he
          subst he
          simp at hn
        exact lt_of_le_of_ne (not_lt.mp hlc) hne
      have : (-f).natDegree = f.natDegree := natDegree_neg f
      obtain ⟨c, hc⟩ := key (-f) this hlc'
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
