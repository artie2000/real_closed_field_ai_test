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

namespace IsRealClosed

variable (R : Type*) [Field R]

section Algebraic

variable [IsRealClosed R]

/-- Classification of monic irreducible polynomials over a real closed field `R`:
they are linear (`X - c`) or quadratic of the form `(X - a)^2 + b^2` with `b ≠ 0`. -/
theorem monic_irreducible_classification {f : Polynomial R} (hf : f.Monic) (hf' : Irreducible f) :
    (∃ c : R, f = Polynomial.X - Polynomial.C c) ∨
    (∃ a b : R, b ≠ 0 ∧
      f = (Polynomial.X - Polynomial.C a) ^ 2 + Polynomial.C (b ^ 2)) := sorry

end Algebraic

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- Polynomials over `R` satisfy the intermediate value property. -/
def PolynomialIVP : Prop :=
  ∀ (f : Polynomial R) (a b : R), a ≤ b → f.eval a ≤ 0 → 0 ≤ f.eval b →
    ∃ c ∈ Set.Icc a b, f.IsRoot c

open Polynomial

/-- For a quadratic monic of the form `(X - α)^2 + β^2` with `β ≠ 0`,
the evaluation is strictly positive everywhere. -/
private lemma quadratic_pos {α β : R} (hβ : β ≠ 0) (x : R) :
    0 < ((X - C α) ^ 2 + C (β ^ 2)).eval x := by
  simp only [eval_add, eval_pow, eval_sub, eval_X, eval_C]
  have h1 : 0 ≤ (x - α) ^ 2 := sq_nonneg _
  have h2 : 0 < β ^ 2 := by positivity
  linarith

/-- Polynomials over a real closed ordered field satisfy the intermediate value property. -/
theorem polynomialIVP_of_isRealClosed [IsRealClosed R] : PolynomialIVP R := by
  intro f a b hab
  -- Strong induction on natDegree of f
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  intro hfa hfb
  -- Case: natDegree = 0, so f = C (f.coeff 0)
  by_cases hn0 : n = 0
  · subst hn0
    have hfC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hn
    rw [hfC] at hfa hfb ⊢
    simp only [eval_C] at hfa hfb
    have hc0 : f.coeff 0 = 0 := le_antisymm hfa hfb
    refine ⟨a, ⟨le_refl a, hab⟩, ?_⟩
    show (C (f.coeff 0)).eval a = 0
    rw [hc0]; simp
  -- Case: natDegree > 0, so f is not a unit
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hfdeg_pos : 0 < f.natDegree := by rw [hn]; exact hnpos
    have hf_not_unit : ¬ IsUnit f := not_isUnit_of_natDegree_pos f hfdeg_pos
    obtain ⟨g, hg_monic, hg_irr, hg_dvd⟩ := exists_monic_irreducible_factor f hf_not_unit
    -- Write f = g * h
    obtain ⟨h, hfgh⟩ := hg_dvd
    -- Use classification
    rcases monic_irreducible_classification hg_monic hg_irr with ⟨c, hgeq⟩ | ⟨α, β, hβ, hgeq⟩
    · -- Case: g = X - C c, natDegree g = 1
      have hg_natDeg : g.natDegree = 1 := by
        rw [hgeq, natDegree_X_sub_C]
      -- f ≠ 0 since natDegree > 0
      have hfne : f ≠ 0 := by
        intro hfz; rw [hfz, natDegree_zero] at hn; omega
      -- h ≠ 0
      have hhne : h ≠ 0 := by
        intro hhz
        rw [hhz, mul_zero] at hfgh
        exact hfne hfgh
      have hg_ne : g ≠ 0 := hg_monic.ne_zero
      have hh_natDeg : h.natDegree = n - 1 := by
        have heq : f.natDegree = g.natDegree + h.natDegree := by
          rw [hfgh]; exact natDegree_mul hg_ne hhne
        rw [hg_natDeg] at heq
        omega
      have hh_lt : h.natDegree < n := by rw [hh_natDeg]; omega
      -- Case analysis on whether c is in [a, b]
      by_cases hcab : a ≤ c ∧ c ≤ b
      · -- c ∈ [a,b]: g(c) = 0, so f(c) = 0
        refine ⟨c, ⟨hcab.1, hcab.2⟩, ?_⟩
        show f.eval c = 0
        rw [hfgh, eval_mul, hgeq]
        simp
      · -- c ∉ [a,b]: both g(a) and g(b) have the same sign
        have hga : g.eval a = a - c := by rw [hgeq]; simp
        have hgb : g.eval b = b - c := by rw [hgeq]; simp
        -- Either c < a (both a-c, b-c > 0) or b < c (both < 0)
        push_neg at hcab
        rcases lt_or_ge c a with hca | hac
        · -- c < a, so g(a) > 0, g(b) > 0
          have hga_pos : 0 < g.eval a := by rw [hga]; linarith
          have hgb_pos : 0 < g.eval b := by rw [hgb]; linarith
          -- f(a) = g(a) * h(a), f(b) = g(b) * h(b)
          have hfa_eq : f.eval a = g.eval a * h.eval a := by rw [hfgh, eval_mul]
          have hfb_eq : f.eval b = g.eval b * h.eval b := by rw [hfgh, eval_mul]
          have hha : h.eval a ≤ 0 := by
            by_contra hha'
            push_neg at hha'
            rw [hfa_eq] at hfa
            exact absurd hfa (not_le.mpr (mul_pos hga_pos hha'))
          have hhb : 0 ≤ h.eval b := by
            by_contra hhb'
            push_neg at hhb'
            rw [hfb_eq] at hfb
            exact absurd hfb (not_le.mpr (mul_neg_of_pos_of_neg hgb_pos hhb'))
          obtain ⟨c', hc'_mem, hc'_root⟩ := ih h.natDegree hh_lt h rfl hfa hab hha hhb
          refine ⟨c', hc'_mem, ?_⟩
          show f.eval c' = 0
          rw [hfgh, eval_mul]
          show g.eval c' * h.eval c' = 0
          rw [hc'_root]; ring
        · -- c ≥ a, so necessarily b < c (since ¬ (a ≤ c ∧ c ≤ b))
          have hbc : b < c := by
            rcases hcab hac with hcontra
            exact lt_of_not_ge hcontra
          have hga_neg : g.eval a < 0 := by rw [hga]; linarith
          have hgb_neg : g.eval b < 0 := by rw [hgb]; linarith
          have hfa_eq : f.eval a = g.eval a * h.eval a := by rw [hfgh, eval_mul]
          have hfb_eq : f.eval b = g.eval b * h.eval b := by rw [hfgh, eval_mul]
          -- f(a) ≤ 0, g(a) < 0, so h(a) ≥ 0
          -- f(b) ≥ 0, g(b) < 0, so h(b) ≤ 0
          -- Apply IH to -h
          have hha_nonneg : 0 ≤ h.eval a := by
            by_contra hha'
            push_neg at hha'
            rw [hfa_eq] at hfa
            -- g(a) < 0, h(a) < 0, so product > 0. But f(a) ≤ 0. Contradiction.
            exact absurd hfa (not_le.mpr (mul_pos_of_neg_of_neg hga_neg hha'))
          have hhb_nonpos : h.eval b ≤ 0 := by
            by_contra hhb'
            push_neg at hhb'
            rw [hfb_eq] at hfb
            -- g(b) < 0, h(b) > 0, so product < 0. But 0 ≤ f(b). Contradiction.
            exact absurd hfb (not_le.mpr (mul_neg_of_neg_of_pos hgb_neg hhb'))
          -- Consider -h: (-h).eval a = -(h.eval a) ≤ 0, (-h).eval b = -(h.eval b) ≥ 0
          have hmh_a : (-h).eval a ≤ 0 := by rw [eval_neg]; linarith
          have hmh_b : 0 ≤ (-h).eval b := by rw [eval_neg]; linarith
          have hmh_deg : (-h).natDegree = h.natDegree := natDegree_neg h
          have hmh_lt : (-h).natDegree < n := hmh_deg ▸ hh_lt
          obtain ⟨c', hc'_mem, hc'_root⟩ :=
            ih (-h).natDegree hmh_lt (-h) rfl hab hmh_a hmh_b
          refine ⟨c', hc'_mem, ?_⟩
          have hc'_h : h.eval c' = 0 := by
            have : (-h).eval c' = 0 := hc'_root
            rw [eval_neg, neg_eq_zero] at this
            exact this
          show f.eval c' = 0
          rw [hfgh, eval_mul, hc'_h, mul_zero]
    · -- Case: g = (X - α)^2 + β^2 quadratic, everywhere positive
      have hg_natDeg : g.natDegree = 2 := by
        rw [hgeq]
        -- (X - C α)^2 has natDegree 2, + C (β^2) is const
        have h1 : ((X - C α) ^ 2).natDegree = 2 := by
          rw [natDegree_pow, natDegree_X_sub_C]
        rw [show ((X - C α) ^ 2 + C (β ^ 2)).natDegree = 2 from ?_]
        rw [natDegree_add_C]
        exact h1
      have hfne : f ≠ 0 := by
        intro hfz; rw [hfz, natDegree_zero] at hn; omega
      have hhne : h ≠ 0 := by
        intro hhz; rw [hhz, mul_zero] at hfgh; exact hfne hfgh
      have hg_ne : g ≠ 0 := hg_monic.ne_zero
      have hh_natDeg : h.natDegree = n - 2 := by
        have heq : f.natDegree = g.natDegree + h.natDegree := by
          rw [hfgh]; exact natDegree_mul hg_ne hhne
        rw [hg_natDeg] at heq
        omega
      have hh_lt : h.natDegree < n := by rw [hh_natDeg]; omega
      -- g is positive everywhere
      have hga_pos : 0 < g.eval a := by rw [hgeq]; exact quadratic_pos R hβ a
      have hgb_pos : 0 < g.eval b := by rw [hgeq]; exact quadratic_pos R hβ b
      have hfa_eq : f.eval a = g.eval a * h.eval a := by rw [hfgh, eval_mul]
      have hfb_eq : f.eval b = g.eval b * h.eval b := by rw [hfgh, eval_mul]
      have hha : h.eval a ≤ 0 := by
        by_contra hha'
        push_neg at hha'
        rw [hfa_eq] at hfa
        exact absurd hfa (not_le.mpr (mul_pos hga_pos hha'))
      have hhb : 0 ≤ h.eval b := by
        by_contra hhb'
        push_neg at hhb'
        rw [hfb_eq] at hfb
        exact absurd hfb (not_le.mpr (mul_neg_of_pos_of_neg hgb_pos hhb'))
      obtain ⟨c', hc'_mem, hc'_root⟩ := ih h.natDegree hh_lt h rfl hab hha hhb
      refine ⟨c', hc'_mem, ?_⟩
      show f.eval c' = 0
      rw [hfgh, eval_mul]
      show g.eval c' * h.eval c' = 0
      rw [show h.eval c' = 0 from hc'_root]
      ring

end IsRealClosed
