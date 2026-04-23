import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.AdjoinRoot

open Polynomial

namespace IsRealClosed

universe u
variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

axiom natDegree_eq_one_or_forall_eval_pos_of_irreducible
    {g : R[X]} (hmonic : g.Monic) (hirred : Irreducible g) :
    g.natDegree = 1 ∨ ∀ x : R, 0 < g.eval x

theorem ivp_poly
    {f : R[X]} {a b : R} (hab : a ≤ b) (ha : f.eval a ≤ 0) (hb : 0 ≤ f.eval b) :
    ∃ c ∈ Set.Icc a b, f.IsRoot c := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f a b with
  | _ n ih =>
    by_cases hf0 : f = 0
    · exact ⟨a, ⟨le_refl a, hab⟩, by simp [hf0]⟩
    by_cases hn0 : n = 0
    · -- f is a nonzero polynomial of natDegree 0
      rw [hn0] at hn
      obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hn
      have heva : f.eval a = c := by rw [← hc]; simp
      have hevb : f.eval b = c := by rw [← hc]; simp
      rw [heva] at ha
      rw [hevb] at hb
      have hceq : c = 0 := le_antisymm ha hb
      exfalso
      apply hf0
      rw [← hc, hceq, map_zero]
    have hfnotunit : ¬ IsUnit f := by
      intro hu
      have := Polynomial.natDegree_eq_zero_of_isUnit hu
      rw [hn] at this
      exact hn0 this
    obtain ⟨g, hgmonic, hgirred, hgdvd⟩ := Polynomial.exists_monic_irreducible_factor f hfnotunit
    obtain ⟨q, hfq⟩ := hgdvd
    have hgne : g ≠ 0 := hgirred.ne_zero
    have hqne : q ≠ 0 := by
      intro hq0
      rw [hq0, mul_zero] at hfq
      exact hf0 hfq
    have hgdeg_pos : 1 ≤ g.natDegree := by
      rcases Nat.lt_or_ge g.natDegree 1 with h | h
      · exfalso
        have hgd0 : g.natDegree = 0 := by omega
        have hg_eq_one : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hgmonic hgd0
        exact hgirred.not_isUnit (by rw [hg_eq_one]; exact isUnit_one)
      · exact h
    have hqdeg_lt : q.natDegree < n := by
      rw [← hn, hfq, Polynomial.natDegree_mul hgne hqne]
      omega
    -- helper: f.eval x = g.eval x * q.eval x
    have hfeval : ∀ x : R, f.eval x = g.eval x * q.eval x := by
      intro x; rw [hfq]; simp
    rcases natDegree_eq_one_or_forall_eval_pos_of_irreducible hgmonic hgirred with hg1 | hgpos
    · -- g has degree 1: g = X + C (g.coeff 0). Let r = -g.coeff 0.
      have hg_eq : g = X + C (g.coeff 0) := hgmonic.eq_X_add_C hg1
      set r : R := -g.coeff 0 with hrdef
      have hg_eval : ∀ x : R, g.eval x = x - r := by
        intro x
        rw [hg_eq]; simp [hrdef]
      by_cases hra : r < a
      · -- r < a: g(x) = x - r > 0 for x ∈ [a,b]
        have hga_pos : 0 < g.eval a := by rw [hg_eval]; linarith
        have hgb_pos : 0 < g.eval b := by rw [hg_eval]; linarith
        have hqa_le : q.eval a ≤ 0 := by
          have hfa := hfeval a
          rw [hfa] at ha
          by_contra h
          push_neg at h
          have : 0 < g.eval a * q.eval a := mul_pos hga_pos h
          linarith
        have hqb_nn : 0 ≤ q.eval b := by
          have hfb := hfeval b
          rw [hfb] at hb
          by_contra h
          push_neg at h
          have : g.eval b * q.eval b < 0 := mul_neg_of_pos_of_neg hgb_pos h
          linarith
        obtain ⟨c, hcmem, hcroot⟩ := ih q.natDegree hqdeg_lt hab hqa_le hqb_nn rfl
        refine ⟨c, hcmem, ?_⟩
        show f.eval c = 0
        rw [hfeval, show q.eval c = 0 from hcroot, mul_zero]
      by_cases hrb : b < r
      · -- r > b: g(x) = x - r < 0 for x ∈ [a,b]
        push_neg at hra
        have hga_neg : g.eval a < 0 := by rw [hg_eval]; linarith
        have hgb_neg : g.eval b < 0 := by rw [hg_eval]; linarith
        have hqa_nn : 0 ≤ q.eval a := by
          have hfa := hfeval a
          rw [hfa] at ha
          by_contra h
          push_neg at h
          have : 0 < g.eval a * q.eval a := mul_pos_of_neg_of_neg hga_neg h
          linarith
        have hqb_le : q.eval b ≤ 0 := by
          have hfb := hfeval b
          rw [hfb] at hb
          by_contra h
          push_neg at h
          have : g.eval b * q.eval b < 0 := mul_neg_of_neg_of_pos hgb_neg h
          linarith
        have hnqa : (-q).eval a ≤ 0 := by simp; linarith
        have hnqb : 0 ≤ (-q).eval b := by simp; linarith
        have hnq_deg : (-q).natDegree = q.natDegree := Polynomial.natDegree_neg q
        have hnq_lt : (-q).natDegree < n := by rw [hnq_deg]; exact hqdeg_lt
        obtain ⟨c, hcmem, hcroot⟩ := ih (-q).natDegree hnq_lt hab hnqa hnqb rfl
        refine ⟨c, hcmem, ?_⟩
        show f.eval c = 0
        have hneqc : (-q).eval c = 0 := hcroot
        have hqc : q.eval c = 0 := by
          have hne : (-q).eval c = -(q.eval c) := by simp
          rw [hne] at hneqc
          linarith
        rw [hfeval, hqc, mul_zero]
      · -- a ≤ r ≤ b
        push_neg at hra hrb
        refine ⟨r, ⟨hra, hrb⟩, ?_⟩
        show f.eval r = 0
        have hgr : g.eval r = 0 := by rw [hg_eval]; ring
        rw [hfeval, hgr, zero_mul]
    · -- g is everywhere positive
      have hga_pos : 0 < g.eval a := hgpos a
      have hgb_pos : 0 < g.eval b := hgpos b
      have hqa_le : q.eval a ≤ 0 := by
        have hfa := hfeval a
        rw [hfa] at ha
        by_contra h
        push_neg at h
        have : 0 < g.eval a * q.eval a := mul_pos hga_pos h
        linarith
      have hqb_nn : 0 ≤ q.eval b := by
        have hfb := hfeval b
        rw [hfb] at hb
        by_contra h
        push_neg at h
        have : g.eval b * q.eval b < 0 := mul_neg_of_pos_of_neg hgb_pos h
        linarith
      obtain ⟨c, hcmem, hcroot⟩ := ih q.natDegree hqdeg_lt hab hqa_le hqb_nn rfl
      refine ⟨c, hcmem, ?_⟩
      show f.eval c = 0
      rw [hfeval, show q.eval c = 0 from hcroot, mul_zero]

end IsRealClosed
