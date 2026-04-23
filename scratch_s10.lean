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
  -- Strong induction on f.natDegree
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f a b with
  | _ n ih =>
    by_cases hf0 : f = 0
    · -- f = 0: a works
      exact ⟨a, ⟨le_refl a, hab⟩, by simp [hf0]⟩
    by_cases hn0 : n = 0
    · -- f is a nonzero constant
      subst hn0
      obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hn
      have heva : f.eval a = c := by rw [← hc]; simp
      have hevb : f.eval b = c := by rw [← hc]; simp
      rw [heva] at ha
      rw [hevb] at hb
      have hceq : c = 0 := le_antisymm ha hb
      exfalso
      apply hf0
      rw [← hc, hceq, map_zero]
    -- n ≥ 1. Extract monic irreducible factor
    have hfnotunit : ¬ IsUnit f := by
      intro hu
      have := Polynomial.natDegree_eq_zero_of_isUnit hu
      rw [hn] at this
      exact hn0 this.symm
    obtain ⟨g, hgmonic, hgirred, hgdvd⟩ := Polynomial.exists_monic_irreducible_factor f hfnotunit
    obtain ⟨q, hfq⟩ := hgdvd
    have hgne : g ≠ 0 := hgirred.ne_zero
    have hqne : q ≠ 0 := by
      intro hq0
      rw [hq0, mul_zero] at hfq
      exact hf0 hfq
    have hgdeg_pos : 1 ≤ g.natDegree := by
      rcases Nat.lt_or_ge g.natDegree 1 with h | h
      · interval_cases g.natDegree
        · have : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hgmonic rfl
          exact absurd hgirred (by rw [this]; exact not_irreducible_one)
      · exact h
    have hqdeg_lt : q.natDegree < n := by
      rw [← hn, hfq, Polynomial.natDegree_mul hgne hqne]
      omega
    -- Apply S9 classification
    rcases natDegree_eq_one_or_forall_eval_pos_of_irreducible hgmonic hgirred with hg1 | hgpos
    · -- g has degree 1: g = X + C (g.coeff 0). Set r = -g.coeff 0.
      have hg_eq : g = X + C (g.coeff 0) := hgmonic.eq_X_add_C hg1
      set r : R := -g.coeff 0 with hrdef
      have hg_eval : ∀ x : R, g.eval x = x - r := by
        intro x
        rw [hg_eq]
        simp [hrdef]
      -- Split on position of r
      by_cases hra : r < a
      · -- r < a: g > 0 on [a,b]
        have hga_pos : 0 < g.eval a := by rw [hg_eval]; linarith
        have hgb_pos : 0 < g.eval b := by rw [hg_eval]; linarith [hra, hab]
        have hqa_le : q.eval a ≤ 0 := by
          have hfa : f.eval a = g.eval a * q.eval a := by rw [hfq]; simp
          rw [hfa] at ha
          exact (mul_nonpos_iff.mp ha).resolve_left
            (fun ⟨h1, _⟩ => absurd h1 (not_le.mpr hga_pos)) |>.2
        have hqb_nn : 0 ≤ q.eval b := by
          have hfb : f.eval b = g.eval b * q.eval b := by rw [hfq]; simp
          rw [hfb] at hb
          exact (nonneg_of_mul_nonneg_left hb hgb_pos)
        -- Apply IH to q
        obtain ⟨c, hcmem, hcroot⟩ := ih q.natDegree hqdeg_lt hab hqa_le hqb_nn rfl
        refine ⟨c, hcmem, ?_⟩
        show f.eval c = 0
        rw [hfq]
        simp [hcroot]
      by_cases hrb : b < r
      · -- r > b: g < 0 on [a,b]
        push_neg at hra
        have hga_neg : g.eval a < 0 := by rw [hg_eval]; linarith [hra, hab, hrb]
        have hgb_neg : g.eval b < 0 := by rw [hg_eval]; linarith
        have hqa_nn : 0 ≤ q.eval a := by
          have hfa : f.eval a = g.eval a * q.eval a := by rw [hfq]; simp
          rw [hfa] at ha
          -- ga * qa ≤ 0, ga < 0 ⇒ qa ≥ 0
          rcases le_or_lt (q.eval a) 0 with h | h
          · -- ga * qa ≥ 0 actually
            have hpos : 0 ≤ g.eval a * q.eval a := mul_nonneg_of_nonpos_nonpos hga_neg.le h
            have : g.eval a * q.eval a = 0 := le_antisymm ha hpos
            rcases mul_eq_zero.mp this with h1 | h1
            · linarith
            · rw [h1]
          · exact h.le
        have hqb_le : q.eval b ≤ 0 := by
          have hfb : f.eval b = g.eval b * q.eval b := by rw [hfq]; simp
          rw [hfb] at hb
          rcases le_or_lt (q.eval b) 0 with h | h
          · exact h
          · have hneg : g.eval b * q.eval b < 0 := mul_neg_of_neg_of_pos hgb_neg h
            linarith
        -- Apply IH to -q
        have hnqa : (-q).eval a ≤ 0 := by simp; linarith
        have hnqb : 0 ≤ (-q).eval b := by simp; linarith
        have hnq_deg : (-q).natDegree = q.natDegree := Polynomial.natDegree_neg q
        have hnq_lt : (-q).natDegree < n := by rw [hnq_deg]; exact hqdeg_lt
        obtain ⟨c, hcmem, hcroot⟩ := ih (-q).natDegree hnq_lt hab hnqa hnqb rfl
        refine ⟨c, hcmem, ?_⟩
        show f.eval c = 0
        rw [hfq]
        have hneqc : (-q).eval c = 0 := hcroot
        have hqc : q.eval c = 0 := by
          have : (-q).eval c = -(q.eval c) := by simp
          rw [this] at hneqc
          linarith
        simp [hqc]
      · -- a ≤ r ≤ b: r is a root of g, hence of f
        push_neg at hra hrb
        refine ⟨r, ⟨hra, hrb⟩, ?_⟩
        show f.eval r = 0
        rw [hfq]
        have hgr : g.eval r = 0 := by rw [hg_eval]; ring
        simp [hgr]
    · -- g is everywhere positive
      have hga_pos : 0 < g.eval a := hgpos a
      have hgb_pos : 0 < g.eval b := hgpos b
      have hqa_le : q.eval a ≤ 0 := by
        have hfa : f.eval a = g.eval a * q.eval a := by rw [hfq]; simp
        rw [hfa] at ha
        rcases le_or_lt (q.eval a) 0 with h | h
        · exact h
        · exfalso
          have : 0 < g.eval a * q.eval a := mul_pos hga_pos h
          linarith
      have hqb_nn : 0 ≤ q.eval b := by
        have hfb : f.eval b = g.eval b * q.eval b := by rw [hfq]; simp
        rw [hfb] at hb
        exact nonneg_of_mul_nonneg_left hb hgb_pos
      obtain ⟨c, hcmem, hcroot⟩ := ih q.natDegree hqdeg_lt hab hqa_le hqb_nn rfl
      refine ⟨c, hcmem, ?_⟩
      show f.eval c = 0
      rw [hfq]
      simp [hcroot]

end IsRealClosed
