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
    · rw [hn0] at hn
      obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hn
      have heva : f.eval a = c := by rw [← hc]; simp
      have hevb : f.eval b = c := by rw [← hc]; simp
      rw [heva] at ha
      rw [hevb] at hb
      have hceq : c = 0 := le_antisymm ha hb
      exact absurd (by rw [← hc, hceq, map_zero] : f = 0) hf0
    have hfnotunit : ¬ IsUnit f := fun hu => hn0 (by
      have := Polynomial.natDegree_eq_zero_of_isUnit hu; rw [hn] at this; exact this)
    obtain ⟨g, hgmonic, hgirred, q, hfq⟩ := Polynomial.exists_monic_irreducible_factor f hfnotunit
    have hgne : g ≠ 0 := hgirred.ne_zero
    have hqne : q ≠ 0 := fun hq0 => hf0 (by rw [hfq, hq0, mul_zero])
    have hgdeg_pos : 1 ≤ g.natDegree := by
      by_contra h
      have hgd0 : g.natDegree = 0 := by omega
      have hg_eq_one : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hgmonic hgd0
      exact hgirred.not_isUnit (by rw [hg_eq_one]; exact isUnit_one)
    have hqdeg_lt : q.natDegree < n := by
      rw [← hn, hfq, Polynomial.natDegree_mul hgne hqne]; omega
    have hfeval : ∀ x : R, f.eval x = g.eval x * q.eval x := fun x => by rw [hfq]; simp
    -- Helper: given sign info on g at a and b, derive sign info on q and apply IH
    have apply_ih : ∀ (q' : R[X]), q'.natDegree < n → q'.eval a ≤ 0 → 0 ≤ q'.eval b →
        ∃ c ∈ Set.Icc a b, q'.IsRoot c := fun q' hq'lt hq'a hq'b =>
      ih q'.natDegree hq'lt hab hq'a hq'b rfl
    rcases natDegree_eq_one_or_forall_eval_pos_of_irreducible hgmonic hgirred with hg1 | hgpos
    · -- g = X + C (g.coeff 0); let r = -g.coeff 0
      have hg_eq : g = X + C (g.coeff 0) := hgmonic.eq_X_add_C hg1
      set r : R := -g.coeff 0 with hrdef
      have hg_eval : ∀ x : R, g.eval x = x - r := fun x => by rw [hg_eq]; simp [hrdef]
      by_cases hra : r < a
      · -- g > 0 on [a,b]: q(a) ≤ 0, q(b) ≥ 0
        have hga_pos : 0 < g.eval a := by rw [hg_eval]; linarith
        have hgb_pos : 0 < g.eval b := by rw [hg_eval]; linarith
        have hqa_le : q.eval a ≤ 0 := by
          have := (hfeval a).symm.le.trans ha
          rcases le_or_gt (q.eval a) 0 with h | h
          · exact h
          · exact absurd (mul_pos hga_pos h) (by linarith)
        have hqb_nn : 0 ≤ q.eval b := by
          have := hb.trans (hfeval b).le
          rcases le_or_gt 0 (q.eval b) with h | h
          · exact h
          · exact absurd (mul_neg_of_pos_of_neg hgb_pos h) (by linarith)
        obtain ⟨c, hcmem, hcroot⟩ := apply_ih q hqdeg_lt hqa_le hqb_nn
        exact ⟨c, hcmem, by show f.eval c = 0; rw [hfeval, show q.eval c = 0 from hcroot, mul_zero]⟩
      by_cases hrb : b < r
      · -- g < 0 on [a,b]: q(a) ≥ 0, q(b) ≤ 0; apply IH to -q
        have hra : a ≤ r := not_lt.mp hra
        have hga_neg : g.eval a < 0 := by rw [hg_eval]; linarith
        have hgb_neg : g.eval b < 0 := by rw [hg_eval]; linarith
        have hqa_nn : 0 ≤ q.eval a := by
          have := (hfeval a).symm.le.trans ha
          rcases le_or_gt 0 (q.eval a) with h | h
          · exact h
          · exact absurd (mul_pos_of_neg_of_neg hga_neg h) (by linarith)
        have hqb_le : q.eval b ≤ 0 := by
          have := hb.trans (hfeval b).le
          rcases le_or_gt (q.eval b) 0 with h | h
          · exact h
          · exact absurd (mul_neg_of_neg_of_pos hgb_neg h) (by linarith)
        have hnqa : (-q).eval a ≤ 0 := by simp; linarith
        have hnqb : 0 ≤ (-q).eval b := by simp; linarith
        have hnq_lt : (-q).natDegree < n := by rw [Polynomial.natDegree_neg]; exact hqdeg_lt
        obtain ⟨c, hcmem, hcroot⟩ := apply_ih (-q) hnq_lt hnqa hnqb
        refine ⟨c, hcmem, ?_⟩
        show f.eval c = 0
        have hqc : q.eval c = 0 := by
          have : (-q).eval c = 0 := hcroot
          rw [eval_neg] at this; linarith
        rw [hfeval, hqc, mul_zero]
      · -- a ≤ r ≤ b: r is a root of g (hence of f)
        refine ⟨r, ⟨not_lt.mp hra, not_lt.mp hrb⟩, ?_⟩
        show f.eval r = 0
        rw [hfeval, show g.eval r = 0 by rw [hg_eval]; ring, zero_mul]
    · -- g everywhere positive
      have hga_pos : 0 < g.eval a := hgpos a
      have hgb_pos : 0 < g.eval b := hgpos b
      have hqa_le : q.eval a ≤ 0 := by
        have := (hfeval a).symm.le.trans ha
        rcases le_or_gt (q.eval a) 0 with h | h
        · exact h
        · exact absurd (mul_pos hga_pos h) (by linarith)
      have hqb_nn : 0 ≤ q.eval b := by
        have := hb.trans (hfeval b).le
        rcases le_or_gt 0 (q.eval b) with h | h
        · exact h
        · exact absurd (mul_neg_of_pos_of_neg hgb_pos h) (by linarith)
      obtain ⟨c, hcmem, hcroot⟩ := apply_ih q hqdeg_lt hqa_le hqb_nn
      exact ⟨c, hcmem, by show f.eval c = 0; rw [hfeval, show q.eval c = 0 from hcroot, mul_zero]⟩

end IsRealClosed
