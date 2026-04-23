import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Polynomial

namespace IsRealClosed

universe u
variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

axiom finrank_eq_one_or_two_of_finite
    (K : Type u) [Field K] [Algebra R K] [Module.Finite R K] [Nontrivial K] :
    Module.finrank R K = 1 ∨ Module.finrank R K = 2

theorem natDegree_eq_one_or_forall_eval_pos_of_irreducible
    {g : R[X]} (hmonic : g.Monic) (hirred : Irreducible g) :
    g.natDegree = 1 ∨ ∀ x : R, 0 < g.eval x := by
  -- AdjoinRoot g is a finite extension of R of dimension g.natDegree.
  have hne : g ≠ 0 := hirred.ne_zero
  have hdeg_ne : g.degree ≠ 0 := by
    intro h
    have : g.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (by rw [h])
    -- natDegree zero with monic means g = 1, contradiction with irreducibility
    have : g = 1 := by
      rw [Polynomial.eq_one_of_monic_natDegree_zero hmonic this]
    exact hirred.not_isUnit (by rw [this]; exact isUnit_one)
  haveI : Fact (Irreducible g) := ⟨hirred⟩
  haveI : Nontrivial (AdjoinRoot g) := AdjoinRoot.nontrivial g hdeg_ne
  haveI : Module.Finite R (AdjoinRoot g) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hne).basis
  have hfinrank : Module.finrank R (AdjoinRoot g) = g.natDegree := by
    have := (AdjoinRoot.powerBasis hne).finrank
    rw [AdjoinRoot.powerBasis_dim hne] at this
    exact this
  rcases finrank_eq_one_or_two_of_finite (R := R) (AdjoinRoot g) with h1 | h2
  · left
    rw [hfinrank] at h1
    exact h1
  · right
    rw [hfinrank] at h2
    -- g has natDegree 2, write g = X^2 + C a * X + C b, prove a^2 - 4b < 0
    set a : R := g.coeff 1
    set b : R := g.coeff 0
    have hcoeff2 : g.coeff 2 = 1 := by
      have := hmonic.coeff_natDegree
      rw [h2] at this
      exact this
    have hab : g = X ^ 2 + C a * X + C b := by
      apply Polynomial.ext
      intro n
      rw [coeff_add, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
      rcases lt_trichotomy n 2 with hn | rfl | hn
      · interval_cases n
        · show b = _; simp
        · show a = _; simp
      · show g.coeff 2 = _; rw [hcoeff2]; simp
      · have hn_gt : n > g.natDegree := by rw [h2]; exact hn
        rw [coeff_eq_zero_of_natDegree_lt hn_gt]
        have hn2 : n ≠ 2 := Nat.ne_of_gt hn
        have hn1 : (1 : ℕ) ≠ n := by omega
        have hn0 : n ≠ 0 := by omega
        simp [hn2, hn1, hn0]
    -- discriminant δ = (a/2)^2 - b, and we want δ < 0
    set δ : R := (a / 2) ^ 2 - b with hδdef
    have hdelta_neg : δ < 0 := by
      by_contra hnn
      obtain ⟨c, hc⟩ :=
        (IsRealClosed.nonneg_iff_isSquare (R := R) (x := δ)).mp (not_lt.mp hnn)
      -- r = -a/2 + c is a root of g
      set r : R := -a/2 + c with hrdef
      have hroot : g.IsRoot r := by
        simp only [IsRoot, hab, eval_add, eval_pow, eval_X, eval_mul, eval_C]
        have hcc : c * c = (a/2)^2 - b := hc.symm
        show r ^ 2 + a * r + b = 0
        rw [hrdef]
        linear_combination hcc
      have hdeg1 : g.degree = 1 :=
        Polynomial.degree_eq_one_of_irreducible_of_root hirred hroot
      have hnatdeg1 : g.natDegree = 1 := natDegree_eq_of_degree_eq_some hdeg1
      rw [h2] at hnatdeg1
      exact absurd hnatdeg1 (by norm_num)
    -- Now for any x, g.eval x = (x + a/2)^2 + (-δ) > 0
    intro x
    have heval : g.eval x = (x + a/2) ^ 2 + (-δ) := by
      rw [hab]
      simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
      rw [hδdef]
      ring
    rw [heval]
    have hsq : 0 ≤ (x + a/2) ^ 2 := sq_nonneg _
    linarith
  end IsRealClosed
