/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.Algebra.Order.Algebra
import RealClosedField.Algebra.Order.Field.IsSemireal
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.TFAE

open Polynomial

namespace IsRealClosed

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A polynomial of the form `X^2 - C a` with `a` not a square is irreducible in `R[X]`. -/
private lemma irreducible_X_sq_sub_C_of_not_isSquare
    {a : R} (hsq : ¬ IsSquare a) : Irreducible (X ^ 2 - C a : R[X]) := by
  have hmonic : (X ^ 2 - C a : R[X]).Monic := monic_X_pow_sub_C a (by decide)
  have hdeg : (X ^ 2 - C a : R[X]).natDegree = 2 := natDegree_X_pow_sub_C
  rw [Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hmonic
        (by rw [hdeg]) (by rw [hdeg]; decide)]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro c hc
  rw [mem_roots hmonic.ne_zero] at hc
  simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hc
  exact hsq ⟨c, by linear_combination hc.symm⟩

/-- Any irreducible polynomial of natDegree > 1 gives a non-surjective algebraMap into its
AdjoinRoot. -/
private lemma algebraMap_not_bijective_of_irreducible_natDegree_pos
    {p : R[X]} (hirred : Irreducible p) (hdeg : 1 < p.natDegree) :
    ¬ Function.Bijective (algebraMap R (AdjoinRoot p)) := by
  intro hbij
  -- root p has minpoly (up to unit) = p, which has natDegree > 1, so is not in the range
  haveI : Fact (Irreducible p) := ⟨hirred⟩
  -- Since algebraMap is bijective, every element is in its range
  have hsurj : Function.Surjective (algebraMap R (AdjoinRoot p)) := hbij.2
  obtain ⟨r, hr⟩ := hsurj (AdjoinRoot.root p)
  -- But evaluating p at r gives 0, contradicting that p has degree > 1 and no linear factor
  have hroot : p.IsRoot r := by
    have h₁ : (AdjoinRoot.mk p) p = 0 := AdjoinRoot.mk_self
    have h₂ : (aeval (AdjoinRoot.root p) p) = 0 := AdjoinRoot.eval₂_root p
    -- Since algebraMap r = root p, r should be a root of p in R
    have : algebraMap R (AdjoinRoot p) (p.eval r) = 0 := by
      rw [← hr] at h₂
      rw [show algebraMap R (AdjoinRoot p) (p.eval r) = (aeval (algebraMap R (AdjoinRoot p) r) p)
          from (Polynomial.aeval_algebraMap_apply _ _ _).symm]
      exact h₂
    have : p.eval r = 0 := hbij.1 (by simpa using this)
    exact this
  -- But p is irreducible of degree > 1, so has no root
  exact hirred.not_isRoot_of_natDegree_ne_one hdeg.ne' hroot

/-- If an ordered field `R` has no nontrivial ordered algebraic extension, then it is
real closed. -/
theorem of_bijective_algebraMap_of_isOrderedAlgebra
    (h : ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
         [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K],
         Function.Bijective (algebraMap R K)) :
    IsRealClosed R := by
  refine IsRealClosed.of_linearOrderedField (fun {a} ha => ?_) (fun {f} hodd => ?_)
  · -- PART A: every nonneg element is a square
    -- Apply part A by contradiction
    by_contra hsq
    have hirred : Irreducible (X ^ 2 - C a : R[X]) :=
      irreducible_X_sq_sub_C_of_not_isSquare hsq
    haveI : Fact (Irreducible (X ^ 2 - C a : R[X])) := ⟨hirred⟩
    set K := AdjoinRoot (X ^ 2 - C a : R[X])
    haveI : Module.Finite R K :=
      (monic_X_pow_sub_C a (by decide : (2 : ℕ) ≠ 0)).finite_adjoinRoot
    haveI : Algebra.IsAlgebraic R K := Algebra.IsAlgebraic.of_finite R K
    -- Provide an ordered algebra structure on K. For that, use the functional
    -- π : K → R given by taking 'real part' (coefficient of 1 in basis {1, root}).
    -- We show -1 ∉ span_{R≥0} {squares in K}
    have : (∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule R K) := by
      rw [Field.exists_isOrderedAlgebra_iff_neg_one_notMem_span_nonneg_isSquare]
      sorry
    obtain ⟨_, _, _⟩ := this
    have hdeg : (1 : ℕ) < (X ^ 2 - C a : R[X]).natDegree := by
      rw [natDegree_X_pow_sub_C]; decide
    exact algebraMap_not_bijective_of_irreducible_natDegree_pos hirred hdeg (h K)
  · -- PART B: every odd-degree polynomial has a root
    sorry

end IsRealClosed
