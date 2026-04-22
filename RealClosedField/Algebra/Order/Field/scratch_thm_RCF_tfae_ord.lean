/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Tactic.TFAE
import RealClosedField.Algebra.Order.Algebra

/-!
# Equivalent conditions for a real closed field (ordered case)

For an ordered field `R`, the following are equivalent:
1. `R` is real closed.
2. `R` is maximal with respect to ordered algebraic extensions.
3. Polynomials over `R` satisfy the intermediate value property.
-/

namespace IsRealClosed

variable (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]

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

open Polynomial in
/-- Algebraic bound: For a polynomial `f` of positive natDegree `n` with positive leading
coefficient, there is a point where `f` is positive. -/
private lemma exists_eval_pos_of_leadingCoeff_pos {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (f : R[X]) (hdeg : 0 < f.natDegree) (hlead : 0 < f.leadingCoeff) :
    ∃ x : R, 0 < f.eval x := by
  -- Induction on natDegree
  -- Key idea: take M = 1 + (sum of |coeffs|) / leadingCoeff, then eval at M is positive
  sorry

open Polynomial in
/-- For odd-degree polynomials, sign changes occur. -/
private lemma exists_eval_neg_and_pos_of_odd {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (f : R[X]) (hodd : Odd f.natDegree) :
    ∃ a b : R, f.eval a ≤ 0 ∧ 0 ≤ f.eval b := by
  sorry

/-- For an ordered field `R`, the following are equivalent:
1. `R` is real closed.
2. `R` is maximal with respect to ordered algebraic extensions.
3. Polynomials over `R` satisfy the intermediate value property. -/
theorem tfae_of_linearOrderedField :
    List.TFAE
      [ IsRealClosed R,
        NoNontrivialOrderedAlgExt R,
        PolynomialIVP R ] := by
  sorry

end IsRealClosed
