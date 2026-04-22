/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
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

/-- Helper lemma (`lem:IVP_poly`): polynomials over a real closed ordered field satisfy the
intermediate value property. -/
private lemma polynomialIVP_of_isRealClosed [IsRealClosed R] : PolynomialIVP R := by
  sorry

/-- Helper lemma (`thm:IVP_poly_imp_RCF`): an ordered field whose polynomials satisfy the
intermediate value property is real closed. -/
private lemma isRealClosed_of_polynomialIVP (h : PolynomialIVP R) : IsRealClosed R := by
  sorry

/-- Helper lemma (`lem:RCF_max_ord`): a real closed ordered field has no nontrivial ordered
algebraic extensions. -/
private lemma noNontrivialOrderedAlgExt_of_isRealClosed [IsRealClosed R] :
    NoNontrivialOrderedAlgExt R := by
  sorry

/-- Helper lemma (`thm:ord_max_imp_RCF`): an ordered field with no nontrivial ordered
algebraic extensions is real closed. -/
private lemma isRealClosed_of_noNontrivialOrderedAlgExt (h : NoNontrivialOrderedAlgExt R) :
    IsRealClosed R := by
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
  tfae_have 1 → 2 := fun _ ↦ noNontrivialOrderedAlgExt_of_isRealClosed R
  tfae_have 2 → 1 := isRealClosed_of_noNontrivialOrderedAlgExt R
  tfae_have 1 → 3 := fun _ ↦ polynomialIVP_of_isRealClosed R
  tfae_have 3 → 1 := isRealClosed_of_polynomialIVP R
  tfae_finish

end IsRealClosed
