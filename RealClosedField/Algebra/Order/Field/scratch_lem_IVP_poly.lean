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

/-- Polynomials over a real closed ordered field satisfy the intermediate value property. -/
theorem polynomialIVP_of_isRealClosed [IsRealClosed R] : PolynomialIVP R := by
  sorry

end IsRealClosed
