import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree

open Polynomial
namespace IsRealClosed
universe u
variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

axiom irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : R[X])
private instance : Fact (Irreducible (X ^ 2 + 1 : R[X])) := ⟨irreducible_X_sq_add_one⟩
private abbrev Ri (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] : Type u := AdjoinRoot (X ^ 2 + 1 : R[X])
private noncomputable instance : Module.Finite R (Ri R) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis irreducible_X_sq_add_one.ne_zero).basis

theorem nonempty_algEquiv_Ri_of_finrank_eq_two
    (K : Type u) [Field K] [Algebra R K] (h : Module.finrank R K = 2) :
    Nonempty (K ≃ₐ[R] Ri R) := by
  sorry

end IsRealClosed
