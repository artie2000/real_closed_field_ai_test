/-
Scratch file for proving S8 (`bijective_algebraMap_of_isOrderedAlgebra'`).

Once the proof is complete, the tactic block will be merged into
`RealClosedField/Algebra/Order/Field/IsRealClosed/Closure.lean`
to replace the `sorry` at the body of `theorem bijective_algebraMap_of_isOrderedAlgebra'`.
-/
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Trace

open Polynomial

namespace IsRealClosedS8Scratch

universe u
variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- Shim for `Ri R` from Closure.lean. -/
abbrev Ri (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] : Type u := AdjoinRoot (X ^ 2 + 1 : R[X])

/-- Shim: `-1` is not a square in a real closed field. -/
axiom not_isSquare_neg_one : ¬ IsSquare (-1 : R)

/-- Shim for S3: quadratic extension is `Ri R`. -/
axiom nonempty_algEquiv_Ri_of_finrank_eq_two
    (K : Type u) [Field K] [Algebra R K] (h : Module.finrank R K = 2) :
    Nonempty (K ≃ₐ[R] Ri R)

/-- Shim for S5: every finite extension of an RCF has finrank 1 or 2. -/
axiom finrank_eq_one_or_two_of_finite
    (K : Type u) [Field K] [Algebra R K] [Module.Finite R K] [Nontrivial K] :
    Module.finrank R K = 1 ∨ Module.finrank R K = 2

/-- Shim for S6: every algebraic extension of an RCF is finite. -/
axiom finite_of_isAlgebraic
    (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K] :
    Module.Finite R K

/-- **S8.** An RCF has no nontrivial ordered algebraic extension. -/
theorem bijective_algebraMap_of_isOrderedAlgebra'
    (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
    [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K] :
    Function.Bijective (algebraMap R K) := by
  haveI : Module.Finite R K := finite_of_isAlgebraic K
  rcases finrank_eq_one_or_two_of_finite (R := R) K with h1 | h2
  · exact Module.Free.bijective_algebraMap_of_finrank_eq_one h1
  · exfalso
    obtain ⟨φ⟩ := nonempty_algEquiv_Ri_of_finrank_eq_two K h2
    -- Build i : K with i^2 = -1
    set i : K := φ.symm (AdjoinRoot.root (X ^ 2 + 1 : R[X])) with hi_def
    have hroot_sq : (AdjoinRoot.root (X ^ 2 + 1 : R[X])) ^ 2 = (-1 : Ri R) := by
      have : (AdjoinRoot.root (X ^ 2 + 1 : R[X])) ^ 2 + 1 = 0 := by
        have := AdjoinRoot.mk_self (X ^ 2 + 1 : R[X])
        have h2 : AdjoinRoot.mk (X ^ 2 + 1 : R[X]) (X ^ 2 + 1) =
            (AdjoinRoot.root (X ^ 2 + 1 : R[X])) ^ 2 + 1 := by
          rw [← AdjoinRoot.aeval_eq]
          simp [map_add, map_pow, map_one]
        rw [h2] at this
        exact this
      linarith [this]
    have hi_sq : i ^ 2 = (-1 : K) := by
      have : φ.symm ((AdjoinRoot.root (X ^ 2 + 1 : R[X])) ^ 2) = φ.symm (-1) := by
        rw [hroot_sq]
      simp [map_pow, map_neg, map_one] at this
      rw [hi_def]
      rw [map_pow] at this
      convert this using 1
      simp
    have hsq : (0 : K) ≤ i ^ 2 := sq_nonneg i
    rw [hi_sq] at hsq
    linarith
end IsRealClosedS8Scratch
