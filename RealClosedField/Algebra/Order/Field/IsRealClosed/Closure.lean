/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Fundamental theorem of algebra for real closed fields

This file collects the key consequences of `IsRealClosed R` that together yield FTA
for an RCF: every finite extension of `R` is either `R` itself or `R[i]`.

The main applications are the two remaining sorries in
`RealClosedField/Algebra/Order/Field/IsRealClosed.lean`:

* `IsRealClosed.bijective_algebraMap_of_isOrderedAlgebra`:
  a real closed field has no nontrivial ordered algebraic extension.
* `IsRealClosed.exists_isRoot_of_nonpos_of_nonneg`:
  polynomials over a real closed field satisfy the intermediate value property.
-/

open Polynomial

namespace IsRealClosed

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `X^2 + 1` has no root in an RCF because `-1` is not a square. -/
private lemma not_isSquare_neg_one [IsRealClosed R] : ¬ IsSquare (-1 : R) := by
  intro hsq
  have h : (0 : R) ≤ -1 := (IsRealClosed.nonneg_iff_isSquare (R := R) (x := -1)).mpr hsq
  linarith

private lemma irreducible_X_sq_add_one [IsRealClosed R] :
    Irreducible (X ^ 2 + 1 : R[X]) := by
  have h : (X ^ 2 + 1 : R[X]) = X ^ 2 - C (-1) := by simp [map_neg, map_one, sub_neg_eq_add]
  have hmonic : (X ^ 2 - C (-1 : R)).Monic := monic_X_pow_sub_C _ (by decide)
  have hdeg : (X ^ 2 - C (-1 : R)).natDegree = 2 := natDegree_X_pow_sub_C
  rw [h]
  rw [Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hmonic
        (by rw [hdeg]) (by rw [hdeg]; decide),
      Multiset.eq_zero_iff_forall_notMem]
  intro c hc
  rw [mem_roots hmonic.ne_zero] at hc
  simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_neg_eq_add] at hc
  have hsq : IsSquare (-1 : R) := ⟨c, by linear_combination hc.symm - sq c⟩
  exact not_isSquare_neg_one hsq

/-- `Ri R` is the adjoinment of a square root of `-1` to `R`, i.e. `R[i]`.
It is modelled as `AdjoinRoot (X^2 + 1)`. Marked `abbrev` so instance resolution
fires automatically via `AdjoinRoot`. -/
private abbrev Ri (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] : Type u := AdjoinRoot (X ^ 2 + 1 : R[X])

private instance [IsRealClosed R] : Fact (Irreducible (X ^ 2 + 1 : R[X])) :=
  ⟨irreducible_X_sq_add_one⟩

private noncomputable instance [IsRealClosed R] : Module.Finite R (Ri R) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis (irreducible_X_sq_add_one).ne_zero).basis

section FTA

variable [IsRealClosed R]

/-- **S1.** In a real closed linearly ordered field, a sum of squares is a square. -/
theorem isSquare_of_isSumSq {s : R} (hs : IsSumSq s) : IsSquare s :=
  (IsRealClosed.nonneg_iff_isSquare).mp hs.nonneg

/-- **S2.** No proper odd-degree finite extension of a real closed field. -/
theorem finrank_eq_one_of_odd_finrank
    (K : Type u) [Field K] [Algebra R K] [Module.Finite R K]
    (h : Odd (Module.finrank R K)) : Module.finrank R K = 1 := by
  sorry

/-- **S4.** Every element of `R[i]` is a square. -/
theorem Ri_isSquare (z : Ri R) : IsSquare z := by
  sorry

/-- **S3.** Every degree-2 extension of an RCF is isomorphic to `R[i]`. -/
theorem nonempty_algEquiv_Ri_of_finrank_eq_two
    (K : Type u) [Field K] [Algebra R K] (h : Module.finrank R K = 2) :
    Nonempty (K ≃ₐ[R] Ri R) := by
  sorry

/-- Auxiliary: no proper quadratic extension of `R[i]`. -/
theorem no_quadratic_ext_Ri
    (M : Type u) [Field M] [Algebra (Ri R) M] (h : Module.finrank (Ri R) M = 2) : False := by
  sorry

/-- **S5.** FTA for RCF: every finite extension has degree 1 or 2. -/
theorem finrank_eq_one_or_two_of_finite
    (K : Type u) [Field K] [Algebra R K] [Module.Finite R K] [Nontrivial K] :
    Module.finrank R K = 1 ∨ Module.finrank R K = 2 := by
  sorry

/-- **S6.** An algebraic extension of an RCF is finite. -/
theorem finite_of_isAlgebraic
    (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K] :
    Module.Finite R K := by
  sorry

/-- **S9** (for IVP use). Every monic irreducible polynomial over an RCF is either
linear or is everywhere positive. -/
theorem natDegree_eq_one_or_forall_eval_pos_of_irreducible
    {g : R[X]} (hmonic : g.Monic) (hirred : Irreducible g) :
    g.natDegree = 1 ∨ ∀ x : R, 0 < g.eval x := by
  sorry

/-- **S10.** IVP for polynomials over an RCF. -/
theorem ivp_poly
    {f : R[X]} {a b : R} (hab : a ≤ b) (ha : f.eval a ≤ 0) (hb : 0 ≤ f.eval b) :
    ∃ c ∈ Set.Icc a b, f.IsRoot c := by
  sorry

/-- **S8.** An RCF has no nontrivial ordered algebraic extension. -/
theorem bijective_algebraMap_of_isOrderedAlgebra'
    (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
    [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K] :
    Function.Bijective (algebraMap R K) := by
  sorry

end FTA

end IsRealClosed
