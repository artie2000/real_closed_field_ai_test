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

open Polynomial

namespace IsRealClosed

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

section FTA

variable [IsRealClosed R]

/-- **S2.** No proper odd-degree finite extension of a real closed field. -/
theorem finrank_eq_one_of_odd_finrank
    (K : Type u) [Field K] [Algebra R K] [Module.Finite R K]
    (h : Odd (Module.finrank R K)) : Module.finrank R K = 1 := by
  -- Key fact: char zero (as R is strictly ordered field)
  haveI : CharZero R := IsStrictOrderedRing.toCharZero
  -- Module.Finite ⇒ Algebra.IsAlgebraic R K
  haveI : Algebra.IsAlgebraic R K := Algebra.IsAlgebraic.of_finite R K
  -- Char zero field is perfect, so algebraic ⇒ separable
  haveI : Algebra.IsSeparable R K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- Primitive element theorem
  obtain ⟨α, hα⟩ := Field.exists_primitive_element R K
  -- α is integral
  have hint : IsIntegral R α := Algebra.IsIntegral.isIntegral α
  -- finrank R K = finrank R R⟮α⟯ = (minpoly R α).natDegree
  have hfinrank_top : Module.finrank R (⊤ : IntermediateField R K) = Module.finrank R K :=
    IntermediateField.finrank_top'
  rw [← hα] at hfinrank_top
  have heq : Module.finrank R K = (minpoly R α).natDegree := by
    rw [← hfinrank_top, IntermediateField.adjoin.finrank hint]
  -- So minpoly has odd natDegree
  have hodd : Odd (minpoly R α).natDegree := heq ▸ h
  -- So minpoly has a root
  obtain ⟨x, hx⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree hodd
  -- minpoly is irreducible
  have hirr : Irreducible (minpoly R α) := minpoly.irreducible hint
  -- So minpoly has degree 1
  have hdeg : (minpoly R α).degree = 1 := Polynomial.degree_eq_one_of_irreducible_of_root hirr hx
  have hnatdeg : (minpoly R α).natDegree = 1 := Polynomial.natDegree_eq_of_degree_eq_some hdeg
  rw [heq, hnatdeg]

end FTA

end IsRealClosed
