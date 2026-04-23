import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Polynomial

namespace IsRealClosed

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/- Axiomatize S2, S3, S4 from the main file. -/

axiom irreducible_X_sq_add_one' : Irreducible (X ^ 2 + 1 : R[X])

private instance factIrr : Fact (Irreducible (X ^ 2 + 1 : R[X])) :=
  ⟨irreducible_X_sq_add_one'⟩

private abbrev Ri' (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] : Type u := AdjoinRoot (X ^ 2 + 1 : R[X])

private noncomputable instance : Module.Finite R (Ri' R) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis irreducible_X_sq_add_one'.ne_zero).basis

axiom finrank_eq_one_of_odd_finrank'
    (K : Type u) [Field K] [Algebra R K] [Module.Finite R K]
    (h : Odd (Module.finrank R K)) : Module.finrank R K = 1

axiom nonempty_algEquiv_Ri_of_finrank_eq_two'
    (K : Type u) [Field K] [Algebra R K] (h : Module.finrank R K = 2) :
    Nonempty (K ≃ₐ[R] Ri' R)

axiom no_quadratic_ext_Ri'
    (M : Type u) [Field M] [Algebra (Ri' R) M] (h : Module.finrank (Ri' R) M = 2) : False

/-- Any finite Galois extension of an RCF has degree 1 or 2. -/
private theorem finrank_le_two_of_galois
    (L : Type u) [Field L] [Algebra R L] [FiniteDimensional R L] [IsGalois R L] :
    Module.finrank R L ≤ 2 := by
  sorry

/-- Any finite Galois extension of an RCF has degree 1 or 2. -/
private theorem finrank_one_or_two_of_galois
    (L : Type u) [Field L] [Algebra R L] [FiniteDimensional R L] [IsGalois R L] :
    Module.finrank R L = 1 ∨ Module.finrank R L = 2 := by
  have h : Module.finrank R L ≤ 2 := finrank_le_two_of_galois (R := R) L
  have hpos : 0 < Module.finrank R L := Module.finrank_pos
  interval_cases (Module.finrank R L) <;> simp_all <;> omega

theorem finrank_eq_one_or_two_of_finite
    (K : Type u) [Field K] [Algebra R K] [Module.Finite R K] [Nontrivial K] :
    Module.finrank R K = 1 ∨ Module.finrank R K = 2 := by
  haveI : CharZero R := IsStrictOrderedRing.toCharZero
  haveI : Algebra.IsAlgebraic R K := Algebra.IsAlgebraic.of_finite R K
  -- Step 1: embed K into an algebraic closure of R
  let AR : Type u := AlgebraicClosure R
  let φ : K →ₐ[R] AR := IsAlgClosed.lift
  have hφ_inj : Function.Injective φ := φ.toRingHom.injective
  -- L = normalClosure of K over R inside AR
  let L : IntermediateField R AR := IntermediateField.normalClosure R K AR
  haveI hfin_L : FiniteDimensional R L := normalClosure.is_finiteDimensional R K AR
  haveI hgal_L : IsGalois R L := by
    haveI : Algebra.IsSeparable R K := Algebra.IsAlgebraic.isSeparable_of_perfectField
    exact IsGalois.normalClosure R K AR
  -- The image of K under φ lies inside L, as intermediate field
  have hrange_le : φ.fieldRange ≤ L := AlgHom.fieldRange_le_normalClosure φ
  -- φ.fieldRange is an IntermediateField of AR sitting inside L; as a field it's ≃ₐ[R] K
  let K' : IntermediateField R AR := φ.fieldRange
  have hK'_eq_range : Module.finrank R K = Module.finrank R K' := by
    let eq : K ≃ₐ[R] φ.range := AlgEquiv.ofInjectiveField φ
    have := LinearEquiv.finrank_eq eq.toLinearEquiv
    -- φ.range (as subalgebra) and K' (as intermediate field) have the same carrier
    -- Module.finrank R φ.range = Module.finrank R K'
    have hEq : Module.finrank R φ.range = Module.finrank R K' :=
      IntermediateField.finrank_eq_finrank_subalgebra K' |>.symm
    rw [this, ← hEq]
  -- K' ≤ L. Use restriction of scalars: K' is a subfield of L
  -- Use IntermediateField.relfinrank for the tower: finrank R K' * relfinrank K' L = finrank R L.
  have hdvd : Module.finrank R K ∣ Module.finrank R L := by
    rw [hK'_eq_range]
    -- finrank R K' * finrank K' L = finrank R L (tower law via IntermediateField inclusion)
    -- K' as a field has Algebra K' L (after restricting scalars since K' ≤ L in AR)
    -- Use relfinrank
    have htower : IntermediateField.relfinrank K' L * Module.finrank R K' = Module.finrank R L := by
      -- This is the main tower law. Let me use a different approach
      sorry
    exact ⟨IntermediateField.relfinrank K' L, by rw [mul_comm]; exact htower.symm⟩
  -- Now use finrank_one_or_two_of_galois
  rcases finrank_one_or_two_of_galois L with hL1 | hL2
  · rw [hL1] at hdvd
    left; exact Nat.dvd_one.mp hdvd
  · rw [hL2] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · left; exact h
    · right; exact h

end IsRealClosed
