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
  have h := finrank_le_two_of_galois L
  have hpos : 0 < Module.finrank R L := Module.finrank_pos
  interval_cases (Module.finrank R L) <;> simp_all <;> omega

theorem finrank_eq_one_or_two_of_finite
    (K : Type u) [Field K] [Algebra R K] [Module.Finite R K] [Nontrivial K] :
    Module.finrank R K = 1 ∨ Module.finrank R K = 2 := by
  haveI : CharZero R := IsStrictOrderedRing.toCharZero
  haveI : Algebra.IsAlgebraic R K := Algebra.IsAlgebraic.of_finite R K
  -- Step 1: embed K into an algebraic closure of R, then into its normal closure
  let AR : Type u := AlgebraicClosure R
  let φ : K →ₐ[R] AR := IsAlgClosed.lift
  have hφ_inj : Function.Injective φ := φ.toRingHom.injective
  -- L = normalClosure of K over R inside AR
  let L : IntermediateField R AR := normalClosure R K AR
  haveI : FiniteDimensional R L := normalClosure.is_finiteDimensional R K AR
  haveI : IsGalois R L := by
    haveI : Algebra.IsSeparable R K := Algebra.IsAlgebraic.isSeparable_of_perfectField
    exact IsGalois.normalClosure R K AR
  -- The image of K under φ lies inside L
  have hrange_le : φ.fieldRange ≤ L := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    refine IntermediateField.mem_iSup_of_mem φ ?_
    exact ⟨y, rfl⟩
  -- Define ψ : K →ₐ[R] L (Algebra K L via φ and inclusion)
  let ψ : K →ₐ[R] L :=
    { toFun := fun x => ⟨φ x, hrange_le ⟨x, rfl⟩⟩
      map_one' := by ext; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp
      map_mul' := fun _ _ => by ext; simp
      commutes' := fun r => by
        apply Subtype.ext
        show φ (algebraMap R K r) = _
        rw [AlgHom.commutes]; rfl }
  have hψ_inj : Function.Injective ψ := by
    intro a b h
    have : φ a = φ b := by
      apply Subtype.ext_iff.mp
      exact congrArg Subtype.val (congrArg ψ.toFun (by exact h))
    exact hφ_inj this
  -- φ.fieldRange as intermediate field of L
  -- Let K' = range of ψ in L: K' ≃ₐ[R] K via `AlgEquiv.ofInjectiveField`.
  -- Then finrank R K = finrank R K'. And K' is a subfield of L, so its finrank divides finrank R L.
  -- Build the AlgEquiv and transfer finrank
  let eq : K ≃ₐ[R] (ψ : K →ₐ[R] L).range := AlgEquiv.ofInjectiveField ψ
  -- finrank R K = finrank R ψ.range
  have hK_eq_range : Module.finrank R K = Module.finrank R ψ.range :=
    LinearEquiv.finrank_eq eq.toLinearEquiv
  -- ψ.range is a subalgebra of L with Algebra structure, finrank | finrank R L
  have hdvd : Module.finrank R K ∣ Module.finrank R L := by
    rw [hK_eq_range]
    have ht := Module.finrank_mul_finrank R ψ.range L
    exact ⟨_, ht.symm⟩
  -- Now use finrank_one_or_two_of_galois
  rcases finrank_one_or_two_of_galois L with hL1 | hL2
  · rw [hL1] at hdvd
    have : Module.finrank R K = 1 := Nat.dvd_one.mp hdvd
    left; exact this
  · rw [hL2] at hdvd
    have hfin_pos : 0 < Module.finrank R K := Module.finrank_pos
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · left; exact h
    · right; exact h

end IsRealClosed
