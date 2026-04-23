/-
Scratch file for proving `IsRealClosed.no_quadratic_ext_Ri`.
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

open Polynomial

namespace IsRealClosed

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

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

private abbrev Ri (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] : Type u := AdjoinRoot (X ^ 2 + 1 : R[X])

private instance [IsRealClosed R] : Fact (Irreducible (X ^ 2 + 1 : R[X])) :=
  ⟨irreducible_X_sq_add_one⟩

private noncomputable instance [IsRealClosed R] : Module.Finite R (Ri R) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis (irreducible_X_sq_add_one).ne_zero).basis

section FTA

variable [IsRealClosed R]

/-- Axiomatize the already-proved theorem so this scratch file is short. -/
axiom Ri_isSquare (z : Ri R) : IsSquare z

/-- Auxiliary: no proper quadratic extension of `R[i]`. -/
theorem no_quadratic_ext_Ri
    (M : Type u) [Field M] [Algebra (Ri R) M] (h : Module.finrank (Ri R) M = 2) : False := by
  haveI : CharZero R := IsStrictOrderedRing.toCharZero
  -- M is finite over Ri R since finrank = 2
  haveI : Module.Finite (Ri R) M := Module.finite_of_finrank_eq_succ h
  haveI : Algebra.IsAlgebraic (Ri R) M := Algebra.IsAlgebraic.of_finite (Ri R) M
  -- CharZero lifts through the (injective) algebraMap R → Ri R → M; but we just need
  -- separability for the primitive element theorem over Ri R.
  haveI : CharZero (Ri R) :=
    charZero_of_injective_algebraMap (R := R) (A := Ri R)
      (AdjoinRoot.coe_injective' (f := (X ^ 2 + 1 : R[X])))
  haveI : Algebra.IsSeparable (Ri R) M := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (Ri R) M
  have hint : IsIntegral (Ri R) α := Algebra.IsIntegral.isIntegral α
  have hfinrank_top : Module.finrank (Ri R) (⊤ : IntermediateField (Ri R) M)
      = Module.finrank (Ri R) M := IntermediateField.finrank_top'
  rw [← hα] at hfinrank_top
  -- finrank of simple extension equals natDegree of minpoly
  have hnatdeg : (minpoly (Ri R) α).natDegree = 2 := by
    have : Module.finrank (Ri R) (IntermediateField.adjoin (Ri R) {α})
        = (minpoly (Ri R) α).natDegree := IntermediateField.adjoin.finrank hint
    -- IntermediateField.adjoin (Ri R) {α} = (Ri R)⟮α⟯
    rw [this] at hfinrank_top
    omega
  have hirr : Irreducible (minpoly (Ri R) α) := minpoly.irreducible hint
  have hmonic : (minpoly (Ri R) α).Monic := minpoly.monic hint
  -- Write minpoly = X^2 + C a * X + C b
  set f : (Ri R)[X] := minpoly (Ri R) α with hf
  set a : Ri R := f.coeff 1
  set b : Ri R := f.coeff 0
  have hcoeff2 : f.coeff 2 = 1 := by
    have := hmonic.coeff_natDegree
    rw [hnatdeg] at this
    exact this
  have hab : f = X ^ 2 + C a * X + C b := by
    apply Polynomial.ext
    intro n
    have hrhs_coeff : (X ^ 2 + C a * X + C b : (Ri R)[X]).coeff n =
        (if n = 2 then 1 else 0) + (if n = 1 then a else 0) + (if n = 0 then b else 0) := by
      simp only [coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C, mul_ite, mul_one, mul_zero]
      have h1 : (if 1 = n then a else 0) = if n = 1 then a else 0 := by
        by_cases hn : n = 1 <;> simp [hn, hn.symm]
      have h0 : (if 0 = n then b else 0) = if n = 0 then b else 0 := by
        by_cases hn : n = 0 <;> simp [hn, hn.symm]
      rw [h1, h0]
    rw [hrhs_coeff]
    rcases lt_trichotomy n 2 with hn | rfl | hn
    · interval_cases n
      · simp [b]
      · simp [a]
    · simp [hcoeff2]
    · have hn_gt : n > f.natDegree := by rw [hnatdeg]; exact hn
      rw [coeff_eq_zero_of_natDegree_lt hn_gt]
      have hn2 : n ≠ 2 := Nat.ne_of_gt hn
      have hn1 : n ≠ 1 := by omega
      have hn0 : n ≠ 0 := by omega
      simp [hn2, hn1, hn0]
  -- Ri_isSquare: find s with s^2 = (a/2)^2 - b
  obtain ⟨s, hs⟩ := Ri_isSquare ((a/2)^2 - b)
  -- Define root r = -a/2 + s
  set r : Ri R := -a/2 + s with hr
  -- Verify r is a root of f
  have hroot : f.IsRoot r := by
    simp only [IsRoot, hab, eval_add, eval_pow, eval_X, eval_mul, eval_C]
    have hss : s ^ 2 = (a/2)^2 - b := by rw [sq]; exact hs.symm
    show r ^ 2 + a * r + b = 0
    rw [hr]
    linear_combination hss
  -- Then f has degree 1
  have hdeg1 : f.degree = 1 :=
    Polynomial.degree_eq_one_of_irreducible_of_root hirr hroot
  have hnatdeg1 : f.natDegree = 1 := natDegree_eq_of_degree_eq_some hdeg1
  omega

end FTA

end IsRealClosed
