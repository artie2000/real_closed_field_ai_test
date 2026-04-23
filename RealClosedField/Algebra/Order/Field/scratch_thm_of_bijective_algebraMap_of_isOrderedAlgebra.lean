/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import RealClosedField.Algebra.Order.Algebra
import RealClosedField.Algebra.Order.Field.IsSemireal
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.TFAE

open Polynomial

namespace IsRealClosed

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A polynomial of the form `X^2 - C a` with `a` not a square is irreducible in `R[X]`. -/
private lemma irreducible_X_sq_sub_C_of_not_isSquare
    {a : R} (hsq : ¬ IsSquare a) : Irreducible (X ^ 2 - C a : R[X]) := by
  have hmonic : (X ^ 2 - C a : R[X]).Monic := monic_X_pow_sub_C a (by decide)
  have hdeg : (X ^ 2 - C a : R[X]).natDegree = 2 := natDegree_X_pow_sub_C
  rw [Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hmonic
        (by rw [hdeg]) (by rw [hdeg]; decide)]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro c hc
  rw [mem_roots hmonic.ne_zero] at hc
  simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hc
  exact hsq ⟨c, by linear_combination hc.symm⟩

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Any irreducible polynomial of natDegree > 1 gives a non-surjective algebraMap into its
AdjoinRoot. -/
private lemma algebraMap_not_bijective_of_irreducible_natDegree_pos
    {p : R[X]} (hirred : Irreducible p) (hdeg : 1 < p.natDegree) :
    ¬ Function.Bijective (algebraMap R (AdjoinRoot p)) := by
  intro hbij
  haveI : Fact (Irreducible p) := ⟨hirred⟩
  obtain ⟨r, hr⟩ := hbij.2 (AdjoinRoot.root p)
  have : algebraMap R (AdjoinRoot p) (p.eval r) = 0 := by
    have h₂ : (aeval (AdjoinRoot.root p) p) = 0 := AdjoinRoot.eval₂_root p
    rw [← hr] at h₂
    rw [show algebraMap R (AdjoinRoot p) (p.eval r) = (aeval (algebraMap R (AdjoinRoot p) r) p)
        from (Polynomial.aeval_algebraMap_apply _ _ _).symm]
    exact h₂
  have hroot : p.IsRoot r := hbij.1 (by simpa using this)
  exact hirred.not_isRoot_of_natDegree_ne_one hdeg.ne' hroot

/-- If `K` is an ordered algebraic field extension of `R` and the embedding `R → K` is
bijective, then the power basis of `AdjoinRoot p` being nontrivial is a contradiction
(for irreducible `p` of natDegree > 1). -/
private lemma not_exists_ordered_algebra_of_bijective
    (h : ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
         [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K],
         Function.Bijective (algebraMap R K))
    {p : R[X]} (hirred : Irreducible p) (hdeg : 1 < p.natDegree)
    (hmod : ∃ _ : LinearOrder (AdjoinRoot p),
      IsStrictOrderedRing (AdjoinRoot p) ∧ IsOrderedModule R (AdjoinRoot p)) :
    False := by
  haveI : Fact (Irreducible p) := ⟨hirred⟩
  haveI : Module.Finite R (AdjoinRoot p) := by
    have hne : p ≠ 0 := hirred.ne_zero
    set pb := AdjoinRoot.powerBasis hne
    exact Module.Finite.of_basis pb.basis
  haveI : Algebra.IsAlgebraic R (AdjoinRoot p) := Algebra.IsAlgebraic.of_finite R (AdjoinRoot p)
  obtain ⟨lo, hsr, hom⟩ := hmod
  letI := lo
  haveI := hsr
  haveI := hom
  exact algebraMap_not_bijective_of_irreducible_natDegree_pos hirred hdeg (h (AdjoinRoot p))

/-- If an ordered field `R` has no nontrivial ordered algebraic extension, then it is
real closed. -/
theorem of_bijective_algebraMap_of_isOrderedAlgebra
    (h : ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
         [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K],
         Function.Bijective (algebraMap R K)) :
    IsRealClosed R := by
  refine IsRealClosed.of_linearOrderedField (fun {a} ha => ?_) (fun {f} hodd => ?_)
  · -- PART A: every nonneg element is a square
    by_contra hsq
    have hirred : Irreducible (X ^ 2 - C a : R[X]) :=
      irreducible_X_sq_sub_C_of_not_isSquare hsq
    have hmonic : (X ^ 2 - C a : R[X]).Monic := monic_X_pow_sub_C a (by decide)
    have hdeg2 : (X ^ 2 - C a : R[X]).natDegree = 2 := natDegree_X_pow_sub_C
    set K := AdjoinRoot (X ^ 2 - C a : R[X])
    haveI : Fact (Irreducible (X ^ 2 - C a : R[X])) := ⟨hirred⟩
    -- Use `IsAdjoinRootMonic` for the projection
    set hm : IsAdjoinRootMonic K (X ^ 2 - C a : R[X]) :=
      AdjoinRoot.isAdjoinRootMonic (X ^ 2 - C a : R[X]) hmonic
    -- π is the 0-th coefficient.
    let π : K →ₗ[R] R :=
      { toFun := fun x => hm.coeff x 0
        map_add' := fun x y => by simp
        map_smul' := fun r x => by simp }
    -- Basic properties of π
    have hπ_one : π 1 = 1 := by
      show hm.coeff 1 0 = 1
      rw [hm.coeff_one]
      simp
    have hπ_algebraMap : ∀ c : R, π (algebraMap R K c) = c := by
      intro c
      show hm.coeff (algebraMap R K c) 0 = c
      rw [hm.coeff_algebraMap]
      simp
    have hπ_root : π hm.root = 0 := by
      show hm.coeff hm.root 0 = 0
      rw [hm.coeff_root (by rw [hdeg2]; decide)]
      simp
    -- root^2 = a
    have hroot_sq : hm.root ^ 2 = algebraMap R K a := by
      have hr : (AdjoinRoot.root (X ^ 2 - C a : R[X])) ^ 2 = algebraMap R K a := by
        have h0 : (aeval (AdjoinRoot.root (X ^ 2 - C a : R[X])) (X ^ 2 - C a : R[X])) = 0 :=
          AdjoinRoot.eval₂_root _
        simp [aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h0
        exact h0
      -- hm.root = AdjoinRoot.root ...?
      have heq : hm.root = AdjoinRoot.root (X ^ 2 - C a : R[X]) := rfl
      rw [heq]; exact hr
    -- Each x in K can be written as u + v*root, using coefficients
    have hcoeff_repr : ∀ x : K,
        x = algebraMap R K (hm.coeff x 0) + algebraMap R K (hm.coeff x 1) * hm.root := by
      intro x
      apply hm.ext_elem
      intro i hi
      rw [hdeg2] at hi
      interval_cases i
      · simp [hm.coeff_algebraMap, hm.coeff_root (by rw [hdeg2]; decide)]
      · simp [hm.coeff_algebraMap, hm.coeff_root (by rw [hdeg2]; decide)]
    -- π(x^2) ≥ 0 for all x in K: compute x = u + v*root, x^2 = u^2 + av^2 + 2uv*root
    have hπ_sq : ∀ x : K, 0 ≤ π (x ^ 2) := by
      intro x
      set u := hm.coeff x 0
      set v := hm.coeff x 1
      have hx : x = algebraMap R K u + algebraMap R K v * hm.root := hcoeff_repr x
      have hx_sq : x ^ 2 = algebraMap R K (u^2 + a * v^2)
                          + algebraMap R K (2 * u * v) * hm.root := by
        rw [hx]
        have e1 : (algebraMap R K u + algebraMap R K v * hm.root) ^ 2
                = (algebraMap R K u)^2
                    + 2 * (algebraMap R K u) * (algebraMap R K v * hm.root)
                    + (algebraMap R K v)^2 * (hm.root ^ 2) := by ring
        rw [e1, hroot_sq]
        push_cast
        ring
      rw [hx_sq]
      show hm.coeff _ 0 ≥ 0
      rw [show (algebraMap R K (u^2 + a*v^2) + algebraMap R K (2*u*v) * hm.root : K)
            = algebraMap R K (u^2 + a*v^2) + algebraMap R K (2*u*v) * hm.root from rfl]
      have : hm.coeff (algebraMap R K (u^2 + a*v^2)
                         + algebraMap R K (2*u*v) * hm.root) 0
           = (u^2 + a*v^2) := by
        rw [map_add]
        rw [hm.coeff_algebraMap]
        have : hm.coeff (algebraMap R K (2*u*v) * hm.root) 0 = 0 := by
          -- algebraMap R K (2*u*v) = (2*u*v) • 1 so product = (2*u*v) • root
          rw [show algebraMap R K (2*u*v) * hm.root = (2*u*v) • hm.root from by
              rw [Algebra.smul_def]]
          rw [map_smul]
          show (2*u*v) * hm.coeff hm.root 0 = 0
          rw [hm.coeff_root (by rw [hdeg2]; decide)]
          simp
        rw [this]
        simp
      rw [this]
      positivity
    -- Construct the ordered structure.
    have hord : ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule R K := by
      rw [Field.exists_isOrderedAlgebra_iff_neg_one_notMem_span_nonneg_isSquare]
      intro hc
      have hπ_in_span :
          ∀ s ∈ Submodule.span (Subsemiring.nonneg R) {x : K | IsSquare x}, 0 ≤ π s := by
        intro s hs
        refine Submodule.span_induction
          (mem := ?_)
          (zero := by rw [map_zero])
          (add := fun x y _ _ hx hy => by rw [map_add]; linarith)
          (smul := fun r x _ hx => by
            show 0 ≤ π (r • x)
            rw [map_smul]
            show 0 ≤ (r : R) * π x
            exact mul_nonneg r.2 hx)
          hs
        rintro y ⟨z, hz⟩
        -- z * z = y
        have : y = z ^ 2 := by rw [← hz]; ring
        rw [this]
        exact hπ_sq z
      have h1 : π (-1 : K) = -1 := by rw [map_neg, hπ_one]
      have h2 : 0 ≤ π (-1 : K) := hπ_in_span _ hc
      rw [h1] at h2
      linarith
    have hdeg_gt : 1 < (X ^ 2 - C a : R[X]).natDegree := by rw [hdeg2]; decide
    exact not_exists_ordered_algebra_of_bijective h hirred hdeg_gt hord
  · -- PART B: every odd-degree polynomial has a root
    sorry

end IsRealClosed
