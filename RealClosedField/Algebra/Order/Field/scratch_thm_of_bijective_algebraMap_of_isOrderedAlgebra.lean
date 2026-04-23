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

/-- Any irreducible polynomial of natDegree > 1 gives a non-surjective algebraMap into its
AdjoinRoot. -/
private lemma algebraMap_not_bijective_of_irreducible_natDegree_pos
    {p : R[X]} (hirred : Irreducible p) (hdeg : 1 < p.natDegree) :
    ¬ Function.Bijective (algebraMap R (AdjoinRoot p)) := by
  intro hbij
  -- root p has minpoly (up to unit) = p, which has natDegree > 1, so is not in the range
  haveI : Fact (Irreducible p) := ⟨hirred⟩
  -- Since algebraMap is bijective, every element is in its range
  have hsurj : Function.Surjective (algebraMap R (AdjoinRoot p)) := hbij.2
  obtain ⟨r, hr⟩ := hsurj (AdjoinRoot.root p)
  -- But evaluating p at r gives 0, contradicting that p has degree > 1 and no linear factor
  have hroot : p.IsRoot r := by
    have h₁ : (AdjoinRoot.mk p) p = 0 := AdjoinRoot.mk_self
    have h₂ : (aeval (AdjoinRoot.root p) p) = 0 := AdjoinRoot.eval₂_root p
    -- Since algebraMap r = root p, r should be a root of p in R
    have : algebraMap R (AdjoinRoot p) (p.eval r) = 0 := by
      rw [← hr] at h₂
      rw [show algebraMap R (AdjoinRoot p) (p.eval r) = (aeval (algebraMap R (AdjoinRoot p) r) p)
          from (Polynomial.aeval_algebraMap_apply _ _ _).symm]
      exact h₂
    have : p.eval r = 0 := hbij.1 (by simpa using this)
    exact this
  -- But p is irreducible of degree > 1, so has no root
  exact hirred.not_isRoot_of_natDegree_ne_one hdeg.ne' hroot

/-- If an ordered field `R` has no nontrivial ordered algebraic extension, then it is
real closed. -/
theorem of_bijective_algebraMap_of_isOrderedAlgebra
    (h : ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
         [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K],
         Function.Bijective (algebraMap R K)) :
    IsRealClosed R := by
  refine IsRealClosed.of_linearOrderedField (fun {a} ha => ?_) (fun {f} hodd => ?_)
  · -- PART A: every nonneg element is a square
    -- Apply part A by contradiction
    by_contra hsq
    have hirred : Irreducible (X ^ 2 - C a : R[X]) :=
      irreducible_X_sq_sub_C_of_not_isSquare hsq
    haveI : Fact (Irreducible (X ^ 2 - C a : R[X])) := ⟨hirred⟩
    set K := AdjoinRoot (X ^ 2 - C a : R[X])
    haveI : Module.Finite R K :=
      (monic_X_pow_sub_C a (by decide : (2 : ℕ) ≠ 0)).finite_adjoinRoot
    haveI : Algebra.IsAlgebraic R K := Algebra.IsAlgebraic.of_finite R K
    -- Define the linear functional π : K → R as the 0th coordinate in the power basis {1, root}.
    set hmonic : (X ^ 2 - C a : R[X]).Monic := monic_X_pow_sub_C a (by decide) with hmonic_def
    set pb : PowerBasis R K := AdjoinRoot.powerBasis' hmonic with hpb_def
    have hdim : pb.dim = 2 := by simp [pb, AdjoinRoot.powerBasis', natDegree_X_pow_sub_C]
    let i0 : Fin pb.dim := ⟨0, by rw [hdim]; decide⟩
    let i1 : Fin pb.dim := ⟨1, by rw [hdim]; decide⟩
    let π : K →ₗ[R] R := pb.basis.coord i0
    -- Key lemma: π((u • 1 + v • root) ^ 2) = u^2 + a * v^2 ≥ 0
    -- Since every element of K is u • pb.basis i0 + v • pb.basis i1, and root^2 = a.
    have hroot_sq : (AdjoinRoot.root (X ^ 2 - C a : R[X])) ^ 2
                    = algebraMap R K a := by
      have : (aeval (AdjoinRoot.root (X ^ 2 - C a : R[X])) (X ^ 2 - C a : R[X])) = 0 :=
        AdjoinRoot.eval₂_root _
      simp [aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at this
      exact this
    have hbasis_i0 : pb.basis i0 = (1 : K) := by
      have := AdjoinRoot.powerBasis'_basis hmonic
      simp [pb, AdjoinRoot.powerBasis', i0]
      rfl
    have hbasis_i1 : pb.basis i1 = AdjoinRoot.root (X ^ 2 - C a : R[X]) := by
      simp [pb, AdjoinRoot.powerBasis', i1]
      rfl
    -- π(1) = 1
    have hπ_one : π 1 = 1 := by
      rw [show (1 : K) = pb.basis i0 from hbasis_i0.symm]
      exact Basis.coord_apply_self pb.basis i0
    -- For any x ∈ K, π(x^2) ≥ 0
    have hπ_sq : ∀ x : K, 0 ≤ π (x ^ 2) := by
      intro x
      -- Write x in basis as u • 1 + v • root
      have := pb.basis.total_repr x
      -- Get coefficients
      set u := pb.basis.repr x i0
      set v := pb.basis.repr x i1
      have hbasis_i0 : pb.basis i0 = (1 : K) := by simp [pb, AdjoinRoot.powerBasis', i0]
      have hbasis_i1 : pb.basis i1 = AdjoinRoot.root (X ^ 2 - C a : R[X]) := by
        simp [pb, AdjoinRoot.powerBasis', i1]
      have hx_eq : x = u • (1 : K) + v • AdjoinRoot.root (X ^ 2 - C a : R[X]) := by
        have := pb.basis.linearCombination_repr x
        rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by intros; simp)] at this
        rw [show (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} from ?_] at this
        · simp at this
          have hi01 : i0 ≠ i1 := by simp [i0, i1]; decide
          rw [Finset.sum_insert (by simp [hi01]), Finset.sum_singleton] at this
          rw [← hbasis_i0, ← hbasis_i1]; exact this.symm
        · ext j
          simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
          have : j.val < 2 := by rw [← hdim]; exact j.isLt
          interval_cases j.val
          · left; apply Fin.ext; rfl
          · right; apply Fin.ext; rfl
      -- Now compute x^2
      have hx_sq : x ^ 2 = algebraMap R K (u ^ 2 + a * v ^ 2)
                          + (2 * u * v) • AdjoinRoot.root (X ^ 2 - C a : R[X]) := by
        rw [hx_eq]
        have h_one : algebraMap R K 1 = 1 := map_one _
        have : (u • (1 : K) + v • AdjoinRoot.root (X ^ 2 - C a : R[X])) ^ 2
              = (algebraMap R K u) ^ 2 + 2 * (algebraMap R K u)
                  * (algebraMap R K v * AdjoinRoot.root (X ^ 2 - C a : R[X]))
                + (algebraMap R K v) ^ 2 * (AdjoinRoot.root (X ^ 2 - C a : R[X])) ^ 2 := by
          rw [Algebra.smul_def, Algebra.smul_def]
          ring
        rw [this, hroot_sq]
        rw [show (algebraMap R K v) ^ 2 * algebraMap R K a = algebraMap R K (v ^ 2 * a) by
            rw [map_mul, map_pow]]
        rw [show (algebraMap R K u) ^ 2 = algebraMap R K (u ^ 2) by rw [map_pow]]
        rw [show algebraMap R K (u ^ 2) + algebraMap R K (v ^ 2 * a) = algebraMap R K (u^2 + a*v^2)
            by rw [map_add]; ring]
        rw [show (2 * u * v : R) • AdjoinRoot.root (X ^ 2 - C a : R[X])
              = 2 * (algebraMap R K u) * (algebraMap R K v *
                   AdjoinRoot.root (X ^ 2 - C a : R[X])) by
            rw [Algebra.smul_def]; rw [map_mul]; push_cast; ring]
      rw [hx_sq]
      -- π(algebraMap R K c + (2uv) • root) = c  (since root is the 2nd basis element)
      have hπ_algMap : ∀ c : R, π (algebraMap R K c) = c := by
        intro c
        rw [Algebra.algebraMap_eq_smul_one]
        show pb.basis.coord i0 (c • (1 : K)) = c
        rw [show (1 : K) = pb.basis i0 from hbasis_i0.symm]
        rw [map_smul]
        rw [pb.basis.coord_apply_self]
        simp
      have hπ_root : π (AdjoinRoot.root (X ^ 2 - C a : R[X])) = 0 := by
        rw [show AdjoinRoot.root (X ^ 2 - C a : R[X]) = pb.basis i1 from hbasis_i1.symm]
        show pb.basis.coord i0 (pb.basis i1) = 0
        rw [pb.basis.coord_apply_ne]
        simp [i0, i1]; decide
      rw [map_add, hπ_algMap, map_smul]
      show u^2 + a * v^2 + (2 * u * v) * π _ ≥ 0
      rw [hπ_root]
      simp
      positivity
    -- Now show -1 ∉ span
    have : (∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule R K) := by
      rw [Field.exists_isOrderedAlgebra_iff_neg_one_notMem_span_nonneg_isSquare]
      intro hc
      -- hc : -1 ∈ Submodule.span (Subsemiring.nonneg R) {x | IsSquare x}
      -- Apply π: π(-1) = -1 < 0, but π(s) ≥ 0 for any s in the span.
      have hπ_in_span : ∀ s ∈ Submodule.span (Subsemiring.nonneg R) {x : K | IsSquare x},
                        0 ≤ π s := by
        intro s hs
        refine Submodule.span_induction
          (mem := fun x ⟨y, hy⟩ => hy ▸ ?_)
          (zero := by rw [map_zero])
          (add := fun x y _ _ hx hy => by rw [map_add]; linarith)
          (smul := fun a x _ hx => by
            rw [LinearMap.map_smul]
            show 0 ≤ (a : R) * π x
            exact mul_nonneg a.2 hx)
          hs
        exact hπ_sq y
      have h1 : π (-1 : K) = -1 := by rw [map_neg, hπ_one]
      have h2 : 0 ≤ π (-1 : K) := hπ_in_span _ hc
      rw [h1] at h2
      linarith
    obtain ⟨_, _, _⟩ := this
    have hdeg : (1 : ℕ) < (X ^ 2 - C a : R[X]).natDegree := by
      rw [natDegree_X_pow_sub_C]; decide
    exact algebraMap_not_bijective_of_irreducible_natDegree_pos hirred hdeg (h K)
  · -- PART B: every odd-degree polynomial has a root
    sorry

end IsRealClosed
