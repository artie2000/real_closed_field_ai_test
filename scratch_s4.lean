import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree

open Polynomial

namespace IsRealClosed

universe u
variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

private lemma not_isSquare_neg_one : ¬ IsSquare (-1 : R) := by
  intro hsq
  have h : (0 : R) ≤ -1 := (IsRealClosed.nonneg_iff_isSquare (R := R) (x := -1)).mpr hsq
  linarith

private lemma irreducible_X_sq_add_one :
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

private instance : Fact (Irreducible (X ^ 2 + 1 : R[X])) := ⟨irreducible_X_sq_add_one⟩

private noncomputable instance : Module.Finite R (Ri R) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis irreducible_X_sq_add_one.ne_zero).basis

theorem Ri_isSquare (z : Ri R) : IsSquare z := by
  have hirred : Irreducible (X ^ 2 + 1 : R[X]) := irreducible_X_sq_add_one
  have hmonic : (X ^ 2 + 1 : R[X]).Monic := by
    have h : (X ^ 2 + 1 : R[X]) = X ^ 2 - C (-1 : R) := by simp [sub_neg_eq_add]
    rw [h]; exact monic_X_pow_sub_C _ (by decide)
  have hdeg2 : (X ^ 2 + 1 : R[X]).natDegree = 2 := by
    have h : (X ^ 2 + 1 : R[X]) = X ^ 2 - C (-1 : R) := by simp [sub_neg_eq_add]
    rw [h]; exact natDegree_X_pow_sub_C
  set hm : IsAdjoinRootMonic (Ri R) (X ^ 2 + 1 : R[X]) :=
    AdjoinRoot.isAdjoinRootMonic (X ^ 2 + 1 : R[X]) hmonic
  have hroot_sq : hm.root ^ 2 = -1 := by
    have heq : hm.root = AdjoinRoot.root (X ^ 2 + 1 : R[X]) := rfl
    have h0 : aeval (AdjoinRoot.root (X ^ 2 + 1 : R[X])) (X ^ 2 + 1 : R[X]) = 0 :=
      AdjoinRoot.eval₂_root _
    simp [aeval_def, eval₂_add, eval₂_pow, eval₂_X, eval₂_one,
          add_eq_zero_iff_eq_neg] at h0
    rw [heq]; exact h0
  -- decomposition via power basis
  have hrepr : ∀ x : Ri R,
      x = algebraMap R (Ri R) (hm.coeff x 0) +
          algebraMap R (Ri R) (hm.coeff x 1) * hm.root := by
    intro x
    apply hm.ext_elem
    intro i hi
    rw [hdeg2] at hi
    have hroot_coeff : hm.coeff hm.root = Pi.single 1 1 :=
      hm.coeff_root (by rw [hdeg2]; decide)
    have hcoeff_aM_mul_root : ∀ (c : R) (j : ℕ),
        hm.coeff (algebraMap R (Ri R) c * hm.root) j =
          c • (Pi.single (M := fun _ : ℕ => R) 1 1) j := by
      intro c j
      rw [show algebraMap R (Ri R) c * hm.root = c • hm.root from by rw [Algebra.smul_def],
          LinearMap.map_smul hm.coeff]
      show c • hm.coeff hm.root j = _
      rw [hroot_coeff]
    interval_cases i
    · rw [LinearMap.map_add hm.coeff, hm.coeff_algebraMap]
      show hm.coeff x 0 = (Pi.single 0 (hm.coeff x 0) : ℕ → R) 0
          + hm.coeff (algebraMap R (Ri R) (hm.coeff x 1) * hm.root) 0
      rw [hcoeff_aM_mul_root]; simp
    · rw [LinearMap.map_add hm.coeff, hm.coeff_algebraMap]
      show hm.coeff x 1 = (Pi.single 0 (hm.coeff x 0) : ℕ → R) 1
          + hm.coeff (algebraMap R (Ri R) (hm.coeff x 1) * hm.root) 1
      rw [hcoeff_aM_mul_root]; simp
  sorry

end IsRealClosed
