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
  have hirred : Irreducible (X ^ 2 + 1 : R[X]) := irreducible_X_sq_add_one
  have hmonic : (X ^ 2 + 1 : R[X]).Monic := by
    have h : (X ^ 2 + 1 : R[X]) = X ^ 2 - C (-1) := by
      simp [map_neg, map_one, sub_neg_eq_add]
    rw [h]; exact monic_X_pow_sub_C _ (by decide)
  have hdeg2 : (X ^ 2 + 1 : R[X]).natDegree = 2 := by
    have h : (X ^ 2 + 1 : R[X]) = X ^ 2 - C (-1) := by
      simp [map_neg, map_one, sub_neg_eq_add]
    rw [h]; exact natDegree_X_pow_sub_C
  set K := Ri R
  set hm : IsAdjoinRootMonic K (X ^ 2 + 1 : R[X]) :=
    AdjoinRoot.isAdjoinRootMonic (X ^ 2 + 1 : R[X]) hmonic
  -- The fact that i^2 = -1 in Ri R.
  have hroot_sq : hm.root ^ 2 = -1 := by
    have heq : hm.root = AdjoinRoot.root (X ^ 2 + 1 : R[X]) := rfl
    have h0 : aeval (AdjoinRoot.root (X ^ 2 + 1 : R[X])) (X ^ 2 + 1 : R[X]) = 0 :=
      AdjoinRoot.eval₂_root _
    simp [aeval_def, eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at h0
    rw [heq]
    linear_combination h0
  -- Every x : K decomposes uniquely as a + b·i.
  have hrepr : ∀ x : K,
      x = algebraMap R K (hm.coeff x 0) + algebraMap R K (hm.coeff x 1) * hm.root := by
    intro x
    apply hm.ext_elem
    intro i hi
    rw [hdeg2] at hi
    have hroot_coeff : hm.coeff hm.root = Pi.single 1 1 :=
      hm.coeff_root (by rw [hdeg2]; decide)
    have hcoeff_aM_mul_root : ∀ (c : R) (j : ℕ),
        hm.coeff (algebraMap R K c * hm.root) j =
          c • (Pi.single (M := fun _ : ℕ => R) 1 1) j := by
      intro c j
      rw [show algebraMap R K c * hm.root = c • hm.root from by rw [Algebra.smul_def],
          LinearMap.map_smul hm.coeff]
      show c • hm.coeff hm.root j = _
      rw [hroot_coeff]
    interval_cases i
    · rw [LinearMap.map_add hm.coeff, hm.coeff_algebraMap]
      show hm.coeff x 0 = (Pi.single 0 (hm.coeff x 0) : ℕ → R) 0
          + hm.coeff (algebraMap R K (hm.coeff x 1) * hm.root) 0
      rw [hcoeff_aM_mul_root]; simp
    · rw [LinearMap.map_add hm.coeff, hm.coeff_algebraMap]
      show hm.coeff x 1 = (Pi.single 0 (hm.coeff x 0) : ℕ → R) 1
          + hm.coeff (algebraMap R K (hm.coeff x 1) * hm.root) 1
      rw [hcoeff_aM_mul_root]; simp
  -- Key algebraic lemma: (u + v·i)^2 = (u^2 - v^2) + (2·u·v)·i.
  have hsq_expand : ∀ u v : R,
      (algebraMap R K u + algebraMap R K v * hm.root) ^ 2
        = algebraMap R K (u^2 - v^2) + algebraMap R K (2 * u * v) * hm.root := by
    intro u v
    have e1 : (algebraMap R K u + algebraMap R K v * hm.root) ^ 2
            = (algebraMap R K u)^2
                + 2 * (algebraMap R K u) * (algebraMap R K v * hm.root)
                + (algebraMap R K v)^2 * (hm.root ^ 2) := by ring
    rw [e1, hroot_sq]
    have hmid : (2 : K) * algebraMap R K u * (algebraMap R K v * hm.root)
            = algebraMap R K (2 * u * v) * hm.root := by
      have h : (algebraMap R K (2 * u * v) : K) =
          2 * algebraMap R K u * algebraMap R K v := by
        rw [map_mul, map_mul, map_ofNat]
      rw [h]; ring
    rw [hmid]
    have h1 : (algebraMap R K u)^2 = algebraMap R K (u^2) := (map_pow _ _ _).symm
    have h2 : (algebraMap R K v)^2 * (-1 : K) = algebraMap R K (-(v^2)) := by
      rw [← map_pow, map_neg]; ring
    have h3 : algebraMap R K (u^2) + algebraMap R K (-(v^2))
            = algebraMap R K (u^2 - v^2) := by
      rw [← map_add]; ring_nf
    linear_combination h1 + h3 + h2
  set a : R := hm.coeff z 0 with ha_def
  set b : R := hm.coeff z 1 with hb_def
  have hz_eq : z = algebraMap R K a + algebraMap R K b * hm.root := hrepr z
  -- Split on whether b = 0.
  by_cases hb : b = 0
  · -- b = 0 case: z = algebraMap R K a.
    have hz_eq' : z = algebraMap R K a := by
      rw [hz_eq, hb, map_zero, zero_mul, add_zero]
    rcases IsRealClosed.isSquare_or_isSquare_neg a with ha | hna
    · -- a = u^2 for some u.
      obtain ⟨u, hu⟩ := ha
      refine ⟨algebraMap R K u, ?_⟩
      rw [hz_eq', hu, map_mul]
    · -- -a = u^2. Then z = (u·i)^2.
      obtain ⟨u, hu⟩ := hna
      refine ⟨algebraMap R K u * hm.root, ?_⟩
      have : algebraMap R K a = algebraMap R K (-(u * u)) := by
        rw [← hu, neg_neg]
      rw [hz_eq', this, map_neg, map_mul]
      have : (algebraMap R K u * hm.root) * (algebraMap R K u * hm.root)
           = (algebraMap R K u)^2 * hm.root ^ 2 := by ring
      rw [this, hroot_sq]; ring
  · -- b ≠ 0 case.
    have hb2_pos : 0 < b^2 := by positivity
    have ha2_nn : 0 ≤ a^2 := sq_nonneg _
    have hs_pos : 0 < a^2 + b^2 := by linarith
    have hs_nn : 0 ≤ a^2 + b^2 := le_of_lt hs_pos
    -- Let r = sqrt (a^2 + b^2), r > 0.
    have hs_sq : IsSquare (a^2 + b^2) :=
      (IsRealClosed.nonneg_iff_isSquare).mp hs_nn
    obtain ⟨r₀, hr₀⟩ := hs_sq
    set r : R := |r₀|
    have hr_nn : 0 ≤ r := abs_nonneg _
    have hr_sq : r^2 = a^2 + b^2 := by
      rw [sq_abs]; rw [hr₀]; ring
    have hr_pos : 0 < r := by
      rcases lt_or_eq_of_le hr_nn with h | h
      · exact h
      · exfalso
        have : r^2 = 0 := by rw [← h]; ring
        rw [hr_sq] at this; linarith
    -- r^2 ≥ a^2, so r ≥ |a|, so r ≥ a and r ≥ -a.
    have hr_ge_a : r ≥ a := by
      have h1 : r^2 ≥ a^2 := by rw [hr_sq]; linarith
      have h2 : |a| ≤ r := by
        have := abs_le_of_sq_le_sq' h1 hr_nn
        exact this.2
      linarith [le_abs_self a]
    have hr_ge_neg_a : r ≥ -a := by
      have h1 : r^2 ≥ a^2 := by rw [hr_sq]; linarith
      have h2 : |a| ≤ r := by
        have := abs_le_of_sq_le_sq' h1 hr_nn
        exact this.2
      linarith [neg_abs_le a]
    -- (a+r)/2 ≥ 0 and (r-a)/2 ≥ 0.
    have h_ar_nn : 0 ≤ (a + r) / 2 := by linarith
    have h_ra_nn : 0 ≤ (r - a) / 2 := by linarith
    have h_ar_sq : IsSquare ((a + r) / 2) :=
      (IsRealClosed.nonneg_iff_isSquare).mp h_ar_nn
    have h_ra_sq : IsSquare ((r - a) / 2) :=
      (IsRealClosed.nonneg_iff_isSquare).mp h_ra_nn
    obtain ⟨u₀, hu₀⟩ := h_ar_sq
    obtain ⟨v₀, hv₀⟩ := h_ra_sq
    -- Set u := |u₀| and choose sign of v.
    set u := |u₀|
    have hu_nn : 0 ≤ u := abs_nonneg _
    have hu_sq : u^2 = (a + r) / 2 := by rw [sq_abs, hu₀]; ring
    have hv₀_sq : v₀^2 = (r - a) / 2 := by rw [hv₀]; ring
    have hu_pos : 0 < u := by
      rcases lt_or_eq_of_le hu_nn with h | h
      · exact h
      · exfalso
        have : u^2 = 0 := by rw [← h]; ring
        rw [hu_sq] at this
        -- u^2 = (a+r)/2 = 0 means a + r = 0, so r = -a.
        have hr_eq : r = -a := by linarith
        -- But then r^2 = a^2, so a^2 + b^2 = a^2, so b^2 = 0, contradicting b ≠ 0.
        have : r^2 = a^2 := by rw [hr_eq]; ring
        rw [hr_sq] at this
        have : b^2 = 0 := by linarith
        have : b = 0 := by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
          exact this
        exact hb this
    -- Now u^2 - v₀^2 = a.
    have h_uv_a : u^2 - v₀^2 = a := by rw [hu_sq, hv₀_sq]; ring
    -- (2uv₀)^2 = 4 u^2 v₀^2 = 4 · (a+r)/2 · (r-a)/2 = (r+a)(r-a) = r^2 - a^2 = b^2.
    have h_2uv_sq : (2 * u * v₀)^2 = b^2 := by
      have : (2 * u * v₀)^2 = 4 * u^2 * v₀^2 := by ring
      rw [this, hu_sq, hv₀_sq, hr_sq]; ring
    -- So 2 u v₀ = ±b. Pick sign of v accordingly.
    have h_2uv_pm : 2 * u * v₀ = b ∨ 2 * u * v₀ = -b := by
      have h := h_2uv_sq
      have hfactor : (2 * u * v₀ - b) * (2 * u * v₀ + b) = 0 := by linarith [sq b, sq (2*u*v₀)]
      rcases mul_eq_zero.mp hfactor with h1 | h1
      · left; linarith
      · right; linarith
    -- Choose v with the right sign.
    set v : R := if 2 * u * v₀ = b then v₀ else -v₀ with hv_def
    have h_2uv_eq : 2 * u * v = b := by
      rcases h_2uv_pm with heq | heq
      · rw [hv_def, if_pos heq]; exact heq
      · have hne : 2 * u * v₀ ≠ b := by
          intro h'
          rw [h'] at heq
          -- heq : b = -b, so 2b = 0, so b = 0, contradiction.
          have : b = 0 := by linarith
          exact hb this
        rw [hv_def, if_neg hne]; linarith
    have h_u2_v2 : u^2 - v^2 = a := by
      have hv_sq : v^2 = v₀^2 := by
        rw [hv_def]; split_ifs
        · rfl
        · ring
      rw [hv_sq, h_uv_a]
    -- Now (u + v·i)^2 = (u^2 - v^2) + (2·u·v)·i = a + b·i = z.
    refine ⟨algebraMap R K u + algebraMap R K v * hm.root, ?_⟩
    have hsq : (algebraMap R K u + algebraMap R K v * hm.root) *
        (algebraMap R K u + algebraMap R K v * hm.root) =
        (algebraMap R K u + algebraMap R K v * hm.root) ^ 2 := by ring
    rw [hsq, hsq_expand u v]
    rw [hz_eq, h_u2_v2, h_2uv_eq]

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
