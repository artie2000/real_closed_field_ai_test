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
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Relrank
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Trace

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
  haveI : CharZero R := IsStrictOrderedRing.toCharZero
  haveI : Algebra.IsAlgebraic R K := Algebra.IsAlgebraic.of_finite R K
  haveI : Algebra.IsSeparable R K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨α, hα⟩ := Field.exists_primitive_element R K
  have hint : IsIntegral R α := Algebra.IsIntegral.isIntegral α
  have hfinrank_top : Module.finrank R (⊤ : IntermediateField R K) = Module.finrank R K :=
    IntermediateField.finrank_top'
  rw [← hα] at hfinrank_top
  have heq : Module.finrank R K = (minpoly R α).natDegree := by
    rw [← hfinrank_top, IntermediateField.adjoin.finrank hint]
  have hodd : Odd (minpoly R α).natDegree := heq ▸ h
  obtain ⟨x, hx⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree hodd
  have hirr : Irreducible (minpoly R α) := minpoly.irreducible hint
  have hdeg : (minpoly R α).degree = 1 := Polynomial.degree_eq_one_of_irreducible_of_root hirr hx
  have hnatdeg : (minpoly R α).natDegree = 1 := Polynomial.natDegree_eq_of_degree_eq_some hdeg
  rw [heq, hnatdeg]

/-- **S4.** Every element of `R[i]` is a square. -/
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
  set a : R := hm.coeff z 0
  set b : R := hm.coeff z 1
  have hz : z = algebraMap R (Ri R) a + algebraMap R (Ri R) b * hm.root := hrepr z
  have hnn : (0 : R) ≤ a ^ 2 + b ^ 2 := by positivity
  obtain ⟨r, hr⟩ :=
    (IsRealClosed.nonneg_iff_isSquare (R := R) (x := a ^ 2 + b ^ 2)).mp hnn
  set r' : R := |r|
  have hr'_nn : 0 ≤ r' := abs_nonneg r
  have hr'_sq : r' * r' = a ^ 2 + b ^ 2 := by
    rw [show r' * r' = r * r from by rcases abs_choice r with h | h <;>
      rw [show r' = _ from h] <;> ring]
    exact hr.symm
  have hr'_ge_abs_a : |a| ≤ r' := by
    have : a ^ 2 ≤ r' ^ 2 := by
      rw [show r' ^ 2 = r' * r' from sq r', hr'_sq]
      nlinarith [sq_nonneg b]
    have habs_a : 0 ≤ |a| := abs_nonneg a
    nlinarith [sq_abs a, sq_nonneg (|a| - r'), sq_nonneg (|a| + r')]
  have hr'_ge_a : a ≤ r' := le_trans (le_abs_self a) hr'_ge_abs_a
  have hr'_ge_neg_a : -a ≤ r' := le_trans (neg_le_abs a) hr'_ge_abs_a
  by_cases hb0 : b = 0
  · rw [hb0] at hz
    simp only [map_zero, zero_mul, add_zero] at hz
    by_cases ha_nn : 0 ≤ a
    · obtain ⟨s, hs⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R) (x := a)).mp ha_nn
      refine ⟨algebraMap R (Ri R) s, ?_⟩
      rw [hz, hs]; simp [map_mul]
    · push_neg at ha_nn
      have hna_nn : 0 ≤ -a := by linarith
      obtain ⟨s, hs⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R) (x := -a)).mp hna_nn
      refine ⟨algebraMap R (Ri R) s * hm.root, ?_⟩
      have step1 :
          (algebraMap R (Ri R) s * hm.root) * (algebraMap R (Ri R) s * hm.root)
          = (algebraMap R (Ri R) s * algebraMap R (Ri R) s) * (hm.root * hm.root) := by
        ring
      have hmul : algebraMap R (Ri R) s * algebraMap R (Ri R) s
                    = algebraMap R (Ri R) (-a) := by
        rw [← map_mul, ← hs]
      have hii : hm.root * hm.root = -1 := by rw [← sq]; exact hroot_sq
      rw [step1, hmul, hii, hz]
      rw [show algebraMap R (Ri R) (-a) * (-1 : Ri R) = algebraMap R (Ri R) a from by
        rw [map_neg]; ring]
  · have hb2_pos : 0 < b ^ 2 := by positivity
    have hr'2_pos : 0 < r' ^ 2 := by
      rw [show r' ^ 2 = r' * r' from sq r', hr'_sq]; nlinarith [sq_nonneg a]
    have hr'_pos : 0 < r' := by
      rcases lt_or_eq_of_le hr'_nn with h | h
      · exact h
      · exfalso; rw [← h] at hr'2_pos; norm_num at hr'2_pos
    have hapr_pos : 0 < a + r' := by
      by_contra h
      push_neg at h
      have happ_le : a + r' ≤ 0 := h
      have : -a = r' := by linarith [hr'_ge_neg_a, happ_le]
      have ha_sq : a ^ 2 = r' ^ 2 := by nlinarith
      have : b ^ 2 = 0 := by
        have := hr'_sq
        have hr'sq : r' ^ 2 = a ^ 2 + b ^ 2 := by rw [sq]; exact this
        linarith
      have : b = 0 := pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp this
      exact hb0 this
    have hu_nn : 0 ≤ (a + r') / 2 := by linarith
    obtain ⟨u, hu⟩ :=
      (IsRealClosed.nonneg_iff_isSquare (R := R) (x := (a + r') / 2)).mp hu_nn
    set u' : R := |u|
    have hu'_nn : 0 ≤ u' := abs_nonneg u
    have hu'_sq : u' * u' = (a + r') / 2 := by
      rw [show u' * u' = u * u from by rcases abs_choice u with h | h <;>
        rw [show u' = _ from h] <;> ring]
      exact hu.symm
    have hu'_pos : 0 < u' := by
      rcases lt_or_eq_of_le hu'_nn with h | h
      · exact h
      · exfalso; rw [← h] at hu'_sq; linarith
    have hu'_ne : u' ≠ 0 := ne_of_gt hu'_pos
    let v : R := b / (2 * u')
    have h2u'_ne : (2 * u' : R) ≠ 0 := by positivity
    have hv_rel : 2 * u' * v = b := by
      show 2 * u' * (b / (2 * u')) = b
      field_simp
    have hu'2 : u' ^ 2 = (a + r') / 2 := by rw [sq]; exact hu'_sq
    have hv2 : v ^ 2 = b ^ 2 / (4 * u' ^ 2) := by
      show (b / (2 * u')) ^ 2 = b ^ 2 / (4 * u' ^ 2)
      field_simp; ring
    have hu'2_sub_v2 : u' ^ 2 - v ^ 2 = a := by
      have hr'_sq' : r' ^ 2 = a ^ 2 + b ^ 2 := by rw [sq]; exact hr'_sq
      have hapr_ne : (a + r' : R) ≠ 0 := ne_of_gt hapr_pos
      have h4u'2 : 4 * u' ^ 2 = 2 * (a + r') := by rw [hu'2]; ring
      have hv2' : v ^ 2 = b ^ 2 / (2 * (a + r')) := by rw [hv2, h4u'2]
      have h2ne : (2 * (a + r') : R) ≠ 0 := by
        exact mul_ne_zero (by norm_num) hapr_ne
      rw [hu'2, hv2']
      rw [div_sub_div _ _ (by norm_num : (2:R) ≠ 0) h2ne]
      rw [div_eq_iff (mul_ne_zero (by norm_num : (2:R) ≠ 0) h2ne)]
      linear_combination 2 * hr'_sq'
    refine ⟨algebraMap R (Ri R) u' + algebraMap R (Ri R) v * hm.root, ?_⟩
    rw [hz]
    set i : Ri R := hm.root
    set A : Ri R := algebraMap R (Ri R) u'
    set B : Ri R := algebraMap R (Ri R) v
    have hi2 : i * i = -1 := by
      show hm.root * hm.root = -1
      rw [← sq]; exact hroot_sq
    have hsq :
        (A + B * i) * (A + B * i)
        = (A * A - B * B) + (A * B + A * B) * i := by
      have : B * i * (B * i) = -(B * B) := by
        calc B * i * (B * i) = (B * B) * (i * i) := by ring
          _ = (B * B) * (-1) := by rw [hi2]
          _ = -(B * B) := by ring
      calc (A + B * i) * (A + B * i)
          = A * A + A * (B * i) + B * i * A + B * i * (B * i) := by ring
        _ = A * A + A * B * i + A * B * i + (-(B * B)) := by rw [this]; ring
        _ = (A * A - B * B) + (A * B + A * B) * i := by ring
    rw [hsq]
    have hAA : A * A = algebraMap R (Ri R) (u' * u') := by
      show algebraMap R (Ri R) u' * algebraMap R (Ri R) u' = _
      rw [← map_mul]
    have hBB : B * B = algebraMap R (Ri R) (v * v) := by
      show algebraMap R (Ri R) v * algebraMap R (Ri R) v = _
      rw [← map_mul]
    have hAB : A * B + A * B = algebraMap R (Ri R) (2 * u' * v) := by
      show algebraMap R (Ri R) u' * algebraMap R (Ri R) v
          + algebraMap R (Ri R) u' * algebraMap R (Ri R) v = _
      rw [← map_mul, ← map_add]
      congr 1; ring
    rw [hAA, hBB, hAB, ← map_sub]
    have heq_a : u' * u' - v * v = a := by
      have h1 : u' * u' = u' ^ 2 := by rw [sq]
      have h2 : v * v = v ^ 2 := by rw [sq]
      rw [h1, h2]; exact hu'2_sub_v2
    rw [heq_a, hv_rel]

/-- **S3.** Every degree-2 extension of an RCF is isomorphic to `R[i]`. -/
theorem nonempty_algEquiv_Ri_of_finrank_eq_two
    (K : Type u) [Field K] [Algebra R K] (h : Module.finrank R K = 2) :
    Nonempty (K ≃ₐ[R] Ri R) := by
  haveI : CharZero R := IsStrictOrderedRing.toCharZero
  haveI : Module.Finite R K := Module.finite_of_finrank_eq_succ h
  haveI : Algebra.IsAlgebraic R K := Algebra.IsAlgebraic.of_finite R K
  haveI : Algebra.IsSeparable R K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨α, hα⟩ := Field.exists_primitive_element R K
  have hint : IsIntegral R α := Algebra.IsIntegral.isIntegral α
  have hfinrank_top : Module.finrank R (⊤ : IntermediateField R K) = Module.finrank R K :=
    IntermediateField.finrank_top'
  rw [← hα] at hfinrank_top
  have hnatdeg : (minpoly R α).natDegree = 2 := by
    have : Module.finrank R (IntermediateField.adjoin R {α})
        = (minpoly R α).natDegree := IntermediateField.adjoin.finrank hint
    rw [this] at hfinrank_top
    omega
  have hmonic : (minpoly R α).Monic := minpoly.monic hint
  set f : R[X] := minpoly R α with hf
  set a : R := f.coeff 1
  set b : R := f.coeff 0
  have hcoeff2 : f.coeff 2 = 1 := by
    have := hmonic.coeff_natDegree; rw [hnatdeg] at this; exact this
  have hab : f = X ^ 2 + C a * X + C b := by
    apply Polynomial.ext
    intro n
    rw [coeff_add, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
    rcases lt_trichotomy n 2 with hn | rfl | hn
    · interval_cases n
      · show b = _; simp
      · show a = _; simp
    · show f.coeff 2 = _; rw [hcoeff2]; simp
    · have hn_gt : n > f.natDegree := by rw [hnatdeg]; exact hn
      rw [coeff_eq_zero_of_natDegree_lt hn_gt]
      have hn2 : n ≠ 2 := Nat.ne_of_gt hn
      have hn1 : (1 : ℕ) ≠ n := by omega
      have hn0 : n ≠ 0 := by omega
      simp [hn2, hn1, hn0]
  have haeval : α ^ 2 + algebraMap R K a * α + algebraMap R K b = 0 := by
    have h0 : aeval α f = 0 := minpoly.aeval R α
    rw [hab] at h0
    simpa [aeval_def, eval₂_add, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C] using h0
  set β : K := α + algebraMap R K (a / 2) with hβdef
  set δ : R := (a / 2) ^ 2 - b with hδdef
  have hβsq : β ^ 2 = algebraMap R K δ := by
    have haK : algebraMap R K δ = algebraMap R K (a/2) ^ 2 - algebraMap R K b := by
      rw [hδdef, map_sub, map_pow]
    have ha_eq : algebraMap R K a = 2 * algebraMap R K (a/2) := by
      rw [← map_ofNat (algebraMap R K) 2, ← map_mul]
      congr 1; ring
    rw [haK, hβdef]
    have hb_eq : algebraMap R K b = -(α ^ 2 + algebraMap R K a * α) := by
      linear_combination haeval
    rw [hb_eq, ha_eq]; ring
  have hdelta_neg : δ < 0 := by
    by_contra hnn
    obtain ⟨c, hc⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R) (x := δ)).mp (not_lt.mp hnn)
    have hβsq' : β ^ 2 = (algebraMap R K c) ^ 2 := by
      rw [hβsq, show δ = c * c from hc, sq, map_mul]
    have hprod : (β - algebraMap R K c) * (β + algebraMap R K c) = 0 := by
      have : β ^ 2 - (algebraMap R K c) ^ 2 = 0 := by rw [hβsq']; ring
      linear_combination this
    have hα_range : α ∈ (algebraMap R K).range := by
      rcases mul_eq_zero.mp hprod with h1 | h1
      · refine ⟨c - a / 2, ?_⟩
        have hβeq : β = algebraMap R K c := by linear_combination h1
        have : α = algebraMap R K c - algebraMap R K (a/2) := by
          have hh := hβeq; rw [hβdef] at hh; linear_combination hh
        rw [this, map_sub]
      · refine ⟨-c - a/2, ?_⟩
        have hβeq : β = -algebraMap R K c := by linear_combination h1
        have : α = -algebraMap R K c - algebraMap R K (a/2) := by
          have hh := hβeq; rw [hβdef] at hh; linear_combination hh
        rw [this, map_sub, map_neg]
    have hdeg1 : (minpoly R α).natDegree = 1 := (minpoly.natDegree_eq_one_iff).mpr hα_range
    rw [hnatdeg] at hdeg1
    exact absurd hdeg1 (by norm_num)
  have hnegδ_pos : 0 < -δ := by linarith
  obtain ⟨c, hc⟩ :=
    (IsRealClosed.nonneg_iff_isSquare (R := R) (x := -δ)).mp hnegδ_pos.le
  have hcne : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; linarith
  have hcsq_neg : c ^ 2 = -δ := by rw [sq]; exact hc.symm
  set cK : K := algebraMap R K c with hcKdef
  have hcK_ne : cK ≠ 0 := (map_ne_zero (algebraMap R K)).mpr hcne
  set i' : K := β * cK⁻¹ with hi'def
  have hi'sq : i' ^ 2 = -1 := by
    rw [hi'def, mul_pow, hβsq]
    rw [show (cK⁻¹) ^ 2 = (cK ^ 2)⁻¹ from by rw [inv_pow]]
    rw [show cK ^ 2 = algebraMap R K (-δ) from by rw [hcKdef, ← map_pow, hcsq_neg]]
    rw [← map_inv₀, ← map_mul]
    have hδne : δ ≠ 0 := ne_of_lt hdelta_neg
    have h_eq : δ * (-δ)⁻¹ = -1 := by field_simp
    rw [h_eq]; simp
  have h_eval : (X ^ 2 + 1 : R[X]).eval₂ (algebraMap R K) i' = 0 := by
    simp [eval₂_add, eval₂_pow, eval₂_X, eval₂_one, hi'sq]
  set φ : Ri R →ₐ[R] K :=
    AdjoinRoot.liftAlgHom (X ^ 2 + 1 : R[X]) (Algebra.ofId R K) i' h_eval
  have hφ_inj : Function.Injective φ := φ.toRingHom.injective
  have hfinrank_Ri : Module.finrank R (Ri R) = 2 := by
    have hne : (X ^ 2 + 1 : R[X]) ≠ 0 := irreducible_X_sq_add_one.ne_zero
    have hdeg : (X ^ 2 + 1 : R[X]).natDegree = 2 := by
      have heq : (X ^ 2 + 1 : R[X]) = X ^ 2 - C (-1 : R) := by simp [sub_neg_eq_add]
      rw [heq]; exact natDegree_X_pow_sub_C
    have := (AdjoinRoot.powerBasis hne).finrank
    rw [AdjoinRoot.powerBasis_dim hne] at this
    rw [this, hdeg]
  have heq_rank : Module.finrank R K = Module.finrank R (Ri R) := by rw [h, hfinrank_Ri]
  have hφ_surj : Function.Surjective φ := by
    have : Function.Injective φ.toLinearMap := hφ_inj
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq_rank.symm).mp this
  exact ⟨(AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩).symm⟩

/-- Auxiliary: no proper quadratic extension of `R[i]`. -/
theorem no_quadratic_ext_Ri
    (M : Type u) [Field M] [Algebra (Ri R) M] (h : Module.finrank (Ri R) M = 2) : False := by
  haveI : CharZero R := IsStrictOrderedRing.toCharZero
  haveI : Module.Finite (Ri R) M := Module.finite_of_finrank_eq_succ h
  haveI : Algebra.IsAlgebraic (Ri R) M := Algebra.IsAlgebraic.of_finite (Ri R) M
  haveI : CharZero (Ri R) :=
    charZero_of_injective_algebraMap (R := R) (A := Ri R)
      (AdjoinRoot.coe_injective' (f := (X ^ 2 + 1 : R[X])))
  haveI : Algebra.IsSeparable (Ri R) M := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (Ri R) M
  have hint : IsIntegral (Ri R) α := Algebra.IsIntegral.isIntegral α
  have hfinrank_top : Module.finrank (Ri R) (⊤ : IntermediateField (Ri R) M)
      = Module.finrank (Ri R) M := IntermediateField.finrank_top'
  rw [← hα] at hfinrank_top
  have hnatdeg : (minpoly (Ri R) α).natDegree = 2 := by
    have : Module.finrank (Ri R) (IntermediateField.adjoin (Ri R) {α})
        = (minpoly (Ri R) α).natDegree := IntermediateField.adjoin.finrank hint
    rw [this] at hfinrank_top
    omega
  have hirr : Irreducible (minpoly (Ri R) α) := minpoly.irreducible hint
  have hmonic : (minpoly (Ri R) α).Monic := minpoly.monic hint
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
    rw [coeff_add, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
    rcases lt_trichotomy n 2 with hn | rfl | hn
    · interval_cases n
      · show b = _
        simp
      · show a = _
        simp
    · show f.coeff 2 = _
      rw [hcoeff2]; simp
    · have hn_gt : n > f.natDegree := by rw [hnatdeg]; exact hn
      rw [coeff_eq_zero_of_natDegree_lt hn_gt]
      have hn2 : n ≠ 2 := Nat.ne_of_gt hn
      have hn1 : (1 : ℕ) ≠ n := by omega
      have hn0 : n ≠ 0 := by omega
      simp [hn2, hn1, hn0]
  obtain ⟨s, hs⟩ := Ri_isSquare ((a/2)^2 - b)
  set r : Ri R := -a/2 + s with hr
  have hroot : f.IsRoot r := by
    simp only [IsRoot, hab, eval_add, eval_pow, eval_X, eval_mul, eval_C]
    have hss : s ^ 2 = (a/2)^2 - b := by rw [sq]; exact hs.symm
    show r ^ 2 + a * r + b = 0
    rw [hr]
    linear_combination hss
  have hdeg1 : f.degree = 1 :=
    Polynomial.degree_eq_one_of_irreducible_of_root hirr hroot
  have hnatdeg1 : f.natDegree = 1 := natDegree_eq_of_degree_eq_some hdeg1
  omega

/-- Key lemma: any finite Galois extension of an RCF has order a power of 2. -/
private theorem finrank_pow_two_of_galois
    (L : Type u) [Field L] [Algebra R L] [FiniteDimensional R L] [IsGalois R L] :
    ∃ k : ℕ, Module.finrank R L = 2 ^ k := by
  haveI : Finite (L ≃ₐ[R] L) := by
    have h : Nat.card (L ≃ₐ[R] L) = Module.finrank R L := IsGalois.card_aut_eq_finrank R L
    have hpos : 0 < Module.finrank R L := Module.finrank_pos
    rw [← h] at hpos
    exact Nat.finite_of_card_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  set G := L ≃ₐ[R] L with hGdef
  set n := Nat.card G with hndef
  have hn_eq : n = Module.finrank R L := IsGalois.card_aut_eq_finrank R L
  have hn_pos : 0 < n := by rw [hn_eq]; exact Module.finrank_pos
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn_pos
  set k := Nat.factorization n 2 with hkdef
  set q := n / 2 ^ k with hqdef
  have h2_prime : Nat.Prime 2 := Nat.prime_two
  haveI : Fact (Nat.Prime 2) := ⟨h2_prime⟩
  have hn_split : n = 2 ^ k * q := by
    rw [hqdef, hkdef]; exact (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
  have hq_odd : ¬ 2 ∣ q := Nat.not_dvd_ordCompl h2_prime hn_ne
  obtain ⟨H, hH_card⟩ : ∃ H : Subgroup G, Nat.card H = 2 ^ k := by
    refine Sylow.exists_subgroup_card_pow_prime 2 ?_
    exact ⟨q, hn_split⟩
  let M : IntermediateField R L := IntermediateField.fixedField H
  have hM_finrank_L : Module.finrank M L = 2 ^ k := by
    rw [← hH_card]; exact IntermediateField.finrank_fixedField_eq_card H
  have htower : Module.finrank R M * Module.finrank M L = Module.finrank R L :=
    Module.finrank_mul_finrank R M L
  have h2pos : (0 : ℕ) < 2 ^ k := Nat.pos_of_ne_zero (pow_ne_zero k (by decide))
  have hq_pos : 0 < q := by
    rw [hqdef]
    have h1 : 2^k ∣ n := Nat.ordProj_dvd n 2
    exact Nat.div_pos (Nat.le_of_dvd hn_pos h1) h2pos
  have hM_finrank : Module.finrank R M = q := by
    rw [hM_finrank_L] at htower
    rw [← hn_eq, hn_split] at htower
    have h : Module.finrank R M * 2^k = q * 2^k := by rw [mul_comm q]; linarith [htower]
    exact Nat.eq_of_mul_eq_mul_right h2pos h
  haveI : FiniteDimensional R M := inferInstance
  have hq_1 : q = 1 := by
    have hOdd : Odd q := by
      rcases Nat.even_or_odd q with he | ho
      · exact absurd he.two_dvd hq_odd
      · exact ho
    have hfM := hM_finrank
    rw [← hfM] at hOdd
    have := finrank_eq_one_of_odd_finrank M hOdd
    rw [hM_finrank] at this
    exact this
  have hn_pow : n = 2 ^ k := by rw [hn_split, hq_1, mul_one]
  refine ⟨k, ?_⟩
  rw [← hn_eq]; exact hn_pow

/-- Any finite Galois extension of an RCF has degree at most 2. -/
private theorem finrank_le_two_of_galois
    (L : Type u) [Field L] [Algebra R L] [FiniteDimensional R L] [IsGalois R L] :
    Module.finrank R L ≤ 2 := by
  obtain ⟨k, hkeq⟩ := finrank_pow_two_of_galois (R := R) L
  rw [hkeq]
  by_contra hcontra
  push_neg at hcontra
  have hk_ge2 : 2 ≤ k := by
    by_contra h
    push_neg at h
    interval_cases k <;> omega
  haveI : Finite (L ≃ₐ[R] L) := by
    have h : Nat.card (L ≃ₐ[R] L) = Module.finrank R L := IsGalois.card_aut_eq_finrank R L
    have hpos : 0 < Module.finrank R L := Module.finrank_pos
    rw [← h] at hpos
    exact Nat.finite_of_card_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGcard : Nat.card (L ≃ₐ[R] L) = 2 ^ k := by
    rw [IsGalois.card_aut_eq_finrank, hkeq]
  obtain ⟨H₁, hH₁_card⟩ : ∃ H₁ : Subgroup (L ≃ₐ[R] L), Nat.card H₁ = 2 ^ (k - 1) := by
    refine Sylow.exists_subgroup_card_pow_prime 2 ?_
    rw [hGcard]; exact pow_dvd_pow 2 (Nat.sub_le k 1)
  let M : IntermediateField R L := IntermediateField.fixedField H₁
  have hML_finrank : Module.finrank M L = 2 ^ (k - 1) := by
    rw [← hH₁_card]; exact IntermediateField.finrank_fixedField_eq_card H₁
  have htower_M : Module.finrank R M * Module.finrank M L = Module.finrank R L :=
    Module.finrank_mul_finrank R M L
  have hM_finrank : Module.finrank R M = 2 := by
    rw [hML_finrank, hkeq] at htower_M
    have h2k : (2:ℕ) ^ k = 2 * 2 ^ (k - 1) := by
      conv_lhs => rw [show k = 1 + (k - 1) from by omega]
      rw [pow_add, pow_one]
    rw [h2k] at htower_M
    have h2posp : (0 : ℕ) < 2 ^ (k - 1) := Nat.pos_of_ne_zero (pow_ne_zero _ (by decide))
    exact Nat.eq_of_mul_eq_mul_right h2posp htower_M
  haveI hM_fd : FiniteDimensional R M := inferInstance
  obtain ⟨e⟩ : Nonempty (M ≃ₐ[R] Ri R) :=
    nonempty_algEquiv_Ri_of_finrank_eq_two M hM_finrank
  haveI : Finite H₁ := Nat.finite_of_card_ne_zero (by rw [hH₁_card]; positivity)
  obtain ⟨H₂, hH₂_card⟩ : ∃ H₂ : Subgroup H₁, Nat.card H₂ = 2 ^ (k - 2) := by
    refine Sylow.exists_subgroup_card_pow_prime 2 ?_
    rw [hH₁_card]; exact pow_dvd_pow 2 (by omega)
  let H₂' : Subgroup (L ≃ₐ[R] L) := H₂.map H₁.subtype
  have hH₂'_card : Nat.card H₂' = 2 ^ (k - 2) := by
    rw [← hH₂_card]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective H₂ H₁.subtype H₁.subtype_injective).symm.toEquiv
  let N : IntermediateField R L := IntermediateField.fixedField H₂'
  have hNL_finrank : Module.finrank N L = 2 ^ (k - 2) := by
    rw [← hH₂'_card]; exact IntermediateField.finrank_fixedField_eq_card H₂'
  have hH₂'_le_H₁ : H₂' ≤ H₁ := by
    intro x hx
    rcases hx with ⟨y, _, rfl⟩
    exact y.property
  have hM_le_N : M ≤ N := IntermediateField.fixedField_antitone hH₂'_le_H₁
  have htower_N : Module.finrank R N * Module.finrank N L = Module.finrank R L :=
    Module.finrank_mul_finrank R N L
  have hN_finrank : Module.finrank R N = 4 := by
    rw [hNL_finrank, hkeq] at htower_N
    have h2k : (2:ℕ) ^ k = 4 * 2 ^ (k - 2) := by
      conv_lhs => rw [show k = 2 + (k - 2) from by omega]
      rw [pow_add]; ring
    rw [h2k] at htower_N
    have h2posp : (0 : ℕ) < 2 ^ (k - 2) := Nat.pos_of_ne_zero (pow_ne_zero _ (by decide))
    exact Nat.eq_of_mul_eq_mul_right h2posp htower_N
  have hrel_MN : IntermediateField.relfinrank M N = 2 := by
    have := IntermediateField.finrank_bot_mul_relfinrank hM_le_N
    rw [hM_finrank, hN_finrank] at this
    omega
  let N' : IntermediateField M L := IntermediateField.extendScalars hM_le_N
  have hMN'_finrank : Module.finrank M N' = 2 := by
    rw [← IntermediateField.relfinrank_eq_finrank_of_le hM_le_N]
    exact hrel_MN
  let f : Ri R →+* N' :=
    (algebraMap M N').comp (e.symm : Ri R →+* M)
  letI : Algebra (Ri R) N' := f.toAlgebra
  have hRiN_finrank : Module.finrank (Ri R) N' = 2 := by
    have hswap : Module.finrank (Ri R) N' = Module.finrank M N' := by
      refine Algebra.finrank_eq_of_equiv_equiv (e.symm : Ri R ≃+* M) (RingEquiv.refl N') ?_
      apply RingHom.ext
      intro x
      show (algebraMap M N') (e.symm x) = algebraMap (Ri R) N' x
      rfl
    rw [hswap, hMN'_finrank]
  exact no_quadratic_ext_Ri N' hRiN_finrank

/-- Any finite Galois extension of an RCF has degree 1 or 2. -/
private theorem finrank_one_or_two_of_galois
    (L : Type u) [Field L] [Algebra R L] [FiniteDimensional R L] [IsGalois R L] :
    Module.finrank R L = 1 ∨ Module.finrank R L = 2 := by
  have h : Module.finrank R L ≤ 2 := finrank_le_two_of_galois (R := R) L
  have hpos : 0 < Module.finrank R L := Module.finrank_pos
  interval_cases (Module.finrank R L) <;> simp_all

/-- **S5.** FTA for RCF: every finite extension has degree 1 or 2. -/
theorem finrank_eq_one_or_two_of_finite
    (K : Type u) [Field K] [Algebra R K] [Module.Finite R K] [Nontrivial K] :
    Module.finrank R K = 1 ∨ Module.finrank R K = 2 := by
  haveI : CharZero R := IsStrictOrderedRing.toCharZero
  haveI : Algebra.IsAlgebraic R K := Algebra.IsAlgebraic.of_finite R K
  let AR : Type u := AlgebraicClosure R
  let φ : K →ₐ[R] AR := IsAlgClosed.lift
  have hφ_inj : Function.Injective φ := φ.toRingHom.injective
  let L : IntermediateField R AR := IntermediateField.normalClosure R K AR
  haveI hfin_L : FiniteDimensional R L := normalClosure.is_finiteDimensional R K AR
  haveI hgal_L : IsGalois R L := by
    haveI : Algebra.IsSeparable R K := Algebra.IsAlgebraic.isSeparable_of_perfectField
    exact IsGalois.normalClosure R K AR
  have hrange_le : φ.fieldRange ≤ L := AlgHom.fieldRange_le_normalClosure φ
  let K' : IntermediateField R AR := φ.fieldRange
  have hKK' : Module.finrank R K = Module.finrank R K' := by
    let eq : K ≃ₐ[R] φ.range := AlgEquiv.ofInjectiveField φ
    have h1 : Module.finrank R K = Module.finrank R φ.range :=
      LinearEquiv.finrank_eq eq.toLinearEquiv
    have h2 : Module.finrank R K' = Module.finrank R φ.range :=
      (IntermediateField.finrank_eq_finrank_subalgebra K').symm
    rw [h1, ← h2]
  have hdvd : Module.finrank R K' ∣ Module.finrank R L := by
    have htower := IntermediateField.finrank_bot_mul_relfinrank hrange_le
    exact ⟨_, htower.symm⟩
  rw [hKK']
  rcases finrank_one_or_two_of_galois (R := R) L with hL1 | hL2
  · rw [hL1] at hdvd
    left; exact Nat.dvd_one.mp hdvd
  · rw [hL2] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · left; exact h
    · right; exact h

/-- **S6.** An algebraic extension of an RCF is finite. -/
theorem finite_of_isAlgebraic
    (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K] :
    Module.Finite R K := by
  by_contra hnfd
  obtain ⟨L, hLfin, hL_lt⟩ :=
    IntermediateField.exists_lt_finrank_of_infinite_dimensional (F := R) (E := K) hnfd 2
  rcases finrank_eq_one_or_two_of_finite (R := R) L with h | h
  · rw [h] at hL_lt; omega
  · rw [h] at hL_lt; omega

/-- **S9'.** Every monic irreducible polynomial over an RCF is either linear `X - C c`
for some `c : R`, or of the form `(X - C a) ^ 2 + C (b ^ 2)` for some `a b : R` with `b ≠ 0`.
This realises the blueprint lemma `lem:irreds_class`. -/
theorem eq_linear_or_eq_sq_add_sq_of_irreducible
    {g : R[X]} (hmonic : g.Monic) (hirred : Irreducible g) :
    (∃ c : R, g = X - C c) ∨
    (∃ a b : R, b ≠ 0 ∧ g = (X - C a) ^ 2 + C (b ^ 2)) := by
  have hne : g ≠ 0 := hirred.ne_zero
  have hdeg_ne : g.degree ≠ 0 := by
    intro h
    have : g.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (by rw [h])
    have : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hmonic this
    exact hirred.not_isUnit (by rw [this]; exact isUnit_one)
  haveI : Fact (Irreducible g) := ⟨hirred⟩
  haveI : Nontrivial (AdjoinRoot g) := AdjoinRoot.nontrivial g hdeg_ne
  haveI : Module.Finite R (AdjoinRoot g) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hne).basis
  have hfinrank : Module.finrank R (AdjoinRoot g) = g.natDegree := by
    have := (AdjoinRoot.powerBasis hne).finrank
    rw [AdjoinRoot.powerBasis_dim hne] at this
    exact this
  rcases finrank_eq_one_or_two_of_finite (R := R) (AdjoinRoot g) with h1 | h2
  · left
    rw [hfinrank] at h1
    refine ⟨-g.coeff 0, ?_⟩
    have hg_eq : g = X + C (g.coeff 0) := hmonic.eq_X_add_C h1
    rw [map_neg, sub_neg_eq_add]
    exact hg_eq
  · right
    rw [hfinrank] at h2
    set a : R := g.coeff 1
    set b : R := g.coeff 0
    have hcoeff2 : g.coeff 2 = 1 := by
      have := hmonic.coeff_natDegree
      rw [h2] at this
      exact this
    have hab : g = X ^ 2 + C a * X + C b := by
      apply Polynomial.ext
      intro n
      rw [coeff_add, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
      rcases lt_trichotomy n 2 with hn | rfl | hn
      · interval_cases n
        · show b = _; simp
        · show a = _; simp
      · show g.coeff 2 = _; rw [hcoeff2]; simp
      · have hn_gt : n > g.natDegree := by rw [h2]; exact hn
        rw [coeff_eq_zero_of_natDegree_lt hn_gt]
        have hn2 : n ≠ 2 := Nat.ne_of_gt hn
        have hn1 : (1 : ℕ) ≠ n := by omega
        have hn0 : n ≠ 0 := by omega
        simp [hn2, hn1, hn0]
    set δ : R := (a / 2) ^ 2 - b with hδdef
    have hdelta_neg : δ < 0 := by
      by_contra hnn
      obtain ⟨c, hc⟩ :=
        (IsRealClosed.nonneg_iff_isSquare (R := R) (x := δ)).mp (not_lt.mp hnn)
      set r : R := -a/2 + c with hrdef
      have hroot : g.IsRoot r := by
        simp only [IsRoot, hab, eval_add, eval_pow, eval_X, eval_mul, eval_C]
        have hcc : c * c = (a/2)^2 - b := hc.symm
        show r ^ 2 + a * r + b = 0
        rw [hrdef]
        linear_combination hcc
      have hdeg1 : g.degree = 1 :=
        Polynomial.degree_eq_one_of_irreducible_of_root hirred hroot
      have hnatdeg1 : g.natDegree = 1 := natDegree_eq_of_degree_eq_some hdeg1
      rw [h2] at hnatdeg1
      exact absurd hnatdeg1 (by norm_num)
    have hnegδ_pos : 0 < -δ := by linarith
    obtain ⟨b', hb'⟩ :=
      (IsRealClosed.nonneg_iff_isSquare (R := R) (x := -δ)).mp hnegδ_pos.le
    have hb'_sq : b' ^ 2 = -δ := by rw [sq]; exact hb'.symm
    set a' : R := -a/2 with ha'def
    have hb'_ne : b' ≠ 0 := by
      intro h0
      rw [h0] at hb'_sq
      have : (0 : R) ^ 2 = 0 := by ring
      rw [this] at hb'_sq
      linarith
    refine ⟨a', b', hb'_ne, ?_⟩
    have hbeq : b = (a/2)^2 + b'^2 := by
      rw [hb'_sq, hδdef]; ring
    rw [hab, hbeq]
    have hCadd : (C ((a/2)^2 + b'^2) : R[X]) = C ((a/2)^2) + C (b'^2) := map_add C _ _
    have hCsq : (C ((a/2)^2) : R[X]) = (C (a/2))^2 := map_pow C _ _
    have hCa' : (C a' : R[X]) = -(C (a/2)) := by
      show C (-a/2) = -(C (a/2))
      rw [show (-a/2 : R) = -(a/2) from by ring, map_neg]
    rw [hCa', hCadd, hCsq]
    have h2C : (C a : R[X]) = 2 * C (a/2) := by
      have heq : (a : R) = 2 * (a/2) := by ring
      conv_lhs => rw [heq]
      rw [map_mul, map_ofNat]
    rw [h2C]
    ring

/-- **S9** (for IVP use). Every monic irreducible polynomial over an RCF is either
linear or is everywhere positive. -/
theorem natDegree_eq_one_or_forall_eval_pos_of_irreducible
    {g : R[X]} (hmonic : g.Monic) (hirred : Irreducible g) :
    g.natDegree = 1 ∨ ∀ x : R, 0 < g.eval x := by
  have hne : g ≠ 0 := hirred.ne_zero
  have hdeg_ne : g.degree ≠ 0 := by
    intro h
    have : g.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (by rw [h])
    have : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hmonic this
    exact hirred.not_isUnit (by rw [this]; exact isUnit_one)
  haveI : Fact (Irreducible g) := ⟨hirred⟩
  haveI : Nontrivial (AdjoinRoot g) := AdjoinRoot.nontrivial g hdeg_ne
  haveI : Module.Finite R (AdjoinRoot g) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hne).basis
  have hfinrank : Module.finrank R (AdjoinRoot g) = g.natDegree := by
    have := (AdjoinRoot.powerBasis hne).finrank
    rw [AdjoinRoot.powerBasis_dim hne] at this
    exact this
  rcases finrank_eq_one_or_two_of_finite (R := R) (AdjoinRoot g) with h1 | h2
  · left
    rw [hfinrank] at h1
    exact h1
  · right
    rw [hfinrank] at h2
    set a : R := g.coeff 1
    set b : R := g.coeff 0
    have hcoeff2 : g.coeff 2 = 1 := by
      have := hmonic.coeff_natDegree
      rw [h2] at this
      exact this
    have hab : g = X ^ 2 + C a * X + C b := by
      apply Polynomial.ext
      intro n
      rw [coeff_add, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
      rcases lt_trichotomy n 2 with hn | rfl | hn
      · interval_cases n
        · show b = _; simp
        · show a = _; simp
      · show g.coeff 2 = _; rw [hcoeff2]; simp
      · have hn_gt : n > g.natDegree := by rw [h2]; exact hn
        rw [coeff_eq_zero_of_natDegree_lt hn_gt]
        have hn2 : n ≠ 2 := Nat.ne_of_gt hn
        have hn1 : (1 : ℕ) ≠ n := by omega
        have hn0 : n ≠ 0 := by omega
        simp [hn2, hn1, hn0]
    set δ : R := (a / 2) ^ 2 - b with hδdef
    have hdelta_neg : δ < 0 := by
      by_contra hnn
      obtain ⟨c, hc⟩ :=
        (IsRealClosed.nonneg_iff_isSquare (R := R) (x := δ)).mp (not_lt.mp hnn)
      set r : R := -a/2 + c with hrdef
      have hroot : g.IsRoot r := by
        simp only [IsRoot, hab, eval_add, eval_pow, eval_X, eval_mul, eval_C]
        have hcc : c * c = (a/2)^2 - b := hc.symm
        show r ^ 2 + a * r + b = 0
        rw [hrdef]
        linear_combination hcc
      have hdeg1 : g.degree = 1 :=
        Polynomial.degree_eq_one_of_irreducible_of_root hirred hroot
      have hnatdeg1 : g.natDegree = 1 := natDegree_eq_of_degree_eq_some hdeg1
      rw [h2] at hnatdeg1
      exact absurd hnatdeg1 (by norm_num)
    intro x
    have heval : g.eval x = (x + a/2) ^ 2 + (-δ) := by
      rw [hab]
      simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
      rw [hδdef]
      ring
    rw [heval]
    have hsq : 0 ≤ (x + a/2) ^ 2 := sq_nonneg _
    linarith

/-- **S10.** IVP for polynomials over an RCF. -/
theorem ivp_poly
    {f : R[X]} {a b : R} (hab : a ≤ b) (ha : f.eval a ≤ 0) (hb : 0 ≤ f.eval b) :
    ∃ c ∈ Set.Icc a b, f.IsRoot c := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f a b with
  | _ n ih =>
    by_cases hf0 : f = 0
    · exact ⟨a, ⟨le_refl a, hab⟩, by simp [hf0]⟩
    by_cases hn0 : n = 0
    · rw [hn0] at hn
      obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hn
      have heva : f.eval a = c := by rw [← hc]; simp
      have hevb : f.eval b = c := by rw [← hc]; simp
      rw [heva] at ha
      rw [hevb] at hb
      have hceq : c = 0 := le_antisymm ha hb
      exact absurd (by rw [← hc, hceq, map_zero] : f = 0) hf0
    have hfnotunit : ¬ IsUnit f := fun hu => hn0 (by
      have := Polynomial.natDegree_eq_zero_of_isUnit hu; rw [hn] at this; exact this)
    obtain ⟨g, hgmonic, hgirred, q, hfq⟩ := Polynomial.exists_monic_irreducible_factor f hfnotunit
    have hgne : g ≠ 0 := hgirred.ne_zero
    have hqne : q ≠ 0 := fun hq0 => hf0 (by rw [hfq, hq0, mul_zero])
    have hgdeg_pos : 1 ≤ g.natDegree := by
      by_contra h
      have hgd0 : g.natDegree = 0 := by omega
      have hg_eq_one : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hgmonic hgd0
      exact hgirred.not_isUnit (by rw [hg_eq_one]; exact isUnit_one)
    have hqdeg_lt : q.natDegree < n := by
      rw [← hn, hfq, Polynomial.natDegree_mul hgne hqne]; omega
    have hfeval : ∀ x : R, f.eval x = g.eval x * q.eval x := fun x => by rw [hfq]; simp
    -- Helper: given sign info on g at a and b, derive sign info on q and apply IH
    have apply_ih : ∀ (q' : R[X]), q'.natDegree < n → q'.eval a ≤ 0 → 0 ≤ q'.eval b →
        ∃ c ∈ Set.Icc a b, q'.IsRoot c := fun q' hq'lt hq'a hq'b =>
      ih q'.natDegree hq'lt hab hq'a hq'b rfl
    rcases natDegree_eq_one_or_forall_eval_pos_of_irreducible hgmonic hgirred with hg1 | hgpos
    · -- g = X + C (g.coeff 0); let r = -g.coeff 0
      have hg_eq : g = X + C (g.coeff 0) := hgmonic.eq_X_add_C hg1
      set r : R := -g.coeff 0 with hrdef
      have hg_eval : ∀ x : R, g.eval x = x - r := fun x => by rw [hg_eq]; simp [hrdef]
      by_cases hra : r < a
      · -- g > 0 on [a,b]: q(a) ≤ 0, q(b) ≥ 0
        have hga_pos : 0 < g.eval a := by rw [hg_eval]; linarith
        have hgb_pos : 0 < g.eval b := by rw [hg_eval]; linarith
        have hqa_le : q.eval a ≤ 0 := by
          have := (hfeval a).symm.le.trans ha
          rcases le_or_gt (q.eval a) 0 with h | h
          · exact h
          · exact absurd (mul_pos hga_pos h) (by linarith)
        have hqb_nn : 0 ≤ q.eval b := by
          have := hb.trans (hfeval b).le
          rcases le_or_gt 0 (q.eval b) with h | h
          · exact h
          · exact absurd (mul_neg_of_pos_of_neg hgb_pos h) (by linarith)
        obtain ⟨c, hcmem, hcroot⟩ := apply_ih q hqdeg_lt hqa_le hqb_nn
        exact ⟨c, hcmem, by show f.eval c = 0; rw [hfeval, show q.eval c = 0 from hcroot, mul_zero]⟩
      by_cases hrb : b < r
      · -- g < 0 on [a,b]: q(a) ≥ 0, q(b) ≤ 0; apply IH to -q
        have hra : a ≤ r := not_lt.mp hra
        have hga_neg : g.eval a < 0 := by rw [hg_eval]; linarith
        have hgb_neg : g.eval b < 0 := by rw [hg_eval]; linarith
        have hqa_nn : 0 ≤ q.eval a := by
          have := (hfeval a).symm.le.trans ha
          rcases le_or_gt 0 (q.eval a) with h | h
          · exact h
          · exact absurd (mul_pos_of_neg_of_neg hga_neg h) (by linarith)
        have hqb_le : q.eval b ≤ 0 := by
          have := hb.trans (hfeval b).le
          rcases le_or_gt (q.eval b) 0 with h | h
          · exact h
          · exact absurd (mul_neg_of_neg_of_pos hgb_neg h) (by linarith)
        have hnqa : (-q).eval a ≤ 0 := by simp; linarith
        have hnqb : 0 ≤ (-q).eval b := by simp; linarith
        have hnq_lt : (-q).natDegree < n := by rw [Polynomial.natDegree_neg]; exact hqdeg_lt
        obtain ⟨c, hcmem, hcroot⟩ := apply_ih (-q) hnq_lt hnqa hnqb
        refine ⟨c, hcmem, ?_⟩
        show f.eval c = 0
        have hqc : q.eval c = 0 := by
          have : (-q).eval c = 0 := hcroot
          rw [eval_neg] at this; linarith
        rw [hfeval, hqc, mul_zero]
      · -- a ≤ r ≤ b: r is a root of g (hence of f)
        refine ⟨r, ⟨not_lt.mp hra, not_lt.mp hrb⟩, ?_⟩
        show f.eval r = 0
        rw [hfeval, show g.eval r = 0 by rw [hg_eval]; ring, zero_mul]
    · -- g everywhere positive
      have hga_pos : 0 < g.eval a := hgpos a
      have hgb_pos : 0 < g.eval b := hgpos b
      have hqa_le : q.eval a ≤ 0 := by
        have := (hfeval a).symm.le.trans ha
        rcases le_or_gt (q.eval a) 0 with h | h
        · exact h
        · exact absurd (mul_pos hga_pos h) (by linarith)
      have hqb_nn : 0 ≤ q.eval b := by
        have := hb.trans (hfeval b).le
        rcases le_or_gt 0 (q.eval b) with h | h
        · exact h
        · exact absurd (mul_neg_of_pos_of_neg hgb_pos h) (by linarith)
      obtain ⟨c, hcmem, hcroot⟩ := apply_ih q hqdeg_lt hqa_le hqb_nn
      exact ⟨c, hcmem, by show f.eval c = 0; rw [hfeval, show q.eval c = 0 from hcroot, mul_zero]⟩

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
    set i : K := φ.symm (AdjoinRoot.root (X ^ 2 + 1 : R[X])) with hi_def
    have hroot_sum : (AdjoinRoot.root (X ^ 2 + 1 : R[X])) ^ 2 + 1 = (0 : Ri R) := by
      have hms : AdjoinRoot.mk (X ^ 2 + 1 : R[X]) (X ^ 2 + 1) = 0 :=
        AdjoinRoot.mk_self
      have heq : AdjoinRoot.mk (X ^ 2 + 1 : R[X]) (X ^ 2 + 1 : R[X]) =
          (AdjoinRoot.root (X ^ 2 + 1 : R[X])) ^ 2 + 1 := by
        rw [← AdjoinRoot.aeval_eq]
        simp [map_add, map_pow, map_one]
      rw [heq] at hms
      exact hms
    have hroot_sq : (AdjoinRoot.root (X ^ 2 + 1 : R[X])) ^ 2 = (-1 : Ri R) := by
      have := hroot_sum
      linear_combination this
    have hi_sq : i ^ 2 = (-1 : K) := by
      rw [hi_def, ← map_pow, hroot_sq, map_neg, map_one]
    have hsq : (0 : K) ≤ i ^ 2 := sq_nonneg i
    rw [hi_sq] at hsq
    linarith

end FTA

end IsRealClosed

namespace IsRealClosed

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **cor:RCF_ac.** If `R` is real closed, then `AdjoinRoot (X^2 + 1)` is algebraically closed. -/
instance isAlgClosed_adjoinRoot_X_sq_add_one [IsRealClosed R] :
    IsAlgClosed (AdjoinRoot (X ^ 2 + 1 : R[X])) := by
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hmonic hirred
  -- Set K = AdjoinRoot p; show finrank (Ri R) K = 1 hence p has degree 1
  have hne : p ≠ 0 := hirred.ne_zero
  have hdeg_ne : p.degree ≠ 0 := by
    intro h
    have h0 : p.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (by rw [h])
    have hp1 : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hmonic h0
    exact hirred.not_isUnit (by rw [hp1]; exact isUnit_one)
  haveI : Fact (Irreducible p) := ⟨hirred⟩
  haveI : Nontrivial (AdjoinRoot p) := AdjoinRoot.nontrivial p hdeg_ne
  set K : Type u := AdjoinRoot p
  -- K is a finite extension of Ri R
  haveI : Module.Finite (Ri R) K :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hne).basis
  -- Thus K is a finite extension of R via tower
  haveI : Module.Finite R K := Module.Finite.trans (Ri R) K
  -- By S5, finrank R K = 1 or 2
  have hfinrank_Ri : Module.finrank R (Ri R) = 2 := by
    have hne' : (X ^ 2 + 1 : R[X]) ≠ 0 := (irreducible_X_sq_add_one (R := R)).ne_zero
    have hdeg : (X ^ 2 + 1 : R[X]).natDegree = 2 := by
      have h1 : (X ^ 2 + 1 : R[X]) = X ^ 2 - C (-1) := by
        simp [map_neg, map_one, sub_neg_eq_add]
      rw [h1]; exact natDegree_X_pow_sub_C
    have h1 := (AdjoinRoot.powerBasis hne').finrank
    rw [AdjoinRoot.powerBasis_dim hne'] at h1
    rw [h1, hdeg]
  rcases finrank_eq_one_or_two_of_finite (R := R) K with h1 | h2
  · -- finrank R K = 1, and finrank R (Ri R) = 2, so finrank (Ri R) K * 2 = 1: impossible
    exfalso
    have htower : Module.finrank R (Ri R) * Module.finrank (Ri R) K =
        Module.finrank R K := Module.finrank_mul_finrank R (Ri R) K
    rw [h1, hfinrank_Ri] at htower
    omega
  · -- finrank R K = 2, and finrank R (Ri R) = 2, so finrank (Ri R) K = 1
    have htower : Module.finrank R (Ri R) * Module.finrank (Ri R) K =
        Module.finrank R K := Module.finrank_mul_finrank R (Ri R) K
    rw [h2, hfinrank_Ri] at htower
    have hfinrank_K : Module.finrank (Ri R) K = 1 := by omega
    -- deg p = 1, so p has a root
    have hfinrank_eq : Module.finrank (Ri R) K = p.natDegree := by
      have := (AdjoinRoot.powerBasis hne).finrank
      rw [AdjoinRoot.powerBasis_dim hne] at this
      exact this
    rw [hfinrank_eq] at hfinrank_K
    have hdeg1 : p.degree = 1 := by
      rw [degree_eq_natDegree hne, hfinrank_K]; rfl
    exact Polynomial.exists_root_of_degree_eq_one hdeg1

/-- **cor:RCF_ac.** If `R` is real closed, then `AdjoinRoot (X^2 + 1)` is the algebraic
closure of `R`. -/
instance isAlgClosure_adjoinRoot_X_sq_add_one [IsRealClosed R] :
    IsAlgClosure R (AdjoinRoot (X ^ 2 + 1 : R[X])) := by
  refine IsAlgClosure.mk inferInstance ?_
  exact Algebra.IsAlgebraic.of_finite R (AdjoinRoot (X ^ 2 + 1 : R[X]))

end IsRealClosed

section Converse

open Polynomial

universe u

/-- If `-1` is not a square in a field `F`, then `X^2 + 1` is irreducible in `F[X]`. -/
theorem Polynomial.irreducible_X_sq_add_one_of_not_isSquare_neg_one
    {F : Type*} [Field F] (h : ¬ IsSquare (-1 : F)) : Irreducible (X ^ 2 + 1 : F[X]) := by
  have heq : (X ^ 2 + 1 : F[X]) = X ^ 2 - C (-1) := by simp [sub_neg_eq_add]
  have hmonic : (X ^ 2 - C (-1 : F)).Monic := monic_X_pow_sub_C _ (by decide)
  have hdeg : (X ^ 2 - C (-1 : F)).natDegree = 2 := natDegree_X_pow_sub_C
  rw [heq]
  rw [Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hmonic
        (by rw [hdeg]) (by rw [hdeg]; decide),
      Multiset.eq_zero_iff_forall_notMem]
  intro c hc
  rw [mem_roots hmonic.ne_zero] at hc
  simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_neg_eq_add] at hc
  exact h ⟨c, by linear_combination hc.symm - sq c⟩

/-- If a field `F` has `¬ IsSquare (-1)` and `AdjoinRoot (X^2 + 1 : F[X])` is the algebraic
closure of `F`, then there is a `LinearOrder` on `F` making it real closed. -/
theorem IsRealClosed.of_isAlgClosure_adjoinRoot_X_sq_add_one
    {F : Type u} [Field F]
    (h_neg_one : ¬ IsSquare (-1 : F))
    [IsAlgClosure F (AdjoinRoot (X ^ 2 + 1 : F[X]))] :
    ∃ _ : LinearOrder F, IsRealClosed F := by
  -- Set up notation for F(i)
  set Fi : Type u := AdjoinRoot (X ^ 2 + 1 : F[X]) with hFi_def
  -- X^2 + 1 is irreducible, so Fi is a field (already by AdjoinRoot instance)
  have hirred : Irreducible (X ^ 2 + 1 : F[X]) :=
    Polynomial.irreducible_X_sq_add_one_of_not_isSquare_neg_one h_neg_one
  haveI : Fact (Irreducible (X ^ 2 + 1 : F[X])) := ⟨hirred⟩
  -- natDegree and monic for X^2 + 1
  have hmonic : (X ^ 2 + 1 : F[X]).Monic := by
    have heq : (X ^ 2 + 1 : F[X]) = X ^ 2 - C (-1 : F) := by simp [sub_neg_eq_add]
    rw [heq]; exact monic_X_pow_sub_C _ (by decide)
  have hdeg2 : (X ^ 2 + 1 : F[X]).natDegree = 2 := by
    have heq : (X ^ 2 + 1 : F[X]) = X ^ 2 - C (-1 : F) := by simp [sub_neg_eq_add]
    rw [heq]; exact natDegree_X_pow_sub_C
  have hne : (X ^ 2 + 1 : F[X]) ≠ 0 := hirred.ne_zero
  -- Fi is algebraically closed and finite of dim 2 over F
  haveI : IsAlgClosed Fi := IsAlgClosure.isAlgClosed F
  haveI : Module.Finite F Fi :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hne).basis
  have hfinrank_Fi : Module.finrank F Fi = 2 := by
    have h1 := (AdjoinRoot.powerBasis hne).finrank
    rw [AdjoinRoot.powerBasis_dim hne] at h1
    rw [h1, hdeg2]
  -- Every element of Fi is a square (since Fi is algebraically closed)
  have hFi_isSquare : ∀ z : Fi, IsSquare z := by
    intro z
    exact IsAlgClosed.exists_eq_mul_self z
  -- Every sum of squares in F is a square in F
  have hsumSq_isSquare : ∀ {s : F}, IsSumSq s → IsSquare s := fun hs =>
    IsSquare.of_isSumSq_of_forall_isSquare_adjoinRoot h_neg_one hFi_isSquare hs
  -- F is semireal: -1 is not a sum of squares (else it would be a square)
  haveI hsemireal : IsSemireal F := by
    refine .of_not_isSumSq_neg_one ?_
    intro hsum
    exact h_neg_one (hsumSq_isSquare hsum)
  -- Use of_bijective_algebraMap_of_isSemireal: show every semireal algebraic ext
  -- of F is isomorphic to F.
  refine IsRealClosed.of_bijective_algebraMap_of_isSemireal (R := F) ?_
  intro K _ _ _ _
  -- K embeds into Fi via IsAlgClosed.lift since K is algebraic over F
  -- Using nonempty_algEquiv_or_of_finrank_eq_two: K ≃ F or K ≃ Fi
  rcases IsAlgClosed.nonempty_algEquiv_or_of_finrank_eq_two (F := F) (F' := Fi) K
      hfinrank_Fi with ⟨φ⟩ | ⟨φ⟩
  · -- Case K ≃ₐ[F] F: algebraMap F K is bijective
    haveI : Module.Finite F K := Module.Finite.equiv φ.toLinearEquiv.symm
    have hfinrank_K : Module.finrank F K = 1 := by
      rw [φ.toLinearEquiv.finrank_eq]; simp
    exact Module.Free.bijective_algebraMap_of_finrank_eq_one hfinrank_K
  · -- Case K ≃ₐ[F] Fi: K is not semireal (since -1 is a square in Fi, hence in K)
    exfalso
    -- In Fi, -1 = root^2, so -1 is a square
    have hFi_sq : IsSquare (-1 : Fi) := by
      have hroot_sq : (AdjoinRoot.root (X ^ 2 + 1 : F[X])) ^ 2 = (-1 : Fi) := by
        have h0 : aeval (AdjoinRoot.root (X ^ 2 + 1 : F[X])) (X ^ 2 + 1 : F[X]) = 0 :=
          AdjoinRoot.eval₂_root _
        have hsum : (AdjoinRoot.root (X ^ 2 + 1 : F[X])) ^ 2 + 1 = (0 : Fi) := by
          simpa [aeval_def, eval₂_add, eval₂_pow, eval₂_X, eval₂_one] using h0
        linear_combination hsum
      refine ⟨AdjoinRoot.root (X ^ 2 + 1 : F[X]), ?_⟩
      rw [← sq]; exact hroot_sq.symm
    -- Via φ.symm, -1 is a square in K
    have hK_sq : IsSquare (-1 : K) := by
      have := hFi_sq.map φ.symm.toRingHom
      simpa using this
    -- But K is semireal, so -1 is not a sum of squares, contradicting that it's a square
    exact IsSemireal.not_isSumSq_neg_one K hK_sq.isSumSq

end Converse
