/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic.TFAE
import RealClosedField.Algebra.Order.Algebra

/-!
# Equivalent conditions for a real closed field (ordered case)

For an ordered field `R`, the following are equivalent:
1. `R` is real closed.
2. `R` is maximal with respect to ordered algebraic extensions.
3. Polynomials over `R` satisfy the intermediate value property.

This file also develops a number of basic algebraic properties of real closed
fields needed to justify the equivalence: the classification of finite and
algebraic extensions (only `R` and `R(i)`), the classification of monic
irreducible polynomials, and some consequences.
-/

namespace IsRealClosed

variable (R : Type*) [Field R]

section Algebraic

variable [IsRealClosed R]

/-- Every sum of squares in a real closed field is a square. -/
theorem isSquare_of_isSumSq {x : R} (hx : IsSumSq x) : IsSquare x := sorry

/-- There is no nontrivial odd-degree finite extension of a real closed field `R`:
any finite extension `K/R` with `Module.finrank R K` odd has `R → K` surjective. -/
theorem surjective_algebraMap_of_odd_finrank
    (K : Type*) [Field K] [Algebra R K] [FiniteDimensional R K]
    (hodd : Odd (Module.finrank R K)) :
    Function.Surjective (algebraMap R K) := sorry

/-- `R(i)` is the unique quadratic extension of a real closed field `R` (up to `R`-isomorphism):
any quadratic extension of `R` is `R`-isomorphic to any other quadratic extension of `R`. -/
theorem nonempty_algEquiv_of_finrank_eq_two
    (K K' : Type*) [Field K] [Algebra R K] [Field K'] [Algebra R K']
    (hK : Module.finrank R K = 2) (hK' : Module.finrank R K' = 2) :
    Nonempty (K ≃ₐ[R] K') := by
  -- It suffices to show that any quadratic extension `L` of `R` carries a PowerBasis whose
  -- minimal polynomial is `X^2 + 1`. Then two such power bases agree on minimal polynomial
  -- and PowerBasis.equivOfMinpoly gives the algebra equivalence.
  suffices h : ∀ (L : Type*) [Field L] [Algebra R L], Module.finrank R L = 2 →
      ∃ pb : PowerBasis R L, minpoly R pb.gen = Polynomial.X ^ 2 + Polynomial.C (1 : R) by
    obtain ⟨pbK, hminK⟩ := h K hK
    obtain ⟨pbK', hminK'⟩ := h K' hK'
    exact ⟨pbK.equivOfMinpoly pbK' (hminK.trans hminK'.symm)⟩
  intro L _ _ hL
  have hFin : FiniteDimensional R L := .of_finrank_eq_succ hL
  have hInj : Function.Injective (algebraMap R L) := (algebraMap R L).injective
  -- Step 1: find an element `x : L` with `x ∉ range (algebraMap R L)`.
  have hne : ∃ x : L, x ∉ (algebraMap R L).range := by
    by_contra h
    push_neg at h
    have hTop : (⊥ : Subalgebra R L) = ⊤ := by
      apply Subalgebra.toSubmodule_injective
      apply Submodule.eq_top_iff'.mpr
      intro x
      obtain ⟨r, hr⟩ := h x
      rw [← hr]
      exact Algebra.mem_bot.mpr ⟨r, rfl⟩
    have heq : Module.finrank R (⊥ : Subalgebra R L) = Module.finrank R L := by
      rw [hTop]; exact Subalgebra.topEquiv.toLinearEquiv.finrank_eq
    rw [Subalgebra.finrank_bot] at heq
    omega
  obtain ⟨x, hx⟩ := hne
  have hxI : IsIntegral R x := .of_finite R x
  have hdeg2 : (minpoly R x).natDegree = 2 := by
    have h2 : 2 ≤ (minpoly R x).natDegree := (minpoly.two_le_natDegree_iff hxI).mpr hx
    have hle : (minpoly R x).natDegree ≤ Module.finrank R L := minpoly.natDegree_le x
    omega
  -- Step 2: extract coefficients `a = coeff 1`, `b = coeff 0` of minpoly,
  -- and show x^2 + (algebraMap a) * x + (algebraMap b) = 0.
  set a : R := (minpoly R x).coeff 1 with ha_def
  set b : R := (minpoly R x).coeff 0 with hb_def
  have hfm : (minpoly R x).Monic := minpoly.monic hxI
  have hcoeff2 : (minpoly R x).coeff 2 = 1 := by
    have hlc : (minpoly R x).leadingCoeff = 1 := hfm
    rw [Polynomial.leadingCoeff, hdeg2] at hlc
    exact hlc
  have hroot : x ^ 2 + (algebraMap R L) a * x + (algebraMap R L) b = 0 := by
    have haev := minpoly.aeval R x
    rw [Polynomial.aeval_eq_sum_range' (n := 3) (by omega)] at haev
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Algebra.smul_def, pow_zero, mul_one, pow_one] at haev
    rw [hcoeff2, map_one, one_mul] at haev
    -- haev : algebraMap (coeff 0) + algebraMap (coeff 1) * x + x^2 = 0
    -- The local defs `a` and `b` for `coeff 1` and `coeff 0` unfold definitionally.
    show x ^ 2 + (algebraMap R L) ((minpoly R x).coeff 1) * x +
      (algebraMap R L) ((minpoly R x).coeff 0) = 0
    linear_combination haev
  -- Step 3: y = x + algebraMap(a/2); y^2 = algebraMap(a^2/4 - b).
  set c : R := a ^ 2 / 4 - b with hc_def
  set y : L := x + (algebraMap R L) (a / 2) with hy_def
  have h2R : (2 : R) ≠ 0 := two_ne_zero
  have hy_sq : y ^ 2 = (algebraMap R L) c := by
    have half_sq : (algebraMap R L) (a / 2) ^ 2 = (algebraMap R L) (a ^ 2 / 4) := by
      rw [← map_pow]
      congr 1
      field_simp
    have half_times : 2 * (algebraMap R L) (a / 2) = (algebraMap R L) a := by
      have : (2 : L) = (algebraMap R L) 2 := (map_ofNat (algebraMap R L) 2).symm
      rw [this, ← map_mul]
      congr 1
      field_simp
    have expand : y ^ 2 = x ^ 2 + (algebraMap R L) a * x + (algebraMap R L) (a ^ 2 / 4) := by
      show (x + (algebraMap R L) (a / 2)) ^ 2 = _
      have : (x + (algebraMap R L) (a / 2)) ^ 2 =
          x ^ 2 + x * (2 * (algebraMap R L) (a / 2)) + (algebraMap R L) (a / 2) ^ 2 := by ring
      rw [this, half_sq, half_times]
      ring
    rw [expand]
    show x ^ 2 + (algebraMap R L) a * x + (algebraMap R L) (a ^ 2 / 4) =
      (algebraMap R L) (a ^ 2 / 4 - b)
    rw [map_sub]
    linear_combination hroot
  -- Step 4: y ∉ range algebraMap.
  have hy_ni : y ∉ (algebraMap R L).range := by
    rintro ⟨r, hr⟩
    apply hx
    refine ⟨r - a / 2, ?_⟩
    rw [map_sub]
    have hy_eq : x + (algebraMap R L) (a / 2) = (algebraMap R L) r := hr
    linear_combination hy_eq
  -- Step 5: c is not a square in R.
  have hc_ni : ¬ IsSquare c := by
    rintro ⟨s, hs⟩
    -- then (algebraMap s)^2 = algebraMap c = y^2, so y = ± algebraMap s.
    have halg_sq : y ^ 2 = ((algebraMap R L) s) ^ 2 := by
      rw [hy_sq, show c = s * s from hs, map_mul]
      ring
    have hfact : (y - (algebraMap R L) s) * (y + (algebraMap R L) s) = 0 := by
      linear_combination halg_sq
    apply hy_ni
    rcases mul_eq_zero.mp hfact with hd | hd
    · exact ⟨s, by linear_combination -hd⟩
    · refine ⟨-s, ?_⟩
      rw [map_neg]
      linear_combination -hd
  -- Step 6: by RCF axiom, -c is a square. Write -c = s^2.
  have hnc_sq : IsSquare (-c) := (IsRealClosed.isSquare_or_isSquare_neg c).resolve_left hc_ni
  obtain ⟨s, hs⟩ := hnc_sq
  have hs_ne : s ≠ 0 := by
    rintro rfl
    apply hc_ni
    have hmc : -c = 0 := by rw [hs]; ring
    have hc0 : c = 0 := by linear_combination -hmc
    rw [hc0]
    exact ⟨0, by ring⟩
  have hsL_ne : (algebraMap R L) s ≠ 0 :=
    (map_ne_zero_iff _ hInj).mpr hs_ne
  -- Step 7: α = y / algebraMap s. Then α^2 = -1.
  set sL : L := (algebraMap R L) s with hsL_def
  have hsL_sq : sL ^ 2 = - (algebraMap R L) c := by
    show ((algebraMap R L) s) ^ 2 = - (algebraMap R L) c
    rw [← map_pow, ← map_neg]
    congr 1
    -- `hs : -c = s * s`; show `s ^ 2 = -c`.
    rw [sq, ← hs]
  set α : L := y * sL⁻¹ with hα_def
  have hα_sq : α ^ 2 = -1 := by
    have hsL_pow_inv : sL⁻¹ ^ 2 = (sL ^ 2)⁻¹ := by rw [inv_pow]
    calc α ^ 2 = y ^ 2 * (sL ^ 2)⁻¹ := by rw [mul_pow, hsL_pow_inv]
      _ = (algebraMap R L) c * (sL ^ 2)⁻¹ := by rw [hy_sq]
      _ = (algebraMap R L) c * (- (algebraMap R L) c)⁻¹ := by rw [hsL_sq]
      _ = -1 := by
          have hcL_ne : (algebraMap R L) c ≠ 0 := by
            intro hc0
            have : c = 0 := (map_eq_zero_iff _ hInj).mp hc0
            apply hc_ni
            rw [this]; exact ⟨0, by ring⟩
          field_simp
  have hα_ni : α ∉ (algebraMap R L).range := by
    rintro ⟨r, hr⟩
    apply hy_ni
    refine ⟨r * s, ?_⟩
    rw [map_mul]
    -- y = α * sL
    have hy_eq : y = α * sL := by
      show y = (y * sL⁻¹) * sL
      rw [mul_assoc, inv_mul_cancel₀ hsL_ne, mul_one]
    rw [hy_eq, ← hr]
    show (algebraMap R L) r * sL = (algebraMap R L) r * sL
    rfl
  have hαI : IsIntegral R α := .of_finite R α
  -- Step 8: show minpoly R α = X^2 + 1.
  have hmin : minpoly R α = Polynomial.X ^ 2 + Polynomial.C (1 : R) := by
    set g : Polynomial R := Polynomial.X ^ 2 + Polynomial.C (1 : R) with hg_def
    have hgm : g.Monic := Polynomial.monic_X_pow_add_C (1 : R) (by norm_num : (2 : ℕ) ≠ 0)
    have hgroot : Polynomial.aeval α g = 0 := by
      show Polynomial.aeval α (Polynomial.X ^ 2 + Polynomial.C (1 : R)) = 0
      simp [hα_sq]
    have hdα : (minpoly R α).natDegree = 2 := by
      have h2α : 2 ≤ (minpoly R α).natDegree :=
        (minpoly.two_le_natDegree_iff hαI).mpr hα_ni
      have hαle : (minpoly R α).natDegree ≤ Module.finrank R L := minpoly.natDegree_le α
      omega
    have hgdeg : g.natDegree = 2 := by
      show (Polynomial.X ^ 2 + Polynomial.C (1 : R)).natDegree = 2
      exact Polynomial.natDegree_X_pow_add_C
    refine minpoly.unique_of_degree_le_degree_minpoly R α hgm hgroot ?_
    rw [Polynomial.degree_eq_natDegree hgm.ne_zero,
        Polynomial.degree_eq_natDegree (minpoly.ne_zero hαI), hgdeg, hdα]
    -- 2 ≤ 2 in WithBot ℕ
    exact le_refl _
  -- Step 9: build PowerBasis (gen := α, dim := 2).
  have hli : LinearIndependent R ![(1 : L), α] := by
    rw [LinearIndependent.pair_iff]
    intro r t hrt
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hrt
    -- hrt : r • 1 + t • α = 0.
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hrt
      rw [Algebra.smul_def, mul_one] at hrt
      exact ⟨(map_eq_zero_iff _ hInj).mp hrt, rfl⟩
    · exfalso
      apply hα_ni
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hrt
      -- hrt : algebraMap r + algebraMap t * α = 0
      have htL : (algebraMap R L) t ≠ 0 := (map_ne_zero_iff _ hInj).mpr ht
      -- α = - algebraMap r / algebraMap t
      refine ⟨-r / t, ?_⟩
      rw [map_div₀, map_neg]
      field_simp
      linear_combination -hrt
  have hcard : Fintype.card (Fin 2) = Module.finrank R L := by
    rw [Fintype.card_fin, hL]
  let basis2 : Basis (Fin 2) R L := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbasis_eq : ∀ i : Fin 2, basis2 i = α ^ (i : ℕ) := by
    intro i
    show basisOfLinearIndependentOfCardEqFinrank hli hcard i = α ^ (i : ℕ)
    rw [coe_basisOfLinearIndependentOfCardEqFinrank hli hcard]
    match i with
    | ⟨0, _⟩ => simp
    | ⟨1, _⟩ => simp
  refine ⟨{ gen := α, dim := 2, basis := basis2, basis_eq_pow := hbasis_eq }, ?_⟩
  exact hmin

/-- `R(i)` has no quadratic extension: equivalently, every element of any quadratic
extension `K` of `R` is a square in `K`. -/
theorem isSquare_of_finrank_base_eq_two
    (K : Type*) [Field K] [Algebra R K]
    (hK : Module.finrank R K = 2) (x : K) : IsSquare x := sorry

/-- Fundamental theorem of algebra for real closed fields: the only finite extensions
of `R` are `R` itself and the quadratic extension `R(i)`. -/
theorem finrank_le_two_of_finiteDimensional
    (K : Type*) [Field K] [Algebra R K] [FiniteDimensional R K] :
    Module.finrank R K ≤ 2 := sorry

/-- The only algebraic extensions of a real closed field `R` are `R` and `R(i)`. -/
theorem finrank_le_two_of_isAlgebraic
    (K : Type*) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K] :
    Module.finrank R K ≤ 2 := sorry

/-- A real closed field has no nontrivial real algebraic extensions. -/
theorem surjective_algebraMap_of_isAlgebraic_of_isSemireal
    (K : Type*) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K] [IsSemireal K] :
    Function.Surjective (algebraMap R K) := sorry

/-- Classification of monic irreducible polynomials over a real closed field `R`:
they are linear (`X - c`) or quadratic of the form `(X - a)^2 + b^2` with `b ≠ 0`. -/
theorem monic_irreducible_classification {f : Polynomial R} (hf : f.Monic) (hf' : Irreducible f) :
    (∃ c : R, f = Polynomial.X - Polynomial.C c) ∨
    (∃ a b : R, b ≠ 0 ∧
      f = (Polynomial.X - Polynomial.C a) ^ 2 + Polynomial.C (b ^ 2)) := sorry

end Algebraic

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- `R` has no nontrivial ordered algebraic extension: for every field `K` that is an
algebraic extension of `R` and admits a linear order making it a strictly ordered ring
with `R → K` monotone, the structure map `R → K` is surjective. -/
def NoNontrivialOrderedAlgExt : Prop :=
  ∀ (K : Type*) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K],
    (∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule R K) →
    Function.Surjective (algebraMap R K)

/-- Polynomials over `R` satisfy the intermediate value property. -/
def PolynomialIVP : Prop :=
  ∀ (f : Polynomial R) (a b : R), a ≤ b → f.eval a ≤ 0 → 0 ≤ f.eval b →
    ∃ c ∈ Set.Icc a b, f.IsRoot c

/-- Polynomials over a real closed ordered field satisfy the intermediate value property. -/
theorem polynomialIVP_of_isRealClosed [IsRealClosed R] : PolynomialIVP R := sorry

/-- An ordered field whose polynomials satisfy the intermediate value property is real closed. -/
theorem isRealClosed_of_polynomialIVP (h : PolynomialIVP R) : IsRealClosed R := sorry

/-- A real closed ordered field has no nontrivial ordered algebraic extensions. -/
theorem noNontrivialOrderedAlgExt_of_isRealClosed [IsRealClosed R] :
    NoNontrivialOrderedAlgExt R := sorry

/-- An ordered field with no nontrivial ordered algebraic extensions is real closed. -/
theorem isRealClosed_of_noNontrivialOrderedAlgExt (h : NoNontrivialOrderedAlgExt R) :
    IsRealClosed R := sorry

/-- For an ordered field `R`, the following are equivalent:
1. `R` is real closed.
2. `R` is maximal with respect to ordered algebraic extensions.
3. Polynomials over `R` satisfy the intermediate value property. -/
theorem tfae_of_linearOrderedField :
    List.TFAE
      [ IsRealClosed R,
        NoNontrivialOrderedAlgExt R,
        PolynomialIVP R ] := by
  tfae_have 1 → 2 := fun _ ↦ noNontrivialOrderedAlgExt_of_isRealClosed R
  tfae_have 2 → 1 := isRealClosed_of_noNontrivialOrderedAlgExt R
  tfae_have 1 → 3 := fun _ ↦ polynomialIVP_of_isRealClosed R
  tfae_have 3 → 1 := isRealClosed_of_polynomialIVP R
  tfae_finish

end IsRealClosed
