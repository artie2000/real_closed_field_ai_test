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
  -- We show: for any quadratic extension K there is a PowerBasis with gen α where α^2 = -1.
  -- Then two such power bases have the same minimal polynomial and induce an iso.
  have mkPB : ∀ (K : Type*) [Field K] [Algebra R K], Module.finrank R K = 2 →
      ∃ pb : PowerBasis R K, pb.gen ^ 2 = -1 ∧ minpoly R pb.gen =
        Polynomial.X ^ 2 + Polynomial.C (1 : R) := by
    intro K _ _ hK
    have hFin : FiniteDimensional R K := .of_finrank_eq_succ hK
    -- Step 1: find an element not in the image of algebraMap R K.
    have hne : ∃ x : K, x ∉ (algebraMap R K).range := by
      by_contra h
      push_neg at h
      have hTop : (⊥ : Subalgebra R K) = ⊤ := by
        apply Subalgebra.toSubmodule_injective
        apply Submodule.eq_top_iff'.mpr
        intro x
        obtain ⟨r, hr⟩ := h x
        rw [← hr]
        exact Algebra.mem_bot.mpr ⟨r, rfl⟩
      have heq : Module.finrank R (⊥ : Subalgebra R K) = Module.finrank R K := by
        rw [hTop]
        exact Subalgebra.topEquiv.toLinearEquiv.finrank_eq
      rw [Subalgebra.finrank_bot] at heq
      omega
    obtain ⟨x, hx⟩ := hne
    have hxI : IsIntegral R x := .of_finite R x
    have hdeg2 : (minpoly R x).natDegree = 2 := by
      have h2 : 2 ≤ (minpoly R x).natDegree := (minpoly.two_le_natDegree_iff hxI).mpr hx
      have hle : (minpoly R x).natDegree ≤ Module.finrank R K := minpoly.natDegree_le x
      omega
    -- Extract coefficients: minpoly R x = X^2 + C a X + C b for some a, b ∈ R.
    set f := minpoly R x with hf_def
    have hfm : f.Monic := minpoly.monic hxI
    have hfa : Polynomial.aeval x f = 0 := minpoly.aeval R x
    set a := f.coeff 1 with ha_def
    set b := f.coeff 0 with hb_def
    have hf_eq : f = Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b := by
      apply Polynomial.ext
      intro n
      match n with
      | 0 => simp [ha_def, hb_def]
      | 1 => simp [ha_def, hb_def]
      | 2 =>
        have h2 : f.coeff 2 = 1 := by
          have := hfm
          rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg2] at this
          exact this
        simp [h2]
      | k + 3 =>
        have h3 : f.coeff (k + 3) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          omega
        simp [h3]
    -- Since x is a root: x^2 + a * x + b = 0.
    have hroot : x ^ 2 + (algebraMap R K) a * x + (algebraMap R K) b = 0 := by
      have := hfa
      rw [hf_eq] at this
      simp [Polynomial.aeval_def, Polynomial.eval₂_add, Polynomial.eval₂_mul,
            Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] at this
      linear_combination this
    -- Let α := x + a/2. Completing the square: α^2 = a^2/4 - b = c.
    have h2 : (2 : R) ≠ 0 := two_ne_zero
    set y : K := x + (algebraMap R K) (a / 2)
    set c : R := a ^ 2 / 4 - b
    have hy_sq : y ^ 2 = (algebraMap R K) c := by
      have hKchar : (2 : K) ≠ 0 := by
        intro h
        apply h2
        have hi : Function.Injective (algebraMap R K) := (algebraMap R K).injective
        apply hi
        simp [h]
      -- y^2 = x^2 + 2 x (a/2) + (a/2)^2 = x^2 + a x + a^2/4
      -- from hroot: x^2 + a x = -b
      -- so y^2 = -b + a^2/4 = a^2/4 - b = c
      have : y ^ 2 = x ^ 2 + (algebraMap R K) a * x + (algebraMap R K) (a^2 / 4) := by
        simp only [y]
        have : (algebraMap R K) (a / 2) * 2 = (algebraMap R K) a := by
          rw [← map_ofNat (algebraMap R K) 2, ← map_mul]
          congr 1
          field_simp
        ring_nf
        rw [show (algebraMap R K) (a / 2) * ((algebraMap R K) (a / 2) + x * 2) =
                (algebraMap R K) (a / 2) * (algebraMap R K) (a / 2) +
                  (algebraMap R K) (a / 2) * 2 * x by ring, this]
        rw [show (algebraMap R K) (a / 2) * (algebraMap R K) (a / 2) =
                (algebraMap R K) (a^2/4) by
              rw [← map_mul]; congr 1; field_simp; ring]
        ring
      rw [this]
      have : x ^ 2 + (algebraMap R K) a * x = -(algebraMap R K) b := by linear_combination hroot
      rw [this]
      simp only [c]
      rw [map_sub, neg_add_eq_sub]
      ring
    -- Now y ∉ range algebraMap (since y = x + (a/2) and x ∉ range).
    have hy_ni : y ∉ (algebraMap R K).range := by
      intro ⟨r, hr⟩
      apply hx
      refine ⟨r - a/2, ?_⟩
      simp only [y] at hr
      rw [map_sub]
      linear_combination hr
    -- So c is not a square in R (else y = ±√c ∈ R).
    have hc_ni : ¬ IsSquare c := by
      intro ⟨s, hs⟩
      -- s * s = c, so (algebraMap R K s)^2 = algebraMap c = y^2 => (y - algMap s)(y + algMap s) = 0
      apply hy_ni
      have halg : ((algebraMap R K) s) ^ 2 = y ^ 2 := by
        rw [hy_sq]
        rw [show c = s * s from hs]
        rw [map_mul]; ring
      have : (y - (algebraMap R K) s) * (y + (algebraMap R K) s) = 0 := by
        ring_nf
        linear_combination -halg
      rcases mul_eq_zero.mp this with h | h
      · refine ⟨s, ?_⟩; linarith [sub_eq_zero.mp h]
      · refine ⟨-s, ?_⟩; rw [map_neg]; linear_combination -(add_eq_zero_iff_eq_neg.mp h)
    -- By RCF axiom: -c is a square.
    have hnc_sq : IsSquare (-c) := by
      rcases IsRealClosed.isSquare_or_isSquare_neg c with h | h
      · exact absurd h hc_ni
      · exact h
    obtain ⟨s, hs⟩ := hnc_sq
    -- s ≠ 0 since otherwise c = 0 which is a square.
    have hs_ne : s ≠ 0 := by
      intro h
      apply hc_ni
      rw [h] at hs
      have : -c = 0 := by rw [hs]; ring
      rw [show c = 0 by linarith]
      exact ⟨0, by ring⟩
    have hsK_ne : (algebraMap R K) s ≠ 0 := by
      rw [map_ne_zero_iff _ (algebraMap R K).injective]
      exact hs_ne
    -- Let α = y / s in K. Then α^2 = -1.
    set α := y * (algebraMap R K) s⁻¹ with hα_def
    have hα_sq : α ^ 2 = -1 := by
      simp only [α]
      rw [mul_pow, hy_sq, ← map_pow, ← map_mul]
      have hcs : c * (s⁻¹)^2 = -1 := by
        have : s * s = -c := hs
        have hsne : s^2 ≠ 0 := pow_ne_zero _ hs_ne
        have : s^2 = -c := by rw [sq]; exact hs
        field_simp
        linear_combination this
      rw [hcs]
      simp
    -- α ∉ range (algebraMap R K) either, because if α = algMap r, then y = algMap (r*s).
    have hα_ni : α ∉ (algebraMap R K).range := by
      intro ⟨r, hr⟩
      apply hy_ni
      refine ⟨r * s, ?_⟩
      simp only [α] at hr
      have : y = (algebraMap R K) s * α := by
        rw [hα_def]
        rw [mul_comm ((algebraMap R K) s) _]
        rw [mul_assoc]
        rw [← map_mul]
        rw [inv_mul_cancel₀ hs_ne]
        simp
      rw [this, ← hr, map_mul]
      ring
    -- minpoly R α = X^2 + 1.
    have hαI : IsIntegral R α := .of_finite R α
    have hmin : minpoly R α = Polynomial.X ^ 2 + Polynomial.C (1 : R) := by
      -- α satisfies g = X^2 + 1, which is monic of degree 2.
      set g : Polynomial R := Polynomial.X ^ 2 + Polynomial.C (1 : R)
      have hgm : g.Monic := by
        apply Polynomial.monic_X_pow_add_C (1 : R) (by norm_num)
      have hgroot : Polynomial.aeval α g = 0 := by
        simp [g, hα_sq]
      have hdα : (minpoly R α).natDegree = 2 := by
        have h2α : 2 ≤ (minpoly R α).natDegree := by
          apply (minpoly.two_le_natDegree_iff hαI).mpr hα_ni
        have hαle : (minpoly R α).natDegree ≤ Module.finrank R K := minpoly.natDegree_le α
        omega
      refine minpoly.unique_of_degree_le_degree_minpoly R α hgm hgroot ?_
      have hgdeg : g.natDegree = 2 := by
        show (Polynomial.X ^ 2 + Polynomial.C (1 : R)).natDegree = 2
        exact Polynomial.natDegree_X_pow_add_C
      rw [Polynomial.degree_eq_natDegree hgm.ne_zero,
          Polynomial.degree_eq_natDegree (minpoly.ne_zero hαI), hgdeg, hdα]
    -- Now construct PowerBasis using {1, α} as a basis.
    have hli : LinearIndependent R ![(1 : K), α] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      -- s * 1 + t * α = 0  ⇒ s = 0 ∧ t = 0
      -- If t = 0, then s = 0. If t ≠ 0, then α = -s/t ∈ R, contradiction.
      by_cases ht : t = 0
      · rw [ht] at hst
        simp at hst
        -- s • 1 = 0 → s = 0
        have : (algebraMap R K) s = 0 := by
          simp [Algebra.smul_def] at hst
          exact hst
        rw [map_eq_zero_iff _ (algebraMap R K).injective] at this
        exact ⟨this, ht⟩
      · exfalso
        apply hα_ni
        refine ⟨-(s / t), ?_⟩
        have htK : (algebraMap R K) t ≠ 0 :=
          (map_ne_zero_iff _ (algebraMap R K).injective).mpr ht
        rw [map_neg, map_div₀]
        field_simp
        rw [eq_neg_iff_add_eq_zero]
        simp [Algebra.smul_def] at hst
        linear_combination hst
    have hcard : Fintype.card (Fin 2) = Module.finrank R K := by
      rw [Fintype.card_fin, hK]
    let basis : Basis (Fin 2) R K := basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hbasis_eq : ∀ i, basis i = α ^ (i : ℕ) := by
      intro i
      rw [coe_basisOfLinearIndependentOfCardEqFinrank]
      match i with
      | ⟨0, _⟩ => simp
      | ⟨1, _⟩ => simp
    let pb : PowerBasis R K :=
      { gen := α, dim := 2, basis := basis, basis_eq_pow := hbasis_eq }
    exact ⟨pb, hα_sq, hmin⟩
  obtain ⟨pbK, hgenK, hminK⟩ := mkPB K hK
  obtain ⟨pbK', hgenK', hminK'⟩ := mkPB K' hK'
  have : minpoly R pbK.gen = minpoly R pbK'.gen := by rw [hminK, hminK']
  exact ⟨pbK.equivOfMinpoly pbK' this⟩

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
