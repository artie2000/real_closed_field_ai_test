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
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.RingTheory.Algebraic.Basic
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
theorem isSquare_of_isSumSq {x : R} (hx : IsSumSq x) : IsSquare x := by
  rcases isSquare_or_isSquare_neg x with h | h
  · exact h
  · by_cases hx0 : x = 0
    · subst hx0
      exact IsSquare.zero
    · exfalso
      apply IsSemireal.not_isSumSq_neg_one R
      have hneg1 : (-1 : R) = (-x) * x⁻¹ := by
        rw [neg_mul, mul_inv_cancel₀ hx0]
      rw [hneg1]
      have hinv : IsSumSq (x⁻¹) := by
        have hxinv2 : IsSumSq (x⁻¹ * x⁻¹) := IsSumSq.mul_self _
        have heq : x⁻¹ = (x⁻¹ * x⁻¹) * x := by
          rw [mul_assoc, inv_mul_cancel₀ hx0, mul_one]
        rw [heq]
        exact IsSumSq.mul hxinv2 hx
      exact IsSumSq.mul h.isSumSq hinv

/-- There is no nontrivial odd-degree finite extension of a real closed field `R`:
any finite extension `K/R` with `Module.finrank R K` odd has `R → K` surjective. -/
theorem surjective_algebraMap_of_odd_finrank
    (K : Type*) [Field K] [Algebra R K] [FiniteDimensional R K]
    (hodd : Odd (Module.finrank R K)) :
    Function.Surjective (algebraMap R K) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element R K
  have hint : IsIntegral R α := .of_finite R α
  have hirr : Irreducible (minpoly R α) := minpoly.irreducible hint
  have hdeg : (minpoly R α).natDegree = Module.finrank R K :=
    (Field.primitive_element_iff_minpoly_natDegree_eq R α).mp hα
  rw [← hdeg] at hodd
  obtain ⟨r, hr⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree hodd
  have hdeg1 : (minpoly R α).natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (Polynomial.degree_eq_one_of_irreducible_of_root hirr hr)
  have hfin1 : Module.finrank R K = 1 := by omega
  intro x
  have hbot : (⊥ : Subalgebra R K) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one hfin1
  have hx : x ∈ (⊥ : Subalgebra R K) := by rw [hbot]; exact Algebra.mem_top
  exact Algebra.mem_bot.mp hx

/-- `R(i)` is the unique quadratic extension of a real closed field `R` (up to `R`-isomorphism):
any quadratic extension of `R` is `R`-isomorphic to any other quadratic extension of `R`. -/
theorem nonempty_algEquiv_of_finrank_eq_two
    (K K' : Type*) [Field K] [Algebra R K] [Field K'] [Algebra R K']
    (hK : Module.finrank R K = 2) (hK' : Module.finrank R K' = 2) :
    Nonempty (K ≃ₐ[R] K') := sorry

/-- Helper: in a real closed field `R`, with `t² = a² + b²`, at least one of
`(a+t)/2` and `(a-t)/2` is a square. -/
private lemma isSquare_or_isSquare_half_sum_or_diff_sqrt
    (a b t : R) (ht : t ^ 2 = a ^ 2 + b ^ 2) (hb : b ≠ 0) :
    IsSquare ((a + t) / 2) ∨ IsSquare ((a - t) / 2) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  obtain ⟨p, hp⟩ := isSquare_neg_of_not_isSquare hn1
  obtain ⟨q, hq⟩ := isSquare_neg_of_not_isSquare hn2
  -- -((a+t)/2) = p*p and -((a-t)/2) = q*q, so (p*q)² = (a+t)(a-t)/4 = -b²/4.
  have hprod : (p * q) ^ 2 = -(b ^ 2) / 4 := by
    have key : (p * p) * (q * q) = -((a + t) / 2) * -((a - t) / 2) := by
      rw [← hp, ← hq]
    have h2 : -((a + t) / 2) * -((a - t) / 2) = (a ^ 2 - t ^ 2) / 4 := by ring
    have h3 : (a ^ 2 - t ^ 2) / 4 = -(b ^ 2) / 4 := by rw [ht]; ring
    nlinarith [key, h2, h3]
  -- From (p*q)² = -b²/4 and b ≠ 0, deduce IsSumSq (-1) contradicting IsSemireal.
  apply IsSemireal.not_isSumSq_neg_one R
  have hb_half_ne : b / 2 ≠ 0 := by
    intro hh; apply hb; linarith [(by linarith : (2 : R) * (b/2) = b)]
  have hinv : (-1 : R) = (p * q / (b / 2)) ^ 2 + 0 := by
    have : (p * q / (b / 2)) ^ 2 = (p * q) ^ 2 / (b / 2) ^ 2 := by
      rw [div_pow]
    rw [this, hprod, add_zero]
    have h2 : (b / 2) ^ 2 = b ^ 2 / 4 := by ring
    rw [h2]
    have hb2_ne : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
    have hb2_4_ne : b ^ 2 / 4 ≠ 0 := by
      intro hh
      apply hb2_ne
      linarith [(by linarith : (4 : R) * (b ^ 2 / 4) = b ^ 2)]
    field_simp
  rw [hinv]
  exact .sq _ |>.isSumSq.add .zero

/-- `R(i)` has no quadratic extension: equivalently, every element of any quadratic
extension `K` of `R` is a square in `K`. -/
theorem isSquare_of_finrank_base_eq_two
    (K : Type*) [Field K] [Algebra R K]
    (hK : Module.finrank R K = 2) (x : K) : IsSquare x := by
  haveI : FiniteDimensional R K := Module.finite_of_finrank_eq_succ hK
  -- Get a primitive element α.
  obtain ⟨α, hα⟩ := Field.exists_primitive_element R K
  have hint : IsIntegral R α := .of_finite R α
  have halg : IsAlgebraic R α := hint.isAlgebraic
  have hαtop : Algebra.adjoin R ({α} : Set K) = ⊤ := by
    rw [← (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic halg).mp hα]
    exact (IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg).symm
  have hdeg : (minpoly R α).natDegree = 2 := by
    rw [(Field.primitive_element_iff_minpoly_natDegree_eq R α).mp hα, hK]
  -- α is not in the image of algebraMap R K.
  have hα_notin : α ∉ (algebraMap R K).range := by
    intro h
    have : (minpoly R α).natDegree = 1 := (minpoly.natDegree_eq_one_iff).mpr h
    omega
  -- Extract the minpoly and its coefficients.
  set p := minpoly R α with hp_def
  have hp_monic : p.Monic := minpoly.monic hint
  set c₀ : R := p.coeff 0 with hc₀_def
  set c₁ : R := p.coeff 1 with hc₁_def
  have hp_deg2 : p = Polynomial.X ^ 2 + Polynomial.C c₁ * Polynomial.X + Polynomial.C c₀ := by
    -- p is monic of natDegree 2
    have h_as_sum : p = ∑ i ∈ Finset.range (p.natDegree + 1), Polynomial.C (p.coeff i) *
                          Polynomial.X ^ i := Polynomial.as_sum_range_C_mul_X_pow p
    rw [hdeg] at h_as_sum
    -- sum over Fin 3 = 0, 1, 2
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add] at h_as_sum
    -- coeff p 2 = leading = 1 since monic
    have h_lead : p.coeff 2 = 1 := by
      rw [show (2 : ℕ) = p.natDegree from hdeg.symm]
      exact hp_monic.coeff_natDegree
    rw [h_lead] at h_as_sum
    simp [pow_succ] at h_as_sum
    rw [h_as_sum]; ring
  have hαrel : α ^ 2 + algebraMap R K c₁ * α + algebraMap R K c₀ = 0 := by
    have h := minpoly.aeval R α
    rw [← hp_def, hp_deg2] at h
    simp [Polynomial.aeval_def, Polynomial.eval₂_add, Polynomial.eval₂_mul,
          Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X] at h
    linarith [h]
  -- β = α + c₁/2 and β² = d := c₁²/4 - c₀.
  set d : R := c₁ ^ 2 / 4 - c₀ with hd_def
  set β : K := α + algebraMap R K (c₁ / 2) with hβ_def
  have hβsq : β ^ 2 = algebraMap R K d := by
    rw [hβ_def, hd_def]
    have : (α + algebraMap R K (c₁ / 2)) ^ 2
         = α ^ 2 + algebraMap R K c₁ * α + algebraMap R K c₁ ^ 2 / 4 := by
      have h2 : algebraMap R K (c₁ / 2) = algebraMap R K c₁ / 2 := by
        rw [map_div₀]; simp
      rw [h2]; ring
    rw [this]
    have : α ^ 2 + algebraMap R K c₁ * α = -algebraMap R K c₀ := by linarith
    rw [this]
    have : algebraMap R K (c₁ ^ 2 / 4 - c₀) = algebraMap R K c₁ ^ 2 / 4 - algebraMap R K c₀ := by
      rw [map_sub, map_div₀, map_pow]; simp
    rw [this]; ring
  -- d is not a square in R.
  have hd_not_sq : ¬ IsSquare d := by
    rintro ⟨t, ht⟩
    -- β² = t² in K, so (β - t)(β + t) = 0.
    have hβt : (β - algebraMap R K t) * (β + algebraMap R K t) = 0 := by
      have expand : (β - algebraMap R K t) * (β + algebraMap R K t)
                  = β ^ 2 - (algebraMap R K t) ^ 2 := by ring
      rw [expand, hβsq]
      have : (algebraMap R K t) ^ 2 = algebraMap R K (t * t) := by rw [map_mul]; ring
      rw [this]
      rw [show t * t = d from ht.symm]
      ring
    rcases mul_eq_zero.mp hβt with h | h
    · have : β = algebraMap R K t := by linarith
      -- β = t, so α = t - c₁/2 ∈ range
      have hα_range : α = algebraMap R K (t - c₁ / 2) := by
        have := this
        rw [hβ_def] at this
        have hh : α = algebraMap R K t - algebraMap R K (c₁ / 2) := by linarith
        rw [hh, ← map_sub]
      exact hα_notin ⟨_, hα_range.symm⟩
    · have : β = -algebraMap R K t := by linarith
      have hα_range : α = algebraMap R K (-t - c₁ / 2) := by
        rw [hβ_def] at this
        have hh : α = -algebraMap R K t - algebraMap R K (c₁ / 2) := by linarith
        rw [hh]
        rw [← map_neg, ← map_sub]
      exact hα_notin ⟨_, hα_range.symm⟩
  -- So -d is a square: -d = u².
  obtain ⟨u, hu⟩ : IsSquare (-d) := isSquare_neg_of_not_isSquare hd_not_sq
  have hu_ne : u ≠ 0 := by
    rintro rfl
    apply hd_not_sq
    exact ⟨0, by rw [mul_zero] at hu; linarith⟩
  have hu_sq : u * u = -d := hu.symm
  -- Now decompose x = a + b·β using PowerBasis.
  let PB : PowerBasis R K := PowerBasis.ofAdjoinEqTop hint hαtop
  have hPBdim : PB.dim = 2 := hdeg
  -- Use a basis for K over R of {1, α}.
  -- The equivFun gives (Fin 2 → R).
  have hxrepr : ∃ a b : R, x = algebraMap R K a + algebraMap R K b * α := by
    have hbasis := PB.basis.sum_repr x
    have : PB.dim = 2 := hdeg
    -- rewrite sum over Fin PB.dim
    refine ⟨PB.basis.repr x ⟨0, by omega⟩, PB.basis.repr x ⟨1, by omega⟩, ?_⟩
    rw [show α = PB.gen from rfl]
    -- Unfold the sum
    have h0 : PB.basis ⟨0, by rw [this]; omega⟩ = PB.gen ^ (0 : ℕ) := PB.basis_eq_pow _
    have h1 : PB.basis ⟨1, by rw [this]; omega⟩ = PB.gen ^ (1 : ℕ) := PB.basis_eq_pow _
    have hfin : Finset.univ (α := Fin PB.dim) =
                (Finset.univ.image (Fin.cast this.symm)) := by
      ext ⟨i, hi⟩; simp
    sorry
  sorry

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

namespace polynomialIVP_aux

open Polynomial

/-- Helper: for a polynomial `f` with positive leading coefficient, odd `natDegree = n ≥ 1`,
there exists `M > 0` with `f.eval M > 0` and `f.eval (-M) < 0`. -/
private lemma exists_sign_change
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (f : Polynomial R) {n : ℕ} (hn : f.natDegree = n) (hn1 : 1 ≤ n) (hodd : Odd n)
    (hlc : 0 < f.leadingCoeff) :
    ∃ M : R, 0 < M ∧ f.eval (-M) < 0 ∧ 0 < f.eval M := by
  set B := ∑ i ∈ Finset.range n, |f.coeff i| with hB_def
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  set M : R := 1 + B / f.leadingCoeff with hM_def
  have hBdiv : 0 ≤ B / f.leadingCoeff := div_nonneg hB hlc.le
  have hMpos : 0 < M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hM0 : (0 : R) ≤ M := hMpos.le
  have hne : f.leadingCoeff ≠ 0 := ne_of_gt hlc
  have hkey : f.leadingCoeff * M - B = f.leadingCoeff := by
    have hMexpand : f.leadingCoeff * M = f.leadingCoeff + B := by
      rw [hM_def, mul_add, mul_one, mul_div_cancel₀ B hne]
    linarith
  have hMpow_pos : (0 : R) < M ^ (n - 1) := pow_pos hMpos _
  have hMpow_ge_one : (1 : R) ≤ M ^ (n - 1) := one_le_pow₀ hM1
  have hn_split : n = (n - 1) + 1 := by omega
  have hMn_eq : M ^ n = M ^ (n - 1) * M := by
    conv_lhs => rw [hn_split]
    exact pow_succ M (n - 1)
  have hlc_eq : f.coeff n = f.leadingCoeff := by rw [← hn]; rfl
  have heval_general : ∀ x : R, f.eval x =
      f.leadingCoeff * x ^ n + ∑ i ∈ Finset.range n, f.coeff i * x ^ i := by
    intro x
    have h1 : f.eval x = ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i * x ^ i :=
      eval_eq_sum_range x
    rw [h1, hn, Finset.sum_range_succ, hlc_eq]
    exact add_comm _ _
  have heval_M := heval_general M
  have heval_negM := heval_general (-M)
  have htail_M : |∑ i ∈ Finset.range n, f.coeff i * M ^ i| ≤ B * M ^ (n - 1) := by
    calc |∑ i ∈ Finset.range n, f.coeff i * M ^ i|
        ≤ ∑ i ∈ Finset.range n, |f.coeff i * M ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range n, |f.coeff i| * M ^ i := by
            refine Finset.sum_congr rfl (fun i _ ↦ ?_)
            rw [abs_mul, abs_of_nonneg (pow_nonneg hM0 i)]
      _ ≤ ∑ i ∈ Finset.range n, |f.coeff i| * M ^ (n - 1) := by
            refine Finset.sum_le_sum (fun i hi ↦ ?_)
            rw [Finset.mem_range] at hi
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact pow_le_pow_right₀ hM1 (by omega)
      _ = B * M ^ (n - 1) := by rw [← Finset.sum_mul]
  have htail_negM : |∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i| ≤ B * M ^ (n - 1) := by
    calc |∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i|
        ≤ ∑ i ∈ Finset.range n, |f.coeff i * (-M) ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range n, |f.coeff i| * M ^ i := by
            refine Finset.sum_congr rfl (fun i _ ↦ ?_)
            rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg hM0]
      _ ≤ ∑ i ∈ Finset.range n, |f.coeff i| * M ^ (n - 1) := by
            refine Finset.sum_le_sum (fun i hi ↦ ?_)
            rw [Finset.mem_range] at hi
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact pow_le_pow_right₀ hM1 (by omega)
      _ = B * M ^ (n - 1) := by rw [← Finset.sum_mul]
  have hneg_pow : (-M) ^ n = -M ^ n := Odd.neg_pow hodd M
  refine ⟨M, hMpos, ?_, ?_⟩
  · rw [heval_negM, hneg_pow, hMn_eq]
    have htail_upper : ∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i ≤ B * M ^ (n - 1) := by
      have := htail_negM
      rw [abs_le] at this
      exact this.2
    have hcompute :
        f.leadingCoeff * -(M ^ (n - 1) * M) + B * M ^ (n - 1)
          = -(M ^ (n - 1) * f.leadingCoeff) := by
      have h1 : f.leadingCoeff * -(M ^ (n - 1) * M) + B * M ^ (n - 1)
             = -M ^ (n - 1) * (f.leadingCoeff * M - B) := by ring
      rw [h1, hkey]; ring
    have hbound :
        f.leadingCoeff * -(M ^ (n - 1) * M) + ∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i
          ≤ -(M ^ (n - 1) * f.leadingCoeff) := by
      calc
        f.leadingCoeff * -(M ^ (n - 1) * M) + ∑ i ∈ Finset.range n, f.coeff i * (-M) ^ i
            ≤ f.leadingCoeff * -(M ^ (n - 1) * M) + B * M ^ (n - 1) := by linarith
        _ = -(M ^ (n - 1) * f.leadingCoeff) := hcompute
    have : 0 < M ^ (n - 1) * f.leadingCoeff := mul_pos hMpow_pos hlc
    linarith
  · rw [heval_M, hMn_eq]
    have htail_lower : -(B * M ^ (n - 1)) ≤ ∑ i ∈ Finset.range n, f.coeff i * M ^ i := by
      have := htail_M
      rw [abs_le] at this
      linarith
    have hcompute :
        f.leadingCoeff * (M ^ (n - 1) * M) - B * M ^ (n - 1)
          = M ^ (n - 1) * f.leadingCoeff := by
      have h1 : f.leadingCoeff * (M ^ (n - 1) * M) - B * M ^ (n - 1)
             = M ^ (n - 1) * (f.leadingCoeff * M - B) := by ring
      rw [h1, hkey]
    have hbound :
        M ^ (n - 1) * f.leadingCoeff
          ≤ f.leadingCoeff * (M ^ (n - 1) * M) + ∑ i ∈ Finset.range n, f.coeff i * M ^ i := by
      calc M ^ (n - 1) * f.leadingCoeff
          = f.leadingCoeff * (M ^ (n - 1) * M) - B * M ^ (n - 1) := hcompute.symm
        _ ≤ f.leadingCoeff * (M ^ (n - 1) * M) + ∑ i ∈ Finset.range n, f.coeff i * M ^ i := by
            linarith
    have : 0 < M ^ (n - 1) * f.leadingCoeff := mul_pos hMpow_pos hlc
    linarith

end polynomialIVP_aux

/-- An ordered field whose polynomials satisfy the intermediate value property is real closed. -/
theorem isRealClosed_of_polynomialIVP (h : PolynomialIVP R) : IsRealClosed R := by
  refine IsRealClosed.of_linearOrderedField (R := R) ?_ ?_
  · intro a ha
    have h0 : (0 : R) ≤ a + 1 := by linarith
    have heval_0 : (Polynomial.X ^ 2 - Polynomial.C a).eval 0 ≤ 0 := by
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      nlinarith
    have heval_1 : 0 ≤ (Polynomial.X ^ 2 - Polynomial.C a).eval (a + 1) := by
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      nlinarith
    obtain ⟨c, _, hc_root⟩ :=
      h (Polynomial.X ^ 2 - Polynomial.C a) 0 (a + 1) h0 heval_0 heval_1
    have hc_eval : (Polynomial.X ^ 2 - Polynomial.C a).eval c = 0 := hc_root
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        sub_eq_zero] at hc_eval
    exact ⟨c, by rw [← sq]; exact hc_eval.symm⟩
  · intro f hodd
    set n := f.natDegree with hn_def
    have hn1 : 1 ≤ n := by
      rcases hodd with ⟨k, hk⟩
      omega
    have hf_ne : f ≠ 0 := by
      intro hfz
      rw [hfz, Polynomial.natDegree_zero] at hn_def
      omega
    by_cases hlc_pos : 0 < f.leadingCoeff
    · obtain ⟨M, hMpos, hMneg_eval, hMpos_eval⟩ :=
        polynomialIVP_aux.exists_sign_change (R := R) f hn_def.symm hn1 hodd hlc_pos
      obtain ⟨c, _, hc_root⟩ :=
        h f (-M) M (by linarith) hMneg_eval.le hMpos_eval.le
      exact ⟨c, hc_root⟩
    · rw [not_lt] at hlc_pos
      have hlc_ne : f.leadingCoeff ≠ 0 := by
        rw [Ne, Polynomial.leadingCoeff_eq_zero]
        exact hf_ne
      have hlc_neg : f.leadingCoeff < 0 := lt_of_le_of_ne hlc_pos hlc_ne
      have hndeg : (-f).natDegree = n := by rw [Polynomial.natDegree_neg, ← hn_def]
      have hlc' : 0 < (-f).leadingCoeff := by
        rw [Polynomial.leadingCoeff_neg]; linarith
      obtain ⟨M, hMpos, hMneg_eval, hMpos_eval⟩ :=
        polynomialIVP_aux.exists_sign_change (R := R) (-f) hndeg hn1 hodd hlc'
      obtain ⟨c, _, hc_root⟩ :=
        h (-f) (-M) M (by linarith) hMneg_eval.le hMpos_eval.le
      refine ⟨c, ?_⟩
      have : (-f).eval c = 0 := hc_root
      rw [Polynomial.eval_neg, neg_eq_zero] at this
      exact this

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
