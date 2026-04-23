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

/-- In a real closed field `R`, `-1` is not a square. -/
private lemma neg_one_not_isSquare : ¬ IsSquare (-1 : R) := by
  intro h
  exact IsSemireal.not_isSumSq_neg_one R h.isSumSq

/-- Helper: in `R` real closed, if `t² = a² + b²` with `b ≠ 0`, then one of `(a+t)/2` or
`(a-t)/2` is a square. -/
private lemma isSquare_half_sum_or_diff_of_sq_eq_sum_sq
    {a b t : R} (ht : t * t = a * a + b * b) (hb : b ≠ 0) :
    IsSquare ((a + t) / 2) ∨ IsSquare ((a - t) / 2) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  obtain ⟨p, hp⟩ := isSquare_neg_of_not_isSquare hn1
  obtain ⟨q, hq⟩ := isSquare_neg_of_not_isSquare hn2
  -- -((a+t)/2) = p*p, -((a-t)/2) = q*q. So (p*p)(q*q) = -b²/4.
  have hprod : (p * q) * (p * q) = -(b * b) / 4 := by
    have h1 : (p * p) * (q * q) = -((a + t) / 2) * -((a - t) / 2) := by rw [← hp, ← hq]
    have h2 : -((a + t) / 2) * -((a - t) / 2) = (a * a - t * t) / 4 := by ring
    have h3 : (a * a - t * t) / 4 = -(b * b) / 4 := by rw [ht]; ring
    calc (p * q) * (p * q) = (p * p) * (q * q) := by ring
      _ = -((a + t) / 2) * -((a - t) / 2) := h1
      _ = (a * a - t * t) / 4 := h2
      _ = -(b * b) / 4 := h3
  -- So -1 = (2(p*q)/b)². Contradiction.
  apply neg_one_not_isSquare R
  refine ⟨2 * (p * q) / b, ?_⟩
  have h : (2 * (p * q) / b) * (2 * (p * q) / b) = 4 * ((p * q) * (p * q)) / (b * b) := by
    field_simp
  rw [h, hprod]
  field_simp

/-- `R(i)` has no quadratic extension: equivalently, every element of any quadratic
extension `K` of `R` is a square in `K`. -/
theorem isSquare_of_finrank_base_eq_two
    (K : Type*) [Field K] [Algebra R K]
    (hK : Module.finrank R K = 2) (x : K) : IsSquare x := by
  haveI : FiniteDimensional R K := Module.finite_of_finrank_eq_succ hK
  -- Step 1: get primitive element α with (minpoly R α).natDegree = 2.
  obtain ⟨α, hα⟩ := Field.exists_primitive_element R K
  have hint : IsIntegral R α := .of_finite R α
  have halg : IsAlgebraic R α := hint.isAlgebraic
  have hαtop : Algebra.adjoin R ({α} : Set K) = ⊤ := by
    rw [← (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic halg).mp hα]
    exact (IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg).symm
  have hdeg : (minpoly R α).natDegree = 2 := by
    rw [(Field.primitive_element_iff_minpoly_natDegree_eq R α).mp hα, hK]
  have hα_notin_range : α ∉ (algebraMap R K).range := by
    intro h
    have heq1 : (minpoly R α).natDegree = 1 := minpoly.natDegree_eq_one_iff.mpr h
    omega
  -- Step 2: coefficients of minpoly.
  set p := minpoly R α with hp_def
  have hp_monic : p.Monic := minpoly.monic hint
  set c₀ : R := p.coeff 0
  set c₁ : R := p.coeff 1
  -- Using Monic.as_sum: p = X^2 + C c₀ * X^0 + C c₁ * X^1.
  have hp_eq : p = Polynomial.X ^ 2 + Polynomial.C c₀ + Polynomial.C c₁ * Polynomial.X := by
    have h := hp_monic.as_sum
    rw [hdeg] at h
    rw [h]
    rw [show (2 : ℕ) = 1 + 1 from rfl]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        pow_zero, pow_one, mul_one]
  have hαrel : α * α + algebraMap R K c₁ * α + algebraMap R K c₀ = 0 := by
    have h := minpoly.aeval R α
    rw [← hp_def, hp_eq] at h
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h
    linarith [show α * α = α ^ 2 from by ring]
  -- Step 3: β := α + c₁/2 satisfies β² = d := c₁²/4 - c₀.
  set d : R := c₁ * c₁ / 4 - c₀ with hd_def
  set β : K := α + algebraMap R K (c₁ / 2) with hβ_def
  have hβ_sq : β * β = algebraMap R K d := by
    have hac : algebraMap R K (c₁ / 2) = algebraMap R K c₁ / 2 := by
      rw [map_div₀]; simp
    have : β * β = α * α + algebraMap R K c₁ * α + algebraMap R K c₁ * algebraMap R K c₁ / 4 := by
      rw [hβ_def, hac]; ring
    rw [this]
    have : α * α + algebraMap R K c₁ * α = -algebraMap R K c₀ := by linarith
    rw [this]
    rw [hd_def, map_sub, map_div₀, map_mul]
    simp
    ring
  -- Step 4: d is not a square in R.
  have hd_not_sq : ¬ IsSquare d := by
    rintro ⟨t, ht⟩
    -- β² = t² in K, so (β - t)(β + t) = 0.
    have hfact : (β - algebraMap R K t) * (β + algebraMap R K t) = 0 := by
      have : (β - algebraMap R K t) * (β + algebraMap R K t) = β * β - algebraMap R K (t * t) := by
        rw [map_mul]; ring
      rw [this, hβ_sq, show t * t = d from ht.symm]
      ring
    rcases mul_eq_zero.mp hfact with h | h
    · -- β = t, so α ∈ range.
      have hβ_eq : β = algebraMap R K t := by linarith
      apply hα_notin_range
      refine ⟨t - c₁ / 2, ?_⟩
      rw [map_sub, map_div₀, show (algebraMap R K 2 : K) = 2 by simp]
      rw [hβ_def] at hβ_eq
      have hac : algebraMap R K (c₁ / 2) = algebraMap R K c₁ / 2 := by
        rw [map_div₀]; simp
      rw [hac] at hβ_eq
      linarith
    · have hβ_eq : β = -algebraMap R K t := by linarith
      apply hα_notin_range
      refine ⟨-t - c₁ / 2, ?_⟩
      rw [map_sub, map_neg, map_div₀, show (algebraMap R K 2 : K) = 2 by simp]
      rw [hβ_def] at hβ_eq
      have hac : algebraMap R K (c₁ / 2) = algebraMap R K c₁ / 2 := by
        rw [map_div₀]; simp
      rw [hac] at hβ_eq
      linarith
  -- Step 5: -d is a square, so -d = u*u with u ≠ 0.
  obtain ⟨u, hu⟩ : IsSquare (-d) := isSquare_neg_of_not_isSquare hd_not_sq
  have hu_ne : u ≠ 0 := by
    rintro rfl
    apply hd_not_sq
    exact ⟨0, by rw [mul_zero] at hu; linarith⟩
  have hu_sq_neg_d : u * u = -d := hu.symm
  -- Step 6: i := β / u (in K) satisfies i² = -1.
  set i_elem : K := β / algebraMap R K u with hi_def
  have hu_img_ne : algebraMap R K u ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap R K)]
    exact fun h => hu_ne ((algebraMap R K).injective h)
  have hi_sq : i_elem * i_elem = -1 := by
    rw [hi_def]
    have : β / algebraMap R K u * (β / algebraMap R K u) = β * β / (algebraMap R K u * algebraMap R K u) := by
      field_simp
    rw [this, hβ_sq]
    have : algebraMap R K u * algebraMap R K u = algebraMap R K (u * u) := by rw [map_mul]
    rw [this, hu_sq_neg_d, map_neg]
    rw [div_neg, div_self]
    exact fun h => hu_img_ne ((algebraMap R K).injective (by rwa [map_zero]))
  -- Step 7: decompose x = a + b·β using Algebra.adjoin_eq_top and a suitable span argument.
  -- Equivalently, show x ∈ span R {1, β}.
  -- Instead we use PowerBasis {1, α} (dim 2) and rewrite in terms of β.
  let PB : PowerBasis R K := PowerBasis.ofAdjoinEqTop hint hαtop
  have hPBgen : PB.gen = α := rfl
  have hPBdim : PB.dim = 2 := hdeg
  -- Coordinates of x in {1, α} basis.
  have hrepr_sum : ∑ i, (PB.basis.repr x) i • PB.basis i = x := PB.basis.sum_repr x
  -- Cast indices to Fin 2.
  have hd1 : PB.dim = 2 := hdeg
  -- Get explicit a, b such that x = algebraMap R K a + algebraMap R K b * α
  have hrepr : ∃ a b : R, x = algebraMap R K a + algebraMap R K b * α := by
    -- index into PB.dim via Fin.cast from Fin 2
    refine ⟨PB.basis.repr x ⟨0, hd1 ▸ (by decide : (0 : ℕ) < 2)⟩,
            PB.basis.repr x ⟨1, hd1 ▸ (by decide : (1 : ℕ) < 2)⟩, ?_⟩
    have hsum := PB.basis.sum_repr x
    -- Convert sum over Fin PB.dim to sum over Fin 2
    have hfinrw : Finset.univ (α := Fin PB.dim) =
      ({⟨0, hd1 ▸ (by decide : (0 : ℕ) < 2)⟩, ⟨1, hd1 ▸ (by decide : (1 : ℕ) < 2)⟩} : Finset _) := by
      ext ⟨j, hj⟩
      simp
      rw [hd1] at hj
      interval_cases j
      · left; rfl
      · right; rfl
    rw [hfinrw] at hsum
    rw [Finset.sum_insert (by simp [Fin.ext_iff]), Finset.sum_singleton] at hsum
    have h0 : PB.basis ⟨0, hd1 ▸ (by decide : (0 : ℕ) < 2)⟩ = 1 := by
      rw [PB.basis_eq_pow]; simp
    have h1 : PB.basis ⟨1, hd1 ▸ (by decide : (1 : ℕ) < 2)⟩ = α := by
      rw [PB.basis_eq_pow, hPBgen]; simp
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one] at hsum
    linarith [hsum]
  obtain ⟨a, b, hx_eq⟩ := hrepr
  -- Step 8: rewrite x in {1, β} basis: x = a' + b' * β where a' = a - b*c₁/2, b' = b.
  -- Since β = α + c₁/2, α = β - c₁/2.
  have hα_in_β : α = β - algebraMap R K (c₁ / 2) := by rw [hβ_def]; ring
  set a' : R := a - b * c₁ / 2 with ha'_def
  set b' : R := b with hb'_def
  have hx_eq' : x = algebraMap R K a' + algebraMap R K b' * β := by
    rw [hx_eq, hα_in_β]
    rw [ha'_def, hb'_def]
    rw [map_sub, map_div₀, map_mul]
    simp
    ring
  -- Step 9: split on whether b' = 0.
  by_cases hb'_zero : b' = 0
  · -- x = a' (in R image). Use isSquare_or_isSquare_neg.
    rw [hb'_zero] at hx_eq'
    rw [map_zero, zero_mul, add_zero] at hx_eq'
    rcases isSquare_or_isSquare_neg a' with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact ⟨algebraMap R K s, by rw [hx_eq', hs]; simp [map_mul]⟩
    · -- -a' = s*s; a' = -s². Use i² = -1: a' = i² * s² = (is)².
      refine ⟨algebraMap R K s * i_elem, ?_⟩
      rw [hx_eq']
      have : algebraMap R K a' = -algebraMap R K (s * s) := by rw [← map_neg, hs]
      rw [this, map_mul]
      have := hi_sq
      ring_nf
      linarith [this]
  · -- b' ≠ 0. Use quadratic formula.
    -- Want e² + d·f² = a' and 2ef = b'.
    -- Since d = -u*u (from hu_sq_neg_d: u*u = -d): e² - u²f² = a'.
    -- Find t with t² = a'² + (u*b')². Sum of squares, so it's a square.
    have htsq : IsSquare (a' * a' + (u * b') * (u * b')) := by
      apply isSquare_of_isSumSq
      exact (IsSumSq.mul_self _).add (IsSumSq.mul_self _)
    obtain ⟨t, ht⟩ := htsq
    have ht' : t * t = a' * a' + (u * b') * (u * b') := ht.symm
    -- One of (a'+t)/2 or (a'-t)/2 is a square.
    have hub'_ne : u * b' ≠ 0 := mul_ne_zero hu_ne hb'_zero
    have hsq_choice := isSquare_half_sum_or_diff_of_sq_eq_sum_sq (a := a') (b := u * b')
                        (t := t) ht' hub'_ne
    -- In either case, set e² = (a' ± t)/2 and f = b'/(2e).
    rcases hsq_choice with ⟨e, he⟩ | ⟨e, he⟩
    all_goals {
      -- Check e ≠ 0: if e = 0, then (a' ± t)/2 = 0, so t = ∓a', then t² = a'², hence u*b' = 0, contra.
      have he_ne : e ≠ 0 := by
        intro h
        rw [h, mul_zero] at he
        have h1 : a' + t = 0 ∨ a' - t = 0 := by
          try { left; linarith }
          try { right; linarith }
        sorry
      have hf : algebraMap R K b' / (algebraMap R K (2 * e)) = algebraMap R K (b' / (2 * e)) := by
        rw [map_div₀]
      -- Construct y = e + (b' / (2e)) * β.
      refine ⟨algebraMap R K e + algebraMap R K (b' / (2 * e)) * β, ?_⟩
      sorry
    }

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
