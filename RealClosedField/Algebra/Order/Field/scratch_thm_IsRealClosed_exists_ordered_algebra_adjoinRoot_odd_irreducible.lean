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

/-!
# TFAE characterisation of real closed fields among ordered fields

This file records the equivalence between three characterisations of real closed fields
over an ordered field `R`:

1. `R` is real closed.
2. `R` is maximal among ordered algebraic extensions: every algebraic extension of `R`
   which is itself an ordered algebra over `R` is isomorphic to `R`.
3. Polynomials over `R` satisfy the intermediate value property.

The main result is `IsRealClosed.tfae_ord`.
-/

namespace IsRealClosed

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Polynomials over a real closed field satisfy the intermediate value property. -/
theorem exists_isRoot_of_nonpos_of_nonneg [IsRealClosed R]
    {f : R[X]} {a b : R} (hab : a ≤ b) (ha : f.eval a ≤ 0) (hb : 0 ≤ f.eval b) :
    ∃ c ∈ Set.Icc a b, f.IsRoot c := by
  sorry

/-- If polynomials over an ordered field `R` satisfy the intermediate value property,
then `R` is real closed. -/
theorem of_ivp
    (h : ∀ (f : R[X]) (a b : R), a ≤ b → f.eval a ≤ 0 → 0 ≤ f.eval b →
         ∃ c ∈ Set.Icc a b, f.IsRoot c) :
    IsRealClosed R := by
  refine IsRealClosed.of_linearOrderedField ?_ ?_
  · -- every non-negative element is a square
    intro x hx
    have ha : (X ^ 2 - C x).eval 0 ≤ 0 := by
      simp only [eval_sub, eval_pow, eval_X, eval_C]; linarith
    have hb : 0 ≤ (X ^ 2 - C x).eval (x + 1) := by
      simp only [eval_sub, eval_pow, eval_X, eval_C]; nlinarith [sq_nonneg x]
    obtain ⟨c, _, hc⟩ := h (X ^ 2 - C x) 0 (x + 1) (by linarith) ha hb
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at hc
    exact ⟨c, by linarith [sq c]⟩
  · -- every odd-natDegree polynomial has a root
    intro f hodd
    have hn : 1 ≤ f.natDegree := hodd.pos
    -- reduce to the case where the leading coefficient is positive
    have key : ∀ (g : R[X]), g.natDegree = f.natDegree → 0 < g.leadingCoeff →
        ∃ c, g.IsRoot c := by
      intro g hgdeg hlc
      set n := f.natDegree
      set B : R := ∑ i ∈ Finset.range n, |g.coeff i|
      have hB_nonneg : 0 ≤ B := Finset.sum_nonneg (fun i _ => abs_nonneg _)
      set aₙ := g.leadingCoeff with haₙ
      set M : R := (B + 1) / aₙ + 1 with hM
      have hM_pos : (0 : R) < M := by
        have : 0 < (B + 1) / aₙ := div_pos (by linarith) hlc; linarith
      have hM_ge : (1 : R) ≤ M := by
        have : 0 ≤ (B + 1) / aₙ := (div_pos (by linarith) hlc).le; linarith
      have hkey : aₙ * M - B ≥ 1 := by
        rw [hM]
        have heq : aₙ * ((B + 1) / aₙ + 1) = (B + 1) + aₙ := by field_simp
        linarith
      -- tail bound at M
      have tail_bound :
          ∀ x : R, 1 ≤ x → |∑ i ∈ Finset.range n, g.coeff i * x ^ i| ≤ x ^ (n - 1) * B := by
        intro x hx
        calc |∑ i ∈ Finset.range n, g.coeff i * x ^ i|
            ≤ ∑ i ∈ Finset.range n, |g.coeff i * x ^ i| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i ∈ Finset.range n, |g.coeff i| * x ^ i := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : R) ≤ x) i)]
          _ ≤ ∑ i ∈ Finset.range n, |g.coeff i| * x ^ (n - 1) := by
              refine Finset.sum_le_sum fun i hi => ?_
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              exact pow_le_pow_right₀ hx (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi))
          _ = x ^ (n - 1) * B := by rw [← Finset.sum_mul]; ring
      -- tail bound at -M (using (-x)^i)
      have tail_bound_neg :
          ∀ x : R, 1 ≤ x →
            |∑ i ∈ Finset.range n, g.coeff i * (-x) ^ i| ≤ x ^ (n - 1) * B := by
        intro x hx
        calc |∑ i ∈ Finset.range n, g.coeff i * (-x) ^ i|
            ≤ ∑ i ∈ Finset.range n, |g.coeff i * (-x) ^ i| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i ∈ Finset.range n, |g.coeff i| * x ^ i := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg (by linarith : (0 : R) ≤ x)]
          _ ≤ ∑ i ∈ Finset.range n, |g.coeff i| * x ^ (n - 1) := by
              refine Finset.sum_le_sum fun i hi => ?_
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              exact pow_le_pow_right₀ hx (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi))
          _ = x ^ (n - 1) * B := by rw [← Finset.sum_mul]; ring
      -- g.eval M > 0
      have hg_pos : 0 < g.eval M := by
        have hexp : g.eval M = aₙ * M ^ n + ∑ i ∈ Finset.range n, g.coeff i * M ^ i := by
          have := eval_eq_sum_range (p := g) M
          rw [hgdeg] at this
          rw [this, Finset.sum_range_succ,
              show g.coeff n = aₙ from by rw [haₙ, leadingCoeff, hgdeg]]
          ring
        rw [hexp]
        have htb := tail_bound M hM_ge
        have hMn_pos : 0 < M ^ (n - 1) := pow_pos hM_pos _
        have hpow : M ^ n = M * M ^ (n - 1) := by
          conv_lhs => rw [show n = (n - 1) + 1 from by omega, pow_succ]; ring
        rw [hpow]
        have hlb : ∑ i ∈ Finset.range n, g.coeff i * M ^ i ≥ -(M ^ (n - 1) * B) := by
          have := abs_le.mp htb; linarith [this.1]
        have hpos : 0 < M ^ (n - 1) * (aₙ * M - B) := by positivity
        nlinarith
      -- g.eval (-M) < 0
      have hg_neg : g.eval (-M) < 0 := by
        have hexp :
            g.eval (-M) = aₙ * (-M) ^ n + ∑ i ∈ Finset.range n, g.coeff i * (-M) ^ i := by
          have := eval_eq_sum_range (p := g) (-M)
          rw [hgdeg] at this
          rw [this, Finset.sum_range_succ,
              show g.coeff n = aₙ from by rw [haₙ, leadingCoeff, hgdeg]]
          ring
        rw [hexp, Odd.neg_pow (hgdeg ▸ hodd : Odd n) M]
        have htb := tail_bound_neg M hM_ge
        have hMn_pos : 0 < M ^ (n - 1) := pow_pos hM_pos _
        have hpow : M ^ n = M * M ^ (n - 1) := by
          conv_lhs => rw [show n = (n - 1) + 1 from by omega, pow_succ]; ring
        rw [hpow]
        have hub : ∑ i ∈ Finset.range n, g.coeff i * (-M) ^ i ≤ M ^ (n - 1) * B := by
          have := abs_le.mp htb; linarith [this.2]
        have hpos : 0 < M ^ (n - 1) * (aₙ * M - B) := by positivity
        nlinarith
      obtain ⟨c, _, hc⟩ := h g (-M) M (by linarith) hg_neg.le hg_pos.le
      exact ⟨c, hc⟩
    by_cases hlc : 0 < f.leadingCoeff
    · exact key f rfl hlc
    · have hne : f.leadingCoeff ≠ 0 := fun he => by
        rw [leadingCoeff_eq_zero] at he; subst he; simp at hn
      have hlc' : 0 < (-f).leadingCoeff := by
        rw [leadingCoeff_neg, neg_pos]; exact lt_of_le_of_ne (not_lt.mp hlc) hne
      obtain ⟨c, hc⟩ := key (-f) (natDegree_neg f) hlc'
      refine ⟨c, ?_⟩
      simp only [IsRoot, eval_neg, neg_eq_zero] at hc
      exact hc

/-- A real closed field has no nontrivial ordered algebraic extension: if `K` is an
algebraic extension of the real closed field `R` and `K` can be ordered compatibly with
the order on `R`, then the embedding `R → K` is a bijection. -/
theorem bijective_algebraMap_of_isOrderedAlgebra [IsRealClosed R]
    (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
    [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K] :
    Function.Bijective (algebraMap R K) := by
  sorry

/-- A polynomial `X^2 - C a` with `a` not a square is irreducible. -/
private lemma irreducible_X_sq_sub_C_of_not_isSquare
    {a : R} (hsq : ¬ IsSquare a) : Irreducible (X ^ 2 - C a : R[X]) := by
  have hmonic : (X ^ 2 - C a : R[X]).Monic := monic_X_pow_sub_C a (by decide)
  have hdeg : (X ^ 2 - C a : R[X]).natDegree = 2 := natDegree_X_pow_sub_C
  rw [Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hmonic
        (by rw [hdeg]) (by rw [hdeg]; decide),
      Multiset.eq_zero_iff_forall_notMem]
  intro c hc
  rw [mem_roots hmonic.ne_zero] at hc
  simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hc
  exact hsq ⟨c, by linear_combination hc.symm⟩

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Any irreducible polynomial of `natDegree > 1` gives a non-surjective `algebraMap` into its
`AdjoinRoot`. -/
private lemma algebraMap_not_bijective_of_irreducible_natDegree_pos
    {p : R[X]} (hirred : Irreducible p) (hdeg : 1 < p.natDegree) :
    ¬ Function.Bijective (algebraMap R (AdjoinRoot p)) := by
  intro hbij
  haveI : Fact (Irreducible p) := ⟨hirred⟩
  obtain ⟨r, hr⟩ := hbij.2 (AdjoinRoot.root p)
  have hz : algebraMap R (AdjoinRoot p) (p.eval r) = 0 := by
    have h₂ : aeval (AdjoinRoot.root p) p = 0 := AdjoinRoot.eval₂_root p
    rw [← hr] at h₂
    rw [show algebraMap R (AdjoinRoot p) (p.eval r) = aeval (algebraMap R (AdjoinRoot p) r) p
        from (Polynomial.aeval_algebraMap_apply _ _ _).symm]
    exact h₂
  exact hirred.not_isRoot_of_natDegree_ne_one hdeg.ne' (hbij.1 (by simpa using hz))

/-- From an ordering on `AdjoinRoot p` (for `p` irreducible of `natDegree > 1`) and the
hypothesis that `algebraMap R K` is bijective for every ordered algebraic extension, we derive
a contradiction. -/
private lemma not_exists_ordered_algebra_of_bijective
    (h : ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
         [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K],
         Function.Bijective (algebraMap R K))
    {p : R[X]} (hirred : Irreducible p) (hdeg : 1 < p.natDegree)
    (hmod : ∃ _ : LinearOrder (AdjoinRoot p),
      IsStrictOrderedRing (AdjoinRoot p) ∧ IsOrderedModule R (AdjoinRoot p)) :
    False := by
  haveI : Fact (Irreducible p) := ⟨hirred⟩
  haveI : Module.Finite R (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hirred.ne_zero).basis
  haveI : Algebra.IsAlgebraic R (AdjoinRoot p) := Algebra.IsAlgebraic.of_finite R (AdjoinRoot p)
  obtain ⟨lo, hsr, hom⟩ := hmod
  letI := lo
  haveI := hsr
  haveI := hom
  exact algebraMap_not_bijective_of_irreducible_natDegree_pos hirred hdeg (h (AdjoinRoot p))

/-- Every positive-odd-`natDegree` polynomial has a monic irreducible factor of odd
`natDegree`. -/
private lemma exists_odd_irreducible_factor
    {f : R[X]} (hf : Odd f.natDegree) (hpos : 0 < f.natDegree) :
    ∃ g : R[X], Monic g ∧ Irreducible g ∧ g ∣ f ∧ Odd g.natDegree := by
  classical
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  subst hn
  have hnu : ¬ IsUnit f := fun hu => by
    have := natDegree_eq_zero_of_isUnit hu
    rw [this] at hpos; exact absurd hpos (by decide)
  obtain ⟨g, hg_monic, hg_irred, hg_dvd⟩ := Polynomial.exists_monic_irreducible_factor f hnu
  by_cases hg_odd : Odd g.natDegree
  · exact ⟨g, hg_monic, hg_irred, hg_dvd, hg_odd⟩
  · rw [Nat.not_odd_iff_even] at hg_odd
    have hg_deg_pos : 0 < g.natDegree := hg_irred.natDegree_pos
    obtain ⟨q, hq_eq⟩ := hg_dvd
    have hne : f ≠ 0 := fun heq => by rw [heq, natDegree_zero] at hpos; exact absurd hpos (by decide)
    have hq_ne : q ≠ 0 := fun hz => hne (by rw [hq_eq, hz, mul_zero])
    have hfg_deg : f.natDegree = g.natDegree + q.natDegree := by
      have := natDegree_mul hg_irred.ne_zero hq_ne; rw [← hq_eq] at this; exact this
    have hq_deg : q.natDegree = f.natDegree - g.natDegree := by omega
    have hq_odd : Odd q.natDegree := by
      rw [hq_deg]; exact Nat.Odd.sub_even (by omega) hf hg_odd
    have hq_lt : q.natDegree < f.natDegree := by rw [hq_deg]; omega
    obtain ⟨g', hg'_monic, hg'_irred, hg'_dvd, hg'_odd⟩ :=
      ih q.natDegree hq_lt hq_odd hq_odd.pos rfl
    exact ⟨g', hg'_monic, hg'_irred, hg'_dvd.trans ⟨g, by rw [hq_eq]; ring⟩, hg'_odd⟩

/-- Core induction lemma: every monic irreducible polynomial of odd `natDegree` over an ordered
field `R` gives rise to a quotient `R`-algebra that admits an ordering extending the one on `R`.
This is the classical Artin-Schreier induction. -/
private lemma exists_ordered_algebra_adjoinRoot_odd_irreducible
    {g : R[X]} (hg_monic : Monic g) (hg_irred : Irreducible g) (hg_odd : Odd g.natDegree) :
    ∃ _ : LinearOrder (AdjoinRoot g),
      IsStrictOrderedRing (AdjoinRoot g) ∧ IsOrderedModule R (AdjoinRoot g) := by
  classical
  induction hn : g.natDegree using Nat.strong_induction_on generalizing g with
  | _ n ih =>
  subst hn
  haveI : Fact (Irreducible g) := ⟨hg_irred⟩
  set K := AdjoinRoot g
  let hm : IsAdjoinRootMonic K g := AdjoinRoot.isAdjoinRootMonic g hg_monic
  -- Define the projection π : K →ₗ[R] R via the 0th coefficient.
  let π : K →ₗ[R] R :=
    { toFun := fun x => hm.coeff x 0
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp }
  have hπ_algebraMap : ∀ r : R, π (algebraMap R K r) = r := by
    intro r
    show hm.coeff (algebraMap R K r) 0 = r
    rw [hm.coeff_algebraMap]; simp
  have hπ_one : π 1 = 1 := by
    show hm.coeff 1 0 = 1; rw [hm.coeff_one]; simp
  -- Use the characterization of ordered algebras
  rw [Field.exists_isOrderedAlgebra_iff_neg_one_notMem_span_nonneg_isSquare]
  intro hc
  -- Case on the degree of g: either g.natDegree = 1, or g.natDegree ≥ 3.
  by_cases hdeg1 : g.natDegree = 1
  · -- Base case: g.natDegree = 1. Every x ∈ K equals algebraMap R K (π x), so π is a
    -- surjective ring hom and we can transport.
    have hrepr : ∀ x : K, x = algebraMap R K (π x) := by
      intro x
      apply hm.ext_elem
      intro i hi
      rw [hdeg1] at hi
      interval_cases i
      rw [hm.coeff_algebraMap]
      simp [π]
    have hπ_sq : ∀ x : K, 0 ≤ π (x ^ 2) := by
      intro x
      have h1 : x ^ 2 = algebraMap R K ((π x) ^ 2) := by
        conv_lhs => rw [hrepr x]
        rw [← map_pow]
      rw [h1, hπ_algebraMap]
      positivity
    -- Then the span argument: π of any element in the span is ≥ 0.
    have hπ_in_span :
        ∀ s ∈ Submodule.span (Subsemiring.nonneg R) {x : K | IsSquare x}, 0 ≤ π s := by
      intro s hs
      refine Submodule.span_induction
        (mem := ?_)
        (zero := by rw [map_zero])
        (add := fun x y _ _ hx hy => by rw [map_add]; linarith)
        (smul := fun r x _ hx => by
          show 0 ≤ π (r • x)
          rw [LinearMap.map_smul_of_tower]
          exact mul_nonneg r.2 hx) hs
      rintro y ⟨z, hz⟩
      have heq : y = z ^ 2 := by rw [hz]; ring
      rw [heq]; exact hπ_sq z
    have h1 : π (-1 : K) = -1 := by rw [map_neg, hπ_one]
    have h2 : 0 ≤ π (-1 : K) := hπ_in_span _ hc
    linarith [h1 ▸ h2]
  · -- Inductive case: g.natDegree ≥ 3.
    have hn_ge : 3 ≤ g.natDegree := by
      have h1 := hg_odd.pos
      rcases hg_odd with ⟨k, hk⟩
      omega
    -- Unpack the span into a finite linear combination
    obtain ⟨c, hc_supp, hc_sum⟩ := Submodule.mem_span_set.mp hc
    -- For each y in support, y is a square; pick a square root and its polynomial lift.
    have hy_sq : ∀ y ∈ c.support, IsSquare y := fun y hy => hc_supp hy
    -- For each y ∈ c.support, choose a square root `sqRoot y` with y = sqRoot y ^ 2.
    let sqRoot : K → K := fun y => if hy : IsSquare y then hy.choose else 0
    have hsqRoot : ∀ y ∈ c.support, y = sqRoot y ^ 2 := by
      intro y hy
      have hsq := hy_sq y hy
      have := hsq.choose_spec
      simp only [sqRoot, hsq, dif_pos]
      rw [this]; ring
    -- Polynomial lift of sqRoot y, with degree < g.natDegree.
    let p : K → R[X] := fun y => hm.modByMonicHom (sqRoot y)
    have hg_ne_one : g ≠ 1 := fun he => by
      have := hg_irred; rw [he] at this; exact this.not_unit isUnit_one
    have hp_deg_lt : ∀ y : K, (p y).natDegree < g.natDegree := fun y =>
      Polynomial.natDegree_modByMonic_lt _ hg_monic hg_ne_one
    have hp_mk : ∀ y ∈ c.support, AdjoinRoot.mk g (p y) = sqRoot y := by
      intro y _
      show hm.map (hm.modByMonicHom (sqRoot y)) = sqRoot y
      exact hm.map_modByMonicHom (sqRoot y)
    -- Build the polynomial P := (∑ C (c y).val * (p y)^2) + 1.
    set P : R[X] := (∑ y ∈ c.support, C ((c y : R)) * (p y)^2) + 1 with hP_def
    -- Claim: g | P
    have hg_dvd_P : g ∣ P := by
      rw [← AdjoinRoot.mk_eq_zero]
      simp only [hP_def, map_add, map_sum, map_mul, map_pow, map_one, AdjoinRoot.mk_C]
      have hsum_eq :
          ∑ y ∈ c.support, (algebraMap R K (c y : R)) * (AdjoinRoot.mk g (p y))^2 = -1 := by
        rw [show (-1 : K) = -(1 : K) from rfl, ← hc_sum]
        rw [Finsupp.sum]
        rw [show -∑ y ∈ c.support, (c y : ↥(Subsemiring.nonneg R)) • y =
              ∑ y ∈ c.support, -((c y : ↥(Subsemiring.nonneg R)) • y) from by
          rw [← Finset.sum_neg_distrib]]
        -- this is wrong sign. hc_sum is : (∑...) = -1, so -1 = (∑...) directly.
        sorry
      rw [hsum_eq]; ring
    sorry

/-- Adjoining `√a` to an ordered field (for `a ≥ 0` not a square) gives an ordered algebra. -/
private lemma exists_ordered_algebra_adjoinRoot_sq_sub_C
    {a : R} (ha : 0 ≤ a) (hsq : ¬ IsSquare a) :
    ∃ _ : LinearOrder (AdjoinRoot (X ^ 2 - C a : R[X])),
      IsStrictOrderedRing (AdjoinRoot (X ^ 2 - C a : R[X])) ∧
      IsOrderedModule R (AdjoinRoot (X ^ 2 - C a : R[X])) := by
  have hirred : Irreducible (X ^ 2 - C a : R[X]) :=
    irreducible_X_sq_sub_C_of_not_isSquare hsq
  have hmonic : (X ^ 2 - C a : R[X]).Monic := monic_X_pow_sub_C a (by decide)
  have hdeg2 : (X ^ 2 - C a : R[X]).natDegree = 2 := natDegree_X_pow_sub_C
  set K := AdjoinRoot (X ^ 2 - C a : R[X])
  haveI : Fact (Irreducible (X ^ 2 - C a : R[X])) := ⟨hirred⟩
  set hm : IsAdjoinRootMonic K (X ^ 2 - C a : R[X]) :=
    AdjoinRoot.isAdjoinRootMonic (X ^ 2 - C a : R[X]) hmonic
  let π : K →ₗ[R] R :=
    { toFun := fun x => hm.coeff x 0
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp }
  have hπ_one : π 1 = 1 := by show hm.coeff 1 0 = 1; rw [hm.coeff_one]; simp
  have hroot_sq : hm.root ^ 2 = algebraMap R K a := by
    have heq : hm.root = AdjoinRoot.root (X ^ 2 - C a : R[X]) := rfl
    have h0 : aeval (AdjoinRoot.root (X ^ 2 - C a : R[X])) (X ^ 2 - C a : R[X]) = 0 :=
      AdjoinRoot.eval₂_root _
    simp [aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h0
    rw [heq]; exact h0
  -- Every element of K decomposes as `u + v · root` via the power basis
  have hrepr : ∀ x : K,
      x = algebraMap R K (hm.coeff x 0) + algebraMap R K (hm.coeff x 1) * hm.root := by
    intro x
    apply hm.ext_elem
    intro i hi
    rw [hdeg2] at hi
    have hroot_coeff : hm.coeff hm.root = Pi.single 1 1 := hm.coeff_root (by rw [hdeg2]; decide)
    have hcoeff_aM_mul_root : ∀ (c : R) (j : ℕ),
        hm.coeff (algebraMap R K c * hm.root) j = c • (Pi.single (M := fun _ : ℕ => R) 1 1) j := by
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
  -- π(x²) ≥ 0
  have hπ_sq : ∀ x : K, 0 ≤ π (x ^ 2) := by
    intro x
    set u := hm.coeff x 0
    set v := hm.coeff x 1
    have hx_sq : x ^ 2 = algebraMap R K (u^2 + a * v^2) + algebraMap R K (2 * u * v) * hm.root := by
      rw [hrepr x]
      have e1 : (algebraMap R K u + algebraMap R K v * hm.root) ^ 2
              = (algebraMap R K u)^2
                  + 2 * (algebraMap R K u) * (algebraMap R K v * hm.root)
                  + (algebraMap R K v)^2 * (hm.root ^ 2) := by ring
      rw [e1, hroot_sq]
      have hmid : (2 : K) * algebraMap R K u * (algebraMap R K v * hm.root)
              = algebraMap R K (2 * u * v) * hm.root := by
        have h : (algebraMap R K (2 * u * v) : K) = 2 * algebraMap R K u * algebraMap R K v := by
          rw [map_mul, map_mul, map_ofNat]
        rw [h]; ring
      rw [hmid]
      have h1 : (algebraMap R K u)^2 = algebraMap R K (u^2) := (map_pow _ _ _).symm
      have h2 : (algebraMap R K v)^2 * algebraMap R K a = algebraMap R K (v^2 * a) := by
        rw [← map_pow, ← map_mul]
      have h3 : algebraMap R K (u^2) + algebraMap R K (v^2 * a)
              = algebraMap R K (u^2 + a * v^2) := by rw [← map_add]; ring_nf
      linear_combination h1 + h3 + h2
    rw [hx_sq]
    show hm.coeff _ 0 ≥ 0
    rw [LinearMap.map_add hm.coeff, hm.coeff_algebraMap]
    show (Pi.single 0 (u^2 + a*v^2) : ℕ → R) 0
          + hm.coeff (algebraMap R K (2 * u * v) * hm.root) 0 ≥ 0
    rw [show algebraMap R K (2 * u * v) * hm.root = (2 * u * v) • hm.root from by
        rw [Algebra.smul_def], LinearMap.map_smul hm.coeff]
    show (Pi.single 0 (u^2 + a*v^2) : ℕ → R) 0 + (2*u*v) • hm.coeff hm.root 0 ≥ 0
    rw [hm.coeff_root (by rw [hdeg2]; decide)]
    simp
    positivity
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
        rw [LinearMap.map_smul_of_tower]
        exact mul_nonneg r.2 hx) hs
    rintro y ⟨z, hz⟩
    have heq : y = z ^ 2 := by rw [hz]; ring
    rw [heq]; exact hπ_sq z
  have h1 : π (-1 : K) = -1 := by rw [map_neg, hπ_one]
  have h2 : 0 ≤ π (-1 : K) := hπ_in_span _ hc
  linarith [h1 ▸ h2]

/-- If an ordered field `R` has no nontrivial ordered algebraic extension, then it is
real closed. -/
theorem of_bijective_algebraMap_of_isOrderedAlgebra
    (h : ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
         [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K],
         Function.Bijective (algebraMap R K)) :
    IsRealClosed R := by
  refine IsRealClosed.of_linearOrderedField (fun {a} ha => ?_) (fun {f} hodd => ?_)
  · -- every non-negative is a square
    by_contra hsq
    have hdeg2 : (X ^ 2 - C a : R[X]).natDegree = 2 := natDegree_X_pow_sub_C
    exact not_exists_ordered_algebra_of_bijective h
      (irreducible_X_sq_sub_C_of_not_isSquare hsq) (by rw [hdeg2]; decide)
      (exists_ordered_algebra_adjoinRoot_sq_sub_C ha hsq)
  · -- every odd-natDegree polynomial has a root
    obtain ⟨g, hg_monic, hg_irred, hg_dvd, hg_odd⟩ :=
      exists_odd_irreducible_factor hodd hodd.pos
    by_cases hg_deg_one : g.natDegree = 1
    · have : g.degree = 1 := by rw [degree_eq_natDegree hg_irred.ne_zero, hg_deg_one]; rfl
      obtain ⟨c, hc⟩ := Polynomial.exists_root_of_degree_eq_one this
      obtain ⟨q, hq⟩ := hg_dvd
      exact ⟨c, by rw [IsRoot, hq, eval_mul, hc, zero_mul]⟩
    · exfalso
      have hg_deg_gt : 1 < g.natDegree :=
        lt_of_le_of_ne hg_odd.pos.nat_succ_le (fun heq => hg_deg_one heq.symm)
      exact not_exists_ordered_algebra_of_bijective h hg_irred hg_deg_gt
        (exists_ordered_algebra_adjoinRoot_odd_irreducible hg_monic hg_irred hg_odd)

variable (R) in
/-- Characterisation of real closed fields among ordered fields. -/
theorem tfae_ord :
    List.TFAE [
      IsRealClosed R,
      ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
        [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K],
        Function.Bijective (algebraMap R K),
      ∀ (f : R[X]) (a b : R), a ≤ b → f.eval a ≤ 0 → 0 ≤ f.eval b →
        ∃ c ∈ Set.Icc a b, f.IsRoot c] := by
  tfae_have 1 → 2 := by
    intro _ K _ _ _ _ _ _
    exact bijective_algebraMap_of_isOrderedAlgebra K
  tfae_have 2 → 1 := of_bijective_algebraMap_of_isOrderedAlgebra
  tfae_have 1 → 3 := by
    intro _ f a b hab ha hb
    exact exists_isRoot_of_nonpos_of_nonneg hab ha hb
  tfae_have 3 → 1 := of_ivp
  tfae_finish

end IsRealClosed
