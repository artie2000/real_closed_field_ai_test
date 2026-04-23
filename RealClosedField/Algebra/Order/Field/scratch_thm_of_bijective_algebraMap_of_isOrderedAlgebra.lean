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

/-- Given an ordered structure on `AdjoinRoot p` (for `p` irreducible of natDegree > 1),
the hypothesis that `algebraMap R K` is bijective for every ordered algebraic extension gives
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

/-- If `f : R[X]` has odd natDegree, then it has an irreducible factor of odd natDegree. -/
private lemma exists_odd_irreducible_factor
    {f : R[X]} (hf : Odd f.natDegree) :
    ∃ g : R[X], Monic g ∧ Irreducible g ∧ g ∣ f ∧ Odd g.natDegree := by
  classical
  -- Write f as a product of its irreducible factors (via UniqueFactorizationMonoid)
  have hne : f ≠ 0 := fun h => by
    rw [h, natDegree_zero] at hf
    exact (Nat.not_odd_iff_even.mpr (by exact even_zero)) hf
  have hnonunit : ¬ IsUnit f := fun hu => by
    have := natDegree_eq_zero_of_isUnit hu
    rw [this] at hf
    exact (Nat.not_odd_iff_even.mpr (by exact even_zero)) hf
  -- Take the factor set
  have : ∃ s : Multiset R[X], (∀ p ∈ s, Irreducible p) ∧ Associated f s.prod :=
    WfDvdMonoid.exists_factors f hne
  obtain ⟨s, hs_irred, hassoc⟩ := this
  -- The natDegree of f equals sum of natDegrees of irreducible factors (up to units)
  -- Actually this needs some care. Associate f = unit * s.prod.
  -- natDegree respects associates
  rcases hassoc with ⟨u, hu⟩
  -- f = u * s.prod, and s.prod ≠ 0 because f ≠ 0
  have hu_deg : u.1.natDegree = 0 := natDegree_eq_zero_of_isUnit u.isUnit
  have hs_prod_ne : s.prod ≠ 0 := fun hz => hne (by
    -- f = s.prod * u, so f = 0 iff s.prod = 0 or u = 0
    have : f = s.prod * u.1 := by rw [← hu]
    rw [this, hz, zero_mul])
  have hfdeg : f.natDegree = (s.map natDegree).sum := by
    have h1 : f.natDegree = (s.prod * u.1).natDegree := by rw [← hu]
    have h2 : (s.prod * u.1).natDegree = s.prod.natDegree := by
      rw [natDegree_mul hs_prod_ne (fun hu0 => by
        rw [hu0, natDegree_zero] at hu_deg; exact absurd hu_deg (by decide : (0:ℕ) ≠ 0))]
      · rw [hu_deg]; ring
      · exact fun h => (IsUnit.ne_zero u.isUnit) h
    rw [h1, h2]
    induction s using Multiset.induction with
    | empty => simp
    | cons a t ih =>
      simp only [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
      rw [natDegree_mul]
      · congr 1; apply ih
        · intro p hp; exact hs_irred p (Multiset.mem_cons_of_mem hp)
        · intro hz; exact hs_prod_ne (by rw [Multiset.prod_cons, hz, mul_zero])
      · exact (hs_irred a (Multiset.mem_cons_self _ _)).ne_zero
      · intro hz; exact hs_prod_ne (by rw [Multiset.prod_cons, hz, mul_zero])
  -- Now: f.natDegree is odd, = sum. Sum of evens is even. So some natDegree is odd.
  have hexists : ∃ p ∈ s, Odd p.natDegree := by
    by_contra hall
    push_neg at hall
    have : ∀ p ∈ s, Even p.natDegree := fun p hp => Nat.not_odd_iff_even.mp (hall p hp)
    have heven_sum : Even ((s.map natDegree).sum) := by
      refine Multiset.sum_induction_nonneg_of_forall _ ?_ ?_
      · exact Even.add
      · exact fun d hd => by
          rw [Multiset.mem_map] at hd
          obtain ⟨p, hp, hpd⟩ := hd
          rw [← hpd]
          exact this p hp
    rw [← hfdeg] at heven_sum
    exact (Nat.not_even_iff_odd.mpr hf) heven_sum
  obtain ⟨p, hp, hp_odd⟩ := hexists
  -- p is irreducible, so has a monic associate
  have hp_irred : Irreducible p := hs_irred p hp
  have hp_ne : p ≠ 0 := hp_irred.ne_zero
  set g := p * C (p.leadingCoeff)⁻¹
  have hg_monic : g.Monic := monic_mul_leadingCoeff_inv hp_ne
  have hg_irred : Irreducible g := by
    have hassoc : Associated p g := associated_mul_unit_right _ _ <|
      isUnit_C.2 (leadingCoeff_ne_zero.2 hp_ne).isUnit.inv
    exact hassoc.irreducible hp_irred
  have hg_dvd : g ∣ f := by
    have hp_dvd : p ∣ f := by
      have hps : p ∣ s.prod := Multiset.dvd_prod hp
      calc p ∣ s.prod := hps
        _ ∣ s.prod * u.1 := dvd_mul_right _ _
        _ = f := hu
    have hgp : g ∣ p := by
      use C (p.leadingCoeff)
      rw [mul_assoc, ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.2 hp_ne), C_1, mul_one]
    exact hgp.trans hp_dvd
  have hg_deg : g.natDegree = p.natDegree := by
    rw [natDegree_mul hp_ne (by
      simp only [ne_eq, C_eq_zero]
      exact inv_ne_zero (leadingCoeff_ne_zero.2 hp_ne))]
    simp [natDegree_C]
  refine ⟨g, hg_monic, hg_irred, hg_dvd, ?_⟩
  rw [hg_deg]
  exact hp_odd

/-- Part A: showing that adjoining a square root yields an ordered extension. -/
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
  -- π : K →ₗ[R] R is the 0-th coefficient projection
  let π : K →ₗ[R] R :=
    { toFun := fun x => hm.coeff x 0
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp }
  -- Basic properties of π
  have hπ_one : π 1 = 1 := by
    show hm.coeff 1 0 = 1
    rw [hm.coeff_one]
    simp
  have hπ_root : π hm.root = 0 := by
    show hm.coeff hm.root 0 = 0
    rw [hm.coeff_root (by rw [hdeg2]; decide)]
    simp
  have hπ_algebraMap : ∀ c : R, π (algebraMap R K c) = c := by
    intro c
    show hm.coeff (algebraMap R K c) 0 = c
    rw [hm.coeff_algebraMap]
    simp
  -- root^2 = a
  have hroot_sq : hm.root ^ 2 = algebraMap R K a := by
    have heq : hm.root = AdjoinRoot.root (X ^ 2 - C a : R[X]) := rfl
    have h0 : (aeval (AdjoinRoot.root (X ^ 2 - C a : R[X])) (X ^ 2 - C a : R[X])) = 0 :=
      AdjoinRoot.eval₂_root _
    simp [aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h0
    rw [heq]; exact h0
  -- Every x ∈ K can be written as algebraMap u + algebraMap v * root, using hm.coeff
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
      rw [show algebraMap R K c * hm.root = c • hm.root from by rw [Algebra.smul_def]]
      rw [LinearMap.map_smul hm.coeff]
      show c • hm.coeff hm.root j = _
      rw [hroot_coeff]
    interval_cases i
    · -- i = 0
      rw [LinearMap.map_add hm.coeff]
      rw [hm.coeff_algebraMap]
      show hm.coeff x 0 = (Pi.single 0 (hm.coeff x 0) : ℕ → R) 0
          + hm.coeff (algebraMap R K (hm.coeff x 1) * hm.root) 0
      rw [hcoeff_aM_mul_root]
      simp
    · -- i = 1
      rw [LinearMap.map_add hm.coeff]
      rw [hm.coeff_algebraMap]
      show hm.coeff x 1 = (Pi.single 0 (hm.coeff x 0) : ℕ → R) 1
          + hm.coeff (algebraMap R K (hm.coeff x 1) * hm.root) 1
      rw [hcoeff_aM_mul_root]
      simp
  -- π(x^2) ≥ 0 for all x : K
  have hπ_sq : ∀ x : K, 0 ≤ π (x ^ 2) := by
    intro x
    set u := hm.coeff x 0
    set v := hm.coeff x 1
    have hx : x = algebraMap R K u + algebraMap R K v * hm.root := hrepr x
    -- Compute x^2 = algebraMap (u^2 + a*v^2) + algebraMap (2*u*v) * root
    have hx_sq : x ^ 2 = algebraMap R K (u^2 + a * v^2) + algebraMap R K (2 * u * v) * hm.root := by
      rw [hx]
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
    rw [LinearMap.map_add hm.coeff]
    rw [hm.coeff_algebraMap]
    show (Pi.single 0 (u^2 + a*v^2) : ℕ → R) 0
          + hm.coeff (algebraMap R K (2 * u * v) * hm.root) 0 ≥ 0
    rw [show algebraMap R K (2 * u * v) * hm.root = (2 * u * v) • hm.root from by
        rw [Algebra.smul_def]]
    rw [LinearMap.map_smul hm.coeff]
    show (Pi.single 0 (u^2 + a*v^2) : ℕ → R) 0 + (2*u*v) • hm.coeff hm.root 0 ≥ 0
    rw [hm.coeff_root (by rw [hdeg2]; decide)]
    simp
    positivity
  -- Now derive non-membership
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
        show 0 ≤ (r : R) * π x
        exact mul_nonneg r.2 hx)
      hs
    rintro y ⟨z, hz⟩
    have heq : y = z ^ 2 := by rw [hz]; ring
    rw [heq]
    exact hπ_sq z
  have h1 : π (-1 : K) = -1 := by rw [map_neg, hπ_one]
  have h2 : 0 ≤ π (-1 : K) := hπ_in_span _ hc
  rw [h1] at h2
  linarith

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
    have hdeg2 : (X ^ 2 - C a : R[X]).natDegree = 2 := natDegree_X_pow_sub_C
    exact not_exists_ordered_algebra_of_bijective h hirred
      (by rw [hdeg2]; decide)
      (exists_ordered_algebra_adjoinRoot_sq_sub_C ha hsq)
  · -- PART B: every odd-degree polynomial has a root
    -- This requires a strong induction showing that for every odd-degree irreducible
    -- polynomial g, AdjoinRoot g admits a compatible order. The induction goes:
    --   Base (deg = 1): AdjoinRoot g ≅ R, which is already ordered.
    --   Step (deg > 1 odd): if -1 ∈ span_squares in AdjoinRoot g, lift back to R[X] to
    --     get 1 + ∑ cᵢ*pᵢ² = h*g; analyze degrees to find an odd-degree irreducible
    --     factor of h with smaller degree, giving -1 ∈ span_squares there; apply IH.
    -- We leave this full argument as a sorry, reporting the precise claim.
    sorry

end IsRealClosed
