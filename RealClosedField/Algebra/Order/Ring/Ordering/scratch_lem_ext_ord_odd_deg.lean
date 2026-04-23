/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib
import RealClosedField.Algebra.Order.Algebra

/-!
# Sufficient conditions for an ordered field extension
-/

variable {F K : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [Field K] [Algebra F K]

namespace Field

theorem exists_isOrderedAlgebra_of_linearProj_nonneg_sq
    (π : K →ₗ[F] F) (hπ1 : π 1 = 1) (hπ : ∀ x : K, 0 ≤ π (x ^ 2)) :
    ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K := by
  rw [Field.exists_isOrderedAlgebra_iff_neg_one_notMem_span_nonneg_isSquare]
  intro h
  have key : ∀ y ∈ Submodule.span (Subsemiring.nonneg F) {x : K | IsSquare x}, 0 ≤ π y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      have hww : w * w = w ^ 2 := by ring
      rw [hww]
      exact hπ w
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; linarith
    | smul r x _ hx =>
      rw [LinearMap.map_smul_of_tower, Subsemiring.smul_def, smul_eq_mul]
      exact mul_nonneg r.2 hx
  have h1 := key (-1) h
  rw [map_neg, hπ1] at h1
  linarith

/-- Base case: if `K/F` has degree 1, then `K` admits an ordering making `K/F` ordered. -/
private theorem exists_isOrderedAlgebra_of_finrank_eq_one
    [FiniteDimensional F K] (h1 : Module.finrank F K = 1) :
    ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K := by
  have hbij : Function.Bijective (algebraMap F K) :=
    Module.Free.bijective_algebraMap_of_finrank_eq_one h1
  let e : F ≃ₗ[F] K := LinearEquiv.ofBijective (Algebra.linearMap F K) hbij
  have he_apply : ∀ r : F, e r = algebraMap F K r := fun _ => rfl
  refine exists_isOrderedAlgebra_of_linearProj_nonneg_sq e.symm.toLinearMap ?_ ?_
  · show e.symm 1 = 1
    have h1' : e 1 = 1 := by rw [he_apply]; exact map_one _
    rw [← h1', e.symm_apply_apply]
  · intro x
    show 0 ≤ e.symm (x^2)
    set r := e.symm x with hr
    have hxr : x = algebraMap F K r := by
      have h_er : e r = x := e.apply_symm_apply x
      rw [he_apply] at h_er
      exact h_er.symm
    have hx2 : x^2 = algebraMap F K (r^2) := by rw [hxr, ← map_pow]
    have hesx : e.symm (x^2) = r^2 := by
      rw [hx2, ← he_apply, e.symm_apply_apply]
    rw [hesx]
    exact sq_nonneg _

/-- Any polynomial of odd natDegree over a field has a monic irreducible factor of odd
natDegree. -/
private lemma Polynomial.exists_monic_irreducible_factor_odd_natDegree
    {F : Type*} [Field F] (f : F[X]) (hodd : Odd f.natDegree) :
    ∃ g : F[X], g.Monic ∧ Irreducible g ∧ g ∣ f ∧ Odd g.natDegree := by
  have hf : f ≠ 0 := by
    intro hf0
    rw [hf0, natDegree_zero] at hodd
    exact (Nat.not_odd_iff_even.mpr even_zero) hodd
  have hne : ¬ IsUnit f := by
    intro hu
    obtain ⟨n, hn⟩ := hodd
    rw [natDegree_eq_zero_iff_degree_le_zero.mpr
      (le_of_eq (Polynomial.degree_eq_zero_of_isUnit hu))] at hn
    omega
  -- factorise f into irreducibles
  have := WfDvdMonoid.exists_factors f hf
  classical
  obtain ⟨fact, hfact_irred, hfact_assoc⟩ := this
  -- convert each irreducible factor to a monic one
  -- at least one factor has odd natDegree
  -- its natDegree is odd since sum of natDegrees = natDegree f (odd)
  have hsum_deg : (fact.map Polynomial.natDegree).sum = f.natDegree := by
    obtain ⟨u, hu⟩ := hfact_assoc
    have : (fact.prod * (u : F[X])).natDegree = f.natDegree := by rw [hu]
    have hunit : IsUnit (u : F[X]) := u.isUnit
    have hdeg_u : (u : F[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr
        (le_of_eq (Polynomial.degree_eq_zero_of_isUnit hunit))
    have hprod_ne : fact.prod ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hu
      exact hf hu.symm
    have hunit_ne : (u : F[X]) ≠ 0 := hunit.ne_zero
    rw [Polynomial.natDegree_mul hprod_ne hunit_ne, hdeg_u, add_zero] at this
    rw [← this]
    exact Polynomial.natDegree_multiset_prod_of_nonzero (fun p hp => (hfact_irred p hp).ne_zero)
  -- Now, some irreducible factor has odd natDegree
  have hexists : ∃ p ∈ fact, Odd p.natDegree := by
    by_contra hall
    push_neg at hall
    have : ∀ p ∈ fact, Even p.natDegree := fun p hp =>
      Nat.not_odd_iff_even.mp (hall p hp)
    have heven : Even (fact.map Polynomial.natDegree).sum := by
      apply Multiset.sum_induction_nonempty Even
      · intros a b ha hb; exact ha.add hb
      · intro h0
        rw [Multiset.map_eq_zero] at h0
        rw [h0, Multiset.prod_zero] at hfact_assoc
        obtain ⟨u, hu⟩ := hfact_assoc
        rw [one_mul] at hu
        rw [← hu] at hne
        exact hne u.isUnit
      · intro x hx
        rw [Multiset.mem_map] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        exact this p hp
    rw [hsum_deg] at heven
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  obtain ⟨p, hp_mem, hp_odd⟩ := hexists
  have hp_irred : Irreducible p := hfact_irred p hp_mem
  -- Convert p to monic
  let g := p * C p.leadingCoeff⁻¹
  have hp_ne_zero : p ≠ 0 := hp_irred.ne_zero
  have hlc_ne_zero : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp_ne_zero
  have hlc_inv_unit : IsUnit (C p.leadingCoeff⁻¹) :=
    Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero hlc_ne_zero))
  have hassoc : Associated p g := associated_mul_unit_right _ _ hlc_inv_unit
  have hg_monic : g.Monic := Polynomial.monic_mul_leadingCoeff_inv hp_ne_zero
  have hg_irred : Irreducible g := hassoc.irreducible hp_irred
  have hg_dvd_f : g ∣ f := by
    have : p ∣ f := by
      rcases hfact_assoc with ⟨u, hu⟩
      rw [← hu]
      exact (Multiset.dvd_prod hp_mem).mul_right _
    exact hassoc.dvd_iff_dvd_left.mp this
  have hg_deg : g.natDegree = p.natDegree := by
    dsimp [g]
    rw [Polynomial.natDegree_mul hp_ne_zero, Polynomial.natDegree_C, add_zero]
    · rfl
    · simp [hlc_ne_zero]
  refine ⟨g, hg_monic, hg_irred, hg_dvd_f, ?_⟩
  rw [hg_deg]
  exact hp_odd

/-- Any odd-degree finite field extension `K/F` of an ordered field `F` admits an ordering
making it ordered. -/
theorem exists_isOrderedAlgebra_of_odd_finrank
    [FiniteDimensional F K] (hodd : Odd (Module.finrank F K)) :
    ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K := by
  -- Strong induction on n = finrank F K, varying K
  suffices h : ∀ n : ℕ, Odd n → ∀ (K : Type*) [Field K] [Algebra F K]
      [FiniteDimensional F K], Module.finrank F K = n →
      ∃ _ : LinearOrder K, IsStrictOrderedRing K ∧ IsOrderedModule F K by
    exact h (Module.finrank F K) hodd K rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn_odd K _ _ _ hfr
    -- Handle n = 1 case
    by_cases hn1 : n = 1
    · subst hn1
      exact exists_isOrderedAlgebra_of_finrank_eq_one hfr
    -- Now n ≥ 3 is odd.
    -- We proceed by contradiction via exists_isOrderedAlgebra_iff_neg_one_notMem_span_nonneg_isSquare.
    rw [Field.exists_isOrderedAlgebra_iff_neg_one_notMem_span_nonneg_isSquare]
    intro hmem
    -- Get primitive element α for K/F
    haveI : PerfectField F := PerfectField.ofCharZero
    haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.of_finite F K
    obtain ⟨α, hα⟩ := Field.exists_primitive_element F K
    -- minpoly of α
    set p : F[X] := minpoly F α with hp_def
    have hα_int : IsIntegral F α := Algebra.IsIntegral.isIntegral α
    have hp_monic : p.Monic := minpoly.monic hα_int
    have hp_ne_zero : p ≠ 0 := hp_monic.ne_zero
    have hp_irr : Irreducible p := minpoly.irreducible hα_int
    have hp_natDeg : p.natDegree = n := by
      have : (minpoly F α).natDegree = Module.finrank F F⟮α⟯ :=
        (IntermediateField.adjoin.finrank hα_int).symm
      rw [this]
      have := IntermediateField.finrank_top F K
      rw [hα] at this
      -- `this : Module.finrank F (⊤ : IntermediateField F K) = Module.finrank F K`
      -- and `Module.finrank F (⊤ : IntermediateField F K) = Module.finrank F K`
      -- We want `Module.finrank F F⟮α⟯ = n`
      rw [← hα] at this
      rw [this, hfr]
    -- Unpack the span membership.
    rw [Submodule.mem_span_set] at hmem
    obtain ⟨c, hc_supp, hc_sum⟩ := hmem
    -- c : K →₀ (nonneg F), c.support ⊆ {x : K | IsSquare x}, sum c = -1
    -- For each y ∈ support c, y is a square; pick sqrt.
    -- Use c.sum fun y r ↦ r • y
    -- Express each y ∈ support c as qᵧ(α) where deg qᵧ < n (via powerBasis).
    -- Key helper: power basis of F⟮α⟯, transferred to K via hα.
    have hpb_dim : (IntermediateField.adjoin.powerBasis hα_int).dim = n := by
      simp [IntermediateField.adjoin.powerBasis, hp_natDeg]
    -- We will define for each y in K a polynomial poly_of y ∈ F[X] with natDegree < n
    -- such that (poly_of y).eval₂ (algebraMap F K) α = y.
    -- Since F⟮α⟯ = ⊤, every element of K is such an evaluation.
    -- Use: K ≃ₐ[F] AdjoinRoot p, then pull back.
    -- Actually the cleanest way:
    -- Use (PowerBasis.equivOfMinpoly) or adjoinEquiv, but let's use adjoin.powerBasis via hα.
    -- Each y ∈ K can be represented via (adjoin.powerBasis hα_int).basis.repr.
    -- Since F⟮α⟯ = ⊤, top equiv gives us access.
    sorry

end Field
