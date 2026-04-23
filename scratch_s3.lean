import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree

open Polynomial
namespace IsRealClosed
universe u
variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

axiom irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : R[X])
private instance : Fact (Irreducible (X ^ 2 + 1 : R[X])) := ⟨irreducible_X_sq_add_one⟩
private abbrev Ri (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] : Type u := AdjoinRoot (X ^ 2 + 1 : R[X])
private noncomputable instance : Module.Finite R (Ri R) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis irreducible_X_sq_add_one.ne_zero).basis

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
  have hirr : Irreducible (minpoly R α) := minpoly.irreducible hint
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
  -- Now α^2 + a * α + b = 0 in K.
  have haeval : α ^ 2 + algebraMap R K a * α + algebraMap R K b = 0 := by
    have h0 : aeval α f = 0 := minpoly.aeval R α
    rw [hab] at h0
    simpa [aeval_def, eval₂_add, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C] using h0
  -- Set β := α + algebraMap R K (a/2)
  set β : K := α + algebraMap R K (a / 2) with hβdef
  -- Compute β^2 = algebraMap R K δ where δ = (a/2)^2 - b
  set δ : R := (a / 2) ^ 2 - b with hδdef
  have hβsq : β ^ 2 = algebraMap R K δ := by
    have haK : algebraMap R K δ = algebraMap R K (a/2) ^ 2 - algebraMap R K b := by
      rw [hδdef, map_sub, map_pow]
    have ha_eq : algebraMap R K a = 2 * algebraMap R K (a/2) := by
      rw [← map_ofNat (algebraMap R K) 2, ← map_mul]
      congr 1; ring
    rw [haK, hβdef]
    have hb_eq : algebraMap R K b = -(α ^ 2 + algebraMap R K a * α) := by
      have := haeval
      linear_combination this
    rw [hb_eq, ha_eq]; ring
  -- Show δ < 0 : if δ ≥ 0, δ is a square, so β = ±sqrt(δ) ∈ image R, so α ∈ image R,
  -- contradicting finrank = 2.
  have hdelta_neg : δ < 0 := by
    by_contra hnn
    push_neg at hnn
    obtain ⟨c, hc⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R) (x := δ)).mp hnn
    -- hc : δ = c * c, so β^2 = (algebraMap c)^2, so (β - c)(β + c) = 0
    have hβsq' : β ^ 2 = (algebraMap R K c) ^ 2 := by
      rw [hβsq, show δ = c * c from hc, sq, map_mul]
    have hprod : (β - algebraMap R K c) * (β + algebraMap R K c) = 0 := by
      have : β ^ 2 - (algebraMap R K c) ^ 2 = 0 := by rw [hβsq']; ring
      linear_combination this
    have hα_range : α ∈ (algebraMap R K).range := by
      rcases mul_eq_zero.mp hprod with h1 | h1
      · have hβeq : β = algebraMap R K c := by linear_combination h1
        refine ⟨c - a / 2, ?_⟩
        have : α = algebraMap R K c - algebraMap R K (a/2) := by
          have hh := hβeq; rw [hβdef] at hh; linear_combination hh
        rw [this, map_sub]
      · have hβeq : β = -algebraMap R K c := by linear_combination h1
        refine ⟨-c - a/2, ?_⟩
        have : α = -algebraMap R K c - algebraMap R K (a/2) := by
          have hh := hβeq; rw [hβdef] at hh; linear_combination hh
        rw [this, map_sub, map_neg]
    have hdeg1 : (minpoly R α).natDegree = 1 := (minpoly.natDegree_eq_one_iff).mpr hα_range
    rw [hnatdeg] at hdeg1
    exact absurd hdeg1 (by norm_num)
  -- Now -δ > 0. Get c with c^2 = -δ.
  have hnegδ_pos : 0 < -δ := by linarith
  obtain ⟨c, hc⟩ :=
    (IsRealClosed.nonneg_iff_isSquare (R := R) (x := -δ)).mp hnegδ_pos.le
  -- c * c = -δ, so c ≠ 0.
  have hcne : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    linarith
  have hcsq_neg : c ^ 2 = -δ := by rw [sq]; exact hc.symm
  -- Define i' := β * (algebraMap R K c)⁻¹.
  set cK : K := algebraMap R K c with hcKdef
  have hcK_ne : cK ≠ 0 := by
    rw [hcKdef]
    exact (map_ne_zero (algebraMap R K)).mpr hcne
  set i' : K := β * cK⁻¹ with hi'def
  have hi'sq : i' ^ 2 = -1 := by
    rw [hi'def, mul_pow, hβsq]
    rw [show (cK⁻¹) ^ 2 = (cK ^ 2)⁻¹ from by rw [inv_pow]]
    rw [show cK ^ 2 = algebraMap R K (-δ) from by rw [hcKdef, ← map_pow, hcsq_neg]]
    rw [← map_inv₀, ← map_mul]
    have hδne : δ ≠ 0 := ne_of_lt hdelta_neg
    have h_eq : δ * (-δ)⁻¹ = -1 := by field_simp
    rw [h_eq]; simp
  -- Build AlgHom Ri R →ₐ[R] K via liftAlgHom
  have h_eval : (X ^ 2 + 1 : R[X]).eval₂ (algebraMap R K) i' = 0 := by
    simp [eval₂_add, eval₂_pow, eval₂_X, eval₂_one, hi'sq]
  set φ : Ri R →ₐ[R] K :=
    AdjoinRoot.liftAlgHom (X ^ 2 + 1 : R[X]) (Algebra.ofId R K) i' h_eval
  -- φ is injective because domain is a field (nontrivial target)
  have hφ_inj : Function.Injective φ := φ.toRingHom.injective
  -- finrank equal, so injective ↔ surjective for the underlying linear map
  have hfinrank_Ri : Module.finrank R (Ri R) = 2 := by
    have hne : (X ^ 2 + 1 : R[X]) ≠ 0 := irreducible_X_sq_add_one.ne_zero
    have hdeg : (X ^ 2 + 1 : R[X]).natDegree = 2 := by
      have h : (X ^ 2 + 1 : R[X]) = X ^ 2 - C (-1 : R) := by simp [sub_neg_eq_add]
      rw [h]; exact natDegree_X_pow_sub_C
    have := (AdjoinRoot.powerBasis hne).finrank
    rw [AdjoinRoot.powerBasis_dim hne] at this
    rw [this, hdeg]
  have heq_rank : Module.finrank R K = Module.finrank R (Ri R) := by rw [h, hfinrank_Ri]
  have hφ_surj : Function.Surjective φ := by
    have : Function.Injective φ.toLinearMap := hφ_inj
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq_rank.symm).mp this
  -- φ is a bijective AlgHom; invert it.
  let ψ : Ri R ≃ₐ[R] K := AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  exact ⟨ψ.symm⟩

end IsRealClosed
