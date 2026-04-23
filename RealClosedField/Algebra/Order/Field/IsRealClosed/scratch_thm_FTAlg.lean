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

open Polynomial

namespace IsRealClosed

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/- Axiomatize S2, S3, S4 from the main file. -/

axiom irreducible_X_sq_add_one' : Irreducible (X ^ 2 + 1 : R[X])

private instance factIrr : Fact (Irreducible (X ^ 2 + 1 : R[X])) :=
  ⟨irreducible_X_sq_add_one'⟩

private abbrev Ri' (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] : Type u := AdjoinRoot (X ^ 2 + 1 : R[X])

private noncomputable instance : Module.Finite R (Ri' R) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis irreducible_X_sq_add_one'.ne_zero).basis

axiom finrank_eq_one_of_odd_finrank'
    (K : Type u) [Field K] [Algebra R K] [Module.Finite R K]
    (h : Odd (Module.finrank R K)) : Module.finrank R K = 1

axiom nonempty_algEquiv_Ri_of_finrank_eq_two'
    (K : Type u) [Field K] [Algebra R K] (h : Module.finrank R K = 2) :
    Nonempty (K ≃ₐ[R] Ri' R)

axiom no_quadratic_ext_Ri'
    (M : Type u) [Field M] [Algebra (Ri' R) M] (h : Module.finrank (Ri' R) M = 2) : False

/-- Key lemma: Any finite Galois extension of an RCF has order a power of 2. -/
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
  -- n = 2^k * q with q odd
  set k := Nat.factorization n 2 with hkdef
  set q := n / 2 ^ k with hqdef
  have h2_prime : Nat.Prime 2 := Nat.prime_two
  haveI : Fact (Nat.Prime 2) := ⟨h2_prime⟩
  have hn_split : n = 2 ^ k * q := by
    rw [hqdef, hkdef]; exact (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
  have hq_odd : ¬ 2 ∣ q := Nat.not_dvd_ordCompl h2_prime hn_ne
  -- Sylow: exists subgroup H of order 2^k
  obtain ⟨H, hH_card⟩ : ∃ H : Subgroup G, Nat.card H = 2 ^ k := by
    refine Sylow.exists_subgroup_card_pow_prime 2 ?_
    exact ⟨q, hn_split⟩
  -- The fixed field of H has degree q over R, which is odd
  let M : IntermediateField R L := IntermediateField.fixedField H
  have hM_finrank_L : Module.finrank M L = 2 ^ k := by
    rw [← hH_card]; exact IntermediateField.finrank_fixedField_eq_card H
  -- Tower law: finrank R M * finrank M L = finrank R L
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
  -- M is finite-dim over R
  haveI : FiniteDimensional R M := inferInstance
  -- Apply S2
  have hq_1 : q = 1 := by
    have hOdd : Odd q := by
      rcases Nat.even_or_odd q with he | ho
      · exact absurd he.two_dvd hq_odd
      · exact ho
    have hfM := hM_finrank
    rw [← hfM] at hOdd
    have := finrank_eq_one_of_odd_finrank' (R := R) M hOdd
    rw [hM_finrank] at this
    exact this
  -- So n = 2^k
  have hn_pow : n = 2 ^ k := by rw [hn_split, hq_1, mul_one]
  refine ⟨k, ?_⟩
  rw [← hn_eq]; exact hn_pow

/-- Any finite Galois extension of an RCF has degree 1 or 2. -/
private theorem finrank_le_two_of_galois
    (L : Type u) [Field L] [Algebra R L] [FiniteDimensional R L] [IsGalois R L] :
    Module.finrank R L ≤ 2 := by
  obtain ⟨k, hkeq⟩ := finrank_pow_two_of_galois (R := R) L
  -- Show k ≤ 1
  rw [hkeq]
  by_contra hcontra
  push_neg at hcontra
  have hk_ge2 : 2 ≤ k := by
    by_contra h
    push_neg at h
    interval_cases k <;> omega
  -- Given finrank R L = 2^k with k ≥ 2, find contradiction via S4.
  haveI : Finite (L ≃ₐ[R] L) := by
    have h : Nat.card (L ≃ₐ[R] L) = Module.finrank R L := IsGalois.card_aut_eq_finrank R L
    have hpos : 0 < Module.finrank R L := Module.finrank_pos
    rw [← h] at hpos
    exact Nat.finite_of_card_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGcard : Nat.card (L ≃ₐ[R] L) = 2 ^ k := by
    rw [IsGalois.card_aut_eq_finrank, hkeq]
  -- Get subgroup H₁ of G with |H₁| = 2^{k-1}
  obtain ⟨H₁, hH₁_card⟩ : ∃ H₁ : Subgroup (L ≃ₐ[R] L), Nat.card H₁ = 2 ^ (k - 1) := by
    refine Sylow.exists_subgroup_card_pow_prime 2 ?_
    rw [hGcard]; exact pow_dvd_pow 2 (Nat.sub_le k 1)
  -- M = fixed field of H₁, finrank R M = 2
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
  -- Apply S3: M ≃ₐ[R] Ri' R
  obtain ⟨e⟩ : Nonempty (M ≃ₐ[R] Ri' R) :=
    nonempty_algEquiv_Ri_of_finrank_eq_two' (R := R) M hM_finrank
  -- Get H₂ ≤ H₁ with |H₂| = 2^{k-2}
  haveI : Finite H₁ := Nat.finite_of_card_ne_zero (by rw [hH₁_card]; positivity)
  obtain ⟨H₂, hH₂_card⟩ : ∃ H₂ : Subgroup H₁, Nat.card H₂ = 2 ^ (k - 2) := by
    refine Sylow.exists_subgroup_card_pow_prime 2 ?_
    rw [hH₁_card]; exact pow_dvd_pow 2 (by omega)
  -- Embed H₂ into G
  let H₂' : Subgroup (L ≃ₐ[R] L) := H₂.map H₁.subtype
  have hH₂'_card : Nat.card H₂' = 2 ^ (k - 2) := by
    rw [← hH₂_card]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective H₂ H₁.subtype H₁.subtype_injective).symm.toEquiv
  -- N = fixed field of H₂'
  let N : IntermediateField R L := IntermediateField.fixedField H₂'
  have hNL_finrank : Module.finrank N L = 2 ^ (k - 2) := by
    rw [← hH₂'_card]; exact IntermediateField.finrank_fixedField_eq_card H₂'
  have hH₂'_le_H₁ : H₂' ≤ H₁ := by
    intro x hx
    rcases hx with ⟨y, _, rfl⟩
    exact y.property
  have hM_le_N : M ≤ N := IntermediateField.fixedField_antitone hH₂'_le_H₁
  -- finrank R N = 4
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
  -- relfinrank M N = 2
  have hrel_MN : IntermediateField.relfinrank M N = 2 := by
    have := IntermediateField.finrank_bot_mul_relfinrank hM_le_N
    rw [hM_finrank, hN_finrank] at this
    omega
  -- Use extendScalars: N viewed as IntermediateField M L, with finrank M = 2
  let N' : IntermediateField M L := IntermediateField.extendScalars hM_le_N
  have hMN'_finrank : Module.finrank M N' = 2 := by
    rw [← IntermediateField.relfinrank_eq_finrank_of_le hM_le_N]
    exact hrel_MN
  -- Transport Algebra structure: Ri' R → M → N' via e.symm
  let f : Ri' R →+* N' :=
    (algebraMap M N').comp (e.symm : Ri' R →+* M)
  letI : Algebra (Ri' R) N' := f.toAlgebra
  -- Transfer finrank via `Algebra.finrank_eq_of_equiv_equiv`
  have hRiN_finrank : Module.finrank (Ri' R) N' = 2 := by
    have hswap : Module.finrank (Ri' R) N' = Module.finrank M N' := by
      refine Algebra.finrank_eq_of_equiv_equiv (e.symm : Ri' R ≃+* M) (RingEquiv.refl N') ?_
      ext x
      show f x = algebraMap M N' (e.symm x)
      rfl
    rw [hswap, hMN'_finrank]
  exact no_quadratic_ext_Ri' (R := R) N' hRiN_finrank

/-- Any finite Galois extension of an RCF has degree 1 or 2. -/
private theorem finrank_one_or_two_of_galois
    (L : Type u) [Field L] [Algebra R L] [FiniteDimensional R L] [IsGalois R L] :
    Module.finrank R L = 1 ∨ Module.finrank R L = 2 := by
  have h : Module.finrank R L ≤ 2 := finrank_le_two_of_galois (R := R) L
  have hpos : 0 < Module.finrank R L := Module.finrank_pos
  interval_cases (Module.finrank R L) <;> simp_all <;> omega

theorem finrank_eq_one_or_two_of_finite
    (K : Type u) [Field K] [Algebra R K] [Module.Finite R K] [Nontrivial K] :
    Module.finrank R K = 1 ∨ Module.finrank R K = 2 := by
  haveI : CharZero R := IsStrictOrderedRing.toCharZero
  haveI : Algebra.IsAlgebraic R K := Algebra.IsAlgebraic.of_finite R K
  -- Step 1: embed K into an algebraic closure of R
  let AR : Type u := AlgebraicClosure R
  let φ : K →ₐ[R] AR := IsAlgClosed.lift
  have hφ_inj : Function.Injective φ := φ.toRingHom.injective
  -- L = normalClosure of K over R inside AR, an IntermediateField
  let L : IntermediateField R AR := IntermediateField.normalClosure R K AR
  haveI hfin_L : FiniteDimensional R L := normalClosure.is_finiteDimensional R K AR
  haveI hgal_L : IsGalois R L := by
    haveI : Algebra.IsSeparable R K := Algebra.IsAlgebraic.isSeparable_of_perfectField
    exact IsGalois.normalClosure R K AR
  -- The image of K under φ lies inside L
  have hrange_le : φ.fieldRange ≤ L := AlgHom.fieldRange_le_normalClosure φ
  let K' : IntermediateField R AR := φ.fieldRange
  -- K' ≃ₐ[R] K
  have hKK' : Module.finrank R K = Module.finrank R K' := by
    let eq : K ≃ₐ[R] φ.range := AlgEquiv.ofInjectiveField φ
    have h1 : Module.finrank R K = Module.finrank R φ.range :=
      LinearEquiv.finrank_eq eq.toLinearEquiv
    have h2 : Module.finrank R K' = Module.finrank R φ.range :=
      (IntermediateField.finrank_eq_finrank_subalgebra K').symm
    rw [h1, ← h2]
  -- Tower: finrank R K' ∣ finrank R AR (but we want finrank R L). Use the ≤ relation K' ≤ L.
  have hdvd : Module.finrank R K' ∣ Module.finrank R L := by
    -- Use IntermediateField.finrank_bot_mul_relfinrank
    have htower := IntermediateField.finrank_bot_mul_relfinrank hrange_le
    exact ⟨_, htower.symm⟩
  -- Combine
  rw [hKK']
  rcases finrank_one_or_two_of_galois (R := R) L with hL1 | hL2
  · rw [hL1] at hdvd
    left; exact Nat.dvd_one.mp hdvd
  · rw [hL2] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · left; exact h
    · right; exact h

end IsRealClosed
