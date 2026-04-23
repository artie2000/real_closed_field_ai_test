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
  -- Want to show k ≤ 1
  by_contra hcontra
  push_neg at hcontra
  rw [hkeq] at hcontra
  -- 2^k > 2 means k ≥ 2
  have hk_ge2 : 2 ≤ k := by
    by_contra h
    push_neg at h
    interval_cases k <;> simp_all <;> omega
  -- Given that finrank R L = 2^k with k ≥ 2, find contradiction via S4.
  -- Strategy: G = Gal(L/R), order 2^k. A 2-Sylow is all of G.
  -- Take subgroup H₁ ≤ G with |H₁| = 2^{k-1}, hence index 2 in G.
  haveI : Finite (L ≃ₐ[R] L) := by
    have h : Nat.card (L ≃ₐ[R] L) = Module.finrank R L := IsGalois.card_aut_eq_finrank R L
    have hpos : 0 < Module.finrank R L := Module.finrank_pos
    rw [← h] at hpos
    exact Nat.finite_of_card_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  set G := L ≃ₐ[R] L with hGdef
  set n := Nat.card G with hndef
  have hn_eq : n = Module.finrank R L := IsGalois.card_aut_eq_finrank R L
  have h2_prime : Nat.Prime 2 := Nat.prime_two
  haveI : Fact (Nat.Prime 2) := ⟨h2_prime⟩
  have hn_pow : n = 2 ^ k := by rw [hn_eq]; exact hkeq
  -- Get subgroup H₁ of G with |H₁| = 2^{k-1}
  obtain ⟨H₁, hH₁_card⟩ : ∃ H₁ : Subgroup G, Nat.card H₁ = 2 ^ (k - 1) := by
    refine Sylow.exists_subgroup_card_pow_prime 2 ?_
    rw [hn_pow]
    exact pow_dvd_pow 2 (Nat.sub_le k 1)
  -- M = fixed field of H₁, finrank R M = 2
  let M : IntermediateField R L := IntermediateField.fixedField H₁
  have hML_finrank : Module.finrank M L = 2 ^ (k - 1) := by
    rw [← hH₁_card]; exact IntermediateField.finrank_fixedField_eq_card H₁
  have htower_M : Module.finrank R M * Module.finrank M L = Module.finrank R L :=
    Module.finrank_mul_finrank R M L
  have hM_finrank : Module.finrank R M = 2 := by
    rw [hML_finrank] at htower_M
    rw [hkeq] at htower_M
    have h2k : k = (k - 1) + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
    rw [h2k, pow_succ] at htower_M
    have h2posp : (0 : ℕ) < 2 ^ (k - 1) := Nat.pos_of_ne_zero (pow_ne_zero _ (by decide))
    have : Module.finrank R M * 2 ^ (k-1) = 2 * 2 ^ (k-1) := by
      rw [mul_comm 2 (2 ^ (k-1))] at htower_M
      linarith
    exact Nat.eq_of_mul_eq_mul_right h2posp this
  haveI hM_fd : FiniteDimensional R M := inferInstance
  -- Apply S3: M ≃ₐ[R] Ri' R
  obtain ⟨e⟩ : Nonempty (M ≃ₐ[R] Ri' R) :=
    nonempty_algEquiv_Ri_of_finrank_eq_two' (R := R) M hM_finrank
  -- L has Algebra M structure; transport to give L Algebra (Ri' R) structure
  -- Actually: for the contradiction with S4, we need an intermediate field N between M and L
  -- with [N:M] = 2.
  -- Get H₂ ≤ H₁ with |H₂| = 2^{k-2}, exists since k-1 ≥ 1 so we can take a subgroup.
  obtain ⟨H₂, hH₂_card⟩ : ∃ H₂ : Subgroup G, Nat.card H₂ = 2 ^ (k - 2) := by
    refine Sylow.exists_subgroup_card_pow_prime 2 ?_
    rw [hn_pow]
    exact pow_dvd_pow 2 (Nat.sub_le k 2)
  -- Actually, we need H₂ ≤ H₁, not just H₂ ≤ G. Let me use subgroup-of-H₁ approach.
  -- Use Sylow.exists_subgroup_card_pow_prime applied to H₁ with power k-2.
  haveI : Finite H₁ := Finite.of_fintype _
  obtain ⟨H₂, hH₂_card⟩ : ∃ H₂ : Subgroup H₁, Nat.card H₂ = 2 ^ (k - 2) := by
    refine Sylow.exists_subgroup_card_pow_prime 2 ?_
    rw [hH₁_card]
    exact pow_dvd_pow 2 (by omega : k - 2 ≤ k - 1)
  -- Embed H₂ into G as a subgroup via H₁
  let H₂' : Subgroup G := H₂.map H₁.subtype
  have hH₂'_card : Nat.card H₂' = 2 ^ (k - 2) := by
    rw [← hH₂_card]
    exact Nat.card_congr (Subgroup.equivMapOfInjective H₂ H₁.subtype H₁.subtype_injective).symm.toEquiv
  -- N = fixed field of H₂'
  let N : IntermediateField R L := IntermediateField.fixedField H₂'
  have hNL_finrank : Module.finrank N L = 2 ^ (k - 2) := by
    rw [← hH₂'_card]; exact IntermediateField.finrank_fixedField_eq_card H₂'
  -- We have M ⊆ N because H₂' ⊆ H₁
  have hH₂'_le_H₁ : H₂' ≤ H₁ := by
    intro x hx
    rcases hx with ⟨y, _, rfl⟩
    exact y.property
  have hM_le_N : M ≤ N := IntermediateField.fixedField_antitone hH₂'_le_H₁
  -- Tower: finrank R N * finrank N L = finrank R L = 2^k
  have htower_N : Module.finrank R N * Module.finrank N L = Module.finrank R L :=
    Module.finrank_mul_finrank R N L
  have hN_finrank_R : Module.finrank R N = 2 ^ 2 ∨ Module.finrank R N = 2 ^ (k - (k - 2)) := by
    right; rw [hkeq] at htower_N; rw [hNL_finrank] at htower_N
    have hkeq' : k = (k - 2) + 2 := by omega
    conv_lhs => rw [show k - (k-2) = 2 from by omega]
    rw [hkeq', pow_add] at htower_N
    have h2posp : (0 : ℕ) < 2 ^ (k - 2) := Nat.pos_of_ne_zero (pow_ne_zero _ (by decide))
    have : Module.finrank R N * 2 ^ (k-2) = 2 ^ 2 * 2 ^ (k-2) := by
      rw [mul_comm (2^2) (2^(k-2))] at htower_N
      linarith
    exact Nat.eq_of_mul_eq_mul_right h2posp this
  -- Now: M ⊆ N, both intermediate fields of L. We need relfinrank M N = 2.
  have hrel_MN : IntermediateField.relfinrank M N = 2 := by
    -- finrank R M * relfinrank M N = finrank R N
    have := IntermediateField.finrank_bot_mul_relfinrank hM_le_N
    rw [hM_finrank] at this
    have hN_finrank : Module.finrank R N = 4 := by
      rcases hN_finrank_R with h1 | h2
      · rw [h1]; norm_num
      · rw [h2]
        have : k - (k - 2) = 2 := by omega
        rw [this]; norm_num
    rw [hN_finrank] at this
    omega
  -- Now we have M ⊆ N, both IntermediateFields of L.
  -- Via M ≃ₐ[R] Ri' R, we have Ri' R Algebra structure on N with finrank 2.
  -- First: N has Algebra M structure (as M ≤ N in L).
  -- The R-algebra isomorphism M ≃ₐ[R] Ri' R makes N into a Ri' R-algebra.
  -- And the finrank of N over M (= Ri' R) is 2.
  -- Apply S4 to get contradiction.
  -- Set up the algebra structure: N has Algebra M via the inclusion M ≤ N, and M ≃ₐ Ri' R.
  haveI : Algebra M N := (IntermediateField.inclusion hM_le_N).toAlgebra
  -- Check finrank M N = 2
  have hMN_finrank : Module.finrank M N = 2 := by
    -- N over M: this is just relfinrank M N = 2
    -- The Algebra M N structure via the inclusion has N's elements viewed as M-module
    sorry
  -- Transport algebra: Algebra (Ri' R) N
  haveI : Algebra (Ri' R) N := (e.symm.toAlgHom.comp (Algebra.ofId M N)).toAlgebra
  -- Transport finrank: finrank Ri' R N = finrank M N via the AlgEquiv e : M ≃ₐ[R] Ri' R
  have hRiN_finrank : Module.finrank (Ri' R) N = 2 := by
    sorry
  exact no_quadratic_ext_Ri' (R := R) N hRiN_finrank

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
