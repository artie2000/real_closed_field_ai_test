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
import Mathlib.Tactic.TFAE

open Polynomial

namespace IsRealClosed

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

-- Auxiliary lemma: Part A (nonneg => square) via AdjoinRoot of X^2 - C a.
private theorem aux_isSquare_of_nonneg
    (h : ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
         [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K],
         Function.Bijective (algebraMap R K))
    {a : R} (ha : 0 ≤ a) : IsSquare a := by
  by_contra hsq
  -- p := X^2 - C a is irreducible since a is not a square (no root of deg-2 poly)
  set p : R[X] := X ^ 2 - C a with hp_def
  have hp_monic : p.Monic := by
    unfold_let p; exact (monic_X_pow_sub_C a (by decide : 2 ≠ 0))
  have hp_deg : p.natDegree = 2 := by
    unfold_let p; exact natDegree_X_pow_sub_C
  have hp_ne_zero : p ≠ 0 := hp_monic.ne_zero
  have hp_no_root : ∀ c : R, ¬ p.IsRoot c := by
    intro c hc
    simp [hp_def, IsRoot, sub_eq_zero] at hc
    -- hc : c ^ 2 = a  (or a = c^2)
    exact hsq ⟨c, by linear_combination hc.symm⟩
  have hp_irred : Irreducible p := by
    refine (Polynomial.Monic.irreducible_iff_natDegree' hp_monic).mpr ⟨?_, ?_⟩
    · rw [hp_deg]; decide
    · intro g₁ g₂ hg_prod hg_deg
      rcases hg_deg with ⟨hg1, hg2⟩
      -- If g1 is of degree 1 it has a root, which is a root of p
      rw [hp_deg] at hg2
      -- g1.natDegree ∈ Ioc 0 (2/2) = {1}
      interval_cases g₁.natDegree
      · have : ∃ c, g₁.IsRoot c := by
          have hg1_ne : g₁ ≠ 0 := by
            intro he; rw [he, zero_mul] at hg_prod; exact hp_ne_zero hg_prod.symm
          exact ⟨-(g₁.coeff 0 / g₁.coeff 1), by
            have h1 : g₁.natDegree = 1 := by assumption
            have : g₁ = C (g₁.coeff 1) * X + C (g₁.coeff 0) := by
              conv_lhs => rw [g₁.as_sum_range_C_mul_X_pow, h1]
              simp [Finset.sum_range_succ]
              ring
            rw [IsRoot, this]
            have hc1 : g₁.coeff 1 ≠ 0 := by
              intro he
              have := leadingCoeff_eq_zero (p := g₁) |>.mp
              have : g₁.leadingCoeff = 0 := by
                rw [leadingCoeff, (by assumption : g₁.natDegree = 1), he]
              rw [leadingCoeff_eq_zero] at this
              exact hg1_ne this
            simp; field_simp; ring⟩
        obtain ⟨c, hc⟩ := this
        have : p.IsRoot c := by
          rw [show p = g₁ * g₂ from hg_prod]
          simp [IsRoot, hc]
        exact hp_no_root c this
  -- Set up K := AdjoinRoot p
  haveI : Fact (Irreducible p) := ⟨hp_irred⟩
  haveI : Module.Finite R (AdjoinRoot p) := hp_monic.finite_adjoinRoot
  haveI : Algebra.IsAlgebraic R (AdjoinRoot p) := Algebra.IsAlgebraic.of_finite R (AdjoinRoot p)
  -- Construct linear functional π : K → R with π((u + v·root)^2) ≥ 0
  -- Using the R-basis {1, root p} from powerBasis'
  set pb : PowerBasis R (AdjoinRoot p) := AdjoinRoot.powerBasis' hp_monic
  have hpb_dim : pb.dim = 2 := by unfold_let pb; simp [AdjoinRoot.powerBasis', hp_deg]
  -- Define linear projection: take first coordinate in the basis
  -- Use `pb.basis.coord 0` which is the 0th coordinate functional
  let π : AdjoinRoot p →ₗ[R] R := pb.basis.coord ⟨0, by rw [hpb_dim]; decide⟩
  -- π(1) = 1: the basis maps index 0 to root^0 = 1
  have hπ_one : π 1 = 1 := by
    unfold_let π
    have : (1 : AdjoinRoot p) = pb.basis ⟨0, by rw [hpb_dim]; decide⟩ := by
      simp [pb, AdjoinRoot.powerBasis']
    rw [this]
    exact pb.basis.coord_apply_self _
  -- For any u v : R, π(u + v · root p) = u
  have hπ_lin : ∀ u v : R, π (algebraMap R _ u + v • pb.gen) = u := by
    intro u v
    have h_gen : pb.gen = pb.basis ⟨1, by rw [hpb_dim]; decide⟩ := by
      simp [pb, AdjoinRoot.powerBasis']
    have h_one : (1 : AdjoinRoot p) = pb.basis ⟨0, by rw [hpb_dim]; decide⟩ := by
      simp [pb, AdjoinRoot.powerBasis']
    -- algebraMap R _ u = u • 1
    rw [Algebra.algebraMap_eq_smul_one, h_one, h_gen]
    unfold_let π
    rw [map_add, map_smul, map_smul, Basis.coord_apply_self, Basis.coord_apply_ne]
    · ring
    · decide
  sorry

theorem of_bijective_algebraMap_of_isOrderedAlgebra
    (h : ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
         [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K],
         Function.Bijective (algebraMap R K)) :
    IsRealClosed R := by
  sorry

end IsRealClosed
