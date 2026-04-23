# Session progress — rcf-equiv-conds-clean-test

Blueprint: `numina/blueprints/rcf-equiv-conds-clean-test/rcf-equiv-conds-clean-test.tex`
Target: `thm:RCF_tfae_ord` — characterisation of real closed fields among ordered fields.

Main Lean file: `RealClosedField/Algebra/Order/Field/IsRealClosed.lean`.

## State

`IsRealClosed.tfae_ord` compiles sorry-free (at the tactic-script level) against
four helper lemmas. The TFAE proof wires together (1↔2) and (1↔3).

Of the four helper lemmas:

- **[PROVED]** `IsRealClosed.of_ivp`  (blueprint `thm:IVP_poly_imp_RCF`)
  - Uses `IsRealClosed.of_linearOrderedField`.
  - Non-negatives are squares via IVP on `X^2 - C a` on `[0, a+1]`.
  - Odd-degree polynomials get a root via IVP at `±M` for
    `M = (B+1)/a_n + 1` where `B = ∑ |coeff_i|`; bound `|tail| ≤ x^{n-1} B`.
  - Blueprint status: `proved`.

- **[PROVED]** `IsRealClosed.of_bijective_algebraMap_of_isOrderedAlgebra`
  (blueprint `thm:ord_max_imp_RCF`)
  - Does NOT need FTA.
  - Proof via `IsRealClosed.of_linearOrderedField`:
    - Squares: adjoin `√a` for nonsquare nonneg `a ≥ 0`, project via
      `hm.coeff _ 0`, compute `π((u + v√a)²) = u² + av² ≥ 0`.
      Uses `Field.exists_isOrderedAlgebra_iff_neg_one_notMem_span_nonneg_isSquare`.
    - Odd degree: strong induction on the natDegree of an odd irreducible
      factor (Artin-Schreier). If `-1 ∈ span_{R≥0} {squares}` in `AdjoinRoot g`,
      lift to `R[X]` as `(∑ cᵢ pᵢ²) + 1 = h · g`, show the LHS has `natDegree = 2d`
      via leading-coeff analysis, so `h.natDegree = 2d - g.natDegree` is odd and
      smaller, then descend to an irreducible factor of `h`, contradicting IH.
  - Blueprint status: `proved`.

- **[sorry]** `IsRealClosed.exists_isRoot_of_nonpos_of_nonneg`  (`lem:IVP_poly`)
  - Requires FTA for RCF / classification of irreducibles over an RCF.
  - Not in Mathlib; substantial infrastructure (Sylow + Galois) required.

- **[sorry]** `IsRealClosed.bijective_algebraMap_of_isOrderedAlgebra`  (`lem:RCF_max_ord`)
  - Also requires FTA for RCF (via `lem:RCF_max`).

## Mathlib shortcut check

Mathlib does NOT have FTA for general RCF:
- `Irreducible.natDegree_le_two` is ℝ-only (uses `IsAlgClosed ℂ`).
- `Polynomial.IsMonicOfDegree.eq_isMonicOfDegree_two_mul_isMonicOfDegree` has
  TODO comment "generalize to real closed fields when they are available".

So the two remaining sorries require formalising FTA for RCF from scratch.

## Plan to resume

The two remaining sorries (`exists_isRoot_of_nonpos_of_nonneg`,
`bijective_algebraMap_of_isOrderedAlgebra`) both need FTA for RCF. The blueprint
decomposes this via:

- `lem:RCF_sumsq_is_sq` — in an RCF every sum of squares is a square
- `lem:alg_ext_odd_deg` — no odd-degree algebraic extensions of an RCF
- `lem:ext_deg_2` — classification of degree-2 extensions
- `lem:Ri_ext_deg_2` — `R[i]` is degree 2 over `R`
- `thm:FTAlg` — FTA for RCF: `R[i]` is algebraically closed
- `cor:FTAlg_alg` — irreducibles over `R` have degree 1 or 2
- `lem:RCF_max` — RCF has no nontrivial algebraic extensions (ordered)
- `lem:irreds_class` — classification by signs of the constant term

This is a multi-day formalisation effort requiring Sylow + Galois theory
chaining. Confirm with user whether to attempt.

## Files touched this session

- `RealClosedField/Algebra/Order/Field/IsRealClosed.lean`
  — `of_ivp` + `of_bijective_algebraMap_of_isOrderedAlgebra` proved.
  Helper lemmas: `irreducible_X_sq_sub_C_of_not_isSquare`,
  `algebraMap_not_bijective_of_irreducible_natDegree_pos`,
  `not_exists_ordered_algebra_of_bijective`, `exists_odd_irreducible_factor`,
  `exists_ordered_algebra_adjoinRoot_odd_irreducible`,
  `exists_ordered_algebra_adjoinRoot_sq_sub_C`.
- `RealClosedField.lean` — added import for new file.
- `numina/blueprints/rcf-equiv-conds-clean-test/rcf-equiv-conds-clean-test.tex`
  — populated blueprint content and `\lean{}` tags.
- `numina/.metadata/blueprints/rcf-equiv-conds-clean-test/declarations/thm:IVP_poly_imp_RCF.json`
  — status `proved`.
- `numina/.metadata/blueprints/rcf-equiv-conds-clean-test/declarations/thm:ord_max_imp_RCF.json`
  — status `proved`.
