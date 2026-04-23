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

- **[sorry]** `IsRealClosed.exists_isRoot_of_nonpos_of_nonneg`  (`lem:IVP_poly`)
  - Requires FTA for RCF / classification of irreducibles over an RCF.
  - Not in Mathlib; substantial infrastructure (Sylow + Galois) required.

- **[sorry]** `IsRealClosed.bijective_algebraMap_of_isOrderedAlgebra`  (`lem:RCF_max_ord`)
  - Also requires FTA for RCF (via `lem:RCF_max`).

- **[sorry]** `IsRealClosed.of_bijective_algebraMap_of_isOrderedAlgebra`  (`thm:ord_max_imp_RCF`)
  - Does NOT need FTA.
  - Needs blueprint `cor:ext_ord_to_adj_sqrt` and `lem:ext_ord_odd_deg`,
    neither of which is in the repo yet.
  - Main tool already present:
    `Field.exists_isOrderedAlgebra_iff_neg_one_notMem_span_nonneg_isSquare`
    in `RealClosedField/Algebra/Order/Algebra.lean`.

## Plan to resume

Priority order (easiest → hardest):

1. **`of_bijective_algebraMap_of_isOrderedAlgebra`** — feasible without FTA.
   - Implement `cor:ext_ord_to_adj_sqrt`: for `F` ordered, `a ≥ 0` not a square,
     there's an ordered-algebra structure on `AdjoinRoot (X^2 - C a)`.
     Use the projection `π : F(√a) → F`, `π(u + v√a) = u`, noting
     `π((u + v√a)^2) = u^2 + a v^2 ≥ 0`. Combine with
     `Field.exists_isOrderedAlgebra_iff_neg_one_notMem_span_nonneg_isSquare`.
   - Implement `lem:ext_ord_odd_deg`: for `K/F` odd-degree, there's an ordered
     extension. Proof proceeds by strong induction on degree of the minimal
     polynomial; uses the primitive element theorem (`Field.exists_primitive_element`
     in char 0) and manipulates `∑ aᵢ gᵢ^2 ≡ -1 mod f` in `F[X]`.
   - Wire these up to prove the helper via `IsRealClosed.of_linearOrderedField`.

2. **`exists_isRoot_of_nonpos_of_nonneg`** and
   **`bijective_algebraMap_of_isOrderedAlgebra`** — both need FTA for RCF.
   Blueprint decomposes this via `lem:RCF_sumsq_is_sq`, `lem:ext_deg_2`,
   `lem:Ri_ext_deg_2`, `thm:FTAlg`. Significant formalisation effort.

## Files touched this session

- `RealClosedField/Algebra/Order/Field/IsRealClosed.lean` — created; `of_ivp` proved.
- `RealClosedField.lean` — added import for new file.
- `numina/blueprints/rcf-equiv-conds-clean-test/rcf-equiv-conds-clean-test.tex` — populated blueprint content and `\lean{}` tags.
- `numina/.metadata/blueprints/rcf-equiv-conds-clean-test/declarations/thm:IVP_poly_imp_RCF.json` — status `proved`.
