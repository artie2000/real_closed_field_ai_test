# Session progress — rcf-equiv-conds-clean-test

Blueprint: `numina/blueprints/rcf-equiv-conds-clean-test/rcf-equiv-conds-clean-test.tex`
Target: `thm:RCF_tfae_ord` — characterisation of real closed fields among ordered fields.

## Overall state

`IsRealClosed.tfae_ord` compiles sorry-free. All four helper lemmas proved:

- **[PROVED]** `IsRealClosed.of_ivp` (`thm:IVP_poly_imp_RCF`)
- **[PROVED]** `IsRealClosed.of_bijective_algebraMap_of_isOrderedAlgebra` (`thm:ord_max_imp_RCF`)
- **[PROVED]** `IsRealClosed.exists_isRoot_of_nonpos_of_nonneg` (`lem:IVP_poly`)
- **[PROVED]** `IsRealClosed.bijective_algebraMap_of_isOrderedAlgebra` (`lem:RCF_max_ord`)

The supporting FTA-for-RCF development lives in
`RealClosedField/Algebra/Order/Field/IsRealClosed/Closure.lean` (zero sorries).
The top-level file
`RealClosedField/Algebra/Order/Field/IsRealClosed.lean` now imports Closure and
discharges its two former sorries with one-line term mode proofs.

## Sub-lemma status (S1–S10)

| Code | Name | Status |
|------|------|--------|
| S1 | `isSquare_of_isSumSq` | **[PROVED]** (inline, 2 lines) |
| S2 | `finrank_eq_one_of_odd_finrank` | **[PROVED]** |
| S3 | `nonempty_algEquiv_Ri_of_finrank_eq_two` | **[PROVED]** |
| S4 | `Ri_isSquare` | **[PROVED]** |
| — | `no_quadratic_ext_Ri` | **[PROVED]** |
| — | `finrank_pow_two_of_galois` (private) | **[PROVED]** |
| — | `finrank_le_two_of_galois` (private) | **[PROVED]** |
| — | `finrank_one_or_two_of_galois` (private) | **[PROVED]** |
| S5 | `finrank_eq_one_or_two_of_finite` | **[PROVED]** |
| S6 | `finite_of_isAlgebraic` | **[PROVED]** |
| S8 | `bijective_algebraMap_of_isOrderedAlgebra'` | **[PROVED]** |
| S9 | `natDegree_eq_one_or_forall_eval_pos_of_irreducible` | **[PROVED]** |
| S10 | `ivp_poly` | **[PROVED]** |

`lake build` passes cleanly. `lean_diagnostic_messages` on both target files
reports zero errors.

## Files touched this session

- `RealClosedField/Algebra/Order/Field/IsRealClosed/Closure.lean`
  - Added imports: `Mathlib.FieldTheory.Fixed`,
    `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`,
    `Mathlib.FieldTheory.Relrank`,
    `Mathlib.GroupTheory.SpecificGroups.Cyclic`,
    `Mathlib.LinearAlgebra.Trace`.
  - Proved S2–S6, S9, S10, and S8 (plus the private Galois helpers and
    `no_quadratic_ext_Ri`).
- `RealClosedField/Algebra/Order/Field/IsRealClosed.lean`
  - Added import of `Closure`.
  - Discharged the two remaining sorries with term mode proofs calling
    `ivp_poly` and `bijective_algebraMap_of_isOrderedAlgebra'`.
- Scratch files deleted: `scratch_s10.lean`, `scratch_s8.lean`.

## Blueprint metadata

Not yet updated. After wiring, refresh blueprint statuses for:
`isSquare_of_isSumSq`, `finrank_eq_one_of_odd_finrank`, `Ri_isSquare`,
`nonempty_algEquiv_Ri_of_finrank_eq_two`, `no_quadratic_ext_Ri`,
`finrank_eq_one_or_two_of_finite`, `finite_of_isAlgebraic`,
`natDegree_eq_one_or_forall_eval_pos_of_irreducible`, `ivp_poly`,
`bijective_algebraMap_of_isOrderedAlgebra'`,
`exists_isRoot_of_nonpos_of_nonneg`, `bijective_algebraMap_of_isOrderedAlgebra`,
and `tfae_ord` itself.

## Known Mathlib path issues

- `Mathlib.FieldTheory.Adjoin` has been renamed/split. Use
  `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic` and
  `Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra`.

## Operational notes

- Bash cannot run `lake env lean` directly; use `lean_build` via MCP or
  delegate to prover subagents.
- API 529 overload was observed previously when dispatching large prover jobs.

## Resume prompt

Remaining work is blueprint metadata only:

1. `mcp__blueprint-tools__refresh_blueprint_metadata`.
2. For each declaration listed above in “Blueprint metadata”, call
   `mcp__blueprint-tools__set_declaration_status` to mark it proved.
