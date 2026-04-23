# Session progress — rcf-equiv-conds-clean-test

Blueprint: `numina/blueprints/rcf-equiv-conds-clean-test/rcf-equiv-conds-clean-test.tex`
Target: `thm:RCF_tfae_ord` — characterisation of real closed fields among ordered fields.

## Overall state

`IsRealClosed.tfae_ord` compiles sorry-free at the tactic-script level against
four helper lemmas:

- **[PROVED]** `IsRealClosed.of_ivp` (`thm:IVP_poly_imp_RCF`)
- **[PROVED]** `IsRealClosed.of_bijective_algebraMap_of_isOrderedAlgebra` (`thm:ord_max_imp_RCF`)
- **[sorry]** `IsRealClosed.exists_isRoot_of_nonpos_of_nonneg` (`lem:IVP_poly`)
  — still sorry in main file at line 41. Will become `exact ivp_poly hab ha hb`
  once S10 is merged.
- **[sorry]** `IsRealClosed.bijective_algebraMap_of_isOrderedAlgebra` (`lem:RCF_max_ord`)
  — still sorry in main file at line 165. Will become
  `exact bijective_algebraMap_of_isOrderedAlgebra' K` once S8 is proved.

The supporting FTA-for-RCF development lives in
`RealClosedField/Algebra/Order/Field/IsRealClosed/Closure.lean`.

## Sub-lemma status (S1–S10)

| Code | Name | Status |
|------|------|--------|
| S1 | `isSquare_of_isSumSq` | **[PROVED]** (inline, 2 lines) |
| S2 | `finrank_eq_one_of_odd_finrank` | **[PROVED]** |
| S3 | `nonempty_algEquiv_Ri_of_finrank_eq_two` | **[PROVED]** |
| S4 | `Ri_isSquare` | **[PROVED]** (~150 lines) |
| — | `no_quadratic_ext_Ri` | **[PROVED]** |
| — | `finrank_pow_two_of_galois` (private) | **[PROVED]** |
| — | `finrank_le_two_of_galois` (private) | **[PROVED]** |
| — | `finrank_one_or_two_of_galois` (private) | **[PROVED]** |
| S5 | `finrank_eq_one_or_two_of_finite` | **[PROVED]** |
| S6 | `finite_of_isAlgebraic` | **[PROVED]** |
| S9 | `natDegree_eq_one_or_forall_eval_pos_of_irreducible` | **[PROVED]** |
| S10 | `ivp_poly` | **[proved, NOT YET MERGED]** body in `scratch_s10.lean` |
| S8 | `bijective_algebraMap_of_isOrderedAlgebra'` | **[sorry]** |

Current Closure.lean sorries: two (lines 729 and 736), for S10 and S8
respectively. The S10 sorry is ready to be replaced; S8 still needs a
proof.

## Unmerged S10 proof

File `scratch_s10.lean` at the repo root contains a verified proof of
`IsRealClosed.ivp_poly` built over an axiom for S9. To merge:

1. Replace the `sorry` at `Closure.lean:729` (body of `theorem ivp_poly`)
   with the tactic block from `scratch_s10.lean` lines 19–114 (everything
   after `:= by`, starting with
   `induction hn : f.natDegree using Nat.strong_induction_on generalizing f a b with`).
2. Re-verify via `lean_diagnostic_messages` on Closure.lean — expect a
   single remaining sorry (S8).
3. Delete `scratch_s10.lean`.

The proof uses strong induction on `f.natDegree`, extracts a monic
irreducible factor via `Polynomial.exists_monic_irreducible_factor`,
applies S9 to split `g` into linear vs always-positive, and for the linear
case trichotomises on whether the root `r = -g.coeff 0` lies before `a`,
after `b`, or inside `[a, b]`.

## Outstanding: S8 (`bijective_algebraMap_of_isOrderedAlgebra'`)

Located at `Closure.lean:732`. Signature:

```
theorem bijective_algebraMap_of_isOrderedAlgebra'
    (K : Type u) [Field K] [Algebra R K] [Algebra.IsAlgebraic R K]
    [LinearOrder K] [IsStrictOrderedRing K] [IsOrderedModule R K] :
    Function.Bijective (algebraMap R K)
```

Proof strategy (depends on S3, S5, S6):

1. Take a primitive element `α : K` over `R` (use `Field.exists_primitive_element`
   via `Algebra.IsSeparable` which holds in char 0).
2. Let `L = R⟮α⟯` as an intermediate field; by S6 it is finite-dimensional.
3. By S5, `finrank R L ∈ {1, 2}`.
4. If `finrank = 1`, `algebraMap R L` is bijective, hence `algebraMap R K`
   is surjective (and always injective for a field hom); conclude.
5. If `finrank = 2`, by S3 there is `φ : L ≃ₐ[R] Ri R`. Transport
   `AdjoinRoot.root (X^2 + 1)` back to `L` to get `i : L` with `i^2 = -1`.
   This contradicts `sq_nonneg` in the ordered field `K ⊇ L`.
6. Conclude `K = R` and `algebraMap R K` is bijective.

Delegate to a prover subagent with a scratch file axiomatising S3, S5, S6,
plus `Ri R`, `not_isSquare_neg_one`, etc. See `scratch_s10.lean` for the
shim pattern.

## Wiring to main file (after S8)

Two final edits in `RealClosedField/Algebra/Order/Field/IsRealClosed.lean`:

- Line 41 (`exists_isRoot_of_nonpos_of_nonneg` body):
  replace `sorry` with `exact ivp_poly hab ha hb`.
- Line 165 (`bijective_algebraMap_of_isOrderedAlgebra` body):
  replace `sorry` with `exact bijective_algebraMap_of_isOrderedAlgebra' K`
  (signature may need `(R := R)` or similar explicit args — verify via LSP).

Then `lean_diagnostic_messages` on both files should report zero sorries,
and `IsRealClosed.tfae_ord` is complete.

## Files touched this session

- `RealClosedField/Algebra/Order/Field/IsRealClosed/Closure.lean` — heavy work.
  Added sorry-free proofs for S2, S3, S4, no_quadratic_ext_Ri, S5 (+ 3 private
  helpers), S6, S9. Added imports:
  ```
  import Mathlib.FieldTheory.Fixed
  import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
  import Mathlib.FieldTheory.Relrank
  import Mathlib.GroupTheory.SpecificGroups.Cyclic
  ```
- `scratch_s10.lean` — NEW, still at repo root. Delete after merging S10.
- `RealClosedField/Algebra/Order/Field/IsRealClosed.lean` — untouched.
  Still has the two sorries at lines 41 and 165.

## Blueprint metadata

Not yet updated. After wiring completes, refresh blueprint statuses for:
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
  `Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra` (both already in the
  imports of Closure.lean).

## Operational notes

- Bash cannot run `lake env lean` directly; delegate build/verification to
  prover subagents or use MCP `lean_diagnostic_messages` for inspection.
- Run at most one prover subagent at a time per user instruction.
- API 529 overload was observed when dispatching large prover jobs; back off
  via `ScheduleWakeup` (~240s) and retry.

## Resume prompt

To resume in a fresh context:

1. Re-read `NUMINA_PROGRESS.md` and `Closure.lean` (specifically around
   lines 725–740 for the two remaining sorries).
2. Merge `scratch_s10.lean` into `Closure.lean` (replace sorry at 729),
   delete scratch, verify via `lean_diagnostic_messages`.
3. Dispatch a prover subagent for S8 (`bijective_algebraMap_of_isOrderedAlgebra'`).
   Provide axiomatised shims for S3, S5, S6, `Ri R`, and
   `not_isSquare_neg_one`. Follow strategy outlined above.
4. Merge S8 proof body.
5. Wire the two sorries in the main `IsRealClosed.lean` (lines 41, 165) to
   the proved lemmas. Verify via `lean_diagnostic_messages`.
6. Update blueprint metadata (use `mcp__blueprint-tools__refresh_blueprint_metadata`
   then `mcp__blueprint-tools__set_declaration_status` per-declaration).
