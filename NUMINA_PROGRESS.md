# Session progress — rcf-equiv-conds-clean-test

Blueprint: `numina/blueprints/rcf-equiv-conds-clean-test/rcf-equiv-conds-clean-test.tex`
Target: `thm:RCF_tfae_ord` — characterisation of real closed fields among ordered fields.

## Overall state

`IsRealClosed.tfae_ord` compiles sorry-free at the tactic-script level against
four helper lemmas:

- **[PROVED]** `IsRealClosed.of_ivp` (`thm:IVP_poly_imp_RCF`)
- **[PROVED]** `IsRealClosed.of_bijective_algebraMap_of_isOrderedAlgebra` (`thm:ord_max_imp_RCF`)
- **[sorry]** `IsRealClosed.exists_isRoot_of_nonpos_of_nonneg` (`lem:IVP_poly`)
- **[sorry]** `IsRealClosed.bijective_algebraMap_of_isOrderedAlgebra` (`lem:RCF_max_ord`)

Both sorries require FTA for RCF. Mathlib does NOT provide this (confirmed: only
ℂ-specific FTA exists; `Irreducible.natDegree_le_two` and
`Polynomial.IsMonicOfDegree.eq_isMonicOfDegree_two_mul_isMonicOfDegree` are
both ℝ-only with TODOs to generalise to RCF).

## Session 3 progress: FTA-for-RCF scaffold

Created new file `RealClosedField/Algebra/Order/Field/IsRealClosed/Closure.lean`.
Import added to `RealClosedField.lean`.

Compiles cleanly with remaining sorries. The file defines:

```
private abbrev Ri (R : Type u) ... : Type u := AdjoinRoot (X^2 + 1 : R[X])
```

plus local `Fact (Irreducible (X^2+1))` and `Module.Finite R (Ri R)` instances.

### Sub-lemmas in Closure.lean (plan S1–S10, S7 folded into S8)

| Code | Name | Status |
|------|------|--------|
| S1 | `isSquare_of_isSumSq` | **[PROVED]** (2-line inline) |
| S2 | `finrank_eq_one_of_odd_finrank` | **[PROVED]** (prover subagent) |
| S3 | `nonempty_algEquiv_Ri_of_finrank_eq_two` | sorry |
| S4 | `Ri_isSquare` | sorry |
| — | `no_quadratic_ext_Ri` | sorry |
| S5 | `finrank_eq_one_or_two_of_finite` | sorry |
| S6 | `finite_of_isAlgebraic` | sorry |
| S9 | `natDegree_eq_one_or_forall_eval_pos_of_irreducible` | sorry |
| S10 | `ivp_poly` | sorry |
| S8 | `bijective_algebraMap_of_isOrderedAlgebra'` | sorry |

### Dependency order

```
S1 ──────────┐
             ↓
S2 ─────→ S5 (keystone) ──┬─→ S6 ──┐
             ↑            │         │
S3 ──────────┤            │         │
             │            ├─→ S9 ──→ S10  (⇒ fills main sorry #1)
S4 → no_q_R  ┘            │
                          └─→ S8   (⇒ fills main sorry #2)
                              (uses S3, S5, S6)
```

### Lemmas used in S2 (reference for subsequent proofs)

- `Field.exists_primitive_element` (char-0 separability auto-inferred via `Algebra.IsSeparable.of_integral`)
- `Algebra.IsIntegral.isIntegral`
- `IntermediateField.finrank_top'`
- `IntermediateField.adjoin.finrank`
- `minpoly.irreducible`
- `IsRealClosed.exists_isRoot_of_odd_natDegree`
- `Polynomial.degree_eq_one_of_irreducible_of_root`
- `Polynomial.natDegree_eq_of_degree_eq_some`

## Plan to resume

Proceed in dependency order:

1. **S4** `Ri_isSquare`: every `z : Ri R` is a square. Computational (~80-150 lines).
   Explicit formula: `(u+vi)² = z` with `u² = (a + √(a²+b²))/2`, `v = b/(2u)`
   (case `b ≠ 0`) or handle `b = 0` directly via `isSquare_or_isSquare_neg`.
   Mimic style of `exists_ordered_algebra_adjoinRoot_sq_sub_C` in the main file
   (line ~684-785) for the `hrepr` structure using `IsAdjoinRootMonic.coeff`.
2. **S3** `nonempty_algEquiv_Ri_of_finrank_eq_two`: complete-the-square + explicit
   `AdjoinRoot.liftHom` to build `K ≃ₐ[R] Ri R`.
3. **`no_quadratic_ext_Ri`**: follows from S4 (quadratic over `Ri R` splits since
   discriminant is a square in `Ri R`).
4. **S5** `finrank_eq_one_or_two_of_finite`: Galois + Sylow. Take Galois closure,
   use 2-Sylow to extract odd-degree subfield (= R by S2), deduce finrank is 2^k.
   Use S3 + `no_quadratic_ext_Ri` to eliminate k > 1.
5. **S6** `finite_of_isAlgebraic`: short; use
   `IntermediateField.exists_lt_finrank_of_infinite_dimensional` + S5.
6. **S9** `natDegree_eq_one_or_forall_eval_pos_of_irreducible`: over a monic
   irreducible `g`, `AdjoinRoot g` is finite of degree `g.natDegree`; by S5 that's
   1 or 2. For degree-2, complete the square and show `g.eval x > 0`.
7. **S10** `ivp_poly`: strong induction on `f.natDegree`, monic irreducible factor,
   case analysis via S9 on linear vs always-positive.
8. **S8** `bijective_algebraMap_of_isOrderedAlgebra'`: combine S6 + S5; for `finrank = 2`
   use S3 to get `K ≃ₐ[R] Ri R`, transport `i` to `K` to get `i²=-1`, contradict
   `sq_nonneg` in ordered `K`.
9. **Wire up** in `IsRealClosed.lean`: replace the two sorry bodies with thin
   proxies `exact ivp_poly hab ha hb` and
   `exact bijective_algebraMap_of_isOrderedAlgebra' K`.
10. Update blueprint statuses for the intermediate lemmas and final theorem.

## Known Mathlib path issues

- `Mathlib.FieldTheory.Adjoin` has been renamed/split. Use
  `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic` and
  `Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra` (both already in the
  imports of Closure.lean).

## Files touched

- `RealClosedField/Algebra/Order/Field/IsRealClosed.lean` — untouched this session.
  Still has the two sorries at lines 38 and 161.
- `RealClosedField/Algebra/Order/Field/IsRealClosed/Closure.lean` — NEW.
  Skeleton + S1 + S2 proved.
- `RealClosedField.lean` — added import for Closure.lean.

## Resume prompt

To resume: re-read `NUMINA_PROGRESS.md` and `Closure.lean`. Next subagent task
is S4 (`Ri_isSquare`), the computational keystone. Detailed spec for S4 was
drafted this session; search prior context or re-derive from the explicit
formula above.
