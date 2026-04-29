# ns-char Predicate — Spec-Loose Body

**Date:** 2026-04-28
**Status:** Open. Predicate is strictly looser than spec; no test currently exercises the gap.
**Severity:** Latent — correctness bug that does not flip any current test pass→fail.

## Summary

Two character predicates in this codebase approximate YAML 1.2.2 production
[34] `ns-char` as `¬whitespace ∧ ¬linebreak`. The spec defines:

```
[34] ns-char ::= c-printable - b-char - c-byte-order-mark - s-white
```

The current approximation is missing the **printable-range check** and the
**BOM exclusion**. As a result, the predicates admit:

- BOM (`U+FEFF`) anywhere a plain-scalar continuation char is allowed.
- Non-printable control characters (most of `0x00`–`0x1F` except tab/CR/LF,
  plus `0x7F`).

## Affected definitions

| Predicate | Location | Body |
|-----------|----------|------|
| `isNsChar` | [L4YAML/Surface/Basic.lean:42](L4YAML/Surface/Basic.lean#L42) | `¬isLineBreakProp ∧ ¬isWhiteSpaceProp` |
| `isPlainSafeBool` / `isPlainSafeProp` | [L4YAML/Spec/CharPredicates.lean:434,444](L4YAML/Spec/CharPredicates.lean#L434) | `¬whitespace ∧ ¬linebreak` (plus `¬flowIndicator` when `inFlow`) |

`isNsPlainSafe` ([L4YAML/Surface/Scalars.lean:202](L4YAML/Surface/Scalars.lean#L202))
inherits the bug via `isNsChar`.

## What the fix looks like

Per spec, the body must additionally require `isPrintableProp c` (already
defined in [L4YAML/Spec/CharPredicates.lean:202](L4YAML/Spec/CharPredicates.lean#L202))
and exclude `c == '﻿'`.

A `Bool` counterpart `isPrintableBool` plus an `isPrintable_iff` coupling
theorem will need to be added to keep the scanner/spec drift mechanism
intact.

## Blast radius

- **Predicates to tighten:** 2 (`isNsChar`, `isPlainSafe*`).
- **New predicates required:** `isPrintableBool` + `isPrintable_iff`.
- **Proof obligations to update:** ~30 in `L4YAML/Proofs/Production/ScalarProduction.lean`,
  ~7 across `L4YAML/Proofs/Scanner/{ScannerPlainScalar,ScannerPlainContent,ScannerBound,ScannerCorrectness}.lean`,
  plus `isPlainSafe_iff` itself.
- **Scanner runtime:** `collectPlainScalarLoop` ([L4YAML/Scanner/Scalar.lean:526](L4YAML/Scanner/Scalar.lean#L526))
  terminates one character earlier when it hits a BOM or control char mid-scalar.
  Strictly more conformant; no valid YAML changes outcome.

## Test impact

No current test exercises raw BOM or raw control chars inside a plain
scalar body. `SpecExamples.lean` Example 5.2 already expects an error on
mid-document BOM. Double-quoted control-char tests use *escaped* sequences
(`\x00`), not raw bytes. Tightening the predicate should leave the test
suite green.

## Why this is a strict strengthening

The new predicate accepts a strict subset of characters. Therefore every
existing implication of the form `isPlainSafe c inFlow → P` remains valid
(the antecedent grows weaker). Proofs that currently `simp`/`unfold` to
`¬ws ∧ ¬lb` will need to additionally discharge an `isPrintable` (and
`¬BOM`) conjunct. Estimate: ~3–5 theorem statements gain a printability
side-condition; updates are mechanical (`decide` / `simp`).

## Recommended approach

1. Add `isPrintableBool` and `isPrintable_iff` to `Spec/CharPredicates.lean`.
2. Tighten `isNsChar` in `Surface/Basic.lean` to add `isPrintableProp c ∧ c ≠ '﻿'`.
3. Tighten `isPlainSafeBool/Prop` body the same way.
4. Update `isPlainSafe_iff` proof for the new conjuncts.
5. Sweep proof obligations that unfold these predicates; add the printability
   side-condition where needed (mostly mechanical).

Estimated effort: an afternoon.

## Related

The spec-fidelity cleanup that produced this issue also corrected:

- [110] `nb-double-text`, [119] `nb-single-text`, [131] `ns-plain` — body
  dispatch on `YamlContext` now enumerates all four spec contexts explicitly
  (key vs. non-key partition), with `blockOut`/`blockIn` grouped for totality.
- [109] `c-double-quoted` / [120] `c-single-quoted` `_ctx_lift` theorems —
  preconditions strengthened from `c ≠ .flowKey` to
  `c ≠ .blockKey ∧ c ≠ .flowKey` to match the corrected body productions.
- `isPlainSafe*` docstring — documents the spec's 4-context dispatch and
  how the `inFlow : Bool` parameter encodes the 4→2 partition
  (`FLOW-OUT/BLOCK-KEY ↦ false`, `FLOW-IN/FLOW-KEY ↦ true`); notes that
  `BLOCK-OUT/BLOCK-IN` are out-of-spec for [127].
