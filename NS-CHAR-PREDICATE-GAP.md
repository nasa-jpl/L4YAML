# ns-char Predicate — Spec-Loose Body

**Date:** 2026-04-28
**Updated:** 2026-07-31 — line anchors refreshed; fix-plan step 1 landed
(`isPrintableBool` / `isPrintable_iff` exist); steps 2–5 remain open.
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
| `isPlainSafeBool` / `isPlainSafeProp` | [L4YAML/Spec/CharPredicates.lean:1033,1048](L4YAML/Spec/CharPredicates.lean#L1033) | `¬whitespace ∧ ¬linebreak` (plus `¬flowIndicator` when `inFlow`) |

`isNsPlainSafe` ([L4YAML/Surface/Scalars.lean:217](L4YAML/Surface/Scalars.lean#L217))
inherits the bug via `isNsChar`.

## What the fix looks like

Per spec, the body must additionally require `isPrintableProp c` (already
defined in [L4YAML/Spec/CharPredicates.lean:789](L4YAML/Spec/CharPredicates.lean#L789))
and exclude `c == '﻿'`.

The `Bool` counterpart `isPrintableBool` plus the `isPrintable_iff` coupling
lemma needed to keep the scanner/spec drift mechanism intact **have since been
added** ([L4YAML/Spec/CharPredicates.lean:802-805](L4YAML/Spec/CharPredicates.lean#L802),
re-exported through `L4YAML/Spec/Grammar.lean:51`) — step 1 of the
recommended approach below is done.

## Blast radius

- **Predicates to tighten:** 2 (`isNsChar`, `isPlainSafe*`).
- **New predicates required:** `isPrintableBool` + `isPrintable_iff` — **done**
  (see above).
- **Proof obligations to update:** ~30 in `L4YAML/Proofs/Production/ScalarProduction.lean`,
  ~7 across `L4YAML/Proofs/Scanner/{ScannerPlainScalar,ScannerPlainContent,ScannerBound,ScannerCorrectness}.lean`,
  plus `isPlainSafe_iff` itself.
  *Caveat (2026-07-31): these counts predate the wiring of the indexed scanner
  track (`Proofs/Production/IndexedScannerPlainScalarValid.lean`,
  `Proofs/Scanner/Indexed*`) and the 2026-04 folder reorganization — re-count
  the obligations when this fix is scheduled.*
- **Scanner runtime:** `collectPlainScalarLoop` ([L4YAML/Scanner/Scalar.lean:513](L4YAML/Scanner/Scalar.lean#L513))
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

1. ~~Add `isPrintableBool` and `isPrintable_iff` to `Spec/CharPredicates.lean`.~~
   **Done** (CharPredicates.lean:802-805, exported via Grammar.lean:51).
2. Tighten `isNsChar` in `Surface/Basic.lean` to add `isPrintableProp c ∧ c ≠ '﻿'`.
3. Tighten `isPlainSafeBool/Prop` body the same way.
4. Update `isPlainSafe_iff` proof for the new conjuncts.
5. Sweep proof obligations that unfold these predicates; add the printability
   side-condition where needed (mostly mechanical).

Remaining work is steps 2–5. Estimated effort: an afternoon — but the estimate
predates the indexed scanner track and the folder reorganization (see the
blast-radius caveat above); re-validate the obligation count when this fix is
scheduled.

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
