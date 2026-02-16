# Cross-Project Analysis: lean4-yaml → lean4-yaml-verified

**Date**: 2026-02-15
**Purpose**: Insights from the non-verified [lean4-yaml](../lean-yaml/) parser that inform the verified parser's development.

---

## Context

The non-verified `lean4-yaml` parser (built on `Std.Internal.Parsec`) reached **63% yaml-test-suite compliance** (210/333) through iterative debugging. Several architectural patterns emerged from fixing regressions and edge cases. This analysis evaluates which patterns transfer to `lean4-yaml-verified` (built on `lean4-parser`).

---

## 1. What lean4-yaml-verified Already Does Better

### Stream-Based Column Tracking Eliminates the LineState Bug Class

The critical regression in lean4-yaml (65% → 2% compliance) was caused by `skipToNextLine` conflating trailing whitespace with leading indentation. lean4-yaml needed a `LineState` enum (`startOfLine` | `midLine`) to fix this.

lean4-yaml-verified's `YamlStream` tracks `col` natively in every `next?` call, and `setPosition` atomically restores `(offset, line, col)` on backtrack. This means:

- `currentCol` is always correct — no implicit assumptions about position
- Block scalar exit doesn't corrupt column state — the stream just *is* at the right column
- No need for `LineState` at all

**This validates the `YamlStream` design as architecturally superior** to the Parsec `StateT` approach.

---

## 2. Actionable Insights to Port

### A. Three-Valued Error Recovery (High Priority) — ✅ Built and Active

**Foundational principle:** Never use exceptions (parser errors) as a mechanism for making decisions. When processing any input — valid or invalid — the parser should produce explicit result values. Invalid YAML is an expected outcome, not an exceptional condition. Processing the entire yaml-test-suite should produce zero exceptions unless there is a genuine internal bug. See `LEAN4_STYLE.md` § "Parser Error Design: No Exceptions for Decisions".

**Status (2026-02-15):** Validation combinators (`validateNoWrongIndentSeq`, `validateNoWrongIndentMap`, `hasSequenceIndicator`) implemented in `Combinators.lean` and **active** in `Block.lean`'s `blockSequenceItems` and `blockMappingEntries`. Originally disabled because single-line plain scalar left continuation content unconsumed, causing false positives (e.g., AB8U). After §2.B (multi-line `plainScalarContent`), the false-positive issue was resolved and validators were re-enabled. Impact: error rejection improved from 24% to 38% (+10 tests), overall suite from 164→177 passed (39.4%→42.5%). Also confirmed that lean4-parser has **no committed/fatal error mechanism** — all errors are backtrackable (`withBacktracking`, `option?`, `first`, `<|>` all catch every `Result.error` unconditionally), making `throwUnexpected` unreliable for validation: any enclosing combinator silently swallows it.

lean4-yaml discovered that backtracking (`<|>` / `withBacktracking`) conflates **two semantically different failures**:
- "No match, try another parser" (normal backtracking)
- "Matched structure but it's invalid YAML" (validation error — should NOT backtrack)

This caused **43 tests** where invalid YAML was silently accepted. Example: ZVH3 ("wrong indented sequence item") — `blockSequence` detects wrong indent but fails, and `<|>` backtracks to parse it as a plain scalar.

**lean4-yaml-verified has exactly the same gap.** In `Block.lean`, `blockValue` dispatches by first character and uses `withBacktracking` — if a block sequence parser detects invalid indentation and fails, the alternative scalar parser will happily accept it.

lean4-yaml's solution was a `ParseResult` type:
```lean
inductive ParseResult (α : Type) where
  | success (val : α)
  | validationError (msg : String) (context : String := "")
  | noMatch (reason : String := "")
```

With the key semantic: `orElse` propagates `validationError` immediately but retries on `noMatch`.

**Recommendation**: Refactor `blockValue` dispatch from `throwUnexpected` to an explicit `DispatchResult` return type:

```lean
inductive DispatchResult (α : Type) where
  | matched (val : α)           -- parsed successfully
  | noMatch                      -- try next alternative
  | invalid (msg : String)       -- validation error, stop — don't backtrack
```

This makes three-valued semantics **structural** rather than depending on error propagation details. Each variant becomes a case in an inductive proof — `matched` carries the parse result, `noMatch` justifies trying the next alternative, and `invalid` is a provable dead-end. The current `throwUnexpected` approach violates the no-exceptions-for-decisions principle: it uses parser errors to signal both "this branch doesn't match" and "this input is invalid", and lean4-parser's unconditional error catching makes these indistinguishable. The `DispatchResult` encoding works above the combinator level, removing that dependency entirely.

**Incremental plan**: Do this refactoring **before** §2.B (multi-line plain scalar) — building continuation logic on top of the fragile `throwUnexpected` mechanism would require rework later. Get the dispatch structure right first, then implement §2.B within the clean framework.

### B. Multi-Line Plain Scalar Continuation (Medium Priority)

lean4-yaml-verified uses `plainScalarSingleLine` — it only handles one line. The non-verified parser identified these continuation edge cases:

1. **Continuation requires `col > baseIndent`** — same-indent or dedented stops the scalar
2. **Must check for `- ` (sequence marker) before treating as continuation** — otherwise the scalar swallows list items
3. **Must check for `: ` (mapping separator) before treating as continuation** — otherwise the scalar swallows mapping entries
4. **Empty lines (paragraph breaks) are preserved** — folded into `\n` chars within the scalar

The `ContinuationCheck` enum pattern was a 40% code reduction:
```lean
inductive ContinuationCheck where
  | notContinuing         -- Dedent or end of input
  | plainContinuation     -- Regular continuation on next line
  | afterEmpty (n : Nat)  -- After n empty lines (paragraph breaks)
  | sequenceMarker        -- Line starts with "- " (not a continuation)
  | mappingEntry          -- Line has ": " separator (not a continuation)
```

**For the verified parser**: This separation of "check" from "consume" will make termination proofs easier — checking is a pure non-consuming `lookAhead`, while consuming is a separate step that provably advances stream position.

### C. `attempt` Does NOT Restore External State (Critical Gotcha)

lean4-yaml discovered: `attempt` (Parsec's backtracking) restores the **iterator position** but NOT `StateT` state. If `checkContinuation` calls `getColumn` which sets `lineState := .midLine`, that state leak persists after backtrack.

**For lean4-yaml-verified**: lean4-parser's `withBacktracking` likely has the same property — it restores `YamlStream` position but any state external to the stream won't be restored. Currently the verified parser has no external state, but if you add any (validation flags, anchor maps, context stacks), this will bite.

### D. Explicit Indentation Validation (Medium Priority)

lean4-yaml added `checkWrongIndentSeqItem` and `checkWrongIndentMappingEntry` — these peek ahead to detect `- ` or `key: ` at wrong indentation levels and raise validation errors instead of silently accepting.

**Recommendation**: Implement using lean4-parser's `lookAhead`, which is cleaner than lean4-yaml's manual save/restore:

```lean
def checkWrongIndentSeqItem (expectedIndent : Nat) : YamlParser Unit := do
  let col ← currentCol
  if col < expectedIndent then
    let hasSeqMarker ← lookAhead (do
      skipHWhitespace; satisfy (· == '-'); satisfy isWhiteSpace; pure true) <|> pure false
    if hasSeqMarker then
      throwUnexpected s!"sequence item at column {col}, expected {expectedIndent}"
```

### E. `attemptOrValidationFail` Combinator (High Priority)

lean4-yaml's key insight: at dispatch points like `blockValue`, replace bare `<|>` with a combinator that checks for validation errors:

```
try primary_parser
  if validation_error_set → propagate as hard failure
  if normal_failure → try alternative_parser
```

This prevents invalid YAML from being silently accepted by a fallback parser. The verified parser should implement this at the `blockValue` dispatch level where it tries block collections before falling back to plain scalars.

### F. Quoted Scalar Line Folding & `c-forbidden` (High Priority)

Analysis of 11 failing scalar tests revealed 5 algorithmic bugs in `foldQuotedNewlines` and one missing feature (`c-forbidden` detection). The failures fall into 6 groups:

| Group | Root cause | Tests | Fix type |
|-------|-----------|-------|----------|
| **A** | `foldQuotedNewlines` requires a mandatory `newline` after `skipHWhitespace`, crashing on the simplest fold case (next line has content, not a blank line) | 4CQQ, 4ZYM, 9MQT, DE56 | Algorithmic |
| **B** | Off-by-one in empty line counting — initial `newline` consumes one blank line before counting starts | 5GBF, 7A4E, NAT4, PRH3, TL85 | Algorithmic |
| **C** | No trimming of trailing whitespace from `acc` before folding | 3RLN, DE56, 7A4E, NP9H, PRH3 | Algorithmic |
| **D** | `skipSpaces` in folding loop only handles `' '`, not `'\t'` — tabs on continuation lines leak into output | 3RLN, 4ZYM, 5GBF, PRH3, TL85 | Algorithmic |
| **E** | `\` + literal newline (escaped line break / line continuation) not handled in `processEscape` | NP9H | Algorithmic |
| **F** | No `c-forbidden` check (YAML §9.1.3) — `--- ` or `... ` at start of continuation line inside quoted scalars should be rejected | 9MQT | **Result type** |

**Group F requires an explicit result type.** When a quoted scalar's continuation line starts with `--- ` or `... `, the parser has successfully *recognized* a quoted scalar but discovered a *forbidden* document indicator. This is semantically identical to `DispatchResult.invalid` — "I matched the structure but the content is definitively ill-formed." Without an explicit error path, backtracking would swallow the rejection and some enclosing combinator might silently accept the input. This is the same class of problem as the validation combinators in `Block.lean`.

**Groups A–E are purely algorithmic** — the `foldQuotedNewlines` function has wrong logic. The correct algorithm:

```
foldQuotedNewlines(acc) :=
  1. Trim trailing whitespace (spaces+tabs) from acc
  2. Count blank lines:
     loop:
       skip whitespace (spaces + tabs)
       if newline → consume it, increment blankCount, repeat
       else → done (leading whitespace on content line already consumed)
  3. If blankCount == 0 → append ' ' to acc   (fold to space)
     If blankCount > 0 → append blankCount × '\n' to acc   (preserved newlines)
  4. Return acc
```

Additionally, `collectChars` needs a `'\\' → '\n' | '\r'` arm for escaped line breaks (line continuation — consumes the newline + leading whitespace, emits nothing).

**Implementation plan**: Add/improve the explicit result type for `c-forbidden` detection first (following the `DispatchResult`/`DocumentResult` pattern of making validation structural), then fix the algorithmic bugs in `foldQuotedNewlines`.

---

## 3. What NOT to Port

| Pattern | Reason to Skip |
|---------|---------------|
| **`LineState` enum** | Unnecessary — `YamlStream` handles this natively |
| **`contextStack : List ParseContext`** | lean4-yaml's block-in/block-out/flow-in/flow-out stack is more complex than needed; `minIndent` parameter threading + flow context flag are simpler and sufficient |
| **`validationError : Option String` as mutable state** | Pragmatic hack that makes proofs harder; better to encode as a combinator or explicit return type |
| **Complex `skipToNextLine`** | lean4-yaml-verified already has a cleaner approach |

---

## 4. Compliance Comparison

| Metric | lean4-yaml | lean4-yaml-verified |
|--------|-----------|-------------------|
| Total tests | 333 | 416 |
| Correct | 210 (63%) | 192 (46.2%) |
| Unexpected passes | 43 | ~34 |
| Infinite loops | 0 | 0 |
| Internal tests | 112/113 (99%) | 42+ (all pass) |
| Escape sequences | Full YAML 1.2 set | Full YAML 1.2 set |
| Multi-line plain | ✅ (with edge cases) | ✅ (ContinuationCheck pattern) |
| Anchors/aliases | Partial (38%) | ❌ Not implemented |
| Tags | Partial (30%) | ❌ Not implemented |
| Flow collections | Partial (55%) | 71% |
| Block collections | Good (~70%) | 58% |
| Document handling | — | 58% |
| Error rejection | — | 54% (40/74) |

---

## 5. Recommended Priorities

1. ~~**Three-valued error recovery (§2.A)**~~ — ✅ Done. Combinators built, ready to re-enable now that §2.B is complete.
2. ~~**Refactor `blockValue` dispatch to `DispatchResult` (§2.A)**~~ — ✅ Done. Defined `DispatchResult` inductive type (`matched`/`noMatch`/`invalid`) in `Combinators.lean`. Extracted shared dispatch logic into `dispatchByChar` in `Block.lean`, eliminating duplicated match statements in `blockValue` and `blockValueSameLine`. Pure refactoring: same behavior, proof-friendly structure. Each variant maps to a lemma obligation; removes dependence on error propagation details.
3. ~~**Add multi-line plain scalar support (§2.B)**~~ — ✅ Done. Defined `ContinuationCheck` inductive type (`notContinuing`/`plainContinuation`/`afterEmpty n`/`sequenceMarker`/`mappingEntry`) in `Combinators.lean`. Implemented `checkContinuation` as a pure `lookAhead` probe (check-then-consume pattern). Replaced `plainScalarSingleLine` with multi-line `plainScalarContent` in `Scalar.lean` — handles line folding (adjacent lines → space, empty lines → paragraph breaks). `dispatchByChar` passes `baseIndent := contentIndent - 1` to track parent indent. Scalar suite: 41/82 passed (50%)
4. ~~**Re-enable validation combinators (§2.A)**~~ — ✅ Done. Uncommented validators in `Block.lean`. Error rejection improved from 24% to 38%, overall suite from 164→177 passed (39.4%→42.5%).
5. ~~**Eliminate infinite loops**~~ — ✅ Done. Discovered 36 timeout cases (not 9), all sharing one root cause: `yamlStream`'s while loop retries `document` at the same position when no input is consumed. Initially fixed with position-advancement guard (compare `currentPos` before/after `document`). Analysis revealed this was an implicit assumption in `document`'s API — the caller was re-deriving information that `document` already had but discarded. Refactored `document` to return an explicit `DocumentResult` inductive type:
   ```lean
   inductive DocumentResult where
     | parsed (doc : YamlDocument)  -- consumed input, produced a document
     | endOfStream                   -- no remaining input
     | stalled (pos : YamlPos)      -- input present, couldn't parse
   ```
   This moves the stall-detection invariant *inside* `document` — `yamlStream` now pattern-matches on the result instead of comparing positions externally. Follows the same explicit-result-type pattern as `DispatchResult` (dispatch) and `ContinuationCheck` (scalar continuation). The `stalled` variant carries position for error reporting and becomes a proof obligation target: `document` returns `stalled` iff no input was consumed and non-blank input remains. Impact: 0 timeouts (was 36), error rejection 38%→54% (28→40/74), overall suite 177→192 passed (42.5%→46.2%). The 36 timeouts fell into 9 root cause categories: anchor/alias `&`/`*` (9), tags `!`/`!!` (5), quoted scalar folding (4), comment before value (3), explicit key `?` (4), same-indent sequence (3), tab handling (2), empty key edge cases (3), flow implicit mapping (3).
6. **Fix multi-line quoted scalars** — analysis revealed 5 algorithmic bugs in `foldQuotedNewlines` and one missing `c-forbidden` check (§2.F). Implementation plan:
   - **6a.** ✅ Added `FoldResult` type (`folded`/`forbidden`) for `c-forbidden` detection on quoted scalar continuation lines (YAML §9.1.2 [206]). `foldQuotedNewlines` now checks `atDocumentBoundary` at column 0 before whitespace consumption on each continuation line. `collectChars` in both `doubleQuotedScalar` and `singleQuotedScalar` pattern-matches on the result, propagating `.forbidden` as a hard error. Suite results unchanged (structural preparation — algorithmic bugs in 6b prevent `foldQuotedNewlines` from reaching the check on most inputs).
   - **6b.** ✅ Fixed all 5 algorithmic bugs in `foldQuotedNewlines` (Groups A–E). Rewrote the function body: (A) removed erroneous mandatory `newline` — the newline is already consumed by `collectChars`'s `anyToken`, so the loop now starts by skipping whitespace and checking for the next newline directly; (B) fixed off-by-one in empty line counting — no separate pre-loop newline consumption means `blankCount` is exact; (C) added `trimTrailingWhitespace` helper that strips trailing spaces+tabs from `acc` before folding; (D) replaced `skipSpaces` with `skipHWhitespace` to handle tabs on continuation lines; (E) added `\` + newline/CRLF handling in `doubleQuotedScalar`'s `collectChars` — escaped line breaks trim trailing whitespace from `acc`, consume the newline + leading whitespace on the next line, and emit nothing (YAML §5.7 [112]). Added `trimTrailingWs` helper in `doubleQuotedScalar`'s `where` block. Created `Tests/QuotedFolding.lean` (33 tests, 290 lines) covering all 5 bug fixes plus combined scenarios, CRLF handling, and edge cases. Suite results unchanged (192/416, 46.2%) — folding fixes affect content correctness rather than parse success/failure.
7. **Add anchor/alias support** — lean4-yaml's `anchorMap : HashMap String YamlValue` approach works
8. **Defer tags** — low coverage even in lean4-yaml, complex spec surface area

---

## 6. Architectural Principle

lean4-yaml's development log established a repeating pattern: **make implicit state explicit with simple enums/types**.

| Refactoring | Pattern | Result |
|------------|---------|--------|
| `LineState` | Position assumptions → enum | Fixed 65% → 2% regression |
| `ContinuationCheck` | Continuation logic → enum | 40% code reduction |
| `ParseResult` | Error semantics → 3-valued type | Addresses 43 unexpected passes |
| `DispatchResult` | Dispatch outcome → 3-valued type | Proof-friendly block value dispatch |
| `DocumentResult` | Document parse outcome → 3-valued type | Eliminates 36 infinite loops |
| `FoldResult` | Quoted fold + `c-forbidden` → explicit type | Prevents backtracking from swallowing `c-forbidden` violations |

For the verified parser, this principle is even more powerful: explicit state becomes **proof targets**. Every enum variant maps to a lemma obligation, and every state transition becomes a provable invariant.

---

## References

- [lean4-yaml DEVELOPMENT_LOG.md](../lean-yaml/DEVELOPMENT_LOG.md) — full timeline with regression analysis
- [lean4-yaml NEXT_STEPS.md](../lean-yaml/NEXT_STEPS.md) — LineState pattern and future priorities
- [lean4-yaml error-recovery-architecture.md](../lean-yaml/docs/error-recovery-architecture.md) — ParseResult design
- [lean4-yaml scalar-continuation-refactor.md](../lean-yaml/docs/scalar-continuation-refactor.md) — ContinuationCheck design
