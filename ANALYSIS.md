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

### A. Three-Valued Error Recovery (High Priority) — ✅ Built, Disabled Pending §2.B

**Status (2026-02-15):** Validation combinators (`validateNoWrongIndentSeq`, `validateNoWrongIndentMap`, `hasSequenceIndicator`) implemented in `Combinators.lean` and integrated into `Block.lean`. During testing, discovered that single-line plain scalar leaves multi-line continuation content unconsumed, causing false positives on valid tests (e.g., AB8U where `" - sequence entry"` looks like a wrong-indent indicator). Combinators are **commented out** with TODO in `blockSequenceItems` and `blockMappingEntries` until §2.B (multi-line plain scalar) is implemented. Also confirmed that lean4-parser has **no committed/fatal error mechanism** — all errors are backtrackable (`withBacktracking`, `option?`, `first`, `<|>` all catch every `Result.error` unconditionally), so validation must use `throwUnexpected` at points where no backtracking wrapper will catch it.

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

This makes three-valued semantics **structural** rather than depending on error propagation details. Each variant becomes a case in an inductive proof — `matched` carries the parse result, `noMatch` justifies trying the next alternative, and `invalid` is a provable dead-end. The current `throwUnexpected` approach works but is fragile: correct only if no `withBacktracking` wrapper catches it higher in the call stack. The `DispatchResult` encoding removes that dependency entirely.

**Incremental plan**: This is a pure refactoring step — same behavior, better structure. Do it after re-enabling validation (§2.A) so correctness is established before restructuring.

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
| Correct | 210 (63%) | 164 (39.4%) |
| Unexpected passes | 43 | ~50 |
| Infinite loops | 0 | 9 |
| Internal tests | 112/113 (99%) | 41+ (all pass) |
| Escape sequences | Full YAML 1.2 set | Full YAML 1.2 set |
| Multi-line plain | ✅ (with edge cases) | ❌ (single-line only) |
| Anchors/aliases | Partial (38%) | ❌ Not implemented |
| Tags | Partial (30%) | ❌ Not implemented |
| Flow collections | Partial (55%) | 67% |
| Block collections | Good (~70%) | 57% |
| Document handling | — | 58% |
| Error rejection | — | 24% (18/74) |

---

## 5. Recommended Priorities

1. ~~**Three-valued error recovery (§2.A)**~~ — ✅ Done. Combinators built, disabled pending §2.B.
2. **🔜 Add multi-line plain scalar support (§2.B)** using the `ContinuationCheck` check-then-consume pattern — **immediate next step**, prerequisite for re-enabling validation
3. **Re-enable validation combinators (§2.A)** once multi-line scalars consume continuation content (addresses ~50 unexpected passes)
4. **Refactor `blockValue` dispatch to `DispatchResult` (§2.A)** — replace `throwUnexpected` with explicit return type. Pure refactoring (same behavior, proof-friendly structure). Each variant maps to a lemma obligation; removes dependence on error propagation details.
5. **Investigate the 9 infinite loops** (4CQQ, 4ZYM, 5GBF + 6 error-stage)
6. **Fix multi-line quoted scalars** — handle line folding in double/single-quoted scalars
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

For the verified parser, this principle is even more powerful: explicit state becomes **proof targets**. Every enum variant maps to a lemma obligation, and every state transition becomes a provable invariant.

---

## References

- [lean4-yaml DEVELOPMENT_LOG.md](../lean-yaml/DEVELOPMENT_LOG.md) — full timeline with regression analysis
- [lean4-yaml NEXT_STEPS.md](../lean-yaml/NEXT_STEPS.md) — LineState pattern and future priorities
- [lean4-yaml error-recovery-architecture.md](../lean-yaml/docs/error-recovery-architecture.md) — ParseResult design
- [lean4-yaml scalar-continuation-refactor.md](../lean-yaml/docs/scalar-continuation-refactor.md) — ContinuationCheck design
