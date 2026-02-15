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

### A. Three-Valued Error Recovery (High Priority)

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

**Recommendation**: Implement validation-aware error propagation at `blockValue` dispatch points. For the verified parser, encoding this as a combinator or explicit return type (rather than mutable state) will be more compatible with proofs.

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
| Total tests | 333 | 82 (scalar stage only) |
| Correct | 210 (63%) | 31 (38%) |
| Unexpected passes | 43 | Not yet measured |
| Internal tests | 112/113 (99%) | 41+ (all pass) |
| Escape sequences | Full YAML 1.2 set | Full YAML 1.2 set |
| Multi-line plain | ✅ (with edge cases) | ❌ (single-line only) |
| Anchors/aliases | Partial (38%) | ❌ Not implemented |
| Tags | Partial (30%) | ❌ Not implemented |
| Flow collections | Partial (55%) | ✅ (untested vs suite) |
| Block collections | Good (~70%) | ✅ (untested vs suite) |

---

## 5. Recommended Priorities

1. **Run flow/block/document stages** against yaml-test-suite — measure actual compliance
2. **Add multi-line plain scalar support** using the `ContinuationCheck` check-then-consume pattern
3. **Add validation error propagation** at `blockValue` dispatch to prevent wrong-indent acceptance
4. **Investigate the 3 infinite loops** (4CQQ, 4ZYM, 5GBF) — likely same complex backtracking patterns lean4-yaml encountered
5. **Add anchor/alias support** — lean4-yaml's `anchorMap : HashMap String YamlValue` approach works
6. **Defer tags** — low coverage even in lean4-yaml, complex spec surface area

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
