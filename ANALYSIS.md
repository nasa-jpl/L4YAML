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

### G. Block Scalar Header: Peek-Before-Consume Discipline (Critical Insight)

**Date discovered**: 2026-02-19
**Status**: ✅ Fixed. Root cause identified, fix applied, formal contracts built.

**The bug**: `parseYaml "data: |\n  line1\n  line2"` returned `.error` instead of correctly parsing a literal block scalar. The test "accept: literal block scalar" was the only failure in the internal test suite.

**Root cause**: In `blockScalarHeader`, the indicator-parsing loop used `option? anyToken` to peek at the next character:

```lean
-- BUGGY: option? anyToken CONSUMES the character
for _ in [:2] do
  match ← option? anyToken with
  | some '-' => chomp := .strip
  | some c => if c >= '1' && c <= '9' then indent := some (c.toNat - '0'.toNat) else break
  | none => pure ()
```

When parsing `|\n  line1\n  line2`, the sequence was:
1. `anyToken` reads `\n` (consumes it, advancing past the newline)
2. The `\n` doesn't match any header pattern → `break`
3. But the newline is already consumed
4. `skipTrailing` now sees `  line1...` — two spaces that belong to the content
5. `skipTrailing` consumes whitespace, eating the content indentation
6. `autoDetectIndent` sees zero indentation (spaces already gone)
7. `blockScalarContent` fails because the content doesn't match

**The implicit contract violated**: `blockScalarHeader` must only consume characters that are header indicators (`-`, `+`, `1`–`9`), trailing whitespace/comment, and at most one newline. The `option? anyToken` pattern consumed a character *before* classifying it, so when the loop broke, the consumed character was lost to the wrong production.

**The fix**: Replace `option? anyToken` with `option? (lookAhead anyToken)` — peek first, then consume only if the character is valid:

```lean
-- FIXED: lookAhead peeks without consuming; only anyToken for valid chars
for _ in [:2] do
  match ← option? (lookAhead anyToken) with
  | some '-' => let _ ← anyToken; chomp := .strip
  | some c => if c >= '1' && c <= '9' then let _ ← anyToken; indent := some (...) else break
  | none => pure ()
```

Now when `lookAhead anyToken` peeks at `\n`, the stream position is unchanged. The `break` exits the loop with `\n` still unconsumed. `skipTrailing` has nothing to skip, `newline` consumes the `\n`, and the stream ends up at column 0 — exactly where `autoDetectIndent` expects it.

**Generalization — the peek-before-consume discipline**: Any parsing loop where the next character might not belong to the current production MUST use `lookAhead` to inspect before consuming. The pattern is:

```
match ← option? (lookAhead anyToken) with
| some c => if isValid c then let _ ← anyToken; ... else break
| none => ...
```

The anti-pattern `option? anyToken` + `break` silently consumes one character from the next production on every exit. This is especially dangerous in YAML because the "stolen" character is typically a newline or space — invisible in output but critical for indentation tracking.

**Formal contracts**: This insight was codified as machine-checked contracts in `Proofs/BlockScalarContracts.lean`:
- **§1** (fully proved): Header character classification — `isBlockScalarHeaderChar` correctly distinguishes header chars from content chars. Properties like `newline_not_header_char`, `space_not_header_char`, and `extractHeaderChars_preserves_non_header` are proved by `native_decide` and structural induction.
- **§2** (decidable predicates): Position contracts expressed as `Bool`-valued functions (`satisfiesG1`, `satisfiesG2`, `satisfiesNonConsuming`) with proved implications about what they mean. The parser's runtime assertions check these exact predicates.
- **§3** (code pattern): The peek-before-consume principle documented as a structural code discipline.

**This follows the §6 pattern**: implicit parser state (which characters are consumed) → explicit contract predicates (decidable, proved). The `lookAhead`-then-consume pattern is the code-level enforcement; the formal contracts are the proof-level enforcement.

### H. Document Parser Contracts: Explicit-Document Boundary Semantics (Critical Insight)

**Date discovered**: 2026-02-19
**Status**: Analysis complete. Three latent contracts identified; formal predicates recommended.

**The gap**: The `document` parser in `Document.lean` tracks several implicit invariants about document boundaries, trailing content, and validation error propagation. The Step 10a flow validation work (fixing KS4U, 9JBA, CVW2, DK4H, ZXT5) revealed three contracts that are enforced by runtime `if` checks but have no formal specification. This is the same class of problem that `BlockScalarContracts.lean` solved for the block scalar pipeline — implicit state made explicit as decidable predicates.

#### Contract D1: Explicit-Document Boundary (`hadExplicitStart` invariant)

**Context**: YAML §9.1.4/§9.2 requires that after an explicit document (preceded by `---`), subsequent content must begin with `---` or `...`. Bare content is invalid.

Previously, `document` used `let _ ← option? documentStartMarker` — silently discarding whether `---` was found. This meant the parser could not distinguish explicit from bare documents, and test KS4U (`---\n[\nsequence item\n]\ninvalid item\n`) was silently accepted.

The fix introduced `hadExplicitStart : Bool`, tracking whether `---` was consumed. The implicit contract:

- **Assume**: `hadExplicitStart = true` iff `documentStartMarker` succeeded
- **Guarantee**: if `hadExplicitStart` and not at EOF, remaining content must begin with `---`, `...`, or whitespace-prefixed document marker. Otherwise, `setValidationError` is called.

**Recommended predicate**:
```lean
def satisfiesExplicitBoundary (hadExplicit : Bool) (atEnd : Bool)
    (nextIsDocMarker : Bool) : Bool :=
  !hadExplicit || atEnd || nextIsDocMarker
```

With specification theorem:
```lean
theorem explicitBoundary_spec (hadExplicit atEnd nextIsDocMarker : Bool) :
    satisfiesExplicitBoundary hadExplicit atEnd nextIsDocMarker = true →
    hadExplicit = false ∨ atEnd = true ∨ nextIsDocMarker = true
```

#### Contract D2: Trailing Content Comment Check (§6.7 column invariant)

**Context**: After `blockValue`, the only valid same-line continuations are whitespace, comments (`#`), or end of line/input. But §6.7 requires that `#` be preceded by whitespace to be a comment — `value#comment` is not valid.

The fix tracks `trailCol`/`afterTrailCol` (column before/after `skipHWhitespace`) and rejects `#` when no whitespace was consumed (unless at column 0). This fixes test 9JBA.

The implicit contract:

- **Assume**: `trailCol` = column before horizontal whitespace skip, `afterTrailCol` = column after
- **Guarantee**: `#` is only treated as a comment start if `afterTrailCol > trailCol` or `afterTrailCol == 0`

**Recommended predicate**:
```lean
def satisfiesCommentPrecondition (colBefore colAfter : Nat) : Bool :=
  colAfter != colBefore || colAfter == 0
```

This is subtle because the `colAfter == 0` edge case handles start-of-line comments — a refactoring could easily drop this guard and break the invariant.

#### Contract D3: `DocumentResult` Monotonicity

**Context**: `yamlStream` depends on `document` returning the correct `DocumentResult` variant. The critical safety property: **`.parsed` is never returned when `validationError` is `some`**.

This is enforced by the `valErr` check in `document` (after parsing the value and trailing content), which converts a validation error into `.stalled`. Breaking this would cause `parseYaml` to reject a document that `yamlStream` thought was valid — the validation error check at the end of `parseYaml` is defense-in-depth, not the primary contract.

- **Assume**: `document` has access to `getValidationError`
- **Guarantee**: if `getValidationError` returns `some msg` at any point during document parsing, `document` returns `.stalled`, never `.parsed`

**Recommended predicate**:
```lean
def satisfiesDocResultMonotonicity (hasValErr : Bool)
    (result : DocumentResult) : Bool :=
  !hasValErr || match result with | .stalled _ => true | _ => false
```

#### What does NOT need formalization

- **`hadExplicitStart` faithfulness** (that it's `true` iff `---` was consumed): trivially correct by construction — direct pattern match on `option?` result.
- **`yamlStream` loop termination**: follows directly from D3. If `document` returns `.stalled` or `.endOfStream`, the loop exits.

#### Implementation plan

Follow the `BlockScalarContracts.lean` pattern:

1. Create `Lean4Yaml/Proofs/DocumentContracts.lean`
2. Define `satisfiesExplicitBoundary`, `satisfiesCommentPrecondition`, `satisfiesDocResultMonotonicity` as decidable `Bool` predicates
3. Prove specification theorems and interplay theorems (all via `native_decide` / `simp` — zero axioms)
4. Runtime assertions already exist in the code (the `if` checks in `document`), so no new runtime guards needed

**This follows the §6 pattern**: implicit parser control flow (which branch is taken, what `hadExplicitStart` means) → explicit contract predicates (decidable, proved). The `hadExplicitStart` boolean is the code-level enforcement; the formal contracts are the proof-level enforcement.

### I. Block Parser Tacit Assumptions: Indentation Semantics & Dispatch Completeness (Critical Insight)

**Date discovered**: 2026-02-19
**Status**: Analysis complete, from `ScalarStageDiag.lean` (20 failing tests, 4 root cause groups).
**Impact**: 20 of 48 scalar-stage failures (42%), plus overlap with block-stage and structure failures.

The scalar stage diagnostic (`Tests/ScalarStageDiag.lean`) revealed that the 20 scalar-stage failures trace to **five tacit assumptions** in the block parser's interactions with `Scalar.lean` and `Document.lean`. These fall into two classes:

- **Class 1 — Indentation parameter confusion** (T1, T2): a single `contentIndent` parameter is used for two semantically distinct purposes, and an off-by-one compounds across call boundaries.
- **Class 2 — Dispatch completeness** (T3, T4, T5): `dispatchByChar` short-circuits on certain first characters without checking for mapping key patterns, and `detectMappingKey` gives up prematurely on valid keys.

Both classes are instances of the §6 meta-pattern: **implicit assumptions about what parameters mean and what conditions hold at each call site, never stated as contracts**.

#### T1: `blockValue` conflates column position with parent indentation context

**Where**: `blockValue` in `Block.lean`
**Code**:
```lean
partial def blockValue (minIndent : Nat) : YamlParser (Option YamlValue) := do
  skipBlankLines
  skipHWhitespace
  let col ← currentCol
  if col < minIndent then return none
  let result ← dispatchByChar col  -- ← col serves as parentIndent for sub-parsers
```

**Tacit assumption**: The column where a value's indicator sits (`col`) equals the indentation level of the enclosing structure. This is the parameter passed to `dispatchByChar`, which forwards it to `blockScalar` as `parentIndent`.

**Why it's wrong**: After `documentStartMarker` consumes `---` and trailing whitespace, a block scalar indicator on the same line (e.g., `--- >`) sits at column 4. But the document-level indentation is 0 (spec's `n = -1`). The parameter `col = 4` is correct for the threshold check (`col >= minIndent`), but wrong as the indentation context for sub-parsers.

**Precise spec production chain**: After `---`, the document value begins via `s-l+block-node(-1, BLOCK-IN)`, which leads to `c-l+folded(-1)`. Content is at `n + m` with `m >= 1`, so `(-1) + 1 = 0` — column 0 content is valid per the spec grammar. The space between `---` and `>` is consumed by `s-separate(n+1, c)`, which is purely separator whitespace and does NOT contribute to the indentation context `n`.

**The specific mechanism**: `documentStartMarker` calls `skipTrailing`, which consumes the space after `---`, advancing the stream column to 4. Then `option? newline` does NOT match (the next character is `>`, not a newline), so the stream stays at column 4 where `>` sits. When `blockValue 0` reads `currentCol`, it gets 4 — a column position that reflects the *separator whitespace consumption*, not the document structure's indentation level.

**Trace for `--- >\nline1\nline2\n`** (test FP8R):
1. `documentStartMarker` consumes `--- ` via `chars "---"` + `skipTrailing`, stream at `>` column 4
2. `blockValue 0` → `col = 4` → threshold OK (`4 >= 0`)
3. `dispatchByChar 4` → `blockScalar 4`
4. `autoDetectIndent(4+1=5)` → content `line1` at col 0, `0 < 5` → **returns fallback `minIndent = 5`** (NOT the actual content indent)
5. `blockScalarContent(5)` → `consumeIndent 5` on `line1` → **fails** (0 spaces)
6. Returns empty scalar, `line1` unconsumed → "unexpected trailing content 'l'"

**`autoDetectIndent` fallback masking**: Step 4 is critical. When the actual content column (0) is below the inflated `minIndent` (5), `autoDetectIndent` doesn't return 0 — it returns the `minIndent` fallback. This means `blockScalarContent` is given an *impossible-to-satisfy* indent level, guaranteeing failure regardless of what the content lines look like. The fallback was designed to handle blank lines (returning a sane default when no content is visible), but here it masks the real problem: `minIndent` was wrong in the first place.

**Contract that should be explicit**:
- **Assume**: `blockValue(minIndent)` is called with `minIndent` = the minimum indentation for this value's content
- **Guarantee (G-BV1)**: The indentation context passed to sub-parsers via `dispatchByChar` reflects the enclosing structure's indentation level (`minIndent`), NOT the column where the value's indicator happens to sit

**Impact**: Affects all 12 block scalar content tests when block scalar appears after `---` on the same line: FP8R, DK3J, 4WA9, 6FWR, 6JQW, 96L6, 96NN, D83L, F6MC, M29M, P2AD, R4YG.

#### T2: `dispatchByChar` double-counts indentation for block scalars

**Where**: Callers of `dispatchByChar` in `Block.lean` + `blockScalar` in `Scalar.lean`
**Code** (caller side in `blockSequenceItems`):
```lean
let contentIndent := seqIndent + 1   -- +1 from caller
blockValueSameLine col' contentIndent
```
**Code** (callee side in `blockScalar`):
```lean
| none => autoDetectIndent (parentIndent + 1)  -- +1 from blockScalar
```

**Tacit assumption**: `contentIndent` passed to `blockScalar` is the YAML spec's `n` parameter (the current indentation level). But callers pass `structIndent + 1`, and `blockScalar` adds another `+1` internally, giving `structIndent + 2`. The YAML spec says content must be at `n + m` with `m >= 1`, so minimum is `n + 1` — not `n + 2`.

**Trace for `- |\n hello\n`** (related to test W42U):
1. `blockSequenceItems` → `seqIndent = 0`, `contentIndent = 0 + 1 = 1`
2. `blockValueSameLine col' 1` → `dispatchByChar 1` → `blockScalar 1`
3. `autoDetectIndent(1+1=2)` → content ` hello` has 1 space → `1 < 2` → **returns fallback 2** (not actual indent 1)
4. `blockScalarContent(2)` → `consumeIndent 2` → **fails** (only 1 space)

**Per YAML spec** (§8.1, §8.2.1): sequence at `n = -1` (document level), item content via `s-l+block-indented(n=0, BLOCK-IN)`, block scalar gets `n=0`, content at `0 + m` with `m=1` → column 1 is valid.

**The double-count**: both the caller (+1 for child content) and `blockScalar` (+1 for content vs. parent) add an offset, netting `structIndent + 2` instead of the spec's `structIndent + 1`.

**"Works by coincidence"**: The common case `x: |\n  hello\n` (2-space content in a mapping) passes because 2 spaces happens to satisfy the inflated indent requirement of 2 (from `mapIndent(0) + 1 + 1`). Only when content uses the minimum spec-legal indentation (1 space) does the bug surface. This masking effect explains why the double-count wasn't caught by the internal test suite — all hand-written tests used 2+ spaces of content indentation, which is the conventional style but not the minimum the spec allows.

**Contract that should be explicit**:
- **Assume (A-BS1)**: `blockScalar(parentIndent)` receives the spec's `n` parameter — the indentation of the enclosing structure, NOT `n+1`
- **Guarantee (G-BS1)**: Auto-detected content is at column `parentIndent + m` with `m >= 1` (spec §8.1)
- **Enforcement**: Either callers pass `structIndent` (not `structIndent + 1`) to block scalar dispatch, or `blockScalar` stops adding `+1` internally. One side must own the offset, not both.

**Impact**: Block scalars with minimum valid indentation fail. Affects W42U directly, and compounds with T1 for all 12 block scalar content tests.

#### T3: `dispatchByChar`'s `?`, `-`, `'`, `"` cases bypass mapping key detection

**Where**: `dispatchByChar` in `Block.lean`
**Code**:
```lean
| '?' => do
    ...
    if isExplicitKey then
      match ← blockMapping contentIndent with ...
    else
      return .matched (← plainScalar ...)  -- No mapping check!
| '-' => do
    ...
    if isSeq then
      match ← blockSequence contentIndent with ...
    else
      return .matched (← plainScalar ...)  -- No mapping check!
| '\'' => return .matched (← singleQuotedScalar)  -- No mapping check!
| '"' => return .matched (← doubleQuotedScalar)   -- No mapping check!
```

Compare with the default case:
```lean
| _ => do
    let isMap ← lookAhead do
      detectMappingKey (inFlow := false)
    if isMap then
      match ← blockMapping contentIndent with ...  -- ✓ Checks for mapping!
```

**Tacit assumption**: Lines starting with `?`, `-`, `'`, or `"` are never mapping key/value entries (only explicit keys, sequences, or standalone scalars). This is false — YAML allows:
- `?foo: value` — plain key starting with `?`
- `-foo: value` — plain key starting with `-`
- `:foo: value` — plain key starting with `:`
- `'quoted key': value` — single-quoted mapping key
- `"quoted key": value` — double-quoted mapping key

**Trace for `?foo: safe\n`** (test 2EBW):
1. `dispatchByChar 0` → `c = '?'`, `isExplicitKey = false` (`f` follows)
2. Dispatches to `plainScalar(false, 0)`
3. `plainScalar` consumes `?foo`, stops at `: ` → returns `"?foo"`
4. Document trailing check finds `:` → "unexpected trailing content ':'"

**Trace for `'foo: bar\': baz'`** (test 6H3V):
1. `dispatchByChar 0` → `c = '\''`, dispatches to `singleQuotedScalar`
2. Parses `'foo: bar\'` → returns scalar `"foo: bar\"`
3. Document trailing check finds `:` → "unexpected trailing content ':'"

**Contract that should be explicit**:
- **Assume (A-DC1)**: `dispatchByChar` is called at the start of a block value
- **Guarantee (G-DC1)**: If the current line contains a mapping key/value pattern — regardless of the first character — `dispatchByChar` dispatches to `blockMapping`, not a scalar parser
- **Enforcement**: After parsing a scalar (plain, quoted, or indicator-prefixed), check for a following `: ` before committing. Alternatively, check for mapping patterns before dispatching special characters.

**Impact**: 2EBW (`?foo:`, `-foo:`, `:foo:` as mapping keys), 6H3V (single-quoted mapping key), 8CWC (key ending with colons), 6SLA (quoted mapping key with special chars). Accounts for all 4 "plain/quoted key parsing" failures.

#### T4: `detectMappingKey` gives false negatives on valid keys

**Where**: `detectMappingKey` in `Block.lean`
**Code**:
```lean
detectLoop : YamlParser Bool := do
    match ← option? anyToken with
    | some ':' =>
      match ← option? anyToken with
      | some c => return (isWhiteSpace c || isLineBreak c)  -- Returns immediately!
    | some c =>
      if c == '"' || c == '\'' then return false  -- Bails on quotes!
      else detectLoop
```

**Two bugs, same tacit assumption** ("the first ambiguous character resolves the line's role"):

1. **Early return on non-separator colons**: When `detectMappingKey` encounters `:` followed by a non-whitespace character (e.g., `::` in `key:::` value`), it returns `false` immediately instead of continuing to scan for a later `: `. The assumption that "the first `:` determines whether this is a mapping" is wrong — YAML plain keys can contain non-separator colons.

2. **Bail on quote characters**: When `detectMappingKey` encounters `"` or `'` mid-scan, it returns `false`. The assumption that these always delimit quoted scalars is wrong — they can appear as literal characters inside plain keys (e.g., `a!"#$: value`).

**Trace for `key ends with two colons::: value`** (test 8CWC):
1. `dispatchByChar 0` → `| _ =>` → `detectMappingKey`
2. Scans: `k,e,y,...,n,s,:`
3. First `:` in `:::` → next char `:` → not whitespace → **returns false**
4. Falls to plain scalar → consumes key, leaves `::: value` → trailing content error

**Contract that should be explicit**:
- **Assume (A-DM1)**: `detectMappingKey` attempts to determine if the current line is a mapping entry
- **Guarantee (G-DM1)**: Returns `true` if ANY position on the line has `: ` or `:\n` or `:` at EOF — not just the first `:` encountered
- **Guarantee (G-DM2)**: Quote characters (`'`, `"`) appearing outside of actual quoting contexts do not cause false negatives

**Impact**: Part of 2EBW, all of 8CWC. Interacts with T3 — even if T3 is fixed so the `| _ =>` path is reached for more cases, T4 would still cause these cases to be misdetected.

#### T5: `blockMappingKey.plainMappingKey` vs. `plainScalarContent` colon handling divergence

**Where**: `blockMappingKey.plainMappingKey` in `Block.lean` vs. `collectPlain` in `Scalar.lean`
**Tacit assumption**: Both parsers handle `:` identically. In practice, `plainMappingKey` correctly continues past non-separator colons (its loop checks `:` + next char and continues if not a separator), but `collectPlain` in `plainScalarContent` (lines 401–413 of `Scalar.lean`, omitted in the attachment) may have divergent behavior.

**This is lower-risk** — `plainMappingKey` handles `:::` correctly when reached. The failures occur because T3 and T4 prevent the mapping path from being reached in the first place. However, the existence of two independent plain-key parsing implementations (`plainMappingKey` and `plainScalarContent`) with no shared contract about colon handling is itself an architectural risk.

**Recommended contract**:
- **Invariant (I-PK1)**: For any input string `s`, `plainMappingKey` and `plainScalarContent` (in single-line mode) must consume the same prefix when both are applied at the same position and stop at `: ` separators
- **Enforcement**: Consider unifying the two implementations, or at minimum adding shared test coverage

#### Root cause → contract mapping

| Root cause group | Tests (20 total) | Tacit assumptions | Primary contract |
|---|---|---|---|
| Block scalar content (12) | 4WA9, 6FWR, 6JQW, 96L6, 96NN, D83L, DK3J, F6MC, FP8R, M29M, P2AD, R4YG | T1 + T2 | G-BV1, A-BS1/G-BS1 |
| Plain/quoted key parsing (4) | 2EBW, 6H3V, 8CWC, 6SLA | T3 + T4 | G-DC1, G-DM1/G-DM2 |
| Block content continuation (2) | AB8U, NB6Z | T1 (partial) | G-BV1 |
| Block structure (2) | H2RW, W42U | T1 + T2 | G-BV1, A-BS1/G-BS1 |

#### The YAML spec's `n` parameter — what our code is missing

The YAML 1.2.2 spec threads an indentation parameter `n` through all block productions:

```
l+block-scalar(n,c) ::= s-separate(n+1,c) ( c-l+literal(n) | c-l+folded(n) )
c-l+literal(n) ::= "|" c-b-block-header(m,t) l-literal-content(n+m,t)
s-l+block-seq(n) ::= ( s-b-block-seq(n) )+
  where s-b-block-seq(n) ::= s-indent(n+1) c-l-block-seq-entry(n+1)
```

Key: `n` is the **enclosing structure's** indentation, not the content's column. For document-level content, `n = -1`. For a sequence item's content, `n` = the sequence's own indentation. The `+1` offset for content vs. parent is applied exactly once, at the point where each production definition requires it.

The critical subtlety: after `---`, `n = -1`. The spec allows this because `s-indent(n)` for `n < 0` is a no-op (zero spaces). But our code uses `Nat` (natural numbers), so `n = -1` is not representable. We implicitly encode it as `n = 0`, but then the `+1` offsets don't work correctly — `0 + 1 = 1` instead of the spec's `(-1) + 1 = 0`. The `Nat` encoding loses the distinction between "document level, no indentation required" (`n = -1`) and "top-level structure at column 0" (`n = 0`).

Our code uses a single `contentIndent` parameter that conflates two concepts:
1. **Threshold**: "content must be at this column or beyond" (correct for blocking under-indented content)
2. **Context**: "the enclosing structure is at this indentation" (needed by `blockScalar` to compute minimum content indent)

These differ by exactly 1. The fix is to either:
- **(Option A)** Thread two parameters: `minIndent` (threshold) and `parentIndent` (context = `minIndent - 1`) through `dispatchByChar`
- **(Option B)** Have `blockScalar` receive `contentIndent` and NOT add `+1` internally (treating the caller's `+1` as the sole offset)
- **(Option C)** Have callers pass `structIndent` directly to block scalar dispatch, with `blockScalar` owning the `+1` offset

Option A is the most explicit and proof-friendly — it makes the dual semantics visible in the type signature. Option B is the simplest code change but hides the semantic distinction. Option C matches the spec most closely.

#### Implementation plan

1. **Define explicit contracts** as decidable predicates in `Proofs/BlockParserContracts.lean`:
   - `satisfiesIndentContext`: verifies that `parentIndent` passed to `blockScalar` matches the spec's `n`
   - `satisfiesDispatchCompleteness`: verifies that mapping patterns are detected regardless of first character
   - `satisfiesMappingDetection`: verifies that `detectMappingKey` scans past non-separator colons and embedded quotes

2. **Fix T1 + T2** (indentation): Thread the spec's `n` parameter correctly through `blockValue` → `dispatchByChar` → `blockScalar`. Choose between Option A/B/C above.

3. **Fix T3** (dispatch completeness): After parsing a scalar in `dispatchByChar`'s `?`/`-`/`'`/`"` cases, check for a following `: ` separator. If found, re-dispatch as a mapping entry. Alternatively, hoist the mapping detection check above the special-character dispatch.

4. **Fix T4** (`detectMappingKey`): Make `detectLoop` continue scanning past non-separator colons (`:` followed by non-whitespace) and past quote characters when they appear mid-key (not at position 0 or after whitespace).

5. **Run diagnostic**: After each fix, run `lake exe scalarstagediag` to track which test groups flip from fail to pass.

**This follows the §6 pattern**: implicit parameter semantics (`contentIndent` serving dual purposes) → explicit contract predicates (decidable, proved). The parameter separation is the code-level enforcement; the formal contracts are the proof-level enforcement.

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
| Error rejection | — | 70% (52/74) |

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
| Block scalar contracts | Implicit consumption → decidable predicates | Prevents header parser from consuming content indentation |
| Document parser contracts | Implicit boundary semantics → decidable predicates | Prevents bare content after explicit documents, enforces §6.7 comment rules |
| Block parser contracts (§2.I) | Dual-purpose parameter → explicit A/G contracts | Prevents indentation double-count and dispatch bypass for 20 scalar-stage failures |

For the verified parser, this principle is even more powerful: explicit state becomes **proof targets**. Every enum variant maps to a lemma obligation, and every state transition becomes a provable invariant.

---

## References

- [lean4-yaml DEVELOPMENT_LOG.md](../lean-yaml/DEVELOPMENT_LOG.md) — full timeline with regression analysis
- [lean4-yaml NEXT_STEPS.md](../lean-yaml/NEXT_STEPS.md) — LineState pattern and future priorities
- [lean4-yaml error-recovery-architecture.md](../lean-yaml/docs/error-recovery-architecture.md) — ParseResult design
- [lean4-yaml scalar-continuation-refactor.md](../lean-yaml/docs/scalar-continuation-refactor.md) — ContinuationCheck design
