# lean4-yaml-verified

A YAML 1.2.2 parser in Lean 4 with the goal of **verified correctness** — proofs that the parser conforms to the [YAML specification](https://yaml.org/spec/1.2.2/) and the [yaml-test-suite](https://github.com/yaml/yaml-test-suite).

## Architecture

```
Lean4Yaml/
├── Types.lean               # YamlValue AST (shared with lean4-yaml)
├── Stream.lean              # Position-aware YamlStream with line/col tracking
├── Grammar.lean             # Formal YAML grammar as Lean Props
├── Parser/
│   ├── Combinators.lean     # Character classification & basic parsers
│   ├── Scalar.lean          # Plain, quoted, and block scalar parsers
│   ├── Flow.lean            # Flow sequences [...] and mappings {...}
│   ├── Block.lean           # Block sequences (- item) and mappings (key: value)
│   └── Document.lean        # Document markers, directives, multi-document streams
│   ├── Anchor.lean          # Anchor (&) / alias (*) parsers with contracts
│   ├── Tag.lean             # Tag (!) parsers: `!!type`, `!local`, `!<uri>`, `!h!suffix`
├── Proofs/
│   ├── Termination.lean     # Termination proofs for recursive parsers
│   ├── Soundness.lean       # Parser produces only valid YAML (planned)
│   ├── RoundTrip.lean       # Parse ∘ emit = id (planned)
│   └── TestSuite.lean       # yaml-test-suite as compile-time checks (blocked)
└── Tests/
    ├── VerifiedResult.lean  # Shared result types (VerifiedSuiteResult, TestCollector)
    ├── Main.lean            # Unit tests (17 tests)
    ├── ParseTest.lean       # Parser integration tests (25 tests)
    ├── QuotedFolding.lean   # Quoted scalar folding tests (34 tests)
    ├── AnchorAlias.lean     # Anchor/alias tests (33 tests)
    ├── TagTests.lean        # Tag tests (44 tests)
    ├── Verification.lean    # Layer 1 verification tests (138 tests)
    ├── StringLemmas.lean    # String/position lemma tests (129 tests)
    ├── TryParse.lean        # Single-file parse binary (subprocess isolation)
    ├── CheckStringPos.lean  # String position utility tests
    └── SuiteRunner/
        ├── Meta.lean        # Line-based yaml-test-suite file parser
        ├── Main.lean        # Programmatic yaml-test-suite runner
        └── HtmlReport.lean  # Interactive HTML coverage reports
Demo.lean                    # End-to-end demo examples (7 tests)
```

### Three-Layer Verification Strategy

Verification uses a deliberate 3-layer approach:

1. **Internal runtime tests** (581 tests across 10 suites) — hand-written Lean tests validating parser properties. Every `theorem` target starts life as a runtime `check` test. These are _separate_ from the yaml-test-suite's 416 external test cases.
2. **Formal proofs** (`theorem`/`lemma` in `Proofs/*.lean`) — machine-checked guarantees. Layered by dependency: pure functions first, then parser invariants, then full soundness.
3. **Compile-time guards** (`#guard`) — blocked until lean4-parser removes `partial def`. Will convert runtime tests to kernel-evaluated checks.

The runtime tests serve as a proof roadmap: each `setCategory`/`check` group maps to a `theorem` target. When a proof is completed, the corresponding tests become redundant (but are kept as regression guards).

## Key Design Decisions

### Built on lean4-parser

Uses [fgdorais/lean4-parser](https://github.com/fgdorais/lean4-parser) as the parser combinator library, providing:
- Parameterized stream/error types (`ParserT ε σ τ m α`)
- Backtracking with `withBacktracking`
- Capture combinators for provenance tracking

### Position-Aware Stream

The `YamlStream` type automatically tracks line and column through the `next?` function. This eliminates the class of bugs demonstrated by the `skipToNextLine` regression in lean4-yaml, where implicit position state caused 230→7 yaml-test-suite test failures.

### Formal Grammar

The YAML grammar is encoded as Lean `Prop`s in `Grammar.lean`, independent of the parser. This enables stating and proving the soundness theorem:

```lean
theorem parse_sound :
  ∀ (input : String) (docs : Array YamlDocument),
    parseYaml input = .ok docs →
    Grammar.ValidYaml input docs
```

### Compatible AST

The `YamlValue` type is identical to lean4-yaml's, allowing the Schema/FromToYaml/Deriving/Emitter layers (~1500 lines) to be shared between implementations.

### No Exceptions for Control Flow

**Parser errors are never used as a decision-making mechanism.** When processing input — valid or invalid — the parser produces explicit result values describing what happened. Invalid YAML (wrong indentation, unexpected EOF, malformed structure) is an expected outcome, not an exceptional condition. The entire yaml-test-suite runs with zero exceptions unless there is a genuine internal bug.

This principle is enforced by the `DispatchResult` type at block-value dispatch points:

```lean
inductive DispatchResult (α : Type) where
  | matched (val : α)       -- parsed successfully
  | noMatch                  -- this branch doesn't apply (a decision, not an error)
  | invalid (msg : String)  -- input is definitively wrong (reported as a value)
```

This is critical because lean4-parser's error model has **no committed/fatal error distinction** — all `Result.error` values are caught unconditionally by `<|>`, `option?`, and `first`. Using `throwUnexpected` for input validation is unreliable since any enclosing combinator silently swallows it.

**P1 architectural change (2026-02-17):** All `throwUnexpected` calls have been eliminated from our codebase (29 occurrences across 7 files). Validation errors now use a `validationError : Option String` field in `YamlStream` that **survives backtracking** (like `anchorMap`). This works above the combinator level: `setValidationError` records the first error, subsequent calls are no-ops, and `parseYaml` checks the field after parsing completes. Decision points use explicit `Option` return types (`blockValue`, `blockSequence`, `blockMapping` now return `Option YamlValue`) instead of throwing. The `DispatchResult` encoding remains for block-value dispatch, but `.toParser` (which called `throwUnexpected`) has been removed — callers must pattern-match directly.

### OS-Level Process Isolation for Testing

The yaml-test-suite runner uses OS-level process isolation (`timeout(1)` wrapping a `tryparse` subprocess) to handle infinite loops in `partial def` parsers. Lean's `IO.asTask` cannot preempt pure infinite loops regardless of thread priority, so subprocess isolation is the correct approach until termination proofs (Phase 3) eliminate infinite loops at the type level.

### Cross-Project Insights

See [ANALYSIS.md](ANALYSIS.md) for a detailed comparison with the non-verified [lean4-yaml](../lean-yaml/) parser. Key takeaways: the `YamlStream` design eliminates an entire class of bugs that required a `LineState` workaround in lean4-yaml, but the three-valued error recovery pattern (`ParseResult`) and multi-line continuation logic (`ContinuationCheck`) should be ported.

## Development Log

### Phase 1: Core Parser ✅

Built the complete parser from scratch on Lean 4.28.0-rc1 / Lake v5.0.0:

| Module | Lines | Description |
|--------|-------|-------------|
| `Types.lean` | ~173 | YamlValue AST, YamlDocument, compatible with lean4-yaml |
| `Stream.lean` | ~272 | Position-aware YamlStream with automatic line/col tracking |
| `Grammar.lean` | ~315 | Formal YAML grammar encoded as Lean Props |
| `Combinators.lean` | ~215 | Character classification, whitespace/indent handling |
| `Scalar.lean` | ~710 | Plain, double-quoted, single-quoted, block scalar parsers |
| `Flow.lean` | ~420 | Flow sequences `[...]` and mappings `{...}` (mutual recursion, implicit single-pair entries §7.5, JSON-like key detection §7.4) |
| `Block.lean` | ~352 | Block sequences and mappings with indentation tracking |
| `Document.lean` | ~230 | Document markers `---`/`...`, directives, multi-document streams |

**Total: ~2472 lines, 217 build jobs, 0 errors.**

### Phase 2: Parser Validation (Current) ← **YOU ARE HERE**

#### 2a. Parser Integration Tests ✅

Created 24+ integration tests in `Tests/ParseTest.lean` covering:
- Double-quoted, single-quoted, and plain scalars
- Flow sequences and mappings (including nested)
- Block sequences and mappings (including nested)
- Multi-document streams
- All tests pass.

#### 2b. Demo End-to-End ✅

All 7 demo examples in `Demo.lean` pass, including deeply nested structures.

#### 2c. Compile-Time `#guard` Tests — Blocked

`#guard` requires kernel reduction, which does not work with `partial def` parsers. This step is deferred until Phase 3 eliminates `partial` annotations.

#### 2d. yaml-test-suite — In Progress

Added [yaml-test-suite](https://github.com/yaml/yaml-test-suite) as a git submodule and built a programmatic test runner.

**Infrastructure built:**
- `Tests/SuiteRunner/Meta.lean` (~280 lines) — line-based meta-parser for the yaml-test-suite file format (bootstrapping: can't use our own YAML parser to parse the test suite's YAML metadata)
- `Tests/SuiteRunner/Main.lean` (~200 lines) — test runner with staged execution, progress output, and result reporting
- `Tests/TryParse.lean` — minimal binary for subprocess-based parse testing with `timeout(1)` for infinite loop protection
- `Lean4Yaml/Parser/Combinators.lean` — validation helpers (`validateNoWrongIndentSeq`, `validateNoWrongIndentMap`) for three-valued error recovery ([ANALYSIS.md](ANALYSIS.md) §2.A), active in `Block.lean`
- Test classification by tags into stages: scalar → flow → block → document → advanced → error
- Cumulative stage execution (e.g., `flow` stage runs both scalar and flow tests)

**Full yaml-test-suite results (416 test cases from 351 files):**

| Stage | Tests | Passed | Failed | Unexpected Pass | Skipped | Correct Rate |
|-------|-------|--------|--------|-----------------|---------|-------------|
| Scalar | 82 | 51 | 2 | 1 | 28 | 62% |
| Flow | 46 | 35 | 8 | 3 | 0 | 76% |
| Block | 109 | 71 | 14 | 14 | 10 | 65% |
| Document | 24 | 14 | 1 | 2 | 7 | 58% |
| Advanced | 81 | 21 | 43 | 0 | 17 | 26% |
| Error | 74 | 0 | 0 | 74 | 0 | 0% |
| **Total** | **416** | **192** | **68** | **94** | **62** | **46.2%** |

**Key findings:**
- **192/416 correct (46.2%)** — up from 175/416 (42.1%) after adding tag support (step 8)
- **94 unexpected passes** — parser is too permissive: 74 in the error stage (parser accepts invalid YAML), 20 in other stages
- **68 failures** — down from 85 after tag support fixed 17 tag-related failures
- **0 infinite loops** — `DocumentResult` type makes parse-progress explicit
- **Advanced stage: 21/81 (26%)** — tag support added (step 8), anchor/alias support added (step 7)

**Failure root cause analysis** (run `python3 tests/analyze_coverage.py` or `python3 tests/analyze_coverage_deep.py` for full details):

| Root Cause | Failures | Description |
|------------|----------|-------------|
| Tags (`!`) edge cases | 11 | Remaining tag failures: verbatim tags in complex contexts, `%TAG` resolution, bare `!` edge cases |
| Explicit key (`?`) not supported | 17 | `?` indicator in block/flow contexts |
| Flow edge cases | 9 | Implicit keys, single-pair entries, empty collections |
| Empty key handling | 6 | Missing/empty keys in block and flow contexts |
| Comment edge cases | 5 | Comments after flow, in multi-line, after directives |
| Escape sequences | 5 | Unicode escapes (`\x`, `\u`, `\U`) in double-quoted scalars |
| Anchor/alias edge cases | 4 | Unicode anchors, anchors before zero-indent, empty-node anchors |
| Complex keys | 3 | Flow collections as mapping keys |
| Other | 8 | Indent edge cases, alias edge cases, document markers |

**Unexpected pass analysis:**

| Category | Count | Description |
|----------|-------|-------------|
| Flow structure | 13 | Missing commas, extra brackets, invalid entries accepted |
| Mapping structure | 12 | Invalid mapping structure accepted |
| Quoted scalars | 10 | Unclosed quotes, invalid escapes accepted |
| Indentation | 9 | Wrong indentation accepted |
| Directives | 7 | Invalid `%YAML`/`%TAG` directives accepted |
| Anchors/aliases | 7 | Double anchors, invalid anchor positions accepted |
| Comments | 6 | Invalid comment positions accepted |
| Block scalars | 3 | Invalid block scalar indicators accepted |
| Document markers | 3 | Invalid content after `...` accepted |
| Tags | 2 | Invalid tag syntax accepted |
| Other | 2 | Edge cases in scalar/sequence validation |

**Key bugs found and fixed during Phase 2:**
1. **Plain scalar consuming flow indicators** — `anyToken` in `collectPlain` consumed `,`, `]`, `}` before the check could reject them. Fixed with `lookAhead anyToken` (peek-before-consume pattern).
2. **Block mapping key consuming `:`** — same peek-before-consume fix applied to `plainMappingKey`.
3. **Missing indentation consumption** — block parsers didn't consume leading whitespace after line breaks before checking column position. Fixed by adding `skipHWhitespace` before `currentCol` checks.
4. **Meta parser `---` handling** — `processLine` checked for `---` separator before checking if inside a yaml block scalar, truncating test yaml content. Fixed by reordering to check block scalar state first.

**Validation work (ANALYSIS.md §2.A):**
Three-valued error recovery combinators (`validateNoWrongIndentSeq`, `validateNoWrongIndentMap`, `hasSequenceIndicator`) are **active** in `blockSequenceItems` and `blockMappingEntries`. They detect wrongly-indented structural indicators (e.g., `- ` at col 1 when `seqIndent = 0`) and raise validation errors. Impact: error rejection improved from 24% to 54% (+22 tests), overall suite from 164→192 passed (39.4%→46.2%).

**P1: Strict validation — `throwUnexpected` elimination (2026-02-17):**
All 29 `throwUnexpected` / `throwUnexpectedWithMessage` calls eliminated from our codebase. Two-mechanism replacement architecture:

1. **`validationError` in `YamlStream`** — a `Option String` field that survives lean4-parser's backtracking (stored in stream state like `anchorMap`). Set via `setValidationError` (first error wins), checked at top level by `parseYaml`. Proved: `setPosition_preserves_validationError` and `next_preserves_validationError` (both `rfl`).
2. **Explicit result types** — `blockValue`, `blockSequence`, `blockMapping` now return `Option YamlValue` (none = under-indented / no match, not an error). `DispatchResult.toParser` removed entirely. Callers pattern-match directly.

Files modified: `Stream.lean` (+validationError field, combinators, theorems), `Combinators.lean` (-toParser, tab/indent validators), `Block.lean` (Option returns, direct dispatch), `Flow.lean` (delimiter validation), `Scalar.lean` (escape validation, plainScalar restructuring with `lookAhead`+`notFollowedBy`), `Document.lean` (marker validation, top-level error check), `Anchor.lean` (undefined alias validation).

Impact: **213→250 correct (+37)**, 51.2%→60.1%. Error stage: 0→26 correctly rejected (0%→35.1%). Parse failures: 47→20 (-27). All 494 internal tests pass. Trade-off: removing `throwUnexpected` made the parser more permissive in some non-error contexts where `<|>` previously accidentally propagated the error — non-error unexpected passes increased from 20→36. Further validation rules needed to close the remaining 48 error-stage and 36 non-error unexpected passes.

**P2: Flow completeness (2026-02-18):**
Flow stage improved from 34/46 (74%) to 43/46 (93.5%). Three changes to `Flow.lean` and one to `Scalar.lean`:

1. **`flowSequenceItems`** — Added implicit single-pair mapping detection: after parsing a `flowValue`, checks for `:` separator (with §7.4 JSON-like rules: collections and quoted scalars don't require whitespace after `:`). Also added empty implicit key detection (`: value` → null-key mapping). ~60 lines added.
2. **`flowMappingEntry`** — Changed normal key parsing from `flowScalar` to `first [flowSequence, flowMapping, flowScalar]` so flow collections can serve as mapping keys (§7.4.2). Added JSON-like `:` awareness using `Bool` pattern matching on `YamlValue` constructors.
3. **`plainScalarContent` (Scalar.lean)** — Removed early `if inFlow then return firstLine` exit. Added `collectFlowLines` helper (~50 lines) for flow-specific multi-line continuation: stops at flow indicators, document boundaries; space-folds lines per §7.3.3.

Suite IDs fixed: 87E4, 8KB6, 8UDB, L9U5, LQZ7, QF4Y, NJ66, CFD4 (all flow-stage). 88 new tests in `FlowTests.lean` covering 7 categories. Trade-off: more permissive flow parsing regressed error stage from 26→0; flow-specific validation rules needed to restore.

**Infinite loop elimination via `DocumentResult`:**
Discovered 36 timeout cases (not 9), all sharing one root cause: `yamlStream`'s while loop retries `document` at the same position when no input is consumed. The initial fix (external position comparison) revealed an implicit assumption: `document` already knew whether it consumed input but didn't communicate this. Refactored `document` to return `DocumentResult` (`parsed`/`endOfStream`/`stalled`) — the same explicit-result-type pattern as `DispatchResult` and `ContinuationCheck`. Now `yamlStream` pattern-matches on the result instead of comparing positions externally. The `stalled` variant carries position for error reporting and becomes a proof obligation target in Phase 4. Eliminated all 36 timeout cases across 9 root cause categories (anchors, tags, quoted scalar folding, comments, explicit keys, same-indent sequences, tabs, empty keys, flow implicit mappings).

### Phase 3: Verification — Layered Approach

Formal verification proceeds in three layers, ordered by feasibility and diagnostic impact.

**Key constraint: lean4-parser `partial` dependency.** The lean4-parser library uses `private partial def efoldlPAux` in its core fold loop, which propagates through `dropMany`, `count`, and other combinators our parsers depend on. Since `#guard` requires kernel reduction and `partial def` blocks kernel reduction, compile-time `#guard` tests remain blocked until lean4-parser removes its internal `partial` annotations. Our verification focuses on what IS provable now: standalone theorems, pure function properties, and specification invariants.

Our own parsers are `partial def` for two independent reasons:
1. **Own recursion** — self-recursive loops (`foldQuotedNewlines.loop`, `blockSequenceItems`, etc.) need termination proofs to remove `partial`
2. **lean4-parser dependency** — even if our recursion is proven total, `#guard` won't work because lean4-parser's kernel-opaque `partial` blocks reduction

Layer 1 targets reason (1) and delivers property proofs independent of lean4-parser. Layer 3 targets the full soundness theorem.

#### Layer 1: Foundation ← **YOU ARE HERE**

Standalone proofs about the stream, pure helper functions, and character classifiers. These have zero lean4-parser dependency. Each item has extensive runtime test coverage (350 tests across `Verification.lean` and `StringLemmas.lean`) that validates the properties empirically before they are proved formally.

| Item | Description | Runtime Tests | Proof Status |
|------|-------------|---------------|-------------|
| **1a** | `next_decreasing`: after `YamlStream.next?`, remaining input strictly decreases | 38 tests (Verification: remainingLength, Stream exhaustive consumption; StringLemmas: advancement, strictly monotone) | 🔄 `theorem` declared, `sorry` on string arithmetic |
| **1b** | Properties of `trimTrailingWhitespace`, `trimTrailingWs` (idempotence, no trailing ws) | 12 tests (Verification: trimTrailingWhitespace) | ⬜ Tests only |
| **1c** | `Grammar.lean` character Props match `Combinators.lean` implementations | 32 tests (Verification: Grammar↔Combinators isLineBreak/isWhiteSpace/isFlowIndicator/isIndentChar, canStartPlainScalar) | ⬜ Tests only |
| **1d** | `FoldResult` type invariants | 4 tests (Verification: FoldResult) | ⬜ Tests only |

Effort: ~2 sessions. Diagnostic value: catches bugs in pure helper functions at compile time.

#### Layer 2: Key Invariants

Property proofs about specific parser behaviors. Where proofs cross into lean4-parser territory, termination is `sorry`-admitted to focus on the invariant itself.

| Item | Description | Status |
|------|-------------|--------|
| **2a** | `foldQuotedNewlines` output has no c-forbidden characters | |
| **2b** | Escape sequence resolution produces valid Unicode in `doubleQuotedScalar` | |
| **2c** | `consumeIndent n` advances column by exactly `n` | |
| **2d** | Decidable instances for `Grammar.lean` propositions | |

Effort: ~2 sessions. Diagnostic value: specification-level checks for scalar parsing.

#### Layer 3: Full Termination & Soundness (After Anchors)

Full termination proofs for block/flow/document mutual recursion + soundness composition into `parse_sound`. Deferred until parser structure stabilizes after anchors/aliases.

| Item | Description | Status |
|------|-------------|--------|
| **3a** | Remove `partial` from leaf parsers (own recursion) | |
| **3b** | Remove `partial` from block/flow/document mutual recursion groups | |
| **3c** | Compose soundness proofs: each parser produces `Grammar.ValidNode` | |
| **3d** | Top-level `parse_sound` theorem | |
| **3e** | Convert `axiom`s in `Soundness.lean` to `theorem`s | |

Effort: ~5+ sessions. Full `#guard` requires lean4-parser `partial` constraint resolved.

### Remaining Phases (Future)

#### Phase 4: yaml-test-suite Proofs

Encode yaml-test-suite test cases as compile-time `#guard` / `theorem` checks (requires Layer 3 + total lean4-parser).

#### Phase 5: Round-Trip Proofs

Prove `parse ∘ emit = id` for a canonical YAML subset.

#### Phase 6: Integration with lean4-yaml

Share the verified implementation with the existing lean4-yaml ecosystem.

## Next Steps

### Completed

1. ~~**Three-valued error recovery**~~ — ✅ Validation combinators active in `Block.lean`.
2. ~~**Refactor `blockValue` dispatch to `DispatchResult`**~~ — ✅ `DispatchResult` type in `Combinators.lean`.
3. ~~**Add multi-line plain scalar support**~~ — ✅ `ContinuationCheck` type, line folding per §6.5.
4. ~~**Re-enable validation combinators**~~ — ✅ Suite: 164→177 passed.
5. ~~**Eliminate infinite loops**~~ — ✅ `DocumentResult` type. All 36 timeouts eliminated.
6. ~~**Fix multi-line quoted scalars**~~ — ✅ `FoldResult` type + 5 algorithmic bug fixes. 33 tests in `QuotedFolding.lean`.
7. ~~**Add anchor/alias support**~~ — ✅ `AnchorMap` abstraction with algebraic laws, `parseAlias`/`parseAnchorPrefix`/`resetAnchorMap`. Document-scoped anchors per §3.2.2.2. 2 backtracking-isolation theorems proved. 33 tests in `AnchorAlias.lean`. Advanced stage: 1→10 passing.
8. ~~**Add tag support**~~ — ✅ `parseTagPrefix` handles all tag forms: verbatim (`!<uri>`), secondary (`!!type`), named (`!handle!suffix`), primary (`!local`), non-specific (`!`). `YamlValue.withTag` applies tags to any node. Tag+anchor ordering (`!tag &anchor val` and `&anchor !tag val`) supported in all dispatch points. 44 tests in `TagTests.lean`. Suite: 175→192 correct (+17), Advanced stage: 10→21 passing.
9. ~~**Flow completeness (P2)**~~ — ✅ Implicit single-pair entries (`[key: value]`, §7.5), JSON-like `:` detection (`["key":adjacent]`, §7.4), multi-line flow plain scalars (`{multi\nline: v}`, §7.3.3), flow mapping collection keys (`{[1,2]: v}`, §7.4.2), empty implicit keys (`[: value]`). 88 tests in `FlowTests.lean`. Flow stage: 34→43/46 (74%→93%).

### Current: Address Failures + Unexpected Passes

Analysis scripts: `python3 tests/analyze_coverage.py` (summary) and `python3 tests/analyze_coverage_deep.py` (detailed root causes).

Current: **241/416 correct (57.9%)**. Flow stage at 93.5% after P2. Projected after remaining steps: **~354/416 (~85.1%)**.

#### Step 8: Tag support (`!tag`, `!!type`, `%TAG` directive) — ✅ COMPLETE

**Result: +17 correct (175→192).** Fixed 17/28 tag-related failures. Remaining 11 tag failures involve:
- Verbatim tags in complex nested contexts (7FWL, UGM3)
- `%TAG` directive resolution not wired to tag handles (5TYM, P76L)
- Named handle tags in sequences (Z9M4, 6CK3)
- Bare `!` and edge cases (UKK6, S4JQ)

Implementation: `Tag.lean` (155 lines) — `parseTagPrefix` with all 5 tag forms. Wired into `dispatchByChar` (`Block.lean`), `blockMappingKey` (`Block.lean`), and `flowValue` (`Flow.lean`). Both tag+anchor orderings supported.

#### Step 9: Explicit key support (`?`) — +17 tests

**Impact: 17 failures fixed.** Second largest feature gap.

The parser doesn't recognize `?` as an explicit key indicator (§8.2.2). This blocks 17 advanced-stage tests including complex mappings, multi-line keys, and spec examples. Need:
- `?` detection at block indent level → starts explicit key
- `?` in flow context → complex key indicator
- Value follows on next line after `:` at same indent

Test IDs: 5WE3, 6M2F, 6PBE, 7W2P, A2M4, CT4Q, DFF7, FRK4, GH63, JTV5, KK5P, M5DY, PW8X, V9D5, X8DW, ZWK4 (+ some overlap with tags).

#### Step 10: Strict validation (error rejection) — ⚠️ IN PROGRESS

**P1 phase 1 complete (2026-02-17).** Architectural change: eliminated all 29 `throwUnexpected` calls, replaced with `validationError` field in `YamlStream` (survives backtracking) + explicit `Option` return types.

**Results so far:** Error stage: regressed to 0/74 after P2 flow changes made the parser more permissive in flow contexts. Overall: 241/416 correct (57.9%). Flow stage improved to 43/46 (93.5%).

**Remaining work:** 48 error-stage + 36 non-error unexpected passes still need validation rules. Sub-steps below track what's done vs remaining:

| Sub-step | Category | Count | Status | Notes |
|----------|----------|-------|--------|-------|
| **10a** | Flow structure | 13 | ⚠️ Partial | `flowSequenceItems`/`flowMappingEntries` delimiter validation active; implicit key width limit not yet checked |
| **10b** | Mapping structure | 12 | ⚠️ Partial | Indentation validators active; duplicate key detection not yet implemented |
| **10c** | Quoted scalars | 10 | ✅ Done | Invalid escapes, `FoldResult.forbidden` now set `validationError` |
| **10d** | Indentation | 9 | ✅ Done | `consumeIndent` (tabs), `validateNoWrongIndentSeq/Map` now use `setValidationError` |
| **10e** | Anchors/aliases | 7 | ⚠️ Partial | Undefined aliases validated; double anchors, invalid positions not yet checked |
| **10f** | Directives | 7 | ❌ Not started | Invalid `%YAML`/`%TAG` syntax not yet validated |
| **10g** | Comments | 6 | ❌ Not started | Invalid comment positions not yet validated |
| **10h** | Block scalars | 3 | ❌ Not started | Invalid block scalar indicators not yet validated |
| **10i** | Document markers | 3 | ✅ Done | `---`/`...` not followed by whitespace now sets `validationError` |
| **10j** | Tags/other | 4 | ❌ Not started | Invalid tag syntax not yet validated |

#### Step 11: Remaining edge cases — +14 tests

| Category | Failures | Description |
|----------|----------|-------------|
| Empty key handling | 6 | Missing/empty keys in block contexts |
| Escape sequences | 5 | Unicode escapes (`\x`, `\u`, `\U`) in double-quoted scalars |
| Complex keys | 3 | Flow collections as block mapping keys (§8.2.2) |

#### Step 12: Iterate toward 60%+ correct rate

After steps 8–11, projected correct rate is ~74.5% (310/416). The remaining ~25% are edge cases in:
- Non-error unexpected passes in block/flow/document stages (20 tests)
- Interactions between features (anchor + tag, explicit-key + tag, etc.)
- YAML 1.3-specific tests (currently skipped, 62 tests)

## Gap Analysis: YAML 1.2.2 Specification Coverage

### Current State (2026-02-18)

**yaml-test-suite: 241/416 correct (57.9%)** — flow stage at 93.5% after P2 flow completeness work.

| Stage | Tests | Correct | Failed | Skipped | Correct Rate |
|-------|-------|---------|--------|---------|-------------|
| Scalar | 82 | 51 | 3 | 28 | 62% |
| Flow | 46 | 43 | 3 | 0 | 93% |
| Block | 109 | 77 | 22 | 10 | 71% |
| Document | 24 | 15 | 2 | 7 | 63% |
| Advanced | 81 | 55 | 9 | 17 | 68% |
| Error | 74 | 0 | 74 | 0 | 0% |
| **Total** | **416** | **241** | **113** | **62** | **57.9%** |

"Failed" includes both parse errors on valid YAML and unexpected passes on invalid YAML.

Note: Error stage regressed from 26→0 after P2 flow changes — the more permissive flow parsing (accepting implicit mappings, JSON-like `:`) now also accepts some invalid flow constructs that P1's `validationError` was catching. Additional flow-specific validation rules needed.

**Internal test suites: 581/581 (100%) across 10 suites** (hand-written Lean tests; separate from the 416 yaml-test-suite cases above).

### What's Implemented vs YAML 1.2.2 Spec

| Spec Chapter | Section | Status | Notes |
|---|---|---|---|
| **§5 Characters** | §5.1 Character set | ✅ | UTF-8 stream |
| | §5.2 Character encodings | ✅ | UTF-8 only (BOM detection deferred) |
| | §5.3 Indicator characters | ✅ | All indicators classified in `Combinators.lean` |
| | §5.4 Line break characters | ✅ | CR, LF, CRLF handled in `Stream.lean` |
| | §5.5 White space characters | ✅ | Space + tab |
| | §5.6 Miscellaneous characters | ✅ | |
| | §5.7 Escaped characters | ✅ | All YAML 1.2 escape sequences including `\\`, `\n`, `\t`, `\x`, `\u`, `\U`, `\` + newline |
| **§6 Structural** | §6.1 Indentation spaces | ✅ | `consumeIndent`, `currentCol` |
| | §6.2 Separation spaces | ✅ | `skipHWhitespace` |
| | §6.3 Line prefixes | ⚠️ | Implicit via indentation; not a discrete parser |
| | §6.4 Empty lines | ✅ | `ContinuationCheck.afterEmpty` |
| | §6.5 Line folding | ✅ | `foldQuotedNewlines` + `FoldResult` for quoted; `plainScalarContent` for plain |
| | §6.6 Comments | ⚠️ | Basic `#` comment; 5 edge-case failures (after flow, in multi-line) |
| | §6.7 Separation lines | ⚠️ | Handled implicitly; no explicit `s-separate` production |
| | §6.8 Directives | ⚠️ | `%YAML` parsed; `%TAG` parsed but handle resolution not wired through |
| | §6.9 Node properties | ✅ | Tags (`Tag.lean`) + anchors (`Anchor.lean`), both orderings |
| **§7 Flow Styles** | §7.1 Alias nodes | ✅ | `parseAlias` with `AnchorMap` lookup |
| | §7.2 Empty nodes | ⚠️ | Partial — 1 failure (WZ62) |
| | §7.3.1 Double-quoted | ✅ | Full escape support + line folding + `c-forbidden` |
| | §7.3.2 Single-quoted | ✅ | Folding + `''` escape |
| | §7.3.3 Plain style | ✅ | Multi-line with `ContinuationCheck`, flow-aware termination |
| | §7.4.1 Flow sequences | ✅ | Nested, trailing commas, explicit entries, implicit single-pair mapping entries (§7.5) |
| | §7.4.2 Flow mappings | ✅ | Explicit keys, empty keys, implicit keys, collection keys, JSON-like `:` detection |
| | §7.5 Flow nodes | ✅ | Single-pair implicit entries, JSON-like keys, multi-line flow plain scalars (P2 complete) |
| **§8 Block Styles** | §8.1.1 Block scalar headers | ⚠️ | Literal `|` and folded `>` with indentation/chomping indicators |
| | §8.1.2 Literal style | ✅ | `blockLiteralScalar` |
| | §8.1.3 Folded style | ✅ | `blockFoldedScalar` |
| | §8.2.1 Block sequences | ✅ | `blockSequence` with indentation tracking |
| | §8.2.2 Block mappings | ✅ | `blockMapping` with explicit key `?` support + `ExplicitKeyTests` (66 tests) |
| | §8.2.3 Block nodes | ✅ | `blockValue` dispatch via `DispatchResult` |
| **§9 Document** | §9.1.1 Document prefix | ✅ | BOM handling, comment prefix |
| | §9.1.2 Document markers | ✅ | `---` and `...` with `c-forbidden` detection in quoted scalars |
| | §9.1.3 Bare documents | ✅ | |
| | §9.1.4 Explicit documents | ✅ | |
| | §9.1.5 Directives documents | ⚠️ | Parsed but `%TAG` not resolved |
| | §9.2 Streams | ✅ | Multi-document via `yamlStream` + `DocumentResult` |
| **§10 Schemas** | §10.1 Failsafe schema | ❌ | No schema layer |
| | §10.2 JSON schema | ❌ | No schema layer |
| | §10.3 Core schema | ❌ | No schema layer |

### Three Categories of Gaps to 100%

#### Category 1: Parser Failures (47 tests) — Content Correctness

Tests where the parser either fails to parse valid YAML or produces incorrect output.

| Root Cause | Count | Spec Section | Description |
|---|---|---|---|
| Flow edge cases | 1 | §7.4 | 9MMW: flow mapping as implicit key with adjacent `:` (`[{JSON: like}:adjacent]`) |
| Block edge cases | 17 | §8.2 | Same-indent sequences, aliases in block mappings, anchor edge cases, missing value handling |
| Quoted scalar content | 4 | §7.3.1, §7.3.2 | Remaining line-folding edge cases (3RLN, DE56, KH5V, M2N8) |
| Comments | 5 | §6.6 | Comments after flow collections, in multi-line scalars, after directives |
| Tag resolution | 4 | §6.8, §6.9 | `%TAG` directive wire-through, verbatim tags in complex contexts |
| Alias/anchor edge cases | 4 | §7.1, §6.9 | Unicode anchors, anchors in complex positions |
| Complex keys | 3 | §7.4.2, §8.2.2 | Flow collections as mapping keys |

#### Category 2: Permissiveness (94 unexpected passes) — Error Rejection

Tests where the parser accepts invalid YAML that should be rejected. The parser has **no strict validation mode** — it is too lenient.

| Category | Count | What Should Be Rejected |
|---|---|---|
| **Error stage** | **74** | Tests specifically designed to trigger parse errors |
| Flow structure | 13 | Missing commas, extra brackets, unterminated collections |
| Mapping structure | 12 | Invalid key-value structure, duplicate keys |
| Quoted scalars | 10 | Unclosed quotes, invalid escapes |
| Indentation | 9 | Wrong indentation accepted |
| Directives | 7 | Invalid `%YAML`/`%TAG` syntax |
| Anchors/aliases | 7 | Double anchors, undefined aliases, invalid positions |
| Comments | 6 | Invalid comment positions |
| Block scalars | 3 | Invalid indicators, wrong indentation |
| Document markers | 3 | Invalid content after `...` |
| Other | 4 | Tag syntax, trailing content |

The root cause was architectural: lean4-parser's `<|>` unconditionally catches all `Result.error` values, making `throwUnexpected` unreliable for validation. **P1 fix (2026-02-17):** All `throwUnexpected` calls eliminated and replaced with `validationError` field in `YamlStream` (survives backtracking). **P2 regression (2026-02-18):** Flow completeness changes (accepting implicit mappings in sequences, JSON-like `:`) made the parser more permissive, regressing error stage from 26/74 to 0/74. Flow-specific validation rules (e.g., rejecting unterminated flow collections, validating implicit key constraints) needed to restore error rejection while keeping the new flow features.

#### Category 3: Skipped Tests (62 tests)

| Category | Count | Reason |
|---|---|---|
| YAML 1.1/1.3 features | 28 | Tests for features outside YAML 1.2.2 scope |
| Block scalar edge cases | 17 | Advanced `|`/`>` features (indentation auto-detection, strip/clip/keep interactions) |
| Advanced document features | 7 | Multi-document edge cases with directives |
| Other | 10 | Tests requiring features not yet categorized |

### Path to 100% yaml-test-suite Compliance

**Current: 250/416 (60.1%).** Target: 354/416 (85.1%), excluding 62 skipped tests outside YAML 1.2.2 scope.

| Phase | Work | Tests Fixed | Projected |
|---|---|---|---|
| **P1: Strict validation** | ⚠️ **Phase 1 complete.** Eliminated all `throwUnexpected`; `validationError` field in `YamlStream` + explicit `Option` returns. +37 correct so far; ~84 UP remain. | +37 done, ~57 remaining | 307/416 (73.8%) |
| **P2: Flow completeness** | ✅ **Complete.** Implicit single-pair entries (§7.5), JSON-like `:` detection (§7.4), multi-line flow plain scalars (§7.3.3), flow mapping collection keys (§7.4.2), empty implicit keys. Flow stage: 34→43/46 (74%→93%). 88 new tests in `FlowTests.lean`. | +9 done | — |
| **P3: Block completeness** | Same-indent sequence edge cases, alias interactions, missing value handling | +17 | 334/416 (80.3%) |
| **P4: Content correctness** | Remaining quoted scalar folding, comment edge cases, `%TAG` resolution | +13 | 347/416 (83.4%) |
| **P5: Advanced features** | Complex keys (flow collections as keys), Unicode anchors, directive edge cases | +7 | 354/416 (85.1%) |

The remaining 62 skipped tests are YAML 1.1/1.3 features or tests that require behavior outside the YAML 1.2.2 specification. Full 100% of the YAML 1.2.2-applicable tests (354/354) requires all five phases.

### YAML 1.2.2 Spec Sections Not Yet Covered

| Section | Description | Difficulty | Dependency |
|---|---|---|---|
| §6.8.2 `%TAG` directive resolution | Map `!handle!suffix` → expanded URI using directive declarations | Medium | Wire `%TAG` declarations into parser state |
| §7.5 Flow nodes (complete) | ✅ Done (P2) | — | Implicit single-pair entries, JSON-like `:`, multi-line flow plain scalars |
| §9.1.3 `c-forbidden` (complete) | Reject `---`/`...` inside block scalars at column 0 | Low | Already partial in `FoldResult` |
| §10 Recommended Schemas | Failsafe, JSON, Core schema type resolution | High | **Separate schema layer** (see below) |

---

## Verified Schema Layer

### Motivation

The non-verified `lean4-yaml` project (now deprecated) implemented a **684-line schema layer** (`Schema.lean` + `Schema/Api.lean` + `Schema/FromToYaml.lean` + `Schema/Struct.lean`) plus a 296-line `Deriving.lean` macro. This layer provides:

1. **`YamlType`** — resolved typed values: `.null`, `.bool`, `.int`, `.float`, `.str`, `.seq`, `.map`
2. **`resolve : YamlValue → YamlType`** — Core Schema implicit typing (null → bool → int → float → str precedence)
3. **`FromYaml`/`ToYaml`** — typeclasses for Lean type ↔ YAML conversion
4. **`Struct.lean`** — helpers for manual struct serialization (`getField`, `addField`, `mkMapping`)
5. **`Deriving.lean`** — `deriving FromYaml, ToYaml` metaprogramming with automatic `Option` field detection

The architecture is designed for reuse: `lean4-yaml-verified` and `lean4-yaml` share identical `YamlValue` types (documented in `Types.lean`). The schema layer sits entirely above the parser — it operates on `YamlValue` and has zero parser dependency. This means the verified parser can adopt the schema layer with no parser changes.

### Architecture: Two-Layer Separation

```
                    ┌─────────────────────────────────────────────┐
                    │         Application Code                    │
                    │   structure Config deriving FromYaml, ToYaml│
                    └──────────────────┬──────────────────────────┘
                                       │ parseAs Config yaml
                    ┌──────────────────▼──────────────────────────┐
                    │         Schema Layer (NEW)                  │
                    │                                             │
                    │  YamlType    — resolved typed values        │
                    │  resolve     — Core Schema resolution       │
                    │  FromYaml    — typeclass: YamlValue → α     │
                    │  ToYaml      — typeclass: α → YamlValue     │
                    │  Deriving    — deriving macro                │
                    │  Emitter     — YamlValue → String           │
                    │                                             │
                    │  PROOFS:                                    │
                    │  resolve_preserves_structure                │
                    │  resolve_idempotent                         │
                    │  fromYaml_toYaml_roundtrip                  │
                    │  resolveImplicit_complete                   │
                    └──────────────────┬──────────────────────────┘
                                       │ parseSingle / parseYaml
                    ┌──────────────────▼──────────────────────────┐
                    │         Parser Layer (EXISTING)             │
                    │                                             │
                    │  String → YamlValue                         │
                    │  (verified correctness: Phase 3+)           │
                    └─────────────────────────────────────────────┘
```

The critical property: **the schema layer is pure functions on inductive types** — no IO, no parser combinators, no lean4-parser dependency. This makes it the ideal target for formal verification since every function is kernel-reducible.

### Verified Schema Roadmap

#### Phase S1: Core Types & Resolution (~300 lines)

Port `Schema.lean` with proof targets. The resolution functions are pure pattern-matching on strings — ideal for formal verification.

**Module: `Lean4Yaml/Schema.lean`**

```
YamlType          — Inductive type (identical to lean4-yaml)
FloatValue        — .finite | .inf | .nan
isNull            — String → Bool
isBool            — String → Option Bool
isInt             — String → Option Int
isFloat           — String → Option FloatValue
resolveImplicit   — String → YamlType  (Core Schema precedence)
resolveScalar     — String → Option String → YamlType  (explicit tag dispatch)
resolve           — YamlValue → YamlType  (recursive resolution)
```

**Proof targets:**

| Theorem | Statement | Difficulty |
|---|---|---|
| `resolve_preserves_structure` | `resolve (.sequence s items t) = .seq (items.map resolve)` — resolution doesn't change collection shape | Low |
| `resolve_scalar_with_str_tag` | `resolveScalar s (some "tag:yaml.org,2002:str") = .str s` — explicit `!!str` always produces string | Low |
| `resolveImplicit_complete` | `∀ s, resolveImplicit s` matches exactly one of `null/bool/int/float/str` — no unhandled case | Low |
| `resolveImplicit_deterministic` | `resolveImplicit s = resolveImplicit s` (trivially true, but the real content: resolution is a pure function with no hidden state) | Low |
| `isNull_spec` | `isNull s ↔ s ∈ {"", "null", "Null", "NULL", "~"}` — matches YAML 1.2.2 §10.3.2 exactly | Low |
| `isBool_spec` | `isBool s = some b ↔ s ∈ {"true","True","TRUE"} ∧ b = true ∨ s ∈ {"false","False","FALSE"} ∧ b = false` | Low |
| `isInt_hex_correct` | `isInt "0xFF" = some 255` (and general hex → Int correctness) | Medium |
| `isInt_octal_correct` | `isInt "0o17" = some 15` | Medium |
| `resolve_idempotent` | `resolve (toYamlValue (resolve v)) = resolve v` — resolving a re-serialized value gives the same type | Medium |

Estimated effort: 1 session for port, 1 session for proofs.

#### Phase S2: FromYaml/ToYaml Typeclasses (~200 lines)

Port `Schema/FromToYaml.lean`. The typeclass instances are small pattern-match functions — each is independently provable.

**Module: `Lean4Yaml/Schema/FromToYaml.lean`**

```
class FromYamlType α   — fromYamlType? : YamlType → Except String α
class FromYaml α       — fromYaml? : YamlValue → Except String α
class ToYaml α         — toYaml : α → YamlValue

-- Bridge instance: FromYamlType α → FromYaml α (via resolve)
-- Instances: Unit, Bool, Int, Nat, String, Array α, List α, Option α, HashMap String α
```

**Proof targets:**

| Theorem | Statement | Difficulty |
|---|---|---|
| `fromYaml_toYaml_Bool` | `fromYaml? (toYaml b) = .ok b` — Bool round-trips | Low |
| `fromYaml_toYaml_Int` | `fromYaml? (toYaml n) = .ok n` — Int round-trips | Low |
| `fromYaml_toYaml_String` | `fromYaml? (toYaml s) = .ok s` — String round-trips | Low |
| `fromYaml_toYaml_Nat` | `fromYaml? (toYaml n) = .ok n` — Nat round-trips | Low |
| `fromYaml_toYaml_Array` | `[FromYaml α] [ToYaml α] → fromYaml? (toYaml arr) = .ok arr` — lifts element round-trip to arrays | Medium |
| `fromYaml_toYaml_Option` | `fromYaml? (toYaml (some x)) = .ok (some x)` and `fromYaml? (toYaml none) = .ok none` | Low |
| `fromYaml_resolve_bridge` | The default `FromYaml` instance via `FromYamlType` + `resolve` agrees with direct `FromYaml` instances | Medium |

Estimated effort: 1 session.

#### Phase S3: Struct Helpers & Deriving (~430 lines)

Port `Schema/Struct.lean` and `Deriving.lean`. The struct helpers are simple mapping operations; the deriving macro is metaprogramming.

**Module: `Lean4Yaml/Schema/Struct.lean`**

```
getMapping       — YamlValue → Except String (Array (YamlValue × YamlValue))
findField        — pairs → fieldName → Option YamlValue
getField         — [FromYaml α] → pairs → fieldName → Except String α
getFieldOpt      — [FromYaml α] → pairs → fieldName → Except String (Option α)
mkMapping        — List (String × YamlValue) → YamlValue
addField         — [ToYaml α] → acc → name → value → acc'
addFieldOpt      — [ToYaml α] → acc → name → Option value → acc'
```

**Module: `Lean4Yaml/Schema/Deriving.lean`**

Auto-generate `FromYaml`/`ToYaml` instances for structures via Lean metaprogramming (`deriving` handler).

**Proof targets:**

| Theorem | Statement | Difficulty |
|---|---|---|
| `findField_mkMapping` | `findField (mkMapping [..., (k, v), ...]).pairs k = some v` — fields round-trip through serialization | Medium |
| `getField_addField` | For each field added with `addField`, `getField` recovers it | Medium |
| `getFieldOpt_none` | `getFieldOpt pairs "missing" = .ok none` for absent fields | Low |
| `mkMapping_preserves_order` | `(mkMapping pairs).pairs.map (·.1.content) = pairs.map (·.1)` | Low |

Deriving macro proofs are out of scope — macro-generated code is validated empirically by the type system at instantiation time.

Estimated effort: 1 session for struct helpers, 1 session for deriving port.

#### Phase S4: Emitter (~210 lines)

Port the YAML emitter (`YamlValue → String`). Together with `ToYaml`, this completes the full pipeline: `α → YamlValue → String`.

**Proof target (Phase 5 prerequisite):**

| Theorem | Statement | Difficulty |
|---|---|---|
| `emit_produces_valid_yaml` | `∀ v, parse (emit v) = .ok v'` where `v'` is structurally equivalent to `v` | Hard (requires parser proofs) |

#### Phase S5: End-to-End Round-Trip

Compose parser + schema + emitter proofs into:

```lean
theorem roundtrip :
  ∀ (v : YamlValue),
    parseSingle (emit v) = .ok v' →
    resolve v' = resolve v
```

This is the verified-correctness analog of lean4-yaml's empirical round-trip tests. It requires parser soundness proofs (Phase 3 of the main verification roadmap) and is the long-term goal.

### Design Principles for the Verified Schema Layer

The schema layer follows the same architectural principles documented in ANALYSIS.md §6:

1. **Make implicit state explicit.** Resolution precedence (null → bool → int → float → str) is encoded as a match chain — each arm is a provable case. No hidden priority tables or mutable state.

2. **No exceptions for decisions.** `FromYaml` returns `Except String α`, not `IO α`. Schema resolution errors are values, not exceptions. The `resolve` function is total — every `YamlValue` produces a `YamlType`.

3. **Pure functions on inductive types.** Every schema function (`resolve`, `resolveImplicit`, `resolveScalar`, `isNull`, `isBool`, `isInt`, `isFloat`) is a pure function with no IO, no state, no parser dependency. This makes them kernel-reducible and directly provable, unlike the parser layer which is blocked by lean4-parser's `partial def`.

4. **Compatible types enable sharing.** The `YamlValue` type is identical between projects. The schema layer can be developed and proved correct independently, then composed with parser proofs when they become available.

5. **Proofs follow the same layered strategy.** Layer 1 (pure function properties) → Layer 2 (typeclass laws) → Layer 3 (round-trip composition). Each layer is independently valuable: Layer 1 catches implementation bugs at compile time, Layer 2 ensures typeclass coherence, Layer 3 provides the full end-to-end guarantee.

### Estimated Effort

| Phase | Lines | Sessions | Proofs |
|---|---|---|---|
| S1: Core types & resolution | ~300 | 2 | ~9 theorems |
| S2: FromToYaml typeclasses | ~200 | 1 | ~7 theorems |
| S3: Struct helpers & deriving | ~430 | 2 | ~4 theorems |
| S4: Emitter | ~210 | 1 | ~1 theorem |
| S5: Round-trip composition | ~50 | 2+ | ~1 theorem (hard) |
| **Total** | **~1190** | **8+** | **~22 theorems** |

The schema layer is **~1190 lines** of Lean code plus ~22 formal theorems. This is significantly less than the parser (~2500 lines) and has far better proof tractability since everything is pure functions on inductive types with no parser combinator dependency.

---

## Building

```sh
lake build
```

## Running Tests

```sh
# yaml-test-suite coverage (416 unique test cases from 351 files)
lake build suiterunner tryparse && lake exe suiterunner --html docs/

# Internal test suites (581 hand-written tests across 10 suites)
lake exe tests              # Unit tests (17)
lake exe parsetest           # Parser integration (25)
lake exe quotedfolding       # Quoted folding (34)
lake exe anchortests         # Anchor/alias tests (33)
lake exe tagtests            # Tag tests (44)
lake exe explicitkeytests    # Explicit key tests (66)
lake exe flowtests           # Flow completeness tests (88)
lake exe verification        # Layer 1 verification (138)
lake exe stringlemmas        # String lemma tests (129)
lake exe demo                # Demo examples (7)

# yaml-test-suite by stage (cumulative: each stage includes all prior stages)
# Stages: scalar(82) → flow(+46=128) → block(+109=237) → document(+24=261) → advanced(+81=342)
# The --html mode runs all 416 unique tests once (non-cumulative) and generates per-stage pages
lake build suiterunner tryparse && lake exe suiterunner scalar
```

## YAML Spec Coverage

Every parser module references the relevant YAML 1.2.2 specification
sections with full URLs, e.g.:

```
§6.1: https://yaml.org/spec/1.2.2/#61-indentation-spaces
§8.2.1: https://yaml.org/spec/1.2.2/#821-block-sequences
```

## License

Apache 2.0
