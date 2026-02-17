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

1. **Runtime tests** (427 tests across 8 suites) — empirical validation that properties hold. Every `theorem` target starts life as a runtime `check` test.
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

This is critical because lean4-parser's error model has **no committed/fatal error distinction** — all `Result.error` values are caught unconditionally by `<|>`, `option?`, and `first`. Using `throwUnexpected` for input validation is unreliable since any enclosing combinator silently swallows it. The `DispatchResult` encoding works *above* the combinator level, making three-valued semantics structural and proof-friendly.

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
| `Flow.lean` | ~205 | Flow sequences `[...]` and mappings `{...}` (mutual recursion) |
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
Three-valued error recovery combinators (`validateNoWrongIndentSeq`, `validateNoWrongIndentMap`, `hasSequenceIndicator`) are **active** in `blockSequenceItems` and `blockMappingEntries`. They detect wrongly-indented structural indicators (e.g., `- ` at col 1 when `seqIndent = 0`) and raise validation errors. Impact: error rejection improved from 24% to 54% (+22 tests), overall suite from 164→192 passed (39.4%→46.2%). Note: these validators still use `throwUnexpected`, which lean4-parser's `<|>` can swallow in some contexts — the `DispatchResult.invalid` path is not yet propagated through all callers.

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

### Current: Address 85 Failures + 94 Unexpected Passes

Analysis scripts: `python3 tests/analyze_coverage.py` (summary) and `python3 tests/analyze_coverage_deep.py` (detailed root causes).

Current: **192/416 correct (46.2%)**. Projected after all steps below: **~310/416 (~74.5%)**.

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

#### Step 10: Strict validation (error rejection) — +74 unexpected passes

**Impact: 0 failures, up to 74 unexpected passes resolved.** The parser is too permissive — it accepts invalid YAML that should be rejected. This should be done incrementally:

| Sub-step | Category | Count | What to validate |
|----------|----------|-------|------------------|
| **10a** | Flow structure | 13 | Missing commas, extra brackets, unterminated flow collections |
| **10b** | Mapping structure | 12 | Invalid key-value structure, duplicate implicit keys |
| **10c** | Quoted scalars | 10 | Unclosed quotes, invalid escape sequences, multiline quoted keys |
| **10d** | Indentation | 9 | Wrong indentation in sequences, mappings, block scalars |
| **10e** | Anchors/aliases | 7 | Double anchors, invalid anchor positions, undefined aliases |
| **10f** | Directives | 7 | Invalid `%YAML`, `%TAG`, reserved directives |
| **10g** | Comments | 6 | Invalid comment positions (in flow, after scalars) |
| **10h** | Block scalars | 3 | Invalid block scalar indicators, wrong indentation |
| **10i** | Document markers | 3 | Invalid content after `...`, wrong `---` positions |
| **10j** | Tags/other | 4 | Invalid tag syntax, trailing content |

Approach: Use the existing `DispatchResult.invalid` pattern to propagate validation errors above lean4-parser's `<|>` swallowing. Extend `validateNoWrongIndentSeq`/`validateNoWrongIndentMap` to cover more contexts.

#### Step 11: Remaining edge cases — +23 tests

| Category | Failures | Description |
|----------|----------|-------------|
| Flow edge cases | 9 | Implicit keys in flow, single-pair entries, empty flow collections |
| Empty key handling | 6 | Missing/empty keys in block and flow contexts |
| Escape sequences | 5 | Unicode escapes (`\x`, `\u`, `\U`) in double-quoted scalars |
| Complex keys | 3 | Flow collections as mapping keys (§7.4.2) |

#### Step 12: Iterate toward 60%+ correct rate

After steps 8–11, projected correct rate is ~74.5% (310/416). The remaining ~25% are edge cases in:
- Non-error unexpected passes in block/flow/document stages (20 tests)
- Interactions between features (anchor + tag, explicit-key + tag, etc.)
- YAML 1.3-specific tests (currently skipped, 62 tests)

## Building

```sh
lake build
```

## Running Tests

```sh
# All verified test suites (427 tests across 8 suites)
lake build suiterunner tryparse && lake exe suiterunner --html docs/

# Individual suites (each produces structured VerifiedSuiteResult)
lake exe tests              # Unit tests (17)
lake exe parsetest           # Parser integration (25)
lake exe quotedfolding       # Quoted folding (34)
lake exe anchortests         # Anchor/alias tests (33)
lake exe tagtests            # Tag tests (44)
lake exe verification        # Layer 1 verification (138)
lake exe stringlemmas        # String lemma tests (129)
lake exe demo                # Demo examples (7)

# yaml-test-suite (by stage: scalar, flow, block, document, advanced, error, all)
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
