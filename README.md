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

1. **Runtime tests** (350 tests across 6 suites) — empirical validation that properties hold. Every `theorem` target starts life as a runtime `check` test.
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

| Stage | Tests | Passed | Failed | Skipped | Pass Rate |
|-------|-------|--------|--------|---------|-----------|
| Scalar | 82 | 40 | 14 | 28 | 48.8% |
| + Flow | 128 | 71 | 29 | 28 | 55.5% |
| + Block | 237 | 137 | 62 | 38 | 57.8% |
| + Document | 261 | 151 | 65 | 45 | 57.9% |
| + Advanced | 342 | 152 | 128 | 62 | 44.4% |
| Error | 74 | 40 | 34 | 0 | 54.1% |
| **All unique** | **416** | **192** | **162** | **62** | **46.2%** |

**Per-feature pass rates (non-cumulative):**

| Feature | Tests | Passed | Rate |
|---------|-------|--------|------|
| Scalar | 82 | 40 | 49% |
| Flow | 46 | 31 | 67% |
| Block | 109 | 66 | 61% |
| Document | 24 | 14 | 58% |
| Advanced | 81 | 1 | 1% |
| Error | 74 | 40 | 54% |

**Key findings:**
- **~34 unexpected passes** — parser is still too permissive in some cases, but validation combinators (`validateNoWrongIndentSeq`, `validateNoWrongIndentMap`) now catch wrongly-indented structural indicators, reducing this from ~50
- **0 infinite loops** — `DocumentResult` type in `document` makes parse-progress explicit; `yamlStream` pattern-matches on `parsed`/`endOfStream`/`stalled` instead of comparing positions externally
- **Advanced stage near-zero** — anchors, aliases, tags, complex keys not implemented
- **Meta parser bug fixed** — `---` inside yaml block scalar content was being treated as a test file separator, creating 103 phantom test cases with empty yaml (fixed by checking block scalar state before separator detection)

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

Immediate priorities for continuing Phase 2:

1. ~~**Three-valued error recovery ([ANALYSIS.md](ANALYSIS.md) §2.A)**~~ — ✅ Done. Validation combinators (`validateNoWrongIndentSeq`, `validateNoWrongIndentMap`, `hasSequenceIndicator`) built in `Combinators.lean` and active in `Block.lean`. Error rejection: 24%→38%.
2. ~~**Refactor `blockValue` dispatch to `DispatchResult`**~~ — ✅ Done. Defined `DispatchResult` inductive type (`matched`/`noMatch`/`invalid`) in `Combinators.lean`. Extracted shared `dispatchByChar` in `Block.lean`, eliminating duplicated match statements in `blockValue`/`blockValueSameLine`. See [ANALYSIS.md](ANALYSIS.md) §2.A.
3. ~~**Add multi-line plain scalar support**~~ — ✅ Done. Defined `ContinuationCheck` inductive type in `Combinators.lean` with `checkContinuation` pure `lookAhead` probe. Replaced single-line parser with multi-line `plainScalarContent` in `Scalar.lean`. Line folding per YAML §6.5. See [ANALYSIS.md](ANALYSIS.md) §2.B.
4. ~~**Re-enable validation combinators**~~ — ✅ Done. Uncommented `validateNoWrongIndentSeq` / `validateNoWrongIndentMap` in `Block.lean`. Overall suite: 164→177 passed (39.4%→42.5%).
5. ~~**Eliminate infinite loops**~~ — ✅ Done. Refactored `document` to return `DocumentResult` (`parsed`/`endOfStream`/`stalled`), making parse-progress an explicit result rather than an external position comparison. All 36 timeouts (9 root cause categories) eliminated. Suite: 177→192 passed (42.5%→46.2%), error rejection: 38%→54%. See [ANALYSIS.md](ANALYSIS.md) §5.
6. **Fix multi-line quoted scalars** — analysis identified 5 algorithmic bugs in `foldQuotedNewlines` plus one missing `c-forbidden` check (see [ANALYSIS.md](ANALYSIS.md) §2.F). Two-phase plan:
   - **6a.** ✅ Added `FoldResult` type (`folded`/`forbidden`) and `c-forbidden` detection (YAML §9.1.2 [206]). `foldQuotedNewlines` checks `atDocumentBoundary` at column 0 before whitespace consumption on each continuation line. Both `doubleQuotedScalar` and `singleQuotedScalar` pattern-match on the result.
   - **6b.** ✅ Fixed all 5 algorithmic bugs: (A) removed mandatory `newline` — already consumed by `collectChars`; (B) fixed off-by-one in empty line counting; (C) added trailing whitespace trimming; (D) `skipSpaces`→`skipHWhitespace` for tab handling; (E) added `\` + newline escaped line break in `doubleQuotedScalar`. 33 tests in `Tests/QuotedFolding.lean`.
7. **Add anchor/alias support** — enables the advanced stage (currently 1/81)
8. **Iterate** — fix failures exposed by each stage, target 60%+ overall pass rate

## Building

```sh
lake build
```

## Running Tests

```sh
# All verified test suites (350 tests across 6 suites)
lake build suiterunner && .lake/build/bin/suiterunner --html docs/

# Individual suites (each produces structured VerifiedSuiteResult)
lake build tests && .lake/build/bin/tests              # Unit tests (17)
lake build parsetest && .lake/build/bin/parsetest        # Parser integration (25)
lake build quotedfolding && .lake/build/bin/quotedfolding # Quoted folding (34)
lake build verification && .lake/build/bin/verification  # Layer 1 verification (138)
lake build stringlemmas && .lake/build/bin/stringlemmas  # String lemma tests (129)
lake build demo && .lake/build/bin/demo                  # Demo examples (7)

# yaml-test-suite (by stage: scalar, flow, block, document, advanced, error, all)
lake build suiterunner tryparse && .lake/build/bin/suiterunner scalar
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
