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
│   ├── Soundness.lean       # Parser produces only valid YAML
│   ├── RoundTrip.lean       # Parse ∘ emit = id (planned)
│   └── TestSuite.lean       # yaml-test-suite as compile-time checks (blocked)
└── Tests/
    ├── Main.lean            # Unit test suite (17 tests)
    ├── ParseTest.lean       # Parser integration tests (24+ tests)
    ├── TryParse.lean        # Single-file parse binary (subprocess isolation)
    ├── CheckStringPos.lean  # String position utility tests
    └── SuiteRunner/
        ├── Meta.lean        # Line-based yaml-test-suite file parser
        └── Main.lean        # Programmatic yaml-test-suite runner
```

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
| `Scalar.lean` | ~524 | Plain, double-quoted, single-quoted, block scalar parsers |
| `Flow.lean` | ~205 | Flow sequences `[...]` and mappings `{...}` (mutual recursion) |
| `Block.lean` | ~352 | Block sequences and mappings with indentation tracking |
| `Document.lean` | ~230 | Document markers `---`/`...`, directives, multi-document streams |

**Total: ~2286 lines, 217 build jobs, 0 errors.**

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
- **0 infinite loops** — position-advancement guard in `yamlStream` eliminates all timeouts by detecting when `document` consumes zero input and forcing progress
- **Advanced stage near-zero** — anchors, aliases, tags, complex keys not implemented
- **Meta parser bug fixed** — `---` inside yaml block scalar content was being treated as a test file separator, creating 103 phantom test cases with empty yaml (fixed by checking block scalar state before separator detection)

**Key bugs found and fixed during Phase 2:**
1. **Plain scalar consuming flow indicators** — `anyToken` in `collectPlain` consumed `,`, `]`, `}` before the check could reject them. Fixed with `lookAhead anyToken` (peek-before-consume pattern).
2. **Block mapping key consuming `:`** — same peek-before-consume fix applied to `plainMappingKey`.
3. **Missing indentation consumption** — block parsers didn't consume leading whitespace after line breaks before checking column position. Fixed by adding `skipHWhitespace` before `currentCol` checks.
4. **Meta parser `---` handling** — `processLine` checked for `---` separator before checking if inside a yaml block scalar, truncating test yaml content. Fixed by reordering to check block scalar state first.

**Validation work (ANALYSIS.md §2.A):**
Three-valued error recovery combinators (`validateNoWrongIndentSeq`, `validateNoWrongIndentMap`, `hasSequenceIndicator`) are **active** in `blockSequenceItems` and `blockMappingEntries`. They detect wrongly-indented structural indicators (e.g., `- ` at col 1 when `seqIndent = 0`) and raise validation errors. Impact: error rejection improved from 24% to 54% (+22 tests), overall suite from 164→192 passed (39.4%→46.2%). Note: these validators still use `throwUnexpected`, which lean4-parser's `<|>` can swallow in some contexts — the `DispatchResult.invalid` path is not yet propagated through all callers.

**Infinite loop elimination:**
Added position-advancement guard in `yamlStream` (`Document.lean`): saves `currentPos` before parsing each document, compares after — if no progress, consumes one character and reports a descriptive error. Eliminated all 36 timeout cases across 9 root cause categories (anchors, tags, quoted scalar folding, comments, explicit keys, same-indent sequences, tabs, empty keys, flow implicit mappings).

### Remaining Phases (Future)

#### Phase 3: Termination Proofs

Replace `partial def` with total functions by providing well-founded relations on stream position.

- [ ] **3a.** Prove `next_decreasing`: after `next?`, remaining input strictly decreases
- [ ] **3b.** Prove scalar parsers terminate (each iteration consumes ≥1 char)
- [ ] **3c.** Prove flow collection parsers terminate (mutual recursion with strictly decreasing input)
- [ ] **3d.** Prove block collection parsers terminate (decreasing input + strictly increasing indentation)
- [ ] **3e.** Remove all `partial` annotations

#### Phase 4: Soundness Proofs

Prove that the parser only produces values conforming to `Grammar.lean`.

- [ ] **4a.** Scalar soundness
- [ ] **4b.** Indentation soundness (`consumeIndent n` prevents `skipToNextLine`-class bugs)
- [ ] **4c.** Collection soundness
- [ ] **4d.** Document soundness → `parse_sound` theorem
- [ ] **4e.** Convert `axiom`s in `Soundness.lean` to `theorem`s

#### Phase 5: yaml-test-suite Proofs

Encode yaml-test-suite test cases as compile-time `#guard` / `theorem` checks (requires Phase 3).

#### Phase 6: Round-Trip Proofs

Prove `parse ∘ emit = id` for a canonical YAML subset.

#### Phase 7: Integration with lean4-yaml

Share the verified implementation with the existing lean4-yaml ecosystem.

## Next Steps

Immediate priorities for continuing Phase 2:

1. ~~**Three-valued error recovery ([ANALYSIS.md](ANALYSIS.md) §2.A)**~~ — ✅ Done. Validation combinators (`validateNoWrongIndentSeq`, `validateNoWrongIndentMap`, `hasSequenceIndicator`) built in `Combinators.lean` and active in `Block.lean`. Error rejection: 24%→38%.
2. ~~**Refactor `blockValue` dispatch to `DispatchResult`**~~ — ✅ Done. Defined `DispatchResult` inductive type (`matched`/`noMatch`/`invalid`) in `Combinators.lean`. Extracted shared `dispatchByChar` in `Block.lean`, eliminating duplicated match statements in `blockValue`/`blockValueSameLine`. See [ANALYSIS.md](ANALYSIS.md) §2.A.
3. ~~**Add multi-line plain scalar support**~~ — ✅ Done. Defined `ContinuationCheck` inductive type in `Combinators.lean` with `checkContinuation` pure `lookAhead` probe. Replaced single-line parser with multi-line `plainScalarContent` in `Scalar.lean`. Line folding per YAML §6.5. See [ANALYSIS.md](ANALYSIS.md) §2.B.
4. ~~**Re-enable validation combinators**~~ — ✅ Done. Uncommented `validateNoWrongIndentSeq` / `validateNoWrongIndentMap` in `Block.lean`. Overall suite: 164→177 passed (39.4%→42.5%).
5. ~~**Eliminate infinite loops**~~ — ✅ Done. Position-advancement guard in `yamlStream` detects when `document` consumes zero input, forces progress. All 36 timeouts (9 root cause categories) eliminated. Suite: 177→192 passed (42.5%→46.2%), error rejection: 38%→54%.
6. **Fix multi-line quoted scalars** — handle line folding in double/single-quoted scalars
7. **Add anchor/alias support** — enables the advanced stage (currently 1/81)
8. **Iterate** — fix failures exposed by each stage, target 60%+ overall pass rate

## Building

```sh
lake build
```

## Running Tests

```sh
# Unit tests
lake build tests && .lake/build/bin/tests

# Parser integration tests
lake build parsetest && .lake/build/bin/parsetest

# Demo examples
lake build demo && .lake/build/bin/demo

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
