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
- `Tests/SuiteRunner/Meta.lean` (280 lines) — line-based meta-parser for the yaml-test-suite file format (bootstrapping: can't use our own YAML parser to parse the test suite's YAML metadata)
- `Tests/SuiteRunner/Main.lean` (~200 lines) — test runner with staged execution, progress output, and result reporting
- `Tests/TryParse.lean` — minimal binary for subprocess-based parse testing with `timeout(1)` for infinite loop protection
- Test classification by tags into stages: scalar → flow → block → document → advanced → error
- Cumulative stage execution (e.g., `flow` stage runs both scalar and flow tests)

**Scalar stage results (82 tests):**

| Result | Count |
|--------|-------|
| ✅ Passed | 31 |
| ❌ Failed | 14 |
| ○ Skipped | 37 |

**Failure categories identified:**
- **3 timeouts** (4CQQ, 4ZYM, 5GBF) — infinite loops in parser, root cause not yet investigated
- **8 escape/multi-line failures** (3RLN, 7A4E, 9MQT, DE56, NP9H, PRH3, TL85, 2G84) — missing escape sequence handling (`\\`, tab in quotes, multi-line quoted scalars)
- **1 tag failure** (FBC9) — `!` tag indicator not handled
- **1 comment failure** (W42U) — `#` after `- ` not recognized as comment
- **1 empty line failure** (NB6Z) — empty line in scalar context

**Key bugs found and fixed during Phase 2:**
1. **Plain scalar consuming flow indicators** — `anyToken` in `collectPlain` consumed `,`, `]`, `}` before the check could reject them. Fixed with `lookAhead anyToken` (peek-before-consume pattern).
2. **Block mapping key consuming `:`** — same peek-before-consume fix applied to `plainMappingKey`.
3. **Missing indentation consumption** — block parsers didn't consume leading whitespace after line breaks before checking column position. Fixed by adding `skipHWhitespace` before `currentCol` checks in `blockSequenceItems`, `blockMappingEntries`, and `blockValue`.

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

Immediate priorities for continuing Phase 2d:

1. **Investigate infinite loops** — analyze test cases 4CQQ, 4ZYM, 5GBF to find which parser combinators fail to make progress
2. **Fix escape sequence handling** — implement `\\`, `\t`, `\n`, `\"` etc. in double-quoted scalar parser
3. **Fix multi-line quoted scalars** — handle line folding in double/single-quoted scalars
4. **Add comment handling** — recognize `#` as comment start after whitespace
5. **Run remaining stages** — `flow`, `block`, `document`, `advanced`, `error`
6. **Iterate on failures** — fix parser bugs exposed by each stage, re-run until pass rate stabilizes

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
