# lean4-yaml-verified

A YAML 1.2.2 parser in Lean 4 with the goal of **verified correctness** — proofs that the parser conforms to the YAML specification and the [yaml-test-suite](https://github.com/yaml/yaml-test-suite).

## Architecture

```
Lean4Yaml/
├── Types.lean             # YamlValue AST (shared with lean4-yaml)
├── Stream.lean            # Position-aware YamlStream with line/col tracking
├── Grammar.lean           # Formal YAML grammar as Lean Props
├── Parser/
│   ├── Combinators.lean   # Character classification & basic parsers
│   ├── Scalar.lean        # Plain, quoted, and block scalar parsers
│   ├── Flow.lean          # Flow sequences [...] and mappings {...}
│   ├── Block.lean         # Block sequences (- item) and mappings (key: value)
│   └── Document.lean      # Document markers, directives, multi-document streams
└── Proofs/
    ├── Termination.lean   # Termination proofs for recursive parsers
    ├── Soundness.lean     # Parser produces only valid YAML
    ├── RoundTrip.lean     # Parse ∘ emit = id (planned)
    └── TestSuite.lean     # yaml-test-suite as compile-time checks
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

## Building

```sh
lake build
```

## Running Tests

```sh
lake build tests
lake env lean --run Tests/Main.lean
```

## Running Demo

```sh
lake build demo
lake env lean --run Demo.lean
```

## Status

| Component | Status |
|-----------|--------|
| AST Types | ✅ Complete |
| Stream | ✅ Complete |
| Grammar Spec | ✅ Scaffold |
| Scalar Parsers | 🔄 Implementation |
| Flow Parsers | 🔄 Implementation |
| Block Parsers | 🔄 Implementation |
| Document Parser | 🔄 Implementation |
| Termination Proofs | ⬜ Planned |
| Soundness Proofs | ⬜ Planned |
| Round-Trip Proofs | ⬜ Planned |
| Test Suite | ⬜ Planned |

## License

Apache 2.0
