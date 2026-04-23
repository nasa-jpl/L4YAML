# lean4-yaml-verified (L4YAML)

A **machine-verified** YAML 1.2.2 parser, schema layer, and dumper, written in
[Lean 4](https://lean-lang.org) with FFI adapters for C, Python, and Rust.
Conformance to the [YAML 1.2.2 specification](https://yaml.org/spec/1.2.2/) and
the [yaml-test-suite](https://github.com/yaml/yaml-test-suite) is established
by mathematical proof, not by testing alone.

- **License:** Apache-2.0 — see [LICENSE](LICENSE)
- **Toolchain:** `leanprover/lean4` (see [lean-toolchain](lean-toolchain))
- **Scope:** parser, emitter, style-aware dumper, Core Schema (§10.3), safe-parsing limits, typeclass-driven (de)serialization

## What it is

L4YAML is a YAML implementation whose core is implemented *and verified* in
Lean 4. Everything other languages consume — the C ABI, the Python package,
the Rust crate — is a thin adapter over the same verified Lean kernel, so the
proofs apply uniformly across every binding.

The library is composed of four layers, each pure, total, and kernel-reducible:

| Layer | Source | Role |
|---|---|---|
| Scanner | [L4YAML/Scanner.lean](L4YAML/Scanner.lean) | Characters → tokens (YAML 1.2.2 L-layer) |
| Token parser | [L4YAML/TokenParser.lean](L4YAML/TokenParser.lean) | Tokens → `YamlValue` AST (S-layer) |
| Schema | [L4YAML/Schema.lean](L4YAML/Schema.lean), [L4YAML/Schema/](L4YAML/Schema/) | Implicit typing + `FromYaml`/`ToYaml` |
| Dumper | [L4YAML/Dump.lean](L4YAML/Dump.lean) | `YamlValue` + `DumpConfig` → YAML text |

Grammar and proofs live in [L4YAML/Grammar.lean](L4YAML/Grammar.lean) and
[L4YAML/Proofs/](L4YAML/Proofs/).

## Unique features

### 1. Machine-checked verification

Every function in the core library is a total `def` — **no `partial def`, no
`axiom`, no `sorry`** in the verified core. The proof development covers:

- **Soundness of parsing** — if `parseYaml` accepts an input, the output is a
  structurally valid YAML data model ([Proofs/Soundness.lean](L4YAML/Proofs/Soundness.lean),
  [Proofs/ParserSoundness.lean](L4YAML/Proofs/ParserSoundness.lean)).
- **Parser completeness** — every well-formed token stream under the
  formalized grammar has a successful parse
  ([Proofs/Completeness.lean](L4YAML/Proofs/Completeness.lean),
  [Proofs/ParserCompleteness.lean](L4YAML/Proofs/ParserCompleteness.lean)).
- **Pipeline composition** — the scanner → token parser composition is
  correct ([Proofs/Composition.lean](L4YAML/Proofs/Composition.lean)).
- **Round-trip** — `parse ∘ emit` is the identity on well-formed values
  ([Proofs/RoundTrip.lean](L4YAML/Proofs/RoundTrip.lean),
  [Proofs/DumpRoundTrip.lean](L4YAML/Proofs/DumpRoundTrip.lean)).
- **Scanner invariants** — indentation tracking, simple-key detection, flow
  collection balance, document boundaries
  ([Proofs/ScannerIndent.lean](L4YAML/Proofs/ScannerIndent.lean),
  [Proofs/ScannerSimpleKey.lean](L4YAML/Proofs/ScannerSimpleKey.lean),
  [Proofs/ScannerFlowCollection.lean](L4YAML/Proofs/ScannerFlowCollection.lean),
  [Proofs/ScannerDocument.lean](L4YAML/Proofs/ScannerDocument.lean)).
- **Anchor/alias well-formedness** — every resolved alias refers to a
  previously defined anchor ([Proofs/ParserAnchorProofs.lean](L4YAML/Proofs/ParserAnchorProofs.lean),
  [Proofs/ParserNodeProofs.lean](L4YAML/Proofs/ParserNodeProofs.lean)).
- **Acceptance strictness** — accepted inputs lie in the formalized YAML
  surface language `InYamlLanguage`
  ([Proofs/ScannerCorrectness.lean](L4YAML/Proofs/ScannerCorrectness.lean);
  design note in [docs.internal/README-historical.md](docs.internal/README-historical.md)).
- **Schema resolution** — the Core Schema resolver respects the §10.3
  precedence (null → bool → int → float → str)
  ([Proofs/Schema/SchemaResolution.lean](L4YAML/Proofs/Schema/SchemaResolution.lean),
  [Proofs/Schema/SchemaDump.lean](L4YAML/Proofs/Schema/SchemaDump.lean)).
- **Character-class correspondence** — every YAML character predicate in the
  scanner matches its `Grammar.lean` counterpart
  ([Proofs/Foundation/CharClass.lean](L4YAML/Proofs/Foundation/CharClass.lean)).

**Work in progress.** Two converse theorems round out the correctness picture:

- *Universal round-trip* — for every grammable `YamlValue v`, re-parsing
  `emit v` returns a content-equivalent value
  ([VERSION-0.4.7.md](VERSION-0.4.7.md)).
- *Grammar completeness* — every string in `InYamlLanguage` parses
  successfully, closing the biconditional with acceptance strictness
  ([VERSION-0.4.8.md](VERSION-0.4.8.md)).

Compile-time `#guard` tests in [Tests/](Tests/) — including auto-generated
guards from the yaml-test-suite — back every proof with a kernel-evaluable
regression check.

### 2. Lean core + FFI adapters for C, Python, and Rust

The verified Lean code is the single source of truth; language bindings are
thin shims that preserve the security and correctness guarantees:

- **C ABI** — [ffi/l4yaml.h](ffi/l4yaml.h), [ffi/l4yaml_shim.c](ffi/l4yaml_shim.c).
  Opaque handles, deterministic failure modes, optional
  fixed-size mimalloc pool for memory-budgeted environments (DO-178C, ARINC 653).
  See [C_PYTHON_RUST_APIs.md](C_PYTHON_RUST_APIs.md) for the full API
  surface and pool-allocation design.
- **Python** — [python/](python/), package `l4yaml`. Drop-in safe parser
  with `PyYAML`-compatible surface where it makes sense.
- **Rust** — [rust/](rust/), crates `l4yaml-sys` (raw bindings) and
  `l4yaml` (safe high-level API).

### 3. Schema layer

The Schema layer ([L4YAML/Schema.lean](L4YAML/Schema.lean),
[L4YAML/Schema/](L4YAML/Schema/)) provides:

- **YAML 1.2.2 Core Schema (§10.3)** — complete implicit resolution of
  `null`, `bool`, `int`, `float`, `str` with the specified precedence.
- **Failsafe (§10.1) and JSON (§10.2) schemas** — implicit resolution is
  supported; broader §10.2 coverage is on the roadmap.
- **`FromYaml` / `ToYaml` typeclasses** with instances for standard Lean
  types ([L4YAML/Schema/FromToYaml.lean](L4YAML/Schema/FromToYaml.lean)).
- **`deriving FromYaml, ToYaml`** macros for record and inductive types
  ([L4YAML/Schema/Deriving.lean](L4YAML/Schema/Deriving.lean)).
- **Typed parse API** — `parseAs`, `toYaml`, `parseTyped` in
  [L4YAML/Schema/Api.lean](L4YAML/Schema/Api.lean).

JSON Schema (the [json-schema.org](https://json-schema.org/) validation
vocabulary) is **not** supported in the current release — only the YAML 1.2.2
built-in schemas. Validation-vocabulary support is not currently on the
roadmap; open an issue if this is a blocker for your use case.

### 4. Safe parsing restrictions

The verified parser rejects adversarial and ambiguous input at well-defined
boundaries. All limits are configurable via `ParserLimits`
([L4YAML/Limits.lean](L4YAML/Limits.lean)) and documented in
[LIMITS.md](LIMITS.md).

| Threat | Limit | Default |
|---|---|---|
| Billion-laughs alias expansion | `maxResolvedNodes` | 100,000 |
| Excessive alias depth / count | `maxAliasDepth`, `maxAliasExpansions` | 50 / 10,000 |
| Deep nesting | `maxDepth` | 100 |
| Oversized scalars | `maxScalarBytes` | 10 MB |
| Large collections | `maxSequenceLength`, `maxMappingSize` | 100,000 |
| Too many documents | `maxDocuments` | 100 |
| Input size | `maxInputBytes` | 100 MB |
| Language-specific tags (`!!python/*`, `!!ruby/*`, …) | `rejectLanguageTags` | `true` |
| Non-core-schema tags | `TagPolicy.coreSchemaOnly` | default |
| Custom `%TAG` handles | `rejectCustomHandles` | `false` |

Four presets are provided: `ParserLimits.strict` (web APIs),
default `{}` (general untrusted input), `ParserLimits.permissive` (trusted
internal data), and `ParserLimits.unlimited` (testing only).

### 5. Configurable style-aware dumper

[`L4YAML.Dump.dump`](L4YAML/Dump.lean) turns a `YamlValue` (plus optional
per-document comments) back into YAML text, with control over:

- **Scalar style** — `plain`, `doubleQuoted`, `singleQuoted`, or `auto`
  (chosen from content analysis). Literal and folded block scalars are
  preserved when the AST carries the annotation.
- **Collection style** — `block`, `flow`, or `auto` (honors per-node
  `CollectionStyle` annotations from the parser).
- **Indentation width**, **line-folding behavior**, and **key ordering**.
- **Comment preservation** for documents parsed with comment-aware APIs.

Every dump configuration is deterministic and participates in the round-trip
proofs.

## Quick start

### Lean

```lean
import L4YAML

-- Safe mode (recommended for untrusted input):
let result := parseYamlSafe input                -- default limits
let result := parseYamlSafe input .strict        -- strict limits
let result := parseYamlSingleSafe input          -- single-document variant

-- Typed parse with a derived FromYaml instance:
structure AppConfig where
  host : String
  port : Nat
  deriving Repr, L4YAML.Schema.FromYaml, L4YAML.Schema.ToYaml

def load (s : String) : Except L4YAML.YamlError AppConfig :=
  L4YAML.parseAs AppConfig s

-- Dump with custom style:
let text := L4YAML.Dump.dump value { defaultStyle := .block, indent := 2 }
```

### C

```c
#include "l4yaml.h"

l4yaml_initialize();                             // once per process
l4yaml_result_t r = l4yaml_parse(input, L4YAML_LIMITS_STRICT);
if (l4yaml_result_ok(r)) {
    l4yaml_docs_t docs = l4yaml_result_docs(r);
    // ... walk docs ...
    l4yaml_free(docs);
}
l4yaml_free(r);
```

### Python

```python
import l4yaml

config = l4yaml.safe_load(yaml_text)             # default limits
config = l4yaml.safe_load(yaml_text, limits=l4yaml.Limits.STRICT)
text   = l4yaml.dump(value, style="block", indent=2)
```

### Rust

```rust
use l4yaml::{parse_safe, Limits, Dump};

let docs = parse_safe(input, Limits::Strict)?;
let text = Dump::new().style_block().indent(2).render(&value);
```

## Building

```sh
lake build
```

This builds the Lean library, the proof modules, the compile-time guards, and
every test executable registered in [lakefile.toml](lakefile.toml).

To build and run the FFI adapters:

```sh
# C library + header
cmake -B ffi/build ffi && cmake --build ffi/build

# Python package (editable install)
python -m pip install -e python

# Rust crates
cargo build --manifest-path rust/Cargo.toml
```

## Running tests

```sh
# Full yaml-test-suite coverage (HTML report)
lake build suiterunner tryparse && lake exe suiterunner --html docs/

# Per-stage runs
lake exe suiterunner scalar      # scalar stage only
lake exe suiterunner flow        # cumulative through flow
lake exe suiterunner block       # cumulative through block
lake exe suiterunner document
lake exe suiterunner advanced

# Internal test suites
lake exe tests                   # unit tests
lake exe specexamples            # YAML 1.2.2 spec examples (§2–§10)
lake exe scannerspecexamples     # same examples via tokenized pipeline
lake exe validationtests         # structural validation
lake exe dumproundtrip           # dump round-trip
lake exe schemadump              # Schema ↔ Dump integration
```

The full list of executables is in [lakefile.toml](lakefile.toml).

### Querying test results

`suiterunner --html` also writes structured results to
[docs/reports/coverage-summary.json](docs/reports/coverage-summary.json)
(yaml-test-suite stage breakdown + every verified suite's per-test outcome,
category, and error message). The `queryresults` CLI reads that file so the
dashboard data is scriptable without parsing HTML:

```sh
# List every failing verified test with its error message
lake exe queryresults ./docs/reports/coverage-summary.json verified-failures

# Markdown summary (yaml-test-suite + verified suites)
lake exe queryresults ./docs/reports/coverage-summary.json summary

# Unexpected passes in the yaml-test-suite, grouped by stage
lake exe queryresults ./docs/reports/coverage-summary.json ups --by-stage

# Filter yaml-test-suite entries by id prefix
lake exe queryresults ./docs/reports/coverage-summary.json filter --id Y79Y

# Diff two runs (outcome changes, additions, removals)
lake exe queryresults diff before.json after.json
```

## Project layout

```
L4YAML/              Verified core library (scanner, parser, schema, dump, proofs)
  Grammar.lean       Formal YAML 1.2.2 grammar
  Proofs/            Machine-checked theorems
  Schema/            Typeclasses, deriving macros, typed API
  Surface/           Surface-syntax grammar (acceptance strictness)
Tests/               Runtime tests and compile-time #guard suites
examples/            YAML 1.2.2 specification examples (§2–§10)
yaml-test-suite/     Upstream yaml-test-suite (submodule)
ffi/                 C ABI header, shim, and test driver
python/              Python package (`l4yaml`)
rust/                Rust workspace (`l4yaml`, `l4yaml-sys`)
docs/                Generated documentation (Verso, PDF, coverage reports)
```

## Further reading

- [LIMITS.md](LIMITS.md) — threat model and limit design
- [C_PYTHON_RUST_APIs.md](C_PYTHON_RUST_APIs.md) — FFI design, memory model,
  flight-software integration
- [docs/](docs/) — generated API documentation and coverage reports
- [docs.internal/README-historical.md](docs.internal/README-historical.md) — full development log, phase-by-phase proof history, and design retrospectives

## Contributing

Issues and pull requests are welcome. Please open an issue before starting
substantial work so we can discuss scope and proof strategy.

## License

Apache-2.0. See [LICENSE](LICENSE).
