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
| Scanner | [L4YAML/Scanner/](L4YAML/Scanner/Scanner.lean) | Characters → tokens (YAML 1.2.2 L-layer) |
| Token parser | [L4YAML/Parser/TokenParser.lean](L4YAML/Parser/TokenParser.lean) | Tokens → `YamlValue` AST (S-layer) |
| Schema | [L4YAML/Schema/](L4YAML/Schema/Schema.lean) | Implicit typing + `FromYaml`/`ToYaml` |
| Dumper | [L4YAML/Output/Dump.lean](L4YAML/Output/Dump.lean) | `YamlValue` + `DumpConfig` → YAML text |

Grammar and proofs live in [L4YAML/Spec/Grammar.lean](L4YAML/Spec/Grammar.lean) and
[L4YAML/Proofs/](L4YAML/Proofs/).

## Unique features

### 1. Machine-checked verification

Every function in the core library is a total `def` — **no `partial def`, no
`axiom`, no `sorry`** in the verified core. The proof development covers:

- **Soundness of parsing** — if `parseYaml` accepts an input, the output is a
  structurally valid YAML data model ([Proofs/Soundness.lean](L4YAML/Proofs/Soundness.lean),
  [Proofs/Parser/ParserSoundness.lean](L4YAML/Proofs/Parser/ParserSoundness.lean)).
- **Parser completeness** — every well-formed token stream under the
  formalized grammar has a successful parse
  ([Proofs/Completeness.lean](L4YAML/Proofs/Completeness.lean),
  [Proofs/Parser/ParserCompleteness.lean](L4YAML/Proofs/Parser/ParserCompleteness.lean)).
- **Pipeline composition** — the scanner → token parser composition is
  correct ([Proofs/Composition.lean](L4YAML/Proofs/Composition.lean)).
- **Round-trip** — `parse ∘ emit` is the identity on well-formed values
  ([Proofs/RoundTrip/RoundTrip.lean](L4YAML/Proofs/RoundTrip/RoundTrip.lean),
  [Proofs/Output/DumpRoundTrip.lean](L4YAML/Proofs/Output/DumpRoundTrip.lean)).
- **Scanner invariants** — indentation tracking, simple-key detection, flow
  collection balance, document boundaries
  ([Proofs/Scanner/ScannerIndent.lean](L4YAML/Proofs/Scanner/ScannerIndent.lean),
  [Proofs/Scanner/ScannerSimpleKey.lean](L4YAML/Proofs/Scanner/ScannerSimpleKey.lean),
  [Proofs/Scanner/ScannerFlowCollection.lean](L4YAML/Proofs/Scanner/ScannerFlowCollection.lean),
  [Proofs/Scanner/ScannerDocument.lean](L4YAML/Proofs/Scanner/ScannerDocument.lean)).
- **Anchor/alias well-formedness** — every resolved alias refers to a
  previously defined anchor ([Proofs/Parser/ParserAnchorProofs.lean](L4YAML/Proofs/Parser/ParserAnchorProofs.lean),
  [Proofs/Parser/ParserNodeProofs.lean](L4YAML/Proofs/Parser/ParserNodeProofs.lean)).
- **Acceptance strictness** — accepted inputs lie in the formalized YAML
  surface language `InYamlLanguage`
  ([Proofs/Scanner/ScannerCorrectness.lean](L4YAML/Proofs/Scanner/ScannerCorrectness.lean);
  design note in [STRICTNESS.md](STRICTNESS.md)).
- **Schema resolution** — the Core Schema resolver respects the §10.3
  precedence (null → bool → int → float → str)
  ([Proofs/Schema/SchemaResolution.lean](L4YAML/Proofs/Schema/SchemaResolution.lean),
  [Proofs/Schema/SchemaDump.lean](L4YAML/Proofs/Schema/SchemaDump.lean)).
- **Character-class correspondence** — every YAML character predicate in the
  scanner matches its `Grammar.lean` counterpart
  ([Proofs/Foundation/CharClass.lean](L4YAML/Proofs/Foundation/CharClass.lean)).

**Universal round-trip is complete.** The output-side converse now holds and is
`sorry`-free: for every grammable `YamlValue v`, re-parsing `emit v` returns a
single document whose value is content-equivalent to `v`
([`universal_roundtrip`](L4YAML/Proofs/Output/EmitterScannability.lean);
proof-status SSOT: [Blueprint/04-capstones.md](Blueprint/04-capstones.md),
row 6.1). It composes scanner acceptance,
parser acceptance, single-document production, and per-node content fidelity —
closing the round-trip cluster under [Proofs/Output/](L4YAML/Proofs/Output/).

With it, the verified core carries **no `sorry`, no `axiom` declaration, and no
`partial def`** anywhere: the scanner, token parser, schema, dumper, and every
theorem listed above (`#print axioms universal_roundtrip` reports no `sorryAx`).
Beyond Lean's standard `propext` / `Classical.choice` / `Quot.sound`, a number of
finite content-equivalence and character-class facts are discharged by
`native_decide`, which additionally trusts Lean's compiled evaluator.

**Proof discipline.** The `theorem` keyword is reserved for the 25
`@[capstone]`-tagged headline results (whitelist:
[scripts/capstones.txt](scripts/capstones.txt)); every other proof in the
library — roughly 4,975 of them — is spelled `lemma` (macro in
[L4YAML/Init.lean](L4YAML/Init.lean)). The tagged set and each capstone's
axiom profile (18 pure, 7 `native_decide`-backed) are pinned at build time by
`#guard_msgs` in [L4YAML/Capstones.lean](L4YAML/Capstones.lean), and CI
enforces the discipline with `scripts/check-theorem-keyword.sh`,
`scripts/check-import-closure.sh`, and a kernel-accurate
zero-`sorry`/zero-custom-axiom assertion in
[.github/workflows/test-coverage.yml](.github/workflows/test-coverage.yml).
The rulebook is [Blueprint/06-discipline.md](Blueprint/06-discipline.md); the
proof-status SSOT is [Blueprint/04-capstones.md](Blueprint/04-capstones.md).

**Work in progress.** One converse theorem remains open — *grammar
completeness*, that every string in the formalized surface language
`InYamlLanguage` parses successfully, which would close the acceptance
biconditional:

```lean
theorem parse_iff_grammar (input : String) :
    (∃ docs, parseYaml input = .ok docs) ↔ InYamlLanguage input
```

The forward direction (every accepted input lies in `InYamlLanguage`) is already
proven; the converse is future work, tracked in
[GRAMMAR_COMPLETENESS_PLAN.md](GRAMMAR_COMPLETENESS_PLAN.md). It carries no placeholder `sorry` in the
source — it is simply not yet attempted.

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

The Schema layer ([L4YAML/Schema/](L4YAML/Schema/Schema.lean)) provides:

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
([L4YAML/Config/Limits.lean](L4YAML/Config/Limits.lean)) and documented in
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

[`L4YAML.Dump.dump`](L4YAML/Output/Dump.lean) turns a `YamlValue` (plus optional
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

The recommended one-shot driver is the top-level CMake project, which invokes
Lake for the Lean side and compiles the C FFI and (optionally) Rust shim in
the same configuration:

```sh
cmake -B build -S . -DL4YAML_BUILD_RUST=ON
cmake --build build -j
cmake --install build --prefix /path/to/stage   # optional
```

This produces, in order:

1. The Lean library, proof modules, compile-time guards, and every executable
   listed in `L4YAML_EXES` (a superset of `defaultTargets`) — via `lake build`.
2. `libl4yaml.so` + the C example `tryparse_c` — via [ffi/CMakeLists.txt](ffi/CMakeLists.txt).
3. The Rust workspace (`l4yaml-sys`, `l4yaml`) and the `tryparse_rs` example —
   via `cargo build --release --workspace --examples`.

`cmake --install` lays everything into a standard `${prefix}/{bin,lib,include}`
tree plus the compiled Lean module tree under `${prefix}/lib/lean/`. The
installed C and Rust binaries have RPATHs that find `libl4yaml.so` via
`$ORIGIN/../lib` and `libleanshared.so` from the Lean toolchain.

CMake options:

| Option | Default | Effect |
|---|---|---|
| `L4YAML_BUILD_FFI`       | `ON`     | Build `libl4yaml.so` and `tryparse_c` |
| `L4YAML_BUILD_RUST`      | `OFF`    | Also build the Rust shim and `tryparse_rs` |
| `L4YAML_PYTHON_INSTALL`  | `auto`   | Python install mode: `auto`, `ament`, `venv`, `none` |
| `L4YAML_PYTHON_VENV`     | (empty)  | Path to a Python venv (used when mode is `venv`) |
| `L4YAML_ENABLE_TESTS`    | `OFF`    | Register lake-built test runners with CTest |

`L4YAML_PYTHON_INSTALL=auto` picks `ament` when `ament_cmake_python` is on the
CMake prefix path (i.e. a ROS underlay is sourced), `venv` when
`L4YAML_PYTHON_VENV` is set, otherwise `none`. Each mode does:

- **`ament`** — installs the `l4yaml` package at
  `${prefix}/lib/pythonX.Y/site-packages/l4yaml/` via
  `ament_python_install_package`; colcon's `setup.bash` auto-prepends the path
  to `PYTHONPATH`. This is the right mode for a ROS 2 / colcon workflow.
- **`venv`** — runs `pip install -e python` from `${L4YAML_PYTHON_VENV}/bin/python`
  at configure time. The install is editable so source edits take effect
  without re-running cmake.
- **`none`** — cmake doesn't touch Python; install manually (see below).

Prerequisites: `elan` on `PATH` (provides the `lean`/`lake` matching
[lean-toolchain](lean-toolchain)). `L4YAML_BUILD_RUST=ON` additionally
requires `cargo` and `libclang` (for `bindgen`) and network access on the
first build (cargo fetches `bindgen` and `thiserror` from crates.io).

### ROS 2 (colcon) workflow

In a colcon workspace with a ROS underlay sourced (e.g.
`source /opt/ros/jazzy/setup.bash`), `L4YAML_PYTHON_INSTALL=auto` (the
default) detects `ament_cmake_python` and installs the Python package the
ROS-native way. No venv, no pip, no extra flags:

```sh
colcon build --packages-select L4YAML
# Optional flags:
colcon build --packages-select L4YAML --cmake-args -DL4YAML_BUILD_RUST=ON
```

After build, source the workspace overlay and `import l4yaml` works without
further setup.

### venv workflow (non-ROS)

For local development outside ROS, point the same cmake driver at a venv:

```sh
python -m venv .venv && . .venv/bin/activate
cmake -B build -S . -DL4YAML_PYTHON_INSTALL=venv -DL4YAML_PYTHON_VENV=$VIRTUAL_ENV
cmake --build build -j
```

`pip install -e python` runs at configure time; subsequent `.py` edits in
`python/l4yaml/` are picked up by the venv automatically.

### Lean-only build

If you don't need the C/Rust shims and just want to typecheck and build the
Lean library + proofs + tests:

```sh
lake build
```

### Standalone bindings (without the top-level driver)

Each binding can also be built independently:

```sh
# C library + header (libl4yaml.so → ffi/build/, tryparse_c → ffi/build/)
cmake -B ffi/build ffi && cmake --build ffi/build

# Python package (editable install — use a venv).  Or use the
# top-level cmake driver above with -DL4YAML_PYTHON_INSTALL=venv.
python -m venv .venv && . .venv/bin/activate
python -m pip install -e python

# Rust crates — requires libl4yaml.so somewhere; either build via the line
# above and rely on the default ffi/out path, or set L4YAML_LIB_DIR.
cargo build --manifest-path rust/Cargo.toml
```

### LeanCopilot (optional; interactive proof suggestions)

[LeanCopilot](https://github.com/lean-dojo/LeanCopilot) powers tactics like
`suggest_tactics` while developing proofs. It is **off by default** and needed only
for interactive proving — the library, proofs, FFI, and CI do not depend on it, and no
committed file imports it. It is kept optional deliberately: its release tags do not
track Lean 1:1 (the `v4.31.0` tag is built against Lean `v4.32.0-rc1` and pulls
`aesop`/`batteries` one minor ahead of this project's pin), and its prebuilt
`libctranslate2.so.4` needs `GLIBCXX_3.4.30`, which EL9's system `libstdc++` lacks.

The project-local [pixi](https://pixi.sh) env solves both: it puts a new-enough
`libstdc++` on `LD_LIBRARY_PATH` and sets `L4YAML_LEANCOPILOT=1`, the variable that
switches the conditional `require LeanCopilot` in [lakefile.lean](lakefile.lean) on.
Outside the pixi env the variable is unset, so LeanCopilot (and the ahead-of-pin
`aesop`/`batteries`) are never resolved and CI stays clean.

Enable it once:

```sh
pixi install                              # materialise .pixi/envs/default
pixi run -- lake build LeanCopilot        # build LeanCopilot + its native libs
pixi run -- lake exe LeanCopilot/download # fetch models (~11G -> ~/.cache/lean_copilot)
```

Then prove from *inside* the env, so both the variable and `LD_LIBRARY_PATH` are
present:

- **CLI** — `pixi shell`, then `lake lean Path/To/File.lean` (use `lake lean`, not
  `lake env lean`: only the former passes `--load-dynlib` for LeanCopilot's FFI).
- **VS Code** — launch the editor **from inside `pixi shell`** (e.g. `code .`). The
  Lean 4 extension (0.0.237) builds the server environment from `process.env` only — it
  has no `lean4.serverEnv` setting — so `.vscode/settings.json` cannot inject
  `LD_LIBRARY_PATH` or `L4YAML_LEANCOPILOT`; inheriting them from the launching shell is
  what lets `import LeanCopilot` resolve and its native libs load. (For the same reason
  there is no way to pass `-Kleancopilot=on` from the editor — `lean4.serverArgs` are
  forwarded to `lean --server`, not to lake.)

Lake caches the resolved configuration, so the first build or edit after toggling the
variable needs a reconfigure: `lake -R build …`, or just restart the Lean server.

Keep `import LeanCopilot` out of committed proof files (CI has neither the models nor
the env) — import it transiently while proving. Building an L4YAML **executable** that
imports LeanCopilot additionally needs `-Kleancopilot=on` to link CTranslate2
(`pixi run -- lake build -Kleancopilot=on <exe>`); no current exe does.

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

The full list of executables is in [lakefile.lean](lakefile.lean).

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

### L4YAML and the YAML Test Matrix

Submitted [yaml-runtimes PR #39](https://github.com/yaml/yaml-runtimes/pull/39) to
add L4YAML to the official YAML Test Matrix, which was last updated in [v2022-01-17](https://matrix.yaml.info/). At that time, there were 20 processors; this PR would make L4YAML the 21st processor, and the first verified one. The PR is still open as of 2026-07-05.

**Forks while the PR is pending.** So the comparison is available now rather than
only after PR #39 merges, both projects that produce [matrix.yaml.info](https://matrix.yaml.info/)
have been forked to include L4YAML:

- [NicolasRouquette/yaml-runtimes @ `l4yaml`](https://github.com/NicolasRouquette/yaml-runtimes/tree/l4yaml)
  — adds the `l4yaml` processor: a Debian/glibc runtime image (Lean's toolchain
  is not musl-compatible, so it is standalone, not part of `alpine-runtime-all`)
  exposing the `l4yaml-event` and `l4yaml-json` testers, plus the `l4yaml` entry
  in `list.yaml`. This is the PR #39 branch.
- [NicolasRouquette/yaml-test-matrix @ `l4yaml`](https://github.com/NicolasRouquette/yaml-test-matrix/tree/l4yaml)
  — points the matrix at the fork's `list.yaml`, makes the in-container test
  runner POSIX so it runs in the Debian L4YAML image as well as the Alpine ones,
  and adds a self-contained Perl driver image so the matrix can be generated on
  any Docker host without a hand-installed CPAN stack.

**Self-hosted matrix.** This repository's CI regenerates the matrix from the two
forks and publishes it alongside the documentation. On a `v*` version tag (or a
manual workflow run) it packages the testers built for the commit under test
into the runtime image, runs the full yaml-test-suite through L4YAML and the
other processors, and deploys the result to this repo's GitHub Pages at
[`/matrix/`](matrix/index.html) — so the page always reflects the released
L4YAML, not a snapshot. In that comparison L4YAML passes every case: all 308
valid event streams and all 279 JSON oracles match byte-for-byte, and every
invalid input is rejected (event 402/402, JSON 282/282 over the data form).

The matrix step drives Docker (it builds/pulls runtime images and runs them as
sibling containers), so the CI runner's **service account must be in the
`docker` group** — e.g. `sudo usermod -aG docker <runner-user>` followed by a
restart of the runner service. If Docker is unreachable the step logs a warning
and skips (the release still publishes; the previously-generated matrix is kept)
rather than failing the job.

## Project layout

```
L4YAML/              Verified core library
  Scanner/           Scanner (+ indexed twin)
  Parser/            Token parser (+ indexed twin)
  Token/             Token type
  Spec/              Formal YAML 1.2.2 grammar, character predicates, spec types
  Schema/            Typeclasses, deriving macros, typed API
  Output/            Dumper, emitter, event/JSON test-matrix emitters
  Config/            ParserLimits, safe-parse API, load config
  Surface/           Surface-syntax grammar (acceptance strictness)
  Indexed/           Position-indexed foundations (CharStream, TokenStream, …)
  Algebra/           Value/token algebra (LawfulBEq, equivalence, …)
  FFI/               Lean side of the C ABI
  Proofs/            Machine-checked theorems (Scanner/, Parser/, Production/,
                     Coupling/, Output/, RoundTrip/, Schema/, …)
  Init.lean          `lemma` macro (theorem keyword reserved for capstones)
  Capstones.lean     @[capstone] set + per-capstone axiom-profile pins
Tests/               Runtime tests and compile-time #guard suites
Blueprint/           Methodology + proof-status SSOT (04-capstones.md)
scripts/             CI gates (check-theorem-keyword, check-import-closure),
                     bump-version.sh, report generators
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
- [DOCS.md](DOCS.md) — index of every kept document with its role and
  status (development-history archive deleted 2026-08-01; recoverable
  from git history)

## Versioning

L4YAML's version is declared independently in each language's package
manifest, plus once in the Python package's `__init__` so the value is
introspectable at runtime. The five locations are kept in lockstep by
[scripts/bump-version.sh](scripts/bump-version.sh).

| Location | Field |
|---|---|
| [lakefile.lean](lakefile.lean) | `version = "..."` |
| [rust/l4yaml-sys/Cargo.toml](rust/l4yaml-sys/Cargo.toml) | `version = "..."` |
| [rust/l4yaml/Cargo.toml](rust/l4yaml/Cargo.toml) | `version = "..."` |
| [python/pyproject.toml](python/pyproject.toml) | `version = "..."` |
| [python/l4yaml/\_\_init\_\_.py](python/l4yaml/__init__.py) | `__version__ = "..."` |

To inspect or bump:

```sh
scripts/bump-version.sh       # print the current version (errors on drift)
scripts/bump-version.sh +p    # bump patch  (X.Y.Z -> X.Y.(Z+1))
scripts/bump-version.sh +m    # bump minor  (X.Y.Z -> X.(Y+1).0)
scripts/bump-version.sh +M    # bump major  (X.Y.Z -> (X+1).0.0)
```

The script refuses to bump when the five sites disagree, so a divergence is
fixed by hand rather than half-bumped. CI's YAML Test Matrix keys off the
version: after a bump, commit, then `git tag vX.Y.Z` — the `v*` tag cuts the
release and fires the matrix regeneration.

The Lean side reads its version from the lakefile (no in-source constant);
the Rust workspace currently declares `version` per-crate (it could be
centralized via `[workspace.package]` if cross-crate sync becomes a
maintenance pain).

## Next steps

**Lift the `adaptForFlowContext → hasFlowIndicator` inductive gap.**
The 2026-08-01 inductive-fibration re-run (`L4YAML.FGM`'s `#ifg`, see
FGM's README Phase 4) reports its single non-aux gap on this call
edge: `YamlValue.adaptForFlowContext` recurses on `YamlValue` and
calls `hasFlowIndicator` (recursive on `List`), but no subject-aligned
inductive lemma about the former consumes an inductive lemma about the
latter. A `YamlValue`-induction lemma relating the two (e.g. how
flow-adaptation interacts with `hasFlowIndicator` on scalar payloads)
would close `#ifg` back to 0%.

**Close the event-axis verification gap.** The event stream (the
`+STR`/`+DOC`/`=VAL`… notation scored against the yaml-test-suite) currently
has no formal coverage: nothing under [L4YAML/Proofs/](L4YAML/Proofs/)
references [L4YAML/Output/Events.lean](L4YAML/Output/Events.lean), whose
`parseStreamMarkedLoop` is an unverified mirror of the verified
`TokenParser.parseStreamLoop` (~13 duplicated decision points, plus
`explicitStartAt` re-implementing the directive skip of `parseDirectives`).
Demonstrated 2026-07-04: commenting out the `some .documentEnd` suffix arm
(the C1 fix from commit `7d43fe61`) left `lake build` — and CI — green while
the event axis silently regressed 402→399 (HWV9, QT73, M7A3). YAML 1.2.2
defines no normative event model (events are "a traversal of the
serialization tree", §3.1.1/§3.2.2; the wire format is the de-facto
libyaml/yaml-test-suite DSL), but the serialization tree plus the §9 document
grammar (productions [205]/[206]/[208]/[211]) fully determine event
*semantics*, and the agreement theorem in step 3 needs no external reference
at all. The `Events.lean` definitions are already de-privatized so loop-level
lemmas can be stated from `Proofs/`.

1. **Pin the C1 event streams at build time.** Add a
   `Tests/Reflections/DocumentSuffixEvents.lean` pinning the byte-exact
   `streamToEvents` output for HWV9 (`...\n` → `+STR`/`-STR`), QT73
   (`# comment\n...\n` → `+STR`/`-STR`), and M7A3 (spec Example 9.3 — two
   documents, no phantom empty document between the two `...` lines) via
   `native_decide`, following the existing event-pin convention
   (`EmptyNodePropsSeqEntry`, `EscapedTrailingTab`, `EmitterTagPercentDecode`,
   `OrderAwareAlias`), and **index it in
   [Tests/Reflections.lean](Tests/Reflections.lean)** — an unindexed
   reflection is never built. This makes the `documentEnd` arm a
   build-time-guarded fact like defects C2/B2/D/J2 already are.

2. **Close the CI gap.** The build step of
   [.github/workflows/test-coverage.yml](.github/workflows/test-coverage.yml)
   uses an explicit target list that omits `Tests.Guards`,
   `Tests.Reflections`, `l4yaml-event`, `l4yaml-json`, and `eventscore`, and
   `scripts/run-all-tests.sh` runs nothing event-related — so even the
   existing reflection pins never elaborate in CI. Add the guard/reflection
   libs and the event targets to the build list, and add an event-scoring
   step with a fail threshold:

   ```sh
   lake build eventscore && .lake/build/bin/eventscore --suite yaml-test-suite
   # Baseline on the pinned submodule (478062b9): 347/358 correct.
   # The 11 event-diffs are upstream suite-version skew, not defects.
   # (The full 402-test matrix runs against the suite's data-branch
   # export; see YAML_MATRIX_COMPARISON.md.)
   ```

3. **Prove the agreement theorem** welding the mirror to the verified
   parser. `MarkedDoc` embeds a full `YamlDocument` plus two `Bool` marks, so
   the forget-the-marks projection is just `MarkedDoc.doc`:

   ```lean
   lemma parseYamlRawMarked_agrees (input : String) :
       (parseYamlRawMarked input).map (·.map (·.doc)) = parseYamlRaw input
   ```

   proved from a loop-level lemma by fuel induction:

   ```lean
   lemma parseStreamMarkedLoop_agrees (ps acc ss fuel) :
       (parseStreamMarkedLoop ps acc ss fuel).map (·.map (·.doc))
         = parseStreamLoop ps (acc.map (·.doc)) ss fuel
   ```

   The loop arms are pairwise identical except the push ordering around
   `tryConsume .documentEnd`, which is semantically neutral for the projected
   document list. After this lands, any future drift between the two loops is
   a proof breakage instead of a silent event regression. The theorem does
   not cover the `explicitStart`/`explicitEnd` marks themselves
   (`explicitStartAt` is a second copy of the directive grammar); those stay
   guarded by the step-1 pins, which check the `+DOC ---` / `-DOC ...`
   decorations byte-exactly.

**Port the 100%-matrix fixes to the indexed twin.** The indexed pipeline
(`L4YAML/Parser/TokenParserIx.lean`, `L4YAML/Scanner/IndexedScanner.lean`) is
wired into the library build, but it still models the pre-campaign runtime
behavior for four fixes from the 2026-07 100%-matrix campaign (the
campaign log is retired; the C2/B2 discriminator rationale survives in the
[Tests/Reflections/](Tests/Reflections/) probe docstrings); each
port must also re-prove the corresponding `Indexed*` lemmas:

- **C1** — the `some .documentEnd` suffix arm of the runtime
  `parseStreamLoop` ([L4YAML/Parser/TokenParser.lean](L4YAML/Parser/TokenParser.lean));
  the indexed `parseStreamLoop` has no such arm.
- **C2** — the derived `isSeqEntry` empty-scalar gate in
  `parseNode`/`parseNodeContent`; absent from the indexed twin.
- **C3** — the retroactive-`key` skip in `parseBlockMappingEntryValue`
  (§8.2.2 [191] explicit block-collection keys); the indexed else-branch
  still returns an empty node unconditionally.
- **B2** — the `protectedLen` boundary parameter of
  `collectDoubleQuotedLoop` (escaped-trailing-tab trimming); the indexed
  `collectDoubleQuotedLoopIx` has no such parameter.

## Contributing

Issues and pull requests are welcome. Please open an issue before starting
substantial work so we can discuss scope and proof strategy.

## License

Apache-2.0. See [LICENSE](LICENSE).
