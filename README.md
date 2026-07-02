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

**Work in progress.** Two converse theorems round out the correctness
picture, both in the round-trip cluster under
[Proofs/Output/](L4YAML/Proofs/Output/):

- *Universal round-trip* — for every grammable `YamlValue v`, re-parsing
  `emit v` returns a content-equivalent value
  ([VERSION-0.4.7.md](VERSION-0.4.7.md)).
- *Grammar completeness* — every string in `InYamlLanguage` parses
  successfully, closing the biconditional with acceptance strictness
  ([VERSION-0.4.8.md](VERSION-0.4.8.md)).

**Current frontier (2026-07-01): 5 `sorry` sites** in the universal
round-trip cluster — up from 4, and the increase is a *decomposition, not a
regression*: the R447 co-construction skeleton landed and split the flow
structure blocker into a single, well-characterized navigator residual. The
five reduce to two independent obligations:

| # | Site | Track |
|---|------|-------|
| 1 | [`NonemptyStructure.lean:12131`](L4YAML/Proofs/Output/EmitterScannability/NonemptyStructure.lean#L12131) — `FlowSubrangesOk` (mapping) | A |
| 2 | [`EmitterScannability.lean:411`](L4YAML/Proofs/Output/EmitterScannability.lean#L411) — `FlowSubrangesOk` (sequence) | A |
| 5 | [`SeqInteriorSeparators.lean:11348`](L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean#L11348) — R447 navigator `seqBody_recseqbody_provider` | A (linchpin) |
| 3 | [`EmitterScannability.lean:1066`](L4YAML/Proofs/Output/EmitterScannability.lean#L1066) — non-all-scalar sequence locality | B |
| 4 | [`EmitterScannability.lean:1214`](L4YAML/Proofs/Output/EmitterScannability.lean#L1214) — non-all-scalar mapping locality | B |

- **Track A — `FlowSubrangesOk tokens`** (every balanced flow subrange is
  well-formed), consumed by both structure proofs. All three of its sorries
  bottom out at the single R447 navigator (#5): a carrier-free, per-window
  `RecSeqBody` structural walk whose linchpin is
  `recmappair_window_dispatch_map`. The assembler chain that lifts the
  navigator up to `FlowSubrangesOk` — and thereby discharges #1 and #2 — is
  already verified and waiting on it, so #5 is the sole remaining piece of
  *mathematical* content on this track.
- **Track B — `parseNode` span-locality:** the parser's `YamlValue` output
  depends only on the tokens forward of its start position, never on the
  absolute offset or on trailing siblings (`YamlValue` is position-free;
  `YamlDocument.compose` strips positions into a separate field). The precise
  statement was pinned on 2026-07-01: the earlier `∀k`/whole-state form
  (`parseNode_position_invariant`) is unusable — it disagrees on the output
  position and its hypothesis is unsatisfiable in the application — so the
  target projects the *value* under *bounded* `.val`-agreement
  (`ParseNodeValueSpanLocal`). Closing #3/#4 factors into four pieces,
  cheapest first:
  - **P2a — frame:** `parseNode` advances to exactly its matching bracket
    close (`ParseNodeFrameWithinSpan`, on a positive Dyck span `0 < n`), located
    via `flowBracketBalance_matching_close`. This is *not* a strengthening of the
    existing position-monotonicity lemma, which bounds position only from
    below; the leaf precedent is the scalar `advances_by_one`. The `0 < n` guard
    was found necessary on 2026-07-01 (the degenerate `n = 0` satisfies the Dyck
    conditions vacuously yet forces `ps'.pos = p`, refuting the unguarded form);
    with it the span is unique (`frameSpan_unique`, proved `sorry`-free), so the
    frame's `n` is the matching-close span. The two pure-`flowBracketBalance`
    bricks the frame induction consumes are now proved `sorry`-free:
    `frameHead_classified` (the head is neutral iff `n = 1`, an opener iff
    `n ≥ 2` — the branch dispatcher, and exactly the opener premise
    `flowBracketBalance_matching_close` needs) and `frame_matching_close_at_end`
    (for `n ≥ 2` the matching close is the span's last token, body balanced).
    What remains of P2a is the parser-side fuel-indexed mutual induction (the
    upper-bound companion to the lower-bound `ParseNodePosMono`). Note for that
    build: the flow parser is *lookahead-driven* — its loops exit on
    `peek? = flowSequenceEnd`, never consulting a bracket counter — so no lemma
    yet connects parseNode's consumption to `flowBracketBalance`; that bridge is
    the vertical gap the induction must close (the combinatorial bricks above are
    scanner-side).
  - **Bridge — scanner span:** an element's emitted tokens form a contiguous
    run inside the whole sequence's tokens — the variable-width generalization
    of the all-scalar scanner facts (R596/R597).
  - **P2b — value span-locality** (`ParseNodeValueSpanLocal`): the crux mutual
    induction over the flow parser clique, consuming P2a's frame and the
    Bridge's agreement. Its target statement was corrected again on 2026-07-01:
    the conclusion must project through `.toOption.map` (failure ↦ `none`), not
    the error-sensitive `Except.map`, because parseNode's fuel-0 failure payload
    is position-dependent (`.nestingDepthExceeded ps.currentLine`). The `.map`
    form is `sorry`-free-refuted (`p2b_map_form_false`) at the failing boundary —
    which the success-only probes had never exercised — and the corrected form
    survives it (`p2b_toOption_form_survives`). With the statement fixed, P2b's
    **scalar branch is now landed `sorry`-free**
    (`parseNodeValueSpanLocal_scalar_branch`): a scalar head is
    trailing-independent (`parseNode_scalar_produces_scalar`), so it closes from
    `.val`-agreement at `k = 0` alone — needing *neither* the frame
    side-condition *nor* the `k ≥ 1` agreement (a finding: the frame is consumed
    only by the collection branches). On 2026-07-01 P2b was **re-architected to
    the joint `ParseNodeValueAdvanceLocal`**: value *and* relative advance
    (`·.2.pos - p`) in one conclusion. Because a lookahead parser keeps two
    agreeing runs in lockstep, the advance is a *conclusion* of the same
    induction rather than an imported P2a frame — birth-probed true on a real
    collection (`jvadv_collection_relative_advance_agrees`: absolute `pos` differs
    5≠4, relative advance agrees 3=3), and the joint scalar leaf
    (`parseNodeValueAdvanceLocal_scalar_branch`) is landed `sorry`-free. The
    flow-*collection* head reduces (after `parseNode` peels the bracket + one unit
    of fuel) to a **loop joint** over `parseFlowSequenceLoop`; on 2026-07-01 that
    target (`ParseFlowSequenceLoopValueAdvanceLocal`) was captured and its two base
    branches landed `sorry`-free — fuel-0 (`parseFlowSeqLoop_joint_fuel0`) and the
    empty-collection closer (`parseFlowSeqLoop_joint_close`), birth-probed
    (`loop_joint_birth`: absolute `pos` differs 4≠3, relative advance agrees 1=1)
    and fired on real emission (`loop_close_fires`). The recursive step's
    agreement re-arming is shown to be *balance-free* — `agree_shift` (proved
    `[propext, Quot.sound]`, no `flowBracketBalance`) shifts the bounded agreement
    by the joint's equal advance, the mechanism that would retire P2a's balance
    bridge. Only the recursive loop step (a mutual induction over the parser
    clique) remains to decide it.
  - **P1 — loop-value:** threads P2a and P2b through the flow loop, computing
    each element's cumulative start offset.

  P2a and the Bridge are birth-probed *tight* / *contiguous* on real tokens,
  and the all-scalar branch already closes by canonical form, so only the
  non-scalar branches (#3, #4) remain. The typed targets and boundary
  regression fixtures live in
  [Tests/Reflections/NonAllScalarLocality.lean](Tests/Reflections/NonAllScalarLocality.lean).

The two tracks are independent and can be closed in either order. Apart from
these five `sorry`s, the library carries no incomplete proofs: the verified
core (scanner, token parser, schema, dumper) and every completed theorem
above remain `sorry`-, `axiom`-, and `partial`-free.

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

## Versioning

L4YAML's version is declared independently in each language's package
manifest, plus once in the Python package's `__init__` so the value is
introspectable at runtime. **All five locations must be updated together**
when cutting a release; there is no automation that propagates between them.

| Location | Field |
|---|---|
| [lakefile.toml](lakefile.toml) | `version = "..."` |
| [rust/l4yaml-sys/Cargo.toml](rust/l4yaml-sys/Cargo.toml) | `version = "..."` |
| [rust/l4yaml/Cargo.toml](rust/l4yaml/Cargo.toml) | `version = "..."` |
| [python/pyproject.toml](python/pyproject.toml) | `version = "..."` |
| [python/l4yaml/\_\_init\_\_.py](python/l4yaml/__init__.py) | `__version__ = "..."` |

A grep target for sanity-checking that nothing has drifted:

```sh
grep -REn '^\s*version\s*=' lakefile.toml rust/*/Cargo.toml python/pyproject.toml
grep -n  '^__version__' python/l4yaml/__init__.py
```

The Lean side reads its version from the lakefile (no in-source constant);
the Rust workspace currently declares `version` per-crate (it could be
centralized via `[workspace.package]` if cross-crate sync becomes a
maintenance pain).

## Contributing

Issues and pull requests are welcome. Please open an issue before starting
substantial work so we can discuss scope and proof strategy.

## License

Apache-2.0. See [LICENSE](LICENSE).
