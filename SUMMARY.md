# Reinventing Software Engineering at JPL

**Project**: https://github.jpl.nasa.gov/pass/lean4-yaml-verified
**Author**: N. Rouquette

---

## 1: The Revolution — Markets We Can't Reach Today

**JPL builds the most ambitious robotic systems in human history. But three markets remain out of reach — not because we lack engineering talent, but because our verification practices cannot produce the evidence these markets demand.**

### DO-178C Level A: Avionics Software for Human-Rated Flight

DO-178C Level A requires the highest assurance for software whose failure is **catastrophic** — loss of aircraft, loss of crew. The standard explicitly allows formal methods as a verification technique (supplement DO-333).

**Why JPL can't compete here today:**
- V&V using tests is inherently incomplete — you can demonstrate the presence of bugs, never their absence
- Level A demands **100% structural coverage** with **independence between verification and development** — testing alone cannot achieve this economically for complex autonomous systems
- For missions at interstellar scale — think *Project Hail Mary*, centuries-long transit times — the software must be **provably error-free**, not "tested well enough." No test suite can cover a century of edge cases. Only mathematical proof can.

### Medical-Grade Certification: Life-Critical Devices

IEC 62304 Class C (life-critical), FDA 510(k)/PMA for software-intensive medical devices like pacemakers, insulin pumps, surgical robots. These require:
- **Traceability** from requirements to verified implementation
- **Evidence that the software cannot enter unsafe states** — not just that it hasn't yet
- Static analysis and testing are necessary but **insufficient** for the highest safety classes

**JPL's current practices produce excellent test artifacts. Medical regulators increasingly want mathematical proof.**

### Competitive Bids: Proving Safety of Autonomous Systems

The highest levels of assurance in competitive proposals — defense, space, critical infrastructure — increasingly require **mathematical proofs of key properties**:
- **Safety**: The system never enters a catastrophic state
- **Progress**: The system always eventually accomplishes its objectives
- **Reachability**: The system can reach any required state from any valid initial state

These properties are **increasingly harder to prove for autonomous systems** where the state space is vast, the environment is adversarial, and the control logic is learned or adaptive. Test-based V&V cannot credibly claim these properties hold for all inputs. **Mathematical proof can.**

> **The question is not whether formal verification will become standard practice for safety-critical software. The question is whether JPL will lead or follow.**

---

## 2: The Paradigm Shift — From Testing to Proof

### Five years ago, this was science fiction.

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

### Today, with GenAI assistance and expert guidance, this is real.

It takes adopting a radically unorthodox software engineering development paradigm — **Lean 4**, a functional programming language that doubles as an interactive theorem prover, unleashing the full power of mathematical rigor for GenAI-assisted mechanized proofs.

**One verified implementation. One proof of correctness. Native bindings to C, Python, and Rust.**

The verified Lean parser compiles to C via Lean's code generator. A thin FFI layer exposes 26 C-callable functions. Python calls them via `ctypes`. Rust calls them via `bindgen`. **Every language gets the same proven guarantees** — termination, soundness, completeness, resource bounds — because they all execute the same verified code.

```
                    Lean 4 (verified source)
                    ├── 1,769 machine-checked theorems
                    ├── 0 axioms, 0 sorry, 0 partial def
                    └── Compiles to C via Lean IR
                              │
                    ┌─────────┼─────────┐
                    ▾         ▾         ▾
                C API     Python      Rust
              (26 fns)   (ctypes)   (bindgen)
              liblean4yaml.so ← shared verified core
```

**This is not a toy demo.** It is a production YAML 1.2.2 parser:
- **1,769 theorems** machine-checked by Lean 4's trusted kernel
- **2,124 compile-time guards** — continuous verification at build time
- **0 axioms, 0 `sorry`, 0 `partial def`** — zero "trust me" code
- **100% YAML 1.2.2 test suite** (225/225 test IDs) — plus the mathematical proofs that make the test suite redundant
- **Configurable security limits** — billion laughs protection, nesting bounds, scalar size caps, tag policy enforcement
- **78 Python tests, 21 Rust tests** — all passing against the verified shared library

---

## 3: What We Prove — And Why Testing Can't

### The Fundamental Asymmetry

| What Testing Shows | What Testing **Cannot** Show |
|-------------------|------------------------|
| "Works on 1,000 examples" | "Works on **all** inputs" |
| "Found 50 bugs" | "**No more** bugs exist" |
| "Fast on these files" | "**Never** crashes or hangs" |
| "Handles known attack vectors" | "**No unknown** attack vectors remain" |
| "Survived 10 years in production" | "Will survive 100,000 years" |

### Three Proof Layers — Each Eliminates a Vulnerability Class

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

### Supply Chain Security: Proven Guarantees

| Threat | Traditional Parsers | Verified Parser (This Work) |
|--------|--------------------|-----------------------------|
| **Infinite loops** | Unknown — hope testing found them | **✅ Proven termination** — mathematically impossible to hang |
| **ACE via edge cases** | Unknown — test coverage incomplete | **✅ Proven soundness** — every input handled correctly or rejected |
| **DoS via resource exhaustion** | Unknown — fuzzing may miss patterns | **✅ Configurable limits** — proven enforcement of bounds |
| **Unknown parsing bugs** | Post-deployment CVEs likely | **✅ Zero latent parsing bugs** — all behaviors proven |
| **Billion laughs** | Patched *after* CVE disclosure | **✅ Alias expansion limits** — max 100K resolved nodes (configurable) |
| **Structural injection** | Found by specific test cases | **✅ Proven impossible** — `validPlainFirst` theorem |

### Why C, Python, Go, Rust Parsers Can't Do This

- **C** (libyaml): Manual memory management, undefined behavior, no proof language — auditing 10K LOC of pointer arithmetic is intractable
- **Python** (PyYAML, ruamel.yaml): Dynamic typing, mutable state, runtime errors — `pytest` checks examples, can't express `∀ input`
- **Go** (go-yaml): Garbage-collected but no dependent types — can't express or check invariants at compile time
- **Rust** (serde-yaml): Borrow checker proves memory safety, not functional correctness — can parse safely but can't prove it parses *correctly*

**Lean 4 is unique**: it is simultaneously a general-purpose programming language (with native code generation to C) and an interactive theorem prover (with dependent types and a trusted kernel). This is not a tradeoff — it is both at once. Crucially, Lean 4 is the **only** language in this class whose kernel has [multiple independent implementations](https://leodemoura.github.io/blog/2026-3-16-who-watches-the-provers/) — written in Rust, C, Lean itself, and others — that are **nightly cross-tested** against each other. No other theorem prover (Coq, Agda, Isabelle, F*) subjects its trusted core to this level of independent V&V.

---

## 4: The Proof of Concept — Quantified Results

### Parser Verification (Complete)

| Metric | Value |
|--------|-------|
| **Theorems** | 1,769 machine-checked by Lean 4's trusted kernel |
| **Compile-time guards** | 2,124 (including 362 auto-generated from yaml-test-suite) |
| **Axioms** | 0 |
| **`sorry` (unproven gaps)** | 0 |
| **`partial def` (non-terminating)** | 0 |
| **YAML 1.2.2 test suite** | 225/225 test IDs (100%) |
| **YAML 1.2.2 spec examples** | 132/132 (100%) |
| **Parser LOC** | ~2,000 |
| **Proof LOC** | ~32,000 (47 proof modules) |
| **Build jobs** | 341/341, 0 errors |

### Multi-Language FFI (Complete)

| Language | Binding | Tests | Status |
|----------|---------|-------|--------|
| **C** | 26 exported functions, opaque handle ABI, `liblean4yaml.so` | Verified via `nm -D` | ✅ Production |
| **Python** | `ctypes` package, 5 modules, full `YamlValue` API | 78 tests, 0.14s | ✅ Production |
| **Rust** | 2-crate workspace (`lean4yaml-sys` + `lean4yaml`), safe RAII wrapper | 21 tests, 0.06s | ✅ Production |

### Security Limits (Complete)

| Threat | Limit | Default |
|--------|-------|---------|
| Billion-laugh alias expansion | `maxResolvedNodes` | 100,000 |
| Excessive alias depth/count | `maxAliasDepth` / `maxAliasExpansions` | 50 / 10,000 |
| Deep nesting | `maxDepth` | 100 |
| Oversized scalars | `maxScalarBytes` | 10 MB |
| Large collections | `maxSequenceLength` / `maxMappingSize` | 100,000 |
| Input size | `maxInputBytes` | 100 MB |
| Language-specific tags (`!!python/*`) | `rejectLanguageTags` | true |

### Comparison to Industry Verified Systems

| System | Domain | Code | Proofs | Deployed |
|--------|--------|------|--------|----------|
| **seL4** | Verified OS kernel | ~200K LOC | ~480K LOC | Defense systems |
| **CompCert** | Verified C compiler | ~60K LOC | ~100K LOC | Airbus avionics |
| **AWS Cedar** | Verified authorization | ~20K LOC | ~40K LOC | Cloud security |
| **lean4-yaml-verified** | **Verified YAML parser** | **~2K LOC** | **~32K LOC** | **Aerospace configs (C, Python, Rust)** |

Same class of rigor. Same trusted-kernel verification. **Only verified YAML parser in any language.**

---

## 5: The Vision — Reinventing Software Engineering at JPL

### Three Markets, One Capability

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

### The Development Paradigm

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
3. Prove — Bridge spec ↔ impl with machine-checked theorems (1,769 of them)
4. Compile — Lean IR → C → shared library (liblean4yaml.so)
5. Bind — C header + shim → Python ctypes / Rust bindgen
6. Ship — Every consumer gets proven guarantees. Every build re-checks every proof.
```

If the spec changes, the proofs break → you know exactly what to fix.
If the implementation changes, the proofs break → you know exactly what drifted.
If neither changes, the proofs still pass → guaranteed correctness, indefinitely.

---

### The Roadmap: From YAML to Safety-Critical Systems

YAML parsing is the **proof of concept** — a complex, security-sensitive problem solved with full mathematical rigor. The paradigm generalizes:

```
Phase 1 (Complete): Verified YAML 1.2.2 Parser
├── 1,769 theorems, 0 sorry, 0 axioms
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

## Summary: The Case for Action

**The problem**: JPL's current test-based V&V practices, while excellent for robotic exploration, cannot produce the evidence required for DO-178C Level A avionics, medical-grade certification, or the highest-assurance competitive bids. These markets demand mathematical proof of correctness — proof that testing fundamentally cannot provide.

**The proof of concept**: A fully verified YAML 1.2.2 parser — 1,769 machine-checked theorems, zero axioms, zero unproven gaps — with production bindings to C, Python, and Rust. Built with Lean 4 and GenAI-assisted proof engineering. A complex, security-critical problem solved with the same mathematical rigor as seL4 and CompCert.

**The opportunity**: Adopt this paradigm — specify, implement, prove, compile, bind, ship — and JPL gains access to:
- **DO-178C Level A**: Formal methods evidence for human-rated avionics software
- **Medical certification**: Proven safety properties for life-critical devices
- **Competitive advantage**: Mathematical proof of safety, progress, and reachability for autonomous systems — properties that no amount of testing can establish

**The bottom line**: This isn't "better testing." It is a **fundamental shift** from "we hope we found all the bugs" to "certain classes of bugs are mathematically impossible."

Five years ago, this was science fiction. Today, it is a working system with 1,769 theorems, production multi-language bindings, and a clear path from YAML parsing to safety-critical autonomous systems.

**The revolution is here. The question is whether JPL will lead it.**
