# Proofs — Trust Structure, Inventory, and Roadmap

## 1. Overview

The `Proofs/` directory contains 26 Lean 4 files (20 proof modules +
6 SuiteGuards test suites) totaling ~9,500 lines, 572 theorems/lemmas,
and 653 `#guard` compile-time checks.  Every file compiles with
**zero `sorry`, zero `axiom`, zero `partial def`** in our code.

The proofs establish soundness, completeness (concrete and partial
universal), round-trip correctness, schema resolution, and
structural contracts for a YAML 1.2.2 parser built on
[lean4-parser](https://github.com/NicolasRouquette/lean4-parser)
(PR#97, branch `std-iterators`).

---

## 2. Trust Structure

Our proofs depend on lean4-parser at two distinct levels:

### Level 1 — Deductive (universal `@[simp]` lemmas)

`ParserSpecs.lean` provides 20 universal lemmas that unfold
lean4-parser's combinator definitions into concrete
`Parser.Result` expressions.  These cover:

| Category | Lemmas |
|---|---|
| Monad | `pure_eq`, `bind_eq`, `map_eq` |
| Stream | `getStream_eq`, `setStream_eq`, `getPosition_eq`, `setPosition_eq` |
| Error | `throw_eq`, `tryCatch_eq`, `throwUnexpected_eq`, `throwUnexpected_some_eq` |
| Backtracking | `withBacktracking_eq`, `orElse_eq` |
| Lookahead | `lookAhead_eq`, `notFollowedBy_eq` |
| Option | `eoption_eq`, `option_question_eq` |
| Token | `tokenCore_eq`, `anyToken_eq`, `tokenFilter_eq` |

Any proof that reasons only through these combinators has a
**fully deductive** chain back to lean4-parser definitions.

### Level 2 — Computational (no universal lemmas)

The YAML parser also uses lean4-parser's **fold-based combinators**:

- `dropMany p` — zero-or-more occurrences of `p`, discard results
- `count p` — count occurrences of `p` until failure

These are defined in terms of `foldl`, which delegates to `efoldlPAux`
— a well-founded recursive function that uses `Stream.remaining` as its
termination measure.  **There is no `@[simp]` lemma** that unfolds
`dropMany` or `count` into a concrete `Parser.Result` expression.

This means our proofs that involve `dropMany`/`count` (e.g., via
`skipHWhitespace`, `skipSpaces`, `currentCol`, `skipBlankLines`)
depend on lean4-parser's fold implementation only **computationally**:

- **652 `#guard` checks** execute the full parser pipeline
  (including fold-based combinators) at compile time via Lean's kernel
  evaluator.  A bug in `dropMany`/`count` would cause a build failure.
- **12 `native_decide` theorems** in `Completeness.lean` verify
  end-to-end parse results for concrete inputs, also exercising the
  full code path through fold combinators.

### What this means

The `#guard` / `native_decide` layer provides strong **empirical**
evidence that `dropMany` and `count` behave correctly — 653 distinct
YAML inputs are parsed and verified at compile time.  However, this
is not a **universal** guarantee.  A subtle edge case in
`efoldlPAux`'s `remaining`-based loop termination (e.g., a parser `p`
that succeeds without consuming input and triggers the early-stop branch)
would not be caught unless one of the 653 test inputs triggers it.

The deductive gap is:

```
✅  Deductive:  tokenFilter → anyToken → tokenCore → Stream.next?
                (fully unfolded by @[simp] lemmas)

⚠️  Computational:  dropMany → foldl → efoldl → efoldlM → efoldlP → efoldlPAux
                    (exercised by #guard / native_decide, not unfolded by @[simp])
```

---

## 3. File Inventory

### Proof Modules (20 files)

| File | Lines | Thms | Guards | Description |
|---|---|---|---|---|
| `BlockScalarContracts.lean` | 432 | 33 | — | Contracts for block scalar header extraction and strip/clip/keep modes |
| `CharClass.lean` | 158 | 8 | — | Prop ↔ Bool correspondence for Grammar vs. Parser character classifiers |
| `Completeness.lean` | 378 | 22 | 1 | Bottom-up completeness composition; `native_decide` concrete completeness |
| `Composition.lean` | 338 | 21 | — | Composes per-parser specs + fuel sufficiency into intermediate lemmas |
| `DocumentContracts.lean` | 190 | 17 | — | Document parser boundary detection, trailing comments, monotonicity |
| `DumpRoundTrip.lean` | 453 | 67 | 43 | Style-aware dump produces well-formed output; dump→parse round-trip |
| `EscapeResolution.lean` | 291 | 41 | 24 | Escape sequences produce valid Unicode per YAML 1.2.2 §5.7 |
| `FoldNewlines.lean` | 313 | 36 | 18 | Line folding does not introduce c-forbidden content (doc markers) |
| `FuelSufficiency.lean` | 545 | 35 | — | Fuel `4 * remaining + 4` is always sufficient; no fuel exhaustion |
| `IndentConsumption.lean` | 250 | 11 | 12 | Consuming indentation advances column by exactly the right amount |
| `ParserSpecs.lean` | 424 | 20 | — | Foundation `@[simp]` lemmas unfolding lean4-parser combinators |
| `PerParserSpecs.lean` | 940 | 46 | — | Per-parser correctness for `ValidNode` constructors (partial) |
| `RoundTrip.lean` | 905 | 56 | 66 | Parse-emit-parse round-trip preserves content |
| `SchemaDump.lean` | 311 | 40 | 22 | `ToYaml` + dump pipeline content round-trip |
| `SchemaResolution.lean` | 267 | 35 | 34 | Core Schema (§10.3) resolution: null/bool/int/float determinism |
| `Soundness.lean` | 414 | 27 | — | `NodeToValue` totality, determinism, faithful implementation |
| `StringProperties.lean` | 172 | 13 | — | Pure string/list helpers (whitespace trim, FoldResult invariants) |
| `Termination.lean` | 108 | 6 | — | Foundation lemmas for well-founded recursion on stream length |
| `TestSuite.lean` | 389 | — | 76 | Kernel-evaluated `#guard` tests across all parser components |
| `Validation.lean` | 324 | 35 | — | Backtracking-safe error channel, decision discrimination, indent invariants |

### SuiteGuards (6 files — auto-generated yaml-test-suite `#guard` checks)

| File | Lines | Guards | Category |
|---|---|---|---|
| `Advanced.lean` | 396 | 65 | Advanced-stage YAML tests |
| `Block.lean` | 323 | 84 | Block scalar/sequence/mapping tests |
| `Document.lean` | 96 | 16 | Document boundary tests |
| `Error.lean` | 401 | 94 | Error detection / rejection tests |
| `Flow.lean` | 228 | 44 | Flow sequence/mapping tests |
| `Scalar.lean` | 287 | 54 | Scalar (plain, quoted, literal, folded) tests |

### Totals

- **572** theorems/lemmas (all machine-checked)
- **653** `#guard` compile-time checks (Proofs/ + SuiteGuards/)
- **18** additional `#guard` checks in `Tests/IteratorTests.lean`
- **0** `sorry`, **0** `axiom`, **0** `partial def`

---

## 4. Future Work

### 4a. Items remaining in current proof files

#### `Completeness.lean` — `LawfulBEq YamlValue` / `DecidableEq YamlValue`

Needed for universally quantified completeness (`∀ input docs, ...`).
`Scalar` already has `DecidableEq`.  `YamlValue` requires proving the
derived `BEq` agrees with propositional equality through mutual recursion
on `Array YamlValue` / `Array (YamlValue × YamlValue)`.

#### `PerParserSpecs.lean` — remaining `ValidNode` constructors

Status per constructor:

| Constructor | Parser | Status |
|---|---|---|
| `plainScalarBlock` | `plainScalar` (block ctx) | ✅ Complete |
| `plainScalarFlow` | `plainScalar` (flow ctx) | ✅ Complete |
| `singleQuoted` | `singleQuotedScalar` | 🔧 WIP |
| `doubleQuoted` | `doubleQuotedScalar` | 🔧 WIP |
| `literalScalar` | `literalBlockScalar` | 📋 Planned |
| `foldedScalar` | `foldedBlockScalar` | 📋 Planned |
| `blockSeq` | `blockSequence` | 📋 Planned |
| `blockMap` | `blockMapping` | 📋 Planned |
| `flowSeq` | `flowSequence` | 📋 Planned |
| `flowMap` | `flowMapping` | 📋 Planned |

Remaining technical obligations:
- Special-start plain scalar (initial char restriction for `-`, `?`, `:`)
- Fuel-bounded loop induction for `takeWhileFuel`
- Mutual recursion between `blockValue`/`dispatchByChar`/`blockSequence`/`blockMapping`

#### `RoundTrip.lean` / `DumpRoundTrip.lean` — universal round-trip

Concrete round-trip is verified via `#guard`.  The universal theorem
`∀ v, contentEq v (parseYamlSingle (emit v)).get! = true` requires
unfolding ~8,000 lines of parser + emitter code, or composing
per-constructor round-trip lemmas once `PerParserSpecs` is complete.

#### `Termination.lean` — per-parser termination

Foundation lemmas (6 theorems) are in place.  Planned per-parser
termination proofs (`∀ input, ∃ output, parser input ≠ ⊥`) may be
subsumed by the fuel-sufficiency approach already in `FuelSufficiency.lean`.

### 4b. Closing the fold-combinator gap (ParserSpecs.lean)

Adding universal `@[simp]` lemmas for `dropMany` and `count` would
close the deductive gap described in §2.  The required lemmas:

```lean
-- dropMany: zero-or-more fold
@[simp]
theorem dropMany_eq (p : Parser ε σ τ α) (s : σ) :
    (dropMany p).run s = <concrete expression> := by
  unfold dropMany foldl efoldl efoldlM efoldlP efoldlPAux
  ...

-- count: counting fold
@[simp]
theorem count_eq (p : Parser ε σ τ α) (s : σ) :
    (count p).run s = <concrete expression> := by
  unfold count foldl efoldl efoldlM efoldlP efoldlPAux
  ...
```

The challenge is that `efoldlPAux` is a well-founded recursive function
whose unfolding depends on `Stream.remaining`.  The `@[simp]` lemma
would need to express the result as an inductive/recursive
characterization rather than a closed-form expression.  Possible
approaches:

1. **One-step unfolding**: Express `dropMany p s` as a case split on
   `p.run s` (success → check remaining → recurse / stop; failure → stop).
   This gives `simp` enough to reason step-by-step.

2. **Characterization lemma**: Prove a specification like
   `dropMany_spec`: `(dropMany p).run s = .ok s' ()` ↔
   `∃ n, after applying p exactly n times from s we reach s', and
   applying p once more from s' fails`.

3. **Inductive predicate**: Define `DropManyResult p s s'` as an
   inductive proposition and prove that `(dropMany p).run s = .ok s' ()`
   iff `DropManyResult p s s'`.

These lemmas would ideally live in lean4-parser itself (upstream PR).

---

## 5. Roadmap to Fully Deductive Correctness

A fully deductive end-to-end proof of

```
∀ input docs, ValidYaml input docs → parseYaml input = .ok docs
```

requires the following steps, roughly in dependency order:

### Phase A — Close the fold-combinator gap

1. **Add `dropMany_eq` / `count_eq` to `ParserSpecs.lean`** (or upstream
   to lean4-parser).  This eliminates the computational-only dependency
   on `efoldlPAux` and makes all lean4-parser combinators used by the
   YAML parser deductively transparent.

   Estimated effort: moderate.  The WF recursion in `efoldlPAux` is
   straightforward (decrease on `Stream.remaining`), but expressing the
   result as a simp-friendly equation requires care.

### Phase B — Complete per-parser specifications

2. **Finish `singleQuoted` and `doubleQuoted`** specs (currently WIP in
   `PerParserSpecs.lean`).  These require unfolding escape-sequence
   handling; `EscapeResolution.lean` already provides supporting lemmas.

3. **Add specs for `literalScalar`, `foldedScalar`**.  Block scalar
   contracts in `BlockScalarContracts.lean` provide the assume/guarantee
   framework; the specs must compose these with the `dropMany`/`count`
   specs from Phase A.

4. **Add specs for `blockSeq`, `blockMap`, `flowSeq`, `flowMap`**.
   These involve mutual recursion between `blockValue`, `dispatchByChar`,
   `blockSequence`, and `blockMapping`.  The fuel-sufficiency lemmas in
   `FuelSufficiency.lean` provide the termination arguments.

### Phase C — Type-level infrastructure

5. **Prove `LawfulBEq YamlValue`** by mutual induction on `YamlValue`,
   `Array YamlValue`, and `Array (YamlValue × YamlValue)`.  Derive
   `DecidableEq YamlValue` from it.  This is needed to upgrade
   concrete `native_decide` completeness to universal `∀`-quantified
   completeness.

### Phase D — Compose into full completeness

6. **Compose** per-parser specs (Phase B) + fuel sufficiency +
   `LawfulBEq` (Phase C) + stream initialization lemmas into the
   universal completeness theorem:

   ```lean
   theorem parseYaml_complete :
       ∀ input docs, ValidYaml input docs → parseYaml input = .ok docs
   ```

### Phase E — Universal round-trip

7. **Compose** per-constructor round-trip lemmas (from Phases B+D) with
   the emitter to prove:

   ```lean
   theorem emit_roundtrip :
       ∀ v : YamlValue, contentEq v (parseYamlSingle (emit v)).get! = true
   ```

### Rough effort estimate

| Phase | Items | Difficulty | Prerequisite |
|---|---|---|---|
| A | `dropMany_eq`, `count_eq` | Moderate | — |
| B | 8 per-parser specs | Moderate–Hard | A |
| C | `LawfulBEq YamlValue` | Moderate | — |
| D | Universal completeness | Hard | A, B, C |
| E | Universal round-trip | Hard | D |

Phases A and C are independent and can proceed in parallel.
Phase B depends on A.  The overall critical path is A → B → D → E.
