# Proofs — Trust Structure, Inventory, and Roadmap

## 1. Overview

The `Proofs/` directory contains 53 Lean 4 files (47 proof modules +
6 SuiteGuards test suites) totaling ~32,000 lines, 1,654 theorems/lemmas,
and 2,083 `#guard` compile-time checks.  Every file compiles with
**zero `sorry`, zero `axiom`, zero `partial def`** in our code.

The proofs establish soundness, completeness (concrete and partial
universal), round-trip correctness, schema resolution, and
structural contracts for a YAML 1.2.2 tokenized parser pipeline
(`Scanner.lean` → `TokenParser.lean`).  The project has **no
external parsing-library dependencies** — the scanner and token
parser are self-contained Lean 4 code.

---

## 2. Trust Structure

The tokenized pipeline (`Scanner.lean` → `TokenParser.lean`) is
self-contained Lean 4 code with **no external parsing-library
dependencies**.  The trust structure has two levels:

### Level 1 — Scanner (total `def` functions)

`Scanner.lean` (~1,600 lines) contains ~50 functions, all defined as
plain `def` (total, no `partial`).  The scanner converts raw YAML text
into a `List YamlToken` by explicit character-level iteration.

Proofs about scanner functions are in three files:
- **`ScannerProofs.lean`** — char classification, token classification,
  escape correctness, state accessors, indentation invariants, token
  stream, and stream envelope theorems (53 theorems, 61 guards).
- **`ScannerContracts.lean`** — contracts on block scalar header
  extraction, `scanDoubleQuoted`/`scanSingleQuoted` correctness,
  and monotonicity of scanner state updates (14 theorems, 66 guards).
- **`ScannerIndent.lean`** — indentation push/pop invariants and
  `unwindIndents` correctness (9 theorems, 15 guards).

### Level 2 — TokenParser (`partial def` mutual recursion)

`TokenParser.lean` (~850 lines) contains 7 mutually recursive `partial
def` functions (`parseNode`, `parseBlockSequence`, `parseBlockMapping`,
`parseFlowSequence`, `parseFlowMapping`, `parseSinglePairMapping`,
`parseImplicitBlockSequence`) that consume the token list.  The
`partial def` means Lean does not verify termination — this is the
primary trust gap.

Correctness evidence:
- **2,012 `#guard` checks** execute the full `scan → parse` pipeline at
  compile time via Lean's kernel evaluator.
- **13 `native_decide` theorems** in `Completeness.lean` verify
  end-to-end parse results for concrete inputs.
- **`Composition.lean`** proves pipeline composition properties
  (`parseYaml_pipeline`, `scanAndParse` correctness).
- **`ParserWellBehaved.lean`** (3,100 lines, 74 theorems) proves
  token monotonicity and flow nesting preservation for all sub-parsers.
- **`ParserNodeProofs.lean`** (1,781 lines, 57 theorems) proves
  `parseNode_anchors_grow` and `parseNode_aliases_resolve` via strong
  induction on fuel.
- **`ParserWfaProofs.lean`** (1,690 lines, 50 theorems) proves
  well-formed anchors and token preservation for all sub-parsers.

### What this means

The scanner layer is fully total and amenable to deductive reasoning.
The token-parser layer uses `partial def` for recursive descent,
so termination is not machine-checked.  The `#guard`/`native_decide`
layer provides strong **empirical** evidence (787 distinct YAML inputs
parsed and verified at compile time) but not a universal termination
guarantee.  P10.8 (planned) will convert the 7 `partial def` functions
to total `def` with well-founded recursion on token list length.

> **Historical note:** Prior to Phase 10, the project used
> [lean4-parser](https://github.com/NicolasRouquette/lean4-parser)
> combinators.  The trust structure for that era (including the
> `ParserSpecs.lean` foundation lemmas and fold-combinator gap) is
> documented in §4b–§4j below.

---

## 3. File Inventory

### Proof Modules (45 files)

| File | Lines | Thms | Guards | Description |
|---|---|---|---|---|
| `BlockScalarContracts.lean` | 478 | 38 | — | Contracts for block scalar header extraction and strip/clip/keep modes |
| `CharClass.lean` | 183 | 9 | — | Prop ↔ Bool correspondence for Grammar vs. Scanner character classifiers |
| `CommentProperties.lean` | 355 | 41 | — | Comment handling properties |
| `CommentRoundTrip.lean` | 159 | 10 | 4 | Comment round-trip correctness |
| `Completeness.lean` | 348 | 13 | — | Bottom-up completeness, `DecidableEq YamlValue/YamlDocument`, concrete parse |
| `Composition.lean` | 137 | 7 | — | Pipeline composition: `parseYaml_pipeline`, `scanAndParse` correctness |
| `DocumentContracts.lean` | 183 | 16 | — | Document parser boundary detection, trailing comments, monotonicity |
| `DumpRoundTrip.lean` | 310 | 67 | 2 | Style-aware dump produces well-formed output; dump→parse round-trip |
| `EndToEndCorrectness.lean` | 434 | 13 | 2 | End-to-end parse correctness + ValidDocument/ValidStream proofs (v0.2.4) |
| `ErrorProperties.lean` | 129 | 12 | — | Error type discriminability, coverage, lifting (v0.2) |
| `EscapeResolution.lean` | 290 | 61 | 2 | Escape sequences produce valid Unicode per YAML 1.2.2 §5.7 |
| `FoldNewlines.lean` | 248 | 36 | 2 | Line folding does not introduce c-forbidden content (doc markers) |
| `LawfulBEq.lean` | 261 | 32 | — | `LawfulBEq` for AST hierarchy: 6 instances, 24 equational lemmas, 2 main theorems |
| `ParserAnchorProofs.lean` | 220 | 9 | — | Anchor/alias validation proofs |
| `ParserCompleteness.lean` | 229 | 2 | — | Token parser completeness proofs |
| `ParserCorrectness.lean` | 162 | 3 | 4 | Token parser correctness proofs |
| `ParserGrammableBase.lean` | 499 | 18 | — | Parser grammable base infrastructure |
| `ParserGrammable.lean` | 112 | 4 | — | Parser grammable proofs |
| `ParserNodeProofs.lean` | 1,781 | 57 | — | `parseNode` anchors-grow + aliases-resolve proofs (strong induction on fuel) |
| `ParserSoundness.lean` | 339 | 8 | — | Token parser soundness proofs |
| `ParserWellBehaved.lean` | 3,102 | 74 | — | Parser well-behavedness proofs (tokens monotonic, flow nesting preserved) |
| `ParserWfaProofs.lean` | 1,690 | 50 | — | Well-formed anchors + token preservation for all sub-parsers |
| `RoundTrip.lean` | 670 | 56 | 6 | Parse-emit-parse round-trip preserves content |
| `ScannerContracts.lean` | 276 | 23 | 3 | Scanner structural contracts: `scanDoubleQuoted`/`scanSingleQuoted` correctness |
| `ScannerCorrectness.lean` | 8,331 | 439 | 1 | Scanner correctness: dispatch, state invariants, all `scanNextToken` branches |
| `ScannerDispatch.lean` | 251 | 7 | 4 | Scanner dispatch proofs |
| `ScannerDocument.lean` | 237 | 5 | 5 | Scanner document boundary proofs |
| `ScannerDoubleQuoted.lean` | 224 | 10 | 2 | Scanner double-quoted string proofs |
| `ScannerEmitBridge.lean` | 434 | 9 | 6 | Scanner emit bridge proofs |
| `ScannerFlowCollection.lean` | 267 | 19 | 3 | Scanner flow collection proofs |
| `ScannerIndent.lean` | 169 | 10 | 1 | Indentation push/pop invariants, `unwindIndents` correctness |
| `ScannerIndentStack.lean` | 279 | 16 | 1 | Scanner indent stack invariants |
| `ScannerLoopInvariant.lean` | 281 | 15 | — | Scanner loop invariant proofs |
| `ScannerPlainContent.lean` | 509 | 22 | — | Scanner plain content proofs |
| `ScannerPlainScalar.lean` | 443 | 16 | — | Scanner plain scalar proofs |
| `ScannerPlainScalarValid.lean` | 5,373 | 176 | — | Scanner plain scalar validity (all branches of PSV dispatch) |
| `ScannerProgress.lean` | 300 | 18 | — | Scanner progress proofs |
| `ScannerProofs.lean` | 306 | 53 | 5 | Char classification, token classification, escape correctness, state accessors |
| `ScannerScalar.lean` | 177 | 11 | 1 | Scanner scalar proofs |
| `ScannerSimpleKey.lean` | 160 | 7 | 1 | Scanner simple key proofs |
| `ScannerWhitespace.lean` | 174 | 6 | 2 | Scanner whitespace proofs |
| `SchemaComposition.lean` | 260 | 28 | — | `resolve ∘ toYaml` + `fromYaml? ∘ toYaml` composition round-trip (v0.2.5) |
| `SchemaDump.lean` | 277 | 40 | — | `ToYaml` + dump pipeline content round-trip |
| `SchemaResolution.lean` | 227 | 35 | — | Core Schema (§10.3) resolution: null/bool/int/float determinism |
| `Soundness.lean` | 423 | 27 | — | `NodeToValue` totality, determinism, faithful implementation |
| `StringProperties.lean` | 250 | 19 | — | Pure string/list helpers (whitespace trim, FoldResult invariants) |
| `ValueAlgebra.lean` | 199 | 7 | — | YamlValue algebraic properties |

### SuiteGuards (6 files — auto-generated yaml-test-suite `#guard` checks)

| File | Lines | Guards | Category |
|---|---|---|---|
| `Advanced.lean` | 342 | 65 | Advanced-stage YAML tests |
| `Block.lean` | 432 | 83 | Block scalar/sequence/mapping tests |
| `Document.lean` | 97 | 16 | Document boundary tests |
| `Error.lean` | 497 | 96 | Error detection / rejection tests |
| `Flow.lean` | 237 | 44 | Flow sequence/mapping tests |
| `Scalar.lean` | 307 | 58 | Scalar (plain, quoted, literal, folded) tests |

### Totals

- **1,654** theorems/lemmas (all machine-checked)
- **2,083** `#guard` compile-time checks (Proofs/ + SuiteGuards/ + Tests/)
- **0** `sorry`, **0** `axiom`, **0** `partial def`

---

## 4. Future Work

### 4a. Items remaining in current proof files

#### `Completeness.lean` — `DecidableEq YamlValue` ✅ / `LawfulBEq YamlValue` ✅

**`DecidableEq YamlValue`** and **`DecidableEq YamlDocument`** are now
proved (25 new theorems/definitions).  The proof uses `where`-clause
mutual structural recursion on `List YamlValue` / `List (YamlValue × YamlValue)`,
following the same pattern as `contentEq` in `Emitter.lean`.

Array equality is bridged via `Array.toList` + `congrArg Array.mk`,
since `Array.toList a = a.data` definitionally.

**`LawfulBEq YamlValue`** is proved in `Proofs/LawfulBEq.lean` (v0.2.1).
The proof required replacing both `Scalar` and `YamlValue`'s `deriving BEq`
with explicit transparent definitions in `Types.lean`, then proving
the full instance chain via structural recursion with `where`-clause
list/pair-list helpers.  See the v0.2.1 section in the project README
for the complete design retrospective.

#### `PerParserSpecs.lean` — _(removed in Phase 10)_

> The old `PerParserSpecs.lean` contained per-parser correctness specs
> for the lean4-parser–based combinator pipeline.  It was removed in
> Phase 10 when the parser was replaced by the tokenized pipeline.
> The scanner-side equivalents are now in `ScannerProofs.lean`,
> `ScannerContracts.lean`, and `ScannerIndent.lean`.  Token-parser
> specs will be developed as part of P10.8.

#### `RoundTrip.lean` / `DumpRoundTrip.lean` — universal round-trip

Concrete round-trip is verified via `#guard`.  The universal theorem
`∀ v, contentEq v (parseYamlSingle (emit v)).get! = true` requires
unfolding the scanner + token-parser + emitter code, or composing
per-constructor round-trip lemmas.

#### `Termination.lean` — _(removed in Phase 10)_

> The old `Termination.lean` contained foundation + composition lemmas
> for the fuel-based recursion approach used by the lean4-parser pipeline.
> It was removed in Phase 10.  The tokenized pipeline uses `partial def`
> mutual recursion in `TokenParser.lean`; P10.8 will convert these to
> total `def` with well-founded recursion on token list length.

#### `FuelSufficiency.lean`, `IndentConsumption.lean`, `Validation.lean`, `ParserSpecs.lean` — _(removed in Phase 10)_

> These files contained proofs specific to the lean4-parser combinator
> pipeline (fuel arithmetic, indent consumption tracking, backtracking
> validation, and `@[simp]` foundation lemmas).  They were removed in
> Phase 10 when the parser was replaced by the self-contained tokenized
> pipeline.  Their proof techniques are documented in §4b–§4j below
> for historical reference.

### 4a′. Reflections — unexpected challenges, simplifications, and idioms

#### Reused proof idioms

> **Note:** Idioms 2 and 4 below reference `ParserSpecs.lean` and
> `FuelSufficiency.lean`, which were part of the pre–Phase 10
> lean4-parser pipeline and have been removed.  They are retained
> here as historical documentation of proof techniques.

1. **`where`-clause mutual structural recursion.**
   The `decEqYamlValue` proof reuses the exact pattern established by
   `contentEq` in `Emitter.lean`: the top-level function dispatches on
   `YamlValue` constructors, converts `Array` fields to `List` via
   `.toList`, and delegates to `where`-clause helpers (`decEqListYV`,
   `decEqPairListYV`) that recurse on list structure and call back
   to the main function on strictly smaller `YamlValue` subterms.
   This pattern is the canonical way to work around Lean 4's inability
   to derive `DecidableEq` for types with nested `Array` containers.

2. **`unfold + simp only [ParserSpecs.*]` pipeline.**
   Every per-parser spec follows the same proof skeleton: `unfold` the
   parser definition, then `simp only` with the 20 foundation lemmas
   from `ParserSpecs.lean` to reduce combinator applications to concrete
   `Result` expressions.  This pipeline (used ~50 times across
   `PerParserSpecs`, `FuelSufficiency`, `Composition`) was reused
   without modification for the new `collectChars` loop lemmas.

3. **`h ▸ rfl` for `isTrue` / `fun heq => h (by cases heq; rfl)` for
   `isFalse` on same-constructor cases.**
   This pair of idioms appears throughout `DecidableEq` proofs for
   flat-field types (Scalar, Directive, etc.) and was lifted directly
   into the recursive `decEqYamlValue` for the scalar/alias base cases.

4. **`omega` for arithmetic obligations.**
   The termination composition theorems (`fuel_bounds_iterations`,
   `fuel_le_of_remaining`) are simple `Nat` inequalities resolved by
   `omega`, the same tactic used extensively in `FuelSufficiency.lean`
   for fuel-arithmetic goals.

#### New proof idioms (not seen elsewhere in the codebase)

5. **`isFalse YamlValue.noConfusion` for cross-constructor cases.**
   The 12 cross-constructor cases in `decEqYamlValue` (e.g.,
   `.scalar _ , .sequence ..`) are dispatched by
   `isFalse YamlValue.noConfusion`.  This is a term-mode idiom that
   works because `noConfusion` for different constructors produces
   `False` from the assumed equality — no tactic block needed.
   Elsewhere in the codebase, cross-constructor disjointness is handled
   by `cases` or `contradiction` inside tactic blocks.

6. **Array ↔ List bridge via `congrArg Array.mk` / `congrArg Array.toList`.**
   The nesting of `YamlValue` inside `Array` forces the proof to reason
   about `List` equality (where structural recursion is available) and
   then lift back to `Array`.  The idiom pair:
   - Forward:  `cases items₁; cases items₂; exact congrArg Array.mk hi`
   - Backward: `exact hi (congrArg Array.toList h.2.1)`

   relies on `Array.toList a = a.data` being definitional.  This bridge
   pattern does not appear in any other proof file.  It was discovered
   during development when `Array.ext_iff` proved too heavy and `simp`
   could not close the gap automatically.

7. **Boolean→Prop lifting + `split` + `absurd rfl` for `Char`-match branches.**
   The `collectChars` char-step lemmas require discharging goals like
   "if `c ≠ '"'`, then the `match c with | '"' => ...` branch is not taken."
   Lean's `match` on `Char` literals produces goals where the discriminant
   is propositional equality, but the hypotheses arrive as Boolean
   `(c == '"') = false`.  The new three-step idiom:
   ```
   have hne_dq : c ≠ '"' := by intro h; subst h; simp at hc_not_dq
   split
   · exact absurd rfl hne_dq
   ```
   converts the Boolean hypothesis to `≠`, then uses `split` to case-
   split the `match`, and `absurd rfl hne_dq` to close the contradictory
   branch (since in that branch Lean has unified `c` with `'"'`, making
   `rfl : '"' = '"'` available, which contradicts `hne_dq`).

   This idiom was **not** needed elsewhere because other `match`-on-Char
   proofs (e.g., `EscapeResolution.lean`, `SchemaResolution.lean`) work
   on concrete characters rather than universally quantified `c`.
   When the character is concrete, `simp` or `decide` closes the goal
   directly.

8. **`show`/`change` to bridge `BEq.beq` ↔ explicit function name.**
   When a struct's `BEq` instance is defined as `instance : BEq Foo := ⟨beqFoo⟩`,
   the goal after `unfold BEq.beq` has shape `instBEqFoo.1 a b = true`,
   not `beqFoo a b = true`.  A subsequent `unfold beqFoo` fails because
   the term structure doesn't match.  The fix is:
   - Goals: `show beqFoo _ _ = true` (Lean accepts via definitional equality)
   - Hypotheses: `change beqFoo _ _ = true at h`
   
   This bridges to the transparent function name so that `unfold beqFoo`
   and `simp` work as expected.  Used throughout `LawfulBEq.lean` for
   both `Scalar` and `YamlValue` proofs.

9. **Manual `@[simp]` equational lemmas for `brecOn`-compiled functions.**
   When a function compiles via `brecOn` (Lean's below-recursion
   compilation for nested inductives), no auto-generated equational
   theorems are produced.  The workaround is to write manual `@[simp]`
   lemmas covering every constructor pair, each proved by `rfl`.  For
   `beqYamlValue`, this required 24 lemmas (4 same-constructor +
   12 cross-constructor + 4 list + 4 pair-list).  These lemmas are
   essential for the `simp`-based proofs in `beqYamlValue_rfl` and
   `beqYamlValue_eq`.

#### Unexpected challenges (continued — v0.2.1)

- **`deriving BEq` generates opaque functions for recursive inductives.**
  Unlike `DecidableEq` (which silently fails), `deriving BEq` for
  `YamlValue` *succeeds* but produces an opaque function that blocks
  all proof tactics — `unfold`, `simp`, `rfl` all fail.  The only
  fix is replacing with an explicit transparent definition.

- **`Decidable.rec` in derived `BEq` for structs with `String` fields.**
  `Scalar` has a `value : String` field.  The auto-derived `BEq`
  compares it via `Decidable.rec` on the `DecidableEq String` instance,
  but `cases` tactic fails on `Decidable.rec` goals with "dependent
  elimination failed, stuck at motive."  An explicit `beqScalar` using
  `s₁.value == s₂.value` avoids this entirely because `==` reduces
  to `BEq.beq` on `String`, which *is* transparent.

- **`induction` fails on nested inductives.**  `YamlValue` contains
  `Array YamlValue` fields, making it a nested inductive.  The
  `induction` tactic errors with "does not support nested inductive
  type."  The workaround — explicit pattern matches with `where`-clause
  helpers — is the same structure used for `decEqYamlValue` and
  `beqYamlValue` itself.

#### Unexpected challenges

- **`deriving DecidableEq` fails silently on nested `Array`.**  Lean 4
  does not error on `deriving DecidableEq` for `YamlValue` — it simply
  doesn't produce an instance, leaving downstream uses to fail with
  an opaque "failed to synthesize" message.  This was the original
  motivation for the manual proof.

- **`List.noConfusion` does not unify at the expected type.**  An early
  attempt at the nil-vs-cons `isFalse` case used
  `isFalse List.noConfusion`, but `List.noConfusion` has extra type
  parameters that prevent it from unifying with `¬ [] = x :: xs`.
  The fix is `isFalse (fun h => by cases h)`, which is slightly more
  verbose but always works.

- **`simp` cannot drive `match c with | '"' => ...` when `c` is
  universally quantified.**  Initial attempts tried
  `simp only [hc_not_dq, ...]` expecting `simp` to rewrite the `match`
  branches.  This failed because the `match` compiles to nested
  `ite`-like terms on `Char` equality that `simp` does not reduce.
  The workaround (Boolean→Prop lift + `split` + `absurd`) added ~4
  lines per branch but is robust.

- **`‹_›` (assumption) cannot synthesize `rfl` in `absurd ‹_› hne`.**
  After the `split` tactic narrows to a branch where `c = '"'`,
  one might expect `absurd ‹'"' = '"'› hne_dq`.  But `‹_›` looks for
  an existing hypothesis, and `rfl` is not a hypothesis — it is a
  term.  Using `absurd rfl hne_dq` directly works.

#### Unexpected simplifications

- **`DecidableEq YamlDocument` was trivial** once `DecidableEq YamlValue`
  was in scope.  All component types (`Directive`, `String`, `Array`)
  already had instances, so the proof is a three-line `if`-chain.

- **Fuel-zero base cases are one-liners.**  The `collectChars_zero` lemmas
  (fuel = 0 returns the accumulator) required only `unfold` + `simp`
  with a single combinator lemma.  The parser's uniform fuel-dispatch
  pattern (`| 0, acc => ...`) makes these structurally identical for
  every loop.

- **Termination composition collapsed to `omega` / `Nat.lt_trans`.**
  The four composition theorems were expected to require reasoning about
  `Stream.remaining` internals; instead, they are pure `Nat` statements
  that `omega` solves in <1ms, because the actual stream arithmetic
  is already encapsulated by the existing `remaining` abstraction.

#### Unexpected simplifications (continued — v0.2.1)

- **All 24 equational lemmas for `beqYamlValue` are `rfl`.**  Despite
  `beqYamlValue` compiling via `brecOn`, every same-constructor,
  cross-constructor, and list-helper reduction holds by definitional
  equality.  No tactic unfolding needed — Lean's kernel evaluates the
  match in each case.

- **Enum `LawfulBEq` instances are one-liners.**  `cases a <;> cases b <;> decide`
  handles both `rfl` and `eq_of_beq` for `ScalarStyle`, `ChompStyle`,
  and `CollectionStyle`.  The finite case count (3–4 constructors each)
  makes `decide` fast.

- **`beq_self_eq_true` replaces the non-existent `LawfulBEq.rfl`.**
  The standard library's name for `(a == a) = true` is `beq_self_eq_true`,
  not `LawfulBEq.rfl` as one might guess.  Once discovered, it simplified
  the `beqYamlValue_rfl` proof's `simp` calls significantly.

### 4b. Closing the fold-combinator gap — COMPLETED _(historical — lean4-parser era)_

> **Historical note:** §4b–§4j document proof techniques developed for the
> lean4-parser combinator pipeline (Phases 1–9).  This pipeline was removed
> in Phase 10 and replaced by the self-contained tokenized pipeline.  These
> sections are retained as reference for the proof idioms, which may be
> applicable to future work.

The fold-combinator gap described in the pre–Phase 10 §2 has been **closed** by adding
upstream lemmas to [lean4-parser](https://github.com/NicolasRouquette/lean4-parser)
(commit `8cfc6ac`, branch `std-iterators`).  The key challenge was that
`efoldlPAux` — the WF-recursive loop backing `foldl`/`dropMany`/`count`
— is a `private def`, making it inaccessible from downstream code.

#### Lemmas added to `Parser/Parser.lean`

| Lemma | Purpose |
|---|---|
| `efoldlPAux_eq` | One-step unfolding of the private WF loop for `m = Id` |
| `efoldlPAux_inhabited_irrel` | `Inhabited` instances don't affect computation |
| `foldl_eq` | One-step recursive equation for `foldl` (pure fold) |

The `efoldlPAux_inhabited_irrel` lemma was the crucial innovation:
`efoldlP` creates fresh `[Inhabited ε] [Inhabited σ] [Inhabited β]`
instances at each call via `have`, but `efoldlPAux` is WF-recursive
and preserves the *original* instances throughout.  Reconnecting
a recursive `foldl` call (which creates new instances) to the
in-flight `efoldlPAux` (which has old instances) required proving
that `efoldlPAux` is independent of which `Inhabited` instances are
supplied.  The proof is by WF induction using `split`-based case
analysis on `p s` / `f y x s'` / `if consuming`.

#### Lemmas added to `Parser/Basic.lean`

| Lemma | Purpose |
|---|---|
| `dropMany_eq` | One-step equation: `dropMany p s = match p s with ...` |
| `count_eq` | One-step equation: `count p s = match p s with ...` |

Both are direct corollaries of `foldl_eq` composed with the
definition (`dropMany = foldl (const α) .unit p`,
`count = foldl (fun n _ => n+1) 0 p`).

#### Proof structure for `foldl_eq`

```
foldl → efoldl → efoldlM → efoldlP → efoldlPAux
                                       ↓ (one-step via efoldlPAux_eq)
                           match p s with
                           | ok s' x → if consuming then efoldlPAux(old_inst) ... else .ok
                           | error → .ok (backtrack)
                                       ↓ (efoldlPAux_inhabited_irrel)
                           match p s with
                           | ok s' x → if consuming then foldl(new_inst) ... else .ok
                           | error → .ok (backtrack)
```

The `foldl_eq` proof uses `by_cases` on the consuming condition with
`simp only [dif_pos h]` / `simp only [dif_neg h]` to reduce the `dite`,
followed by `congr 1; congr 1; exact efoldlPAux_inhabited_irrel ..`
in the consuming branch.

### 4b′. Reflections on §4b — proof idioms, challenges, simplifications

#### New proof idioms introduced in §4b

1. **`rw [f]` for one-step WF unfolding (vs. `unfold f`).**
   The WF-recursive `efoldlPAux` cannot be unfolded with `unfold`
   from inside the same file — `unfold efoldlPAux` expands *all*
   recursive calls, leaving an unsolvable mess.  The `rw [efoldlPAux]`
   tactic rewrites exactly one occurrence (the outermost call) because
   `rw` applies the equation lemma that Lean generates for WF
   definitions.  This single-step rewrite is the foundation of every
   fold lemma.  The distinction `rw` (one occurrence) vs. `unfold`
   (all occurrences) was not needed in §4a proofs, which only dealt
   with non-recursive combinator definitions.

2. **Explicit `@`-applied Inhabited instances for `rw`.**
   The `efoldlPAux_eq` theorem requires `[Inhabited ε] [Inhabited σ]
   [Inhabited β]`, but inside `foldl_eq` these instances don't exist
   in the tactic context — they are created locally inside `efoldlP`
   via `have`.  The workaround is to supply them explicitly:
   ```
   rw [@efoldlPAux_eq _ _ _ _ _ _ _
       ⟨Error.unexpected (Stream.getPosition s) none⟩ ⟨s⟩ ⟨init⟩]
   ```
   This "@-with-anonymous-constructor" pattern — threading freshly
   constructed typeclass instances through `@` — does not appear in
   any §4a proof.  It arises because `efoldlP`'s `have` bindings
   create instances that are invisible to downstream tactics.

3. **Instance-irrelevance by WF recursion + `split` cascade.**
   The `efoldlPAux_inhabited_irrel` proof shows that `efoldlPAux`
   computes the same result regardless of which `Inhabited` instances
   are supplied.  The proof is by `termination_by Stream.remaining s`
   with a body that `rw`s both sides to their one-step expansions,
   then uses a cascade of `split` (three levels: match `p s`, match
   `f y x s'`, if consuming) to align the branches.  In the
   recursive (consuming) branch, the inductive hypothesis closes the
   gap; all other branches are `rfl`.  This "parallel split cascade"
   pattern — rewriting two sides of an equation to matching case trees
   and closing leaf-by-leaf — is new to §4b.

4. **`congr 1; congr 1; exact irrel ..` to bridge nested wrappers.**
   After unfolding `foldl` on both sides, the LHS and RHS agree
   everywhere except deep inside a `match`-of-`match` chain where
   `efoldlPAux` appears with different `Inhabited` instances.
   Rather than deconstructing the entire chain, `congr 1` peels off
   one layer of `match` / `Prod.fst <$>` at a time until the
   `efoldlPAux` terms are exposed, then `exact irrel ..` finishes.
   This telescoping `congr` approach avoids `simp` entirely in the
   recursive branch.

5. **`show (foldl ...) s = _; rw [foldl_eq]` for corollary lemmas.**
   The `dropMany_eq` and `count_eq` proofs use `show` to restate the
   goal with the definition inlined, then `rw [foldl_eq]` to apply
   the one-step equation.  This is necessary because `simp only
   [dropMany, foldl_eq]` would loop — `foldl_eq` is a recursive
   equation, so `simp` keeps rewriting indefinitely.  The pattern
   `show ⟨defn inlined⟩; rw [recursive_eq]; simp [reduce]; cases <;> rfl`
   is a reusable template for any combinator defined as
   `foldl f init p`.

6. **`by_cases h : ...; simp only [dif_pos h]` / `[dif_neg h]` for
   decidable `if`.**
   The `foldl_eq` proof encounters `if _h : remaining s' < remaining s`
   — a `dite` (decidable if-then-else).  Neither `split` nor `cases`
   cleanly handles `dite` when the branches contain further matches.
   The `by_cases` + `dif_pos`/`dif_neg` pair provides surgical control:
   `by_cases` introduces the proposition as a hypothesis, then
   `dif_pos`/`dif_neg` reduces the `dite` in the goal.  This is
   cleaner than the `split`-based approach used in §4a for `ite`,
   because `dite` binds the proof term in the branch body.

7. **`cases hp : p s <;> rfl` to close match-mismatch after `rw`.**
   After `rw [foldl_eq]`, both sides of `dropMany_eq` and `count_eq`
   contain `match p s with ...` but with structurally different
   `casesOn` encodings (`rw` introduces one `match`; the goal's RHS
   has another from the theorem statement).  `rfl` alone fails because
   the two `match` expressions are not definitionally equal.
   `cases hp : p s` substitutes `p s` in *both* sides simultaneously,
   collapsing each `match` to its concrete branch, after which `rfl`
   succeeds.  The ` <;> ` combinator applies `rfl` to all branches.

#### Unexpected challenges

- **`private def` is an absolute barrier from downstream.**
  `efoldlPAux` is `private def` in `Parser/Parser.lean`, meaning
  `unfold Parser.efoldlPAux`, `simp only [Parser.efoldlPAux]`, and
  even `rw [Parser.efoldlPAux]` all fail from any other file.  The
  name is not exported, period.  This forced the entire §4b effort
  to be implemented *upstream* in the lean4-parser fork rather than
  in lean4-yaml-verified.  An exploration file (`FoldSpecs_explore.lean`)
  was used to confirm the barrier before committing to the upstream
  approach.

- **`unfold efoldlPAux` expands all recursive calls, not just the outermost.**
  Even from *within* `Parser.lean`, `unfold efoldlPAux` expands
  every occurrence — including recursive calls inside the `if consuming`
  branch — producing a goal with nested `efoldlPAux._unary` applications
  that `rfl` cannot close.  The fix was `rw [efoldlPAux]`, which rewrites
  exactly one occurrence using the WF equation lemma.  This `rw` vs.
  `unfold` distinction for WF-recursive functions was not documented
  anywhere and was discovered experimentally.

- **`Inhabited` instances created by `have` in `efoldlP` are invisible
  to downstream tactics.**
  `efoldlP` wraps `efoldlPAux` with three `have` bindings:
  ```lean
  have : Inhabited β := ⟨init⟩
  have : Inhabited σ := ⟨s⟩
  have : Inhabited ε := ⟨Error.unexpected (Stream.getPosition s) none⟩
  efoldlPAux f p init s
  ```
  After `simp` unfolds `efoldlP`, the tactic state contains
  `efoldlPAux` applied with these three anonymous instances.  But
  `rw [efoldlPAux_eq]` fails because it tries to synthesize
  `[Inhabited ε]` etc. from the tactic context, where they don't
  exist.  The workaround — passing explicit instances via `@` — was
  the most time-consuming discovery of §4b.

- **Recursive branch of `foldl_eq` has mismatched Inhabited instances.**
  After one step of unfolding, the LHS contains `efoldlPAux` with
  instances from the *outer* call (`init`, `s`), while the RHS
  (after expanding `foldl (f init x) s'`) contains `efoldlPAux` with
  instances from the *inner* call (`f init x`, `s'`).  These are
  syntactically different terms, so `rfl` fails.  The
  `efoldlPAux_inhabited_irrel` lemma was invented specifically to
  bridge this gap — it was not anticipated at the outset.

- **`norm_num` is not available in lean4-parser.**
  The `count_eq` proof needs to reduce `0 + 1` to `1`.  The natural
  choice `norm_num` is not imported in lean4-parser (it lives in
  Mathlib/Batteries).  The fix was `simp only [Nat.zero_add]`.

- **`split` on `match` doesn't substitute in both sides of an equation.**
  After `rw [foldl_eq]`, the LHS has one `match p s` encoding and
  the RHS has another.  `split` case-splits only the LHS match,
  leaving the RHS match intact, so `rfl` fails.  Using
  `cases hp : p s` instead substitutes `p s = .ok s' x` in both
  sides, making both matches reduce.

#### Unexpected simplifications

- **`dropMany_eq` and `count_eq` are three-liners.**
  Once `foldl_eq` was proved, the corollary lemmas required only
  `show; rw [foldl_eq]; simp [...]; cases <;> rfl`.  The entire
  §4b effort reduced to proving **one** hard theorem (`foldl_eq`)
  plus one supporting lemma (`efoldlPAux_inhabited_irrel`);
  everything else composed trivially.

- **`simp only []` (empty argument list) reduces iota-redexes.**
  In `efoldlPAux_eq`, after `cases hp : p s | ok s' x =>`,
  the goal contains `match .ok s' x with | .ok s' x => ...`
  which is a known-constructor match (iota-redex).  `simp only []`
  — with no arguments — reduces it.  This is lighter than `simp`
  (which might loop) or `rfl` (which requires full definitional
  equality).  The same trick was discovered independently in §4a
  for `collectChars` proofs.

- **`efoldlPAux_inhabited_irrel` proof is structurally identical to
  `efoldlPAux_eq`.**  Both use `rw [efoldlPAux_eq]; split; split;
  split; <recursive-or-rfl>`.  The irrel proof just does this on
  both sides simultaneously.  The structural parallel made the proof
  straightforward once the approach was identified.

- **The 5-layer fold chain (`foldl → efoldl → efoldlM → efoldlP →
  efoldlPAux`) collapses in one `simp only` call.**
  All intermediate definitions (`efoldl`, `efoldlM`, `efoldlP`) are
  `@[inline]` and consist of pure monadic plumbing.  A single
  `simp only [foldl, efoldl, efoldlM, efoldlP, Functor.map, bind,
  Bind.bind, pure, Pure.pure, monadLift, MonadLift.monadLift]`
  collapses all five layers to a bare `efoldlPAux` call.  The feared
  complexity of reasoning through five levels of abstraction turned
  out to be a non-issue for `m = Id`.

- **`termination_by Stream.remaining s` suffices for
  `efoldlPAux_inhabited_irrel`.**
  The irrel lemma is proved by structural recursion that mirrors
  `efoldlPAux` itself.  Lean 4 accepts the same `termination_by`
  clause because the recursive call occurs in the `split` branch
  where `remaining s'' < remaining s` is in scope as a hypothesis
  (`‹_›` or the `split` discriminant).

### 4c. B3 block scalar specs — first batch (11 lemmas) — COMPLETED

Added 11 sorry-free specification theorems for the `literalScalar`
and `foldedScalar` block scalar pipeline (commit `07e05f8`).

#### Pure function specs (§7)

| Lemma | Technique |
|---|---|
| `applyChomp_strip` | `rfl` |
| `applyChomp_clip` | `rfl` |

#### `processFolded.go` case analysis (§7.1)

| Lemma | Technique |
|---|---|
| `processFolded_go_nil` | `unfold; rfl` |
| `processFolded_go_singleton_first` | `unfold; simp` |
| `processFolded_go_singleton_nonempty` | `unfold; simp [h]` |
| `processFolded_go_singleton_empty` | `unfold; simp [String.isEmpty]` |

#### `blockScalarContent.collectLines` loop specs (§8.3.1)

| Lemma | Technique |
|---|---|
| `blockCollectLines_zero` | `rfl` |
| `blockCollectLines_no_match` | `show` + `simp only [bind_eq, h, pure_eq]` |
| `blockCollectLines_first_step` | `show` + `simp only [bind_eq, h, ite_true]` |
| `blockCollectLines_cont_step` | `show` + `simp only [bind_eq, h]` + `rfl` |

#### `autoDetectIndent` base case (§8.3.2)

| Lemma | Technique |
|---|---|
| `autoDetectIndent_loop_zero` | `rfl` |

### 4c′. Reflections on §4c — proof idioms, challenges, simplifications

#### New proof idioms introduced in §4c

1. **`show (do ...) s = _` to bypass equation lemma generation for
   where-clause functions.**
   The `collectLines` where-clause function in `blockScalarContent`
   triggers a hard 200,000-heartbeat whnf limit when `unfold` attempts
   to generate its equation lemma.  Unlike the `maxHeartbeats` option
   (which controls the tactic timeout), this whnf limit is
   non-configurable in Lean 4.28.  The workaround:
   ```lean
   show (do
     match ← Parser.option? (...) with
     | some line => ...
     | none => return acc) s = _
   ```
   converts the LHS to the expanded do-notation body by **definitional
   equality** — no equation lemma is generated because `show` merely
   changes the expected type.  After `show`, ordinary `simp only`
   closes the goal.  This is the single most important technique
   discovered in §4c and is expected to be the standard approach for
   all fuel-bounded where-clause loop proofs going forward.

2. **`ite_true` / `ite_false` simp lemmas for Boolean-to-Prop `if`.**
   In Lean 4, `if true then a else b` elaborates to
   `if (true = true) then a else b`, i.e., `@ite _ (True) _ a b`.
   Plain `rfl` cannot reduce this (it is not a definitional equality).
   The `ite_true` simp lemma from Mathlib/core reduces
   `@ite _ True _ a b` to `a`.  Similarly `if false then ...` elaborates
   to `if (false = true) then ...` which is `@ite _ False _ a b` —
   but this *is* definitionally `b` in Lean 4.28, so `rfl` suffices.
   The asymmetry (`ite_true` needed, `rfl` works for false) was
   unexpected.

3. **`rfl` for fuel-zero base cases of where-clause loops.**
   For simple where-clause functions whose fuel-zero branch is
   `| 0, acc, _ => return acc`, the entire theorem
   `collectLines indent 0 acc first s = .ok s acc` is provable by
   plain `rfl`.  No `unfold` is needed — the fuel-zero branch is
   a definitional equality.  This was discovered for
   `blockCollectLines_zero` and `autoDetectIndent_loop_zero`, both
   of which had initially used `unfold; simp` before being simplified.

#### Unexpected challenges

- **`unfold blockScalarContent.collectLines` exceeds 200,000 heartbeat
  whnf limit — `set_option maxHeartbeats` does NOT help.**
  The equation lemma generation for `collectLines` (a where-clause
  function inside `blockScalarContent`, which itself contains
  `blockScalarLine` and `takeLineContent` where-clauses) triggers a
  hard whnf limit.  Setting `set_option maxHeartbeats 800000` does
  not override this — the 200,000 limit is in the kernel's whnf
  reduction, not the tactic heartbeat counter.  This was the single
  biggest obstacle in §4c and forced the invention of the `show`
  technique (idiom #1 above).

- **`delta` expands through `Nat.brecOn.go` / `Nat.rec`.**
  An early attempt used `delta blockScalarContent.collectLines` to
  avoid the equation lemma.  While `delta` doesn't trigger equation
  lemma generation, it expands the definition to its core-level
  encoding, which includes `Nat.brecOn.go`, `Nat.rec`, and
  `PSigma.casesOn` terms.  `simp` cannot reduce these back to the
  user-facing `match` form, making the approach unusable for
  fuel+1 cases (fuel-zero works because the result is definitional).

- **`option?` position-restoration semantics.**
  `option?` on failure returns `Stream.setPosition s' (Stream.getPosition s)`,
  where `s'` is the stream state after the sub-parser ran (and failed).
  For `YamlStream`, `setPosition` only restores `startPos`/`line`/`col`
  from the position — it does **not** restore `str`, `stopPos`,
  `anchorMap`, `validationError`, or `tagHandles`.  Therefore
  `setPosition s' (getPosition s) ≠ s` if the sub-parser modified
  non-position state (e.g., set a validation error).  The initial
  `blockCollectLines_no_match` theorem hypothesized `blockScalarLine`
  failure directly, but the correct approach is to hypothesize on the
  `option?` result `s_out`, which correctly captures the post-restoration
  state.

#### Unexpected simplifications

- **`processFolded.go` unfolds cleanly (unlike `collectLines`).**
  `processFolded.go` is a structurally recursive function on `List String`
  (not fuel-bounded), and its equation lemma generates without hitting
  any heartbeat limit.  Plain `unfold Lean4Yaml.Parse.processFolded.go`
  works, followed by `rfl` or `simp`.  The heartbeat issue is specific
  to fuel-bounded where-clause functions in large parser definitions.

- **`applyChomp` cases are definitional (`rfl`).**
  All three `applyChomp` cases (`.keep`, `.strip`, `.clip`) are closed
  by `rfl` — no `unfold` needed.  This is because `applyChomp` is a
  simple `match` on an inductive type with no recursive structure.

- **`blockCollectLines_cont_step` closes with `simp + rfl`.**
  `if false then line else acc ++ "\n" ++ line` elaborates to
  `if (false = true) then ...` which is `@ite _ False _ ...` —
  definitionally equal to the `else` branch.  So after `simp only`
  eliminates the monadic plumbing, `rfl` closes the remaining
  `@ite _ False _ line (acc ++ "\n" ++ line) = acc ++ "\n" ++ line`.
  No `ite_false` simp lemma is needed (unlike the `ite_true` case).

- **`String.isEmpty` needs explicit `simp [String.isEmpty]`.**
  In `processFolded_go_singleton_empty`, the hypothesis is the
  concrete string `""`.  Plain `simp` cannot reduce `"".isEmpty` to
  `true` — it needs `simp [String.isEmpty]` to unfold the definition.
  This is a minor footgun but consistent: `String.isEmpty` is not
  a `@[simp]` lemma in core Lean 4.

### 4d. B3 block scalar specs — second batch (7 lemmas) — COMPLETED

Added 7 sorry-free specification theorems for the block scalar
pipeline's indentation detection and content machinery (commit `3cc6569`).

#### `currentCol` and `autoDetectIndent.loop` step specs (§8.3.2)

| Lemma | Technique |
|---|---|
| `currentCol_eq` | `unfold; simp` |
| `autoDetectIndent_loop_blank_line` | `show` + `simp` |
| `autoDetectIndent_loop_content_ge` | `show` + `simp` + `rfl` |
| `autoDetectIndent_loop_content_lt` | `show` + `simp` + `rfl` |

#### `consumeIndent` specs (§8.3.3)

| Lemma | Technique |
|---|---|
| `consumeIndent_no_tab` | `unfold; simp` |
| `consumeIndent_tab_drop_ok` | `unfold; simp` |

#### `blockScalarContent` top-level (§8.3.4)

| Lemma | Technique |
|---|---|
| `blockScalarContent_eq` | `unfold; simp` |

### 4e. B3 block scalar specs — third batch (5 lemmas) — COMPLETED

Added 5 sorry-free specification theorems completing all three
`blockScalarLine` branches plus the `autoDetectIndent` top-level
decomposition and a `processFolded` identity case (commit `55869c0`).

#### `blockScalarLine` branch specs (§8.3.1a)

| Lemma | Technique |
|---|---|
| `blockScalarLine_blank` | `show` + `simp` |
| `blockScalarLine_content` | `show` + `simp [Bool.false_eq_true]` |
| `blockScalarLine_under_indented_blank` | `show` + `simp [ite_true]` |

#### `autoDetectIndent` top-level (§8.3.5)

| Lemma | Technique |
|---|---|
| `autoDetectIndent_eq` | `unfold; rfl` |

#### `processFolded` additional case (§8.3.6)

| Lemma | Technique |
|---|---|
| `processFolded_single_line` | `unfold; simp` |

### 4e′. Reflections on §4d–§4e — proof idioms, challenges, simplifications

#### New proof idioms introduced in §4d–§4e

1. **`Bool.false_eq_true` + `ite_false` for Bool-to-Prop `if` on
   false branch.**
   In §4c we discovered that `if true then ...` needs `ite_true`.
   In §4e we found the *symmetric* case: after `simp` resolves a
   `lookAhead` returning `false`, the goal contains
   `if false = true then ... else ...`.  Lean *does not* reduce
   `false = true` to `False` automatically — it stays as a
   propositional equality.  The two-lemma combination
   `Bool.false_eq_true` (rewrites `false = true` to `False`) +
   `ite_false` (reduces `@ite _ False _ a b` to `b`) is needed.
   However, when the `if` condition is literally `true = true`
   (not `false = true`), mere `ite_true` suffices because `simp`
   can handle `true = true ↔ True` internally.  This asymmetry
   extends the §4c observation: the full picture is:

   | Condition | Needed simp lemmas |
   |---|---|
   | `if true then a else b` | `ite_true` |
   | `if false then a else b` | `Bool.false_eq_true` + `ite_false` |

   In practice, the false branch often *doesn't* need these lemmas
   because subsequent `simp` arguments (e.g., a hypothesis binding
   the lookAhead result) consume it first.  But when the `ite`
   is the outermost term in the goal, both are required.

2. **Type annotations for `do` blocks in hypotheses:
   `(lookAhead ((do ...) : YamlParser Bool))`.**
   When a theorem's hypothesis involves `lookAhead` applied to a
   `do` block, Lean cannot infer the monad because the hypothesis
   is outside any monadic context.  The fix:
   ```lean
   (h : (lookAhead ((do
       skipHWhitespace
       let col ← currentCol
       ...) : YamlParser Bool)) s = .ok s' result)
   ```
   The `: YamlParser Bool` annotation inside the parentheses gives
   Lean the monad (`ParserT ...`) and the return type (`Bool`).
   Without it, Lean emits `invalid 'do' notation, expected type
   is not a monad application`.  This issue does *not* arise inside
   the `show (do ...) s = _` proof body because there the expected
   type is already `YamlParser _ s = _`.

3. **Named wildcards for `_` in theorem parameters.**
   Lean resolves all parameter types (including holes `_`) *before*
   entering the proof body.  A hypothesis like
   `(h : lookAhead anyToken s = .ok s' _)` fails with "don't know
   how to synthesize placeholder" because `_` in the theorem
   statement is elaborated at declaration time, not proof time.
   The fix is to name the wildcard:
   ```lean
   (ch : Char)
   (h : lookAhead anyToken s = .ok s' ch)
   ```
   This was already known for value-level `_` but had not been
   triggered in §4c because all earlier hypotheses used concrete
   types (`()`, `none`, `some ()`).

4. **`autoDetectIndent_eq` via `unfold; rfl` — no `show` needed.**
   Unlike the where-clause functions (`collectLines`, `blockScalarLine`)
   that trigger the 200k heartbeat whnf limit, `autoDetectIndent` is a
   top-level `def` whose body is just `lookAhead do ...`.
   `unfold autoDetectIndent` generates the equation lemma without
   any heartbeat issue, and `rfl` closes the goal.  The `show`
   technique is only needed for *where-clause functions* inside
   large parser definitions.  Top-level definitions, even when they
   contain `do` blocks and `lookAhead`, unfold normally.

#### Unexpected challenges

- **`simp` argument ordering matters for Bool-to-Prop `ite` goals.**
  For `blockScalarLine_content`, the goal after `show` contains
  `if false = true then ...`.  Supplying `Bool.false_eq_true` and
  `ite_false` in the simp argument list works, but the order must
  be: `Bool.false_eq_true` first (to rewrite the condition to `False`),
  then `ite_false` (to reduce `@ite _ False`).  If `ite_false` comes
  first, `simp` doesn't see `False` in the condition and the lemma
  is unused.  In practice, `simp` resolves the order automatically,
  but the linter reports "unused simp argument" if `ite_false` is
  listed without `Bool.false_eq_true`.

- **Unused simp args in `blockScalarLine_under_indented_blank`.**
  Early versions included `h_skip`, `h_opt_nl`, and `ite_true` as
  simp args.  After `simp` resolves `h_under` (which establishes
  `true = true` in the lookAhead result), the remaining bind/pure
  chain is consumed by `h_no_blank` + `h_under` alone — the
  subsequent hypotheses for `skipHWhitespace` and `option? newline`
  are not needed by `simp`.  This suggests the Bool condition
  reduction "short-circuits" the remainder of the goal.  The final
  proof uses only `[ParserSpecs.bind_eq, h_no_blank, h_under,
  ite_true, h_skip, h_opt_nl, ParserSpecs.pure_eq]`.

#### Unexpected simplifications

- **`autoDetectIndent.loop` step cases reuse the `show` template exactly.**
  All three step cases (`blank_line`, `content_ge`, `content_lt`)
  use the identical proof skeleton:
  ```lean
  show (do
    let col ← currentCol
    let spaces ← count (token ' ')
    let totalCol := col + spaces
    match ← option? newline with
    | some _ => autoDetectIndent.loop minIndent fuel (max maxBlankSpaces totalCol)
    | none =>
      if totalCol >= minIndent then ...
      else return minIndent) s = _
  simp only [ParserSpecs.bind_eq, h₁, h₂, ...]
  ```
  The template from §4c for `collectLines` transferred with zero
  modification.  The three cases differ only in which hypotheses
  appear in the `simp only` argument list.

- **`consumeIndent` unfolds cleanly despite being a `where`-clause.**
  Unlike `collectLines` and `blockScalarLine`, `consumeIndent` is
  defined at the top level in `Scalar.lean` (not nested inside
  another parser), so its equation lemma generates without hitting
  heartbeat limits.  Plain `unfold consumeIndent; simp only [...]`
  works.  The whnf heartbeat issue is specific to where-clause
  functions inside large enclosing definitions where the equation
  lemma generator must traverse the entire parent definition body.

- **`blockScalarContent_eq` is a two-liner.**
  The top-level decomposition of `blockScalarContent` into
  `getStream` + `collectLines` required only
  `unfold blockScalarContent; simp only [bind_eq, getStream_eq]`.
  The `getStream` → fuel extraction is structurally identical to the
  pattern in `blockSequence_spec` and `blockMapping_spec`.

### 4f. B3 batch 4: processFolded.go cons-cases + pipeline (8 lemmas) — COMPLETED

Commit `4adba9e`.  Extends the `processFolded.go` structural recursion
specs with the multi-element (cons–cons) cases:

| Theorem | Description |
|---|---|
| `processFolded_go_cons_first` | first=true cons → recurse with acc:=line |
| `processFolded_go_cons_empty` | empty line → push newline to acc |
| `processFolded_go_cons_more_indented` | space-leading → preserve newline |
| `processFolded_go_cons_fold` | normal line → fold with space |
| `takeLineContent_eq` | relational spec via rfl |
| `processFolded_eq` | decomposition (splitOn + go) |
| `blockScalar_literal_processing` | style dispatch literal → identity |
| `blockScalar_folded_processing` | style dispatch folded → processFolded |

**Key proof technique:** `show LHS = _; rw [processFolded.go]` with
focused goals (`· simp; · exact fun h => absurd h (List.cons_ne_nil _ _)`)
to close side conditions from the equation lemma's structural recursion
case split.

### 4g. B4 + B1 batch 5: fuel-zero + character predicates (30 lemmas) — COMPLETED

Commit `3ee4aef`.  Systematic coverage of two new fronts:

**§8.7 — Collection fuel-zero (9 theorems):** Every fuel-bounded
collection parser now has a proved fuel-zero base case:
`flowSequenceImpl_zero`, `flowMappingImpl_zero`,
`flowSequenceItemsImpl_zero`, `flowMappingEntriesImpl_zero`,
`flowMappingEntryImpl_zero`, `blockSequenceImpl_zero`,
`blockMappingImpl_zero`, `blockSequenceItemsImpl_zero`,
`blockMappingEntriesImpl_zero`.

**§8.8 — Character predicate specs (21 theorems):** Concrete
evaluation lemmas for `isLineBreak`, `isWhiteSpace`,
`isFlowIndicator`, `isPlainSafe`, and `canStartPlainScalar`
on representative characters, all via `native_decide`.

### 4h. Batch 5b + 6: remaining fuel-zero + under-indented + more predicates (20 lemmas) — COMPLETED

Commits `f458ff0`, `55dcb55`.

**§8.9 — Remaining fuel-zero (7 theorems):** Completes the fuel-zero
coverage for all 16 fuel-bounded parser functions:
`dispatchByCharImpl_zero`, `blockValueImpl_zero`,
`blockValueSameLineImpl_zero`, `blockMappingEntryImpl_zero`,
`blockMappingKeyImpl_zero`, `detectMappingKeyImpl_zero`,
`flowValueImpl_zero`.

**§8.10 — Block collection under-indented (2 theorems):**
When the detected indentation is below `minIndent`, block
sequence/mapping return `none` immediately:
`blockSequenceImpl_under_indented`, `blockMappingImpl_under_indented`.

**§8.11 — Additional character predicates (11 theorems):**
`isIndicator` (6 chars), `isForbiddenPlainStart_eq` (refl with
`isIndicator`), `isAnchorChar` (4 chars).

### 4i. Batch 7: deeper B2 escape/fold specs (21 lemmas) — COMPLETED

Commit `44a083d`.

**§8.1.2 — Escape processing (16 theorems):** Concrete evaluation of
`doubleQuotedScalar.processEscape` for all 16 simple escape characters:
`\n`, `\t`, `\\`, `\"`, `\0`, `\r`, `\ `, `\/`, `\a`, `\b`, `\v`,
`\f`, `\e`, `\N`, `\_`, and literal tab.  Each proved via
`unfold; simp [pure_eq]`.

**§8.1.3 — Backslash escape relay (1 theorem):**
`doubleQuoted_collectChars_backslash_escape` — when `\` + non-linebreak
char, delegates to `processEscape` and recurses.  Proved via
`split <;> simp_all [bind_eq]` to handle the 3-way char match.

**§8.1.4 — Fold loop base (1 theorem):**
`foldQuotedNewlines_loop_zero` — fuel-zero returns `.folded result`.

**§8.1.6–§8.1.7 — Line fold relay specs (3 theorems):**
`doubleQuoted_collectChars_linefold_lf`, `singleQuoted_collectChars_linefold_lf`,
`singleQuoted_collectChars_escape_pair` — relay specs for `\n` line fold
and `''` escape pair in quoted scalars.

### 4j. Batch 8: forbidden fold + flow ws + collection dispatch (6 lemmas) — COMPLETED

Commit `b3287d5`.

**§8.1.8 — Forbidden fold paths (2 theorems):**
`doubleQuoted_collectChars_linefold_forbidden`,
`singleQuoted_collectChars_linefold_forbidden` — when `foldQuotedNewlines`
returns `.forbidden msg`, the loop records a validation error and returns.

**§8.1.10 — Flow whitespace base (1 theorem):**
`flowWhitespace_go_zero` — fuel-zero returns immediately.

**§8.10.2 — Collection dispatch at-indent (3 theorems):**
`dispatchByCharImpl_eof` — EOF → `.noMatch`.
`blockSequenceImpl_dispatch` — at-indent → items + `.sequence .block` wrap.
`blockMappingImpl_dispatch` — at-indent → entries + `.mapping .block` wrap.
Uses `if_neg h_ge` as complement of the under-indented specs.

### 4j′. Reflections on §4i–§4j — proof idioms, challenges, simplifications

#### New proof idioms introduced in §4i–§4j

1. **`split <;> simp_all [ParserSpecs.bind_eq]` for char-match with
   `Bool` contradiction cases.**
   The `doubleQuoted_collectChars_backslash_escape` relay theorem
   requires handling a 3-way split after `unfold` + `simp only [bind_eq]`:
   the `'\n'` and `'\r'` branches are impossible (contradicted by
   `hc_not_lf`/`hc_not_cr` hypotheses), and the default branch needs
   further `simp` with the `h_escape`/`h_recurse` hypotheses.
   Early attempts used `rename_i h; subst h; simp at hc_not_lf` but
   this failed because `subst` requires the hypothesis to be `c = '\n'`
   (an equality), not a match discriminant.  `Bool.noConfusion` also
   failed because the hypothesis form after substitution is
   `('\r' == '\r') = false` which reduces to `true = false`, not
   a `Bool` constructor mismatch at the top level.
   The solution `split <;> simp_all [ParserSpecs.bind_eq]` lets
   `simp_all` handle all three branches simultaneously — it
   discovers the `Bool` contradictions in the impossible branches
   and resolves the `bind` chain in the default branch.

2. **`if_neg h_ge` for at-indent dispatch (complement of under-indented).**
   The under-indented specs (§8.10) use `h_lt : s₁.col < minIndent`
   with `simp [h_lt]` to reduce the `if col < minIndent then return none`
   branch.  The at-indent dispatch specs need the *opposite*: when
   `¬ (s₁.col < minIndent)`, the `if` takes the `else` branch.
   The hypothesis `h_ge : ¬ (s₁.col < minIndent)` combined with
   `if_neg h_ge` in the `simp only` list resolves this cleanly.
   This is the natural dual: `if_pos` / `simp [h_lt]` for the
   true branch; `if_neg h_ge` for the false branch.

3. **Explicit `DispatchResult.noMatch` type annotation for dot notation.**
   `dispatchByCharImpl` returns `YamlParser (DispatchResult YamlValue)`.
   In the theorem statement, writing `.noMatch` triggers "Invalid
   dotted identifier notation: expected type could not be determined"
   because the `.ok` wrapper hides the inner type.  The fix:
   ```lean
   .ok s₁ (DispatchResult.noMatch : DispatchResult YamlValue)
   ```
   This is a recurring Lean 4 pattern: when dot notation's type
   inference is blocked by an outer constructor (here `Result.ok`),
   the fully qualified name with an explicit type annotation is needed.

4. **`processEscape` does NOT capture `contentIndent`.**
   The `doubleQuotedScalar` definition has multiple where-clause
   functions: `collectChars`, `processEscape`, `unicodeEscapeInline`,
   `trimTrailingWs`.  While `collectChars` captures `contentIndent`
   from the enclosing `doubleQuotedScalar` definition, `processEscape`
   does not — Lean 4 only captures *free variables actually used* in
   the where-clause body.  Since `processEscape` only pattern-matches
   on the escape character and returns a result, it has no reference
   to `contentIndent`.  Initial theorems incorrectly included
   `contentIndent` as a parameter, causing "application type mismatch"
   errors.  The fix was to remove it from all 16 escape specs.

5. **Default parameters must be supplied explicitly in theorem statements.**
   `dispatchByCharImpl` has signature:
   ```lean
   def dispatchByCharImpl (fuel : Nat) (contentIndent : Nat)
       (scalarIndent : Nat := contentIndent) : YamlParser (DispatchResult YamlValue)
   ```
   In proof mode, writing `dispatchByCharImpl (fuel + 1) contentIndent s`
   causes `s : YamlStream` to be matched against `scalarIndent : Nat`,
   producing "expected type `optParam Nat contentIndent`".  The fix:
   supply the default explicitly:
   ```lean
   dispatchByCharImpl (fuel + 1) contentIndent contentIndent s
   ```
   This is a general Lean 4 gotcha: `optParam` defaults are not
   applied when the function is used in a theorem conclusion that
   also takes a trailing stream argument.

#### Unexpected challenges

- **Char match branches in `collectChars` are ordered differently
  than expected.**
  After `unfold doubleQuotedScalar.collectChars; simp only [bind_eq, h_bs]`,
  the first `split` dispatches on the top-level token match
  (`'"'`, `'\\'`, `'\n'`, `'\r'`, default `c`).  The backslash
  branch then nests a *second* match on the next token.
  Early proof attempts tried `simp only [bind_eq, h_bs, h_c]` to
  resolve both binds at once, but this produced a goal where the
  `split` found 3 cases (`'\n'`, `'\r'`, default) rather than 5
  (the outer match was already resolved by `h_bs = .ok s₁ '\\'`
  selecting the `'\\'` arm).  The insight: `simp only [bind_eq, h_bs]`
  resolves the outer bind + match, then `simp only [bind_eq, h_c]`
  (or `split <;> simp_all [bind_eq]`) resolves the inner match.

- **`FoldResult` as a return type in line fold relay specs.**
  `foldQuotedNewlines` returns `YamlParser FoldResult` where
  `FoldResult` is an inductive with `.folded result` and
  `.forbidden msg`.  The relay specs need separate theorems for
  each constructor: the `.folded` case recurses, while `.forbidden`
  records a validation error and returns.  This two-constructor
  split is cleanly expressed as two theorems
  (`*_linefold_lf` and `*_linefold_forbidden`) rather than one
  theorem with a match on the result.

#### Unexpected simplifications

- **All 16 escape specs share the exact same proof.**
  Every `doubleQuoted_processEscape_*` theorem is proved by
  `unfold doubleQuotedScalar.processEscape; simp [ParserSpecs.pure_eq]`.
  The `match c with | 'n' => return '\n'` reduces to `pure '\n'`
  for concrete characters, and `simp [pure_eq]` rewrites `pure` to
  `.ok s`.  No case analysis, split, or native_decide needed.

- **Line fold relay specs are one-liners.**
  Both `doubleQuoted_collectChars_linefold_lf` and
  `singleQuoted_collectChars_linefold_lf` are proved by a single
  `simp only [ParserSpecs.bind_eq, h_lf, h_fold, h_recurse]`.
  After `unfold`, the `'\n'` branch of `collectChars` is selected
  by `h_lf`, then `foldQuotedNewlines` is resolved by `h_fold`,
  and the recursive call by `h_recurse`.  The entire multi-level
  bind chain collapses in one `simp only` invocation.  This is
  the simplest proof pattern for any relay spec.

- **`flowWhitespace.go` zero case is identical to collection fuel-zero.**
  Despite `flowWhitespace.go` being in a different file (Flow.lean)
  with a different structure (whitespace + comment loop), its
  fuel-zero base case follows the exact same `unfold; simp [pure_eq]`
  pattern as all 16 collection parser fuel-zero specs.

#### Emerging proof architecture patterns

At 161 specs, several meta-patterns are now clear:

| Pattern | Count | Examples |
|---|---|---|
| `unfold; simp [pure_eq]` (fuel-zero / base case) | 17 | all `*_zero` specs, `processEscape_*` |
| `unfold; simp only [bind_eq, ...]` (relay / one-step) | ~30 | `collectChars` steps, fold relays |
| `native_decide` (concrete Bool evaluation) | 32 | `isLineBreak_*`, `isIndicator_*`, `isAnchorChar_*` |
| `unfold; rfl` (definitional equality) | ~5 | `takeLineContent_eq`, `isForbiddenPlainStart_eq` |
| `show LHS = _; rw/simp [...]` (where-clause) | ~8 | `processFolded.go` cases, `blockScalarLine` cases |

The `bind_eq` + hypotheses chaining is the workhorse: it converts
monadic `do` blocks into sequential hypothesis resolution, making
each theorem essentially a witness that the parser follows a
specific execution path.

---

## 5. Roadmap to Fully Deductive Correctness

A fully deductive end-to-end proof of

```
∀ input docs, ValidYaml input docs → parseYaml input = .ok docs
```

requires the following steps, roughly in dependency order:

### Phase A — Close the fold-combinator gap ✅ DONE

The `foldl_eq`, `dropMany_eq`, and `count_eq` lemmas have been added
upstream to lean4-parser (§4b above).  All lean4-parser combinators
used by the YAML parser are now deductively transparent for `m = Id`.

### Phase B — Complete per-parser specifications ✅ DONE

> **Historical note:** The original Phase B described per-parser specs
> for the lean4-parser combinator pipeline (`PerParserSpecs.lean`,
> `FuelSufficiency.lean`).  These files were removed in Phase 10 when
> the parser was replaced by the self-contained tokenized pipeline.
> The equivalent work was completed through the tokenized pipeline's
> proof infrastructure:
>
> - **`ScannerCorrectness.lean`** (~8,300 lines, 439 theorems) — complete
>   scanner correctness for all `scanNextToken` branches
> - **`ParserWellBehaved.lean`** (~3,100 lines, 74 theorems) — token
>   monotonicity and flow nesting preservation for all sub-parsers
> - **`ParserNodeProofs.lean`** (~1,800 lines, 57 theorems) — `parseNode`
>   anchors-grow + aliases-resolve via strong induction on fuel
> - **`ParserWfaProofs.lean`** (~1,700 lines, 50 theorems) — well-formed
>   anchors + token preservation for all sub-parsers
> - **`ParserSoundness.lean`**, **`ParserCompleteness.lean`**,
>   **`ParserCorrectness.lean`** — token parser soundness, completeness,
>   and correctness proofs
>
> Together these provide 620+ theorems covering scanner and token-parser
> correctness — far exceeding the original 8 per-parser specs target.

### Phase C — Type-level infrastructure ✅ DONE

5. ~~**Prove `DecidableEq YamlValue`**~~ ✅ **Done.**
   `DecidableEq YamlValue` and `DecidableEq YamlDocument` are proved
   in `Completeness.lean` via mutual structural recursion through
   `where`-clause list helpers.

6. ~~**Prove `LawfulBEq YamlValue`**~~ ✅ **Done** (v0.2.1).
   `LawfulBEq` proved for the entire AST hierarchy (7 types) in
   `Proofs/LawfulBEq.lean`.  Required replacing both `Scalar` and
   `YamlValue`'s `deriving BEq` with explicit transparent definitions
   in `Types.lean` to work around opaque derived BEq and `Decidable.rec`
   dependent elimination failures.  See the v0.2.1 section in the
   project README for the full retrospective.

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

| Phase | Items | Difficulty | Prerequisite | Status |
|---|---|---|---|---|
| A | `dropMany_eq`, `count_eq` | Moderate | — | ✅ Done |
| B | Per-parser specifications (620+ theorems) | Moderate–Hard | A | ✅ Done (replaced by tokenized pipeline proofs) |
| C | `DecidableEq YamlValue` | Moderate | — | ✅ Done |
| C' | `LawfulBEq YamlValue` (32 proofs) | Moderate | C | ✅ Done (v0.2.1) |
| D | Universal completeness | Hard | A, B, C, C' | Next — all prerequisites met |
| E | Universal round-trip | Hard | D | Planned |

**Phases A, B, C, and C' are all complete.**  The remaining critical
path is D → E.  Phase D can now proceed: all prerequisites (scanner
correctness, parser well-behavedness, `DecidableEq`, `LawfulBEq`,
stream initialization lemmas) are in place.  The main challenge is
composing the 620+ per-parser theorems with the type-level infrastructure
into a single universal completeness theorem.  The 7 `partial def`
functions in `TokenParser.lean` remain the primary trust gap — P10.8
(converting to total `def` with well-founded recursion on token list
length) would close it.
