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
| `Completeness.lean` | 504 | 33 | 1 | Bottom-up completeness, `DecidableEq YamlValue/YamlDocument`, concrete parse |
| `Composition.lean` | 338 | 21 | — | Composes per-parser specs + fuel sufficiency into intermediate lemmas |
| `DocumentContracts.lean` | 190 | 17 | — | Document parser boundary detection, trailing comments, monotonicity |
| `DumpRoundTrip.lean` | 453 | 67 | 43 | Style-aware dump produces well-formed output; dump→parse round-trip |
| `EscapeResolution.lean` | 291 | 41 | 24 | Escape sequences produce valid Unicode per YAML 1.2.2 §5.7 |
| `FoldNewlines.lean` | 313 | 36 | 18 | Line folding does not introduce c-forbidden content (doc markers) |
| `FuelSufficiency.lean` | 545 | 35 | — | Fuel `4 * remaining + 4` is always sufficient; no fuel exhaustion |
| `IndentConsumption.lean` | 250 | 11 | 12 | Consuming indentation advances column by exactly the right amount |
| `ParserSpecs.lean` | 424 | 20 | — | Foundation `@[simp]` lemmas unfolding lean4-parser combinators |
| `PerParserSpecs.lean` | 1080 | 56 | — | Per-parser correctness + `collectChars` loop lemmas (partial) |
| `RoundTrip.lean` | 905 | 56 | 66 | Parse-emit-parse round-trip preserves content |
| `SchemaDump.lean` | 311 | 40 | 22 | `ToYaml` + dump pipeline content round-trip |
| `SchemaResolution.lean` | 267 | 35 | 34 | Core Schema (§10.3) resolution: null/bool/int/float determinism |
| `Soundness.lean` | 414 | 27 | — | `NodeToValue` totality, determinism, faithful implementation |
| `StringProperties.lean` | 172 | 13 | — | Pure string/list helpers (whitespace trim, FoldResult invariants) |
| `Termination.lean` | 164 | 10 | — | Foundation + composition lemmas for well-founded recursion on stream length |
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

- **597** theorems/lemmas (all machine-checked)
- **653** `#guard` compile-time checks (Proofs/ + SuiteGuards/)
- **18** additional `#guard` checks in `Tests/IteratorTests.lean`
- **0** `sorry`, **0** `axiom`, **0** `partial def`

---

## 4. Future Work

### 4a. Items remaining in current proof files

#### `Completeness.lean` — `DecidableEq YamlValue` ✅ / `LawfulBEq YamlValue` (deferred)

**`DecidableEq YamlValue`** and **`DecidableEq YamlDocument`** are now
proved (25 new theorems/definitions).  The proof uses `where`-clause
mutual structural recursion on `List YamlValue` / `List (YamlValue × YamlValue)`,
following the same pattern as `contentEq` in `Emitter.lean`.

Array equality is bridged via `Array.toList` + `congrArg Array.mk`,
since `Array.toList a = a.data` definitionally.

**`LawfulBEq YamlValue`** remains deferred — it requires showing the
auto-derived `BEq` instance agrees with propositional equality through
the same mutual induction.  This is non-blocking: `DecidableEq` is
sufficient for universally quantified completeness proofs.

#### `PerParserSpecs.lean` — remaining `ValidNode` constructors

Status per constructor:

| Constructor | Parser | Status |
|---|---|---|
| `plainScalarBlock` | `plainScalar` (block ctx) | ✅ Complete |
| `plainScalarFlow` | `plainScalar` (flow ctx) | ✅ Complete |
| `singleQuoted` | `singleQuotedScalar` | 🔧 WIP — relational spec + loop lemmas (8) |
| `doubleQuoted` | `doubleQuotedScalar` | 🔧 WIP — relational spec + loop lemmas (8) |
| `literalScalar` | `literalBlockScalar` | � WIP — 11 lemmas (applyChomp, processFolded.go, collectLines loop, autoDetectIndent) |
| `foldedScalar` | `foldedBlockScalar` | 🔧 WIP — 11 lemmas (applyChomp, processFolded.go, collectLines loop, autoDetectIndent) |
| `blockSeq` | `blockSequence` | ✅ Relational spec complete |
| `blockMap` | `blockMapping` | ✅ Relational spec complete |
| `flowSeq` | `flowSequence` | ✅ Relational spec + empty-case complete |
| `flowMap` | `flowMapping` | ✅ Relational spec + empty-case complete |

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

Foundation lemmas (6 theorems) plus composition lemmas (4 theorems)
are in place.  The composition lemmas connect fuel sufficiency with
stream progress to establish the abstract termination argument:
`fuel_bounds_iterations`, `composed_descent`, `remaining_zero_iff_exhausted`,
and `fuel_le_of_remaining`.  Planned per-parser termination proofs
(`∀ input, ∃ output, parser input ≠ ⊥`) are subsumed by the
fuel-sufficiency approach already in `FuelSufficiency.lean`.

### 4a′. Reflections — unexpected challenges, simplifications, and idioms

#### Reused proof idioms

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

### 4b. Closing the fold-combinator gap — COMPLETED

The fold-combinator gap described in §2 has been **closed** by adding
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

5. ~~**Prove `DecidableEq YamlValue`**~~ ✅ **Done.**
   `DecidableEq YamlValue` and `DecidableEq YamlDocument` are proved
   in `Completeness.lean` via mutual structural recursion through
   `where`-clause list helpers.

   **Remaining:** Prove `LawfulBEq YamlValue` by showing the derived
   `BEq` agrees with propositional equality.  Non-blocking for
   completeness proofs (which use `DecidableEq` directly).

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
| B | 8 per-parser specs | Moderate–Hard | A | WIP (4 relational + loops) |
| C | `DecidableEq YamlValue` | Moderate | — | ✅ Done |
| C' | `LawfulBEq YamlValue` | Moderate | C | Deferred (non-blocking) |
| D | Universal completeness | Hard | A, B, C | Planned |
| E | Universal round-trip | Hard | D | Planned |

Phases A and C are independent and can proceed in parallel.
**Phase C is complete** (`DecidableEq YamlValue/YamlDocument` proved).
Phase B depends on A.  The overall critical path is A → B → D → E.
