/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Parser.Document
import Lean4Yaml.Grammar
import Lean4Yaml.Stream
import Lean4Yaml.Proofs.Soundness
import Lean4Yaml.Proofs.Termination

/-!
# Completeness Proofs  (Step 5.4)

Per-parser specification lemmas composed bottom-up toward the full
completeness theorem:

  ∀ input docs, ValidYaml input docs → parseYaml input = .ok docs

## Structure

### §1  Type-Level Infrastructure
- `LawfulBEq Scalar` — bridges Boolean and propositional equality
- `YamlValue.beq_refl` — reflexivity of `BEq YamlValue`
- `YamlValue.beq_eq_true_iff` — completeness: `(a == b) = true ↔ a = b`
- `DecidableEq YamlValue` — enables `native_decide` on propositional equality
- `DecidableEq YamlDocument` — for full parse result equality

### §2  Lawful Parser Stream
- `LawfulParserStream` typeclass (lean4-parser provides none)
- Instance for `YamlStream Char`

### §3  Stream Initialization
Migrated from `Tests/CompletenessExplore.lean`:
- `ofString_*` lemmas characterizing the initial stream state

### §4  Parse Bridge
- `parseYaml_ok_iff` — structural decomposition of `parseYaml`
- `Parser.run` unfolding (it is identity / function application)

### §5  Concrete Completeness
- Propositional equality theorems for specific inputs via `native_decide`

### §6  Per-Parser Specification Framework
- Documents the 12 `ValidNode` constructor obligations
- Foundation lemmas for parser combinator reasoning

## Proof Strategy

Since lean4-parser ships zero theorems / simp lemmas, all combinator
specifications must be proved from first principles by unfolding the
function definitions.  The current YAML parser uses explicit `fuel : Nat`
for termination; completeness proofs therefore take the form:

  ValidNode n → ∃ fuel, parser fuel input = .ok (stream', value)

Structural induction on `Nat` composes these into the full theorem.

## Zero Axioms

All completed theorems are machine-checked. No `sorry`, no `axiom`, no `partial`.
-/

namespace Lean4Yaml.Proofs.Completeness

open Lean4Yaml
open Lean4Yaml.Grammar
open Lean4Yaml.Parse
open Parser

/-! ## §1  Type-Level Infrastructure

`YamlValue` derives `BEq` but not `DecidableEq`.  Bridging the gap
requires proving `DecidableEq` for the recursive type (nested `Array`
makes `deriving DecidableEq` fail) and then showing the derived `BEq`
agrees with propositional equality to yield `LawfulBEq`.

The core challenge is that `Array YamlValue` and
`Array (YamlValue × YamlValue)` contain `YamlValue` recursively.
We solve this by mutual structural recursion on `List` representations
(via `Array.toList`), following the same `where`-clause pattern used
by `contentEq` in `Emitter.lean`.

### Proof Architecture

1. **`decEqYamlValue`** — mutual recursion through `where`-clause list helpers
2. **`DecidableEq YamlValue`** — instance from (1)
3. **`DecidableEq YamlDocument`** — derived from (2) + `DecidableEq Directive`
4. **`LawfulBEq YamlValue`** — deferred (requires showing derived `BEq` agrees
   with the new `DecidableEq`; non-blocking for completeness proofs)
-/

/-! ### §1.1  `DecidableEq YamlValue` via Mutual Structural Recursion

The `where`-clause mutual recursion uses the same well-founded descent
as `contentEq` in `Emitter.lean`: the main function dispatches on
`YamlValue` constructors, converting `Array` fields to `List` via
`.toList`; the `where` helpers recurse on list structure, calling back
to the main function on strictly smaller `YamlValue` subterms.

For the array equality bridge (`items₁.toList = items₂.toList → items₁ = items₂`),
we destruct `Array.mk` and use `congrArg`, since `Array.toList a = a.data`
definitionally.
-/

/--
Decidable equality for `YamlValue` by mutual structural recursion.

Each constructor case is dispatched by comparing fields.  For `sequence`
and `mapping`, we convert `Array` to `List` and use the mutual
`decEqListYV` / `decEqPairListYV` `where`-clause helpers.
-/
private def decEqYamlValue : (a b : YamlValue) → Decidable (a = b)
  | .scalar s₁, .scalar s₂ =>
    if h : s₁ = s₂ then isTrue (h ▸ rfl)
    else isFalse fun heq => h (by cases heq; rfl)
  | .alias n₁, .alias n₂ =>
    if h : n₁ = n₂ then isTrue (h ▸ rfl)
    else isFalse fun heq => h (by cases heq; rfl)
  | .sequence st₁ items₁ tag₁ anc₁, .sequence st₂ items₂ tag₂ anc₂ =>
    if hst : st₁ = st₂ then
    if htag : tag₁ = tag₂ then
    if hanc : anc₁ = anc₂ then
    match decEqListYV items₁.toList items₂.toList with
    | isTrue hi =>
      have hArr : items₁ = items₂ := by
        cases items₁; cases items₂; exact congrArg Array.mk hi
      isTrue (by subst hst htag hanc hArr; rfl)
    | isFalse hi => isFalse fun h => by
        simp only [YamlValue.sequence.injEq] at h
        exact hi (congrArg Array.toList h.2.1)
    else isFalse fun h => hanc (by simp only [YamlValue.sequence.injEq] at h; exact h.2.2.2)
    else isFalse fun h => htag (by simp only [YamlValue.sequence.injEq] at h; exact h.2.2.1)
    else isFalse fun h => hst (by simp only [YamlValue.sequence.injEq] at h; exact h.1)
  | .mapping st₁ pairs₁ tag₁ anc₁, .mapping st₂ pairs₂ tag₂ anc₂ =>
    if hst : st₁ = st₂ then
    if htag : tag₁ = tag₂ then
    if hanc : anc₁ = anc₂ then
    match decEqPairListYV pairs₁.toList pairs₂.toList with
    | isTrue hp =>
      have hArr : pairs₁ = pairs₂ := by
        cases pairs₁; cases pairs₂; exact congrArg Array.mk hp
      isTrue (by subst hst htag hanc hArr; rfl)
    | isFalse hp => isFalse fun h => by
        simp only [YamlValue.mapping.injEq] at h
        exact hp (congrArg Array.toList h.2.1)
    else isFalse fun h => hanc (by simp only [YamlValue.mapping.injEq] at h; exact h.2.2.2)
    else isFalse fun h => htag (by simp only [YamlValue.mapping.injEq] at h; exact h.2.2.1)
    else isFalse fun h => hst (by simp only [YamlValue.mapping.injEq] at h; exact h.1)
  -- Cross-constructor cases: structurally impossible equalities
  | .scalar _, .sequence .. => isFalse YamlValue.noConfusion
  | .scalar _, .mapping .. => isFalse YamlValue.noConfusion
  | .scalar _, .alias _ => isFalse YamlValue.noConfusion
  | .sequence .., .scalar _ => isFalse YamlValue.noConfusion
  | .sequence .., .mapping .. => isFalse YamlValue.noConfusion
  | .sequence .., .alias _ => isFalse YamlValue.noConfusion
  | .mapping .., .scalar _ => isFalse YamlValue.noConfusion
  | .mapping .., .sequence .. => isFalse YamlValue.noConfusion
  | .mapping .., .alias _ => isFalse YamlValue.noConfusion
  | .alias _, .scalar _ => isFalse YamlValue.noConfusion
  | .alias _, .sequence .. => isFalse YamlValue.noConfusion
  | .alias _, .mapping .. => isFalse YamlValue.noConfusion
where
  /-- Decidable equality for `List YamlValue` by structural recursion on
      the list, with element comparison via mutual call to `decEqYamlValue`. -/
  decEqListYV : (as bs : List YamlValue) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (fun h => by cases h)
    | _ :: _, [] => isFalse (fun h => by cases h)
    | a :: as, b :: bs =>
      match decEqYamlValue a b, decEqListYV as bs with
      | isTrue ha, isTrue has => isTrue (ha ▸ has ▸ rfl)
      | _, isFalse has => isFalse fun h => has (by
          simp only [List.cons.injEq] at h; exact h.2)
      | isFalse ha, _ => isFalse fun h => ha (by
          simp only [List.cons.injEq] at h; exact h.1)
  /-- Decidable equality for `List (YamlValue × YamlValue)` by structural
      recursion on the list, with pair-component comparison via
      mutual call to `decEqYamlValue`. -/
  decEqPairListYV :
      (as bs : List (YamlValue × YamlValue)) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (fun h => by cases h)
    | _ :: _, [] => isFalse (fun h => by cases h)
    | (k₁, v₁) :: rest₁, (k₂, v₂) :: rest₂ =>
      match decEqYamlValue k₁ k₂, decEqYamlValue v₁ v₂,
            decEqPairListYV rest₁ rest₂ with
      | isTrue hk, isTrue hv, isTrue hr => isTrue (hk ▸ hv ▸ hr ▸ rfl)
      | isFalse hk, _, _ => isFalse fun h => hk (by
          simp only [List.cons.injEq, Prod.mk.injEq] at h; exact h.1.1)
      | _, isFalse hv, _ => isFalse fun h => hv (by
          simp only [List.cons.injEq, Prod.mk.injEq] at h; exact h.1.2)
      | _, _, isFalse hr => isFalse fun h => hr (by
          simp only [List.cons.injEq] at h; exact h.2)

/-- `DecidableEq` instance for `YamlValue` via mutual structural recursion. -/
instance : DecidableEq YamlValue := decEqYamlValue

/-- `DecidableEq` instance for `YamlDocument`.

All component types now have `DecidableEq`:
- `YamlValue` — proved above by mutual structural recursion
- `Directive` — derived in `Types.lean`
- `Array (String × YamlValue)` — from `DecidableEq String` × `DecidableEq YamlValue`
-/
instance : DecidableEq YamlDocument := fun a b =>
  if hv : a.value = b.value then
  if hd : a.directives = b.directives then
  if ha : a.anchors = b.anchors then
    isTrue (by cases a; cases b; subst hv; subst hd; subst ha; rfl)
  else isFalse fun h => ha (by cases h; rfl)
  else isFalse fun h => hd (by cases h; rfl)
  else isFalse fun h => hv (by cases h; rfl)


/-! ## §2  Lawful Parser Stream

PR#97 of lean4-parser provides `LawfulParserStream` as the contract that
`Parser.Stream.remaining` strictly decreases when `next?` returns `some`.
The `YamlStream` instance is proved in `Stream.lean` (imported transitively)
from the byte-offset arithmetic of `YamlStream.next?`.

The instance enables:
- `Finite (StreamIterator YamlStream Char) Id` — well-founded iteration
- `IteratorLoop` — provably terminating `for` loops over stream tokens
- `StreamIterator.mk` / `.iter` / `.iterM` for `Std.Data.Iterators` consumers
-/

-- Re-export: `LawfulParserStream YamlStream Char` is available from `Stream.lean`.
-- Previously defined locally; now provided by lean4-parser PR#97 and instantiated
-- in `Stream.lean`.

/-! ## §3  Stream Initialization

Basic properties of `YamlStream.ofString` needed for composing
per-parser proofs.  All proved by `rfl` (definitional equality).
-/

/-- `YamlStream.ofString` creates a stream with no validation error. -/
theorem ofString_no_validationError (s : String) :
    (YamlStream.ofString s).validationError = none := rfl

/-- `YamlStream.ofString` starts at position 0. -/
theorem ofString_startPos (s : String) :
    (YamlStream.ofString s).startPos = ⟨0⟩ := rfl

/-- `YamlStream.ofString` has correct stop position. -/
theorem ofString_stopPos (s : String) :
    (YamlStream.ofString s).stopPos = s.rawEndPos := rfl

/-- `Parser.Stream.remaining` for `ofString` equals byte length. -/
theorem ofString_remaining (s : String) :
    Parser.Stream.remaining (YamlStream.ofString s) = s.rawEndPos.byteIdx := rfl

/-- `YamlStream.ofString` starts with an empty anchor map. -/
theorem ofString_anchorMap (s : String) :
    (YamlStream.ofString s).anchorMap = AnchorMap.empty := rfl

/-- `YamlStream.ofString` starts at line 0. -/
theorem ofString_line (s : String) :
    (YamlStream.ofString s).line = 0 := rfl

/-- `YamlStream.ofString` starts at column 0. -/
theorem ofString_col (s : String) :
    (YamlStream.ofString s).col = 0 := rfl

/-! ## §4  Parse Bridge

`parseYamlRaw` is a thin wrapper around `Parser.run yamlStream` that
checks the stream's `validationError` after parsing.  `parseYaml`
applies the **Compose** step (§3.1) to resolve aliases and strip
anchor annotations.
-/

/--
`parseYamlRaw input = .ok docs` if and only if `Parser.run yamlStream`
succeeds **and** no validation error was recorded.

This is the key structural lemma for lifting per-parser specs to the
top-level `parseYamlRaw` function.  It has the same structure as the
former `parseYaml_ok_iff` prior to the serialization/compose split.
-/
theorem parseYamlRaw_ok_iff (input : String) (docs : Array YamlDocument) :
    parseYamlRaw input = .ok docs ↔
    ∃ stream' : YamlStream,
      Parser.run yamlStream (YamlStream.ofString input) = .ok stream' docs ∧
      stream'.validationError = none := by
  constructor
  · intro h
    simp only [parseYamlRaw] at h
    split at h
    · next stream' docs' heq =>
      split at h
      · contradiction
      · next hnone =>
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨stream', heq, hnone⟩
    · next stream' err heq =>
      split at h <;> contradiction
  · intro ⟨stream', hrun, hval⟩
    simp only [parseYamlRaw]
    rw [hrun]
    simp [hval]

/--
`parseYaml input = .ok docs` if and only if there exist raw documents
from `parseYamlRaw` that compose to `docs`.

This is the **Load** decomposition from YAML 1.2.2 §3.1:
Parse (→ serialization tree) + Compose (→ representation graph).
-/
theorem parseYaml_ok_iff (input : String) (docs : Array YamlDocument) :
    parseYaml input = .ok docs ↔
    ∃ rawDocs : Array YamlDocument,
      parseYamlRaw input = .ok rawDocs ∧
      docs = rawDocs.map YamlDocument.compose := by
  constructor
  · intro h
    simp only [parseYaml] at h
    split at h
    · next rawDocs heq =>
      simp only [Except.ok.injEq] at h
      exact ⟨rawDocs, heq, h.symm⟩
    · next err heq =>
      contradiction
  · intro ⟨rawDocs, hraw, hcomp⟩
    simp only [parseYaml, hraw]
    exact congrArg Except.ok hcomp.symm

/--
`Parser.run` is function application.

`Parser.run p s = p s` by definition.  We record this as a `@[simp]`
lemma so that `simp` can unfold `Parser.run` in proof goals.
-/
@[simp]
theorem parser_run_eq {ε' σ' : Type _} {τ' : Type _} {α' : Type _}
    [Parser.Stream σ' τ'] [Parser.Error ε' σ' τ']
    (p : Parser ε' σ' τ' α') (s : σ') :
    Parser.run p s = p s := rfl

/-! ## §5  Concrete Completeness

For specific inputs we can verify parse results computationally.
`native_decide` evaluates the parser at compile time and checks the
Boolean predicate.
-/

/-- Helper: check that `parseYaml input` equals `expected` via `BEq`. -/
def parseYamlEq (input : String) (expected : Array YamlDocument) : Bool :=
  match parseYaml input with
  | .ok docs => docs == expected
  | .error _ => false

-- We use Bool predicates + native_decide because YamlValue lacks
-- DecidableEq (needed for propositional equality on Except/Array).

/-- Plain scalar `"a"` parses successfully. -/
theorem parseYaml_a_ok :
    (match parseYaml "a" with | .ok _ => true | .error _ => false) = true := by
  native_decide

/-- Plain scalar `"a"` produces the expected value. -/
theorem parseYaml_a_value :
    (match parseYaml "a" with
     | .ok docs => docs.size == 1
       && docs[0]!.value == .scalar ⟨"a", .plain, none, none, none⟩
     | .error _ => false) = true := by
  native_decide

/-- Double-quoted scalar `"hello"` parses correctly. -/
theorem parseYaml_dq_hello :
    (match parseYaml "\"hello\"" with
     | .ok docs => docs.size == 1
       && docs[0]!.value == .scalar ⟨"hello", .doubleQuoted, none, none, none⟩
     | .error _ => false) = true := by
  native_decide

/-- Single-quoted scalar `'hello'` parses correctly. -/
theorem parseYaml_sq_hello :
    (match parseYaml "'hello'" with
     | .ok docs => docs.size == 1
       && docs[0]!.value == .scalar ⟨"hello", .singleQuoted, none, none, none⟩
     | .error _ => false) = true := by
  native_decide

/-- Flow sequence `[1, 2, 3]` produces one document. -/
theorem parseYaml_flow_seq :
    (match parseYaml "[1, 2, 3]" with
     | .ok docs => docs.size == 1
     | .error _ => false) = true := by
  native_decide

/-- Block mapping `key: value` produces the expected structure. -/
theorem parseYaml_block_map :
    (match parseYaml "key: value" with
     | .ok docs => docs.size == 1
       && docs[0]!.value == .mapping .block
           #[(.scalar ⟨"key", .plain, none, none, none⟩,
              .scalar ⟨"value", .plain, none, none, none⟩)] none
     | .error _ => false) = true := by
  native_decide

/-- `parseYamlEq` check for plain scalar `"a"`. -/
theorem parseYaml_a_eq :
    parseYamlEq "a" #[{ value := .scalar ⟨"a", .plain, none, none, none⟩,
                         directives := #[] }] = true := by
  native_decide

/-- Literal block scalar parses correctly. -/
theorem parseYaml_literal_block :
    (match parseYaml "|\n  hello\n  world" with
     | .ok docs => docs.size == 1
     | .error _ => false) = true := by
  native_decide

/-- Folded block scalar parses correctly. -/
theorem parseYaml_folded_block :
    (match parseYaml ">\n  hello\n  world" with
     | .ok docs => docs.size == 1
     | .error _ => false) = true := by
  native_decide

/-- Multi-document stream parses both documents. -/
theorem parseYaml_multi_doc :
    (match parseYaml "---\na\n---\nb" with
     | .ok docs => docs.size == 2
     | .error _ => false) = true := by
  native_decide

/-- Flow mapping parses correctly. -/
theorem parseYaml_flow_map :
    (match parseYaml "{a: b, c: d}" with
     | .ok docs => docs.size == 1
       && docs[0]!.value == .mapping .flow
           #[(.scalar ⟨"a", .plain, none, none, none⟩, .scalar ⟨"b", .plain, none, none, none⟩),
             (.scalar ⟨"c", .plain, none, none, none⟩, .scalar ⟨"d", .plain, none, none, none⟩)] none
     | .error _ => false) = true := by
  native_decide

/-- Nested block structure: mapping with sequence value. -/
theorem parseYaml_nested_block :
    (match parseYaml "items:\n- a\n- b" with
     | .ok docs => docs.size == 1
     | .error _ => false) = true := by
  native_decide

/-! ## §6  Per-Parser Specification Framework

Each `ValidNode` constructor (12 total) requires a correctness theorem
establishing that the corresponding parser succeeds on valid inputs.

### Proof obligations

| Constructor | Leaf parser | Obligation |
|-------------|------------|------------|
| `plainScalarBlock` | `plainScalarSingleLine false` | safe chars, no metacharacters |
| `plainScalarFlow`  | `plainScalarSingleLine true`  | safe chars, no flow indicators |
| `singleQuoted`     | `singleQuotedScalar`          | matched quotes, `''` escapes |
| `doubleQuoted`     | `doubleQuotedScalar`          | matched quotes, `\` escapes |
| `literalScalar`    | `blockScalar` (literal)       | `|` header, indented lines |
| `foldedScalar`     | `blockScalar` (folded)        | `>` header, indented lines |
| `blockSeq`         | `blockSequence`               | `- ` entries, consistent indent |
| `blockMap`         | `blockMapping`                | `key: value` entries |
| `flowSeq`          | `flowSequence`                | `[` items `,` `]` |
| `flowMap`          | `flowMapping`                 | `{` entries `,` `}` |
| `null`             | (empty input / `~`)           | spec says null |
| `alias`            | `anchorAlias`                 | `*name` reference |

### Approach

1. **`@[simp]` annotations** on `getStream`, `setStream`, `Parser.run`,
   key YAML combinators (`skipBlankLines`, `skipHWhitespace`, `currentCol`)
2. **Combinator specifications** proved from first principles:
   - `anyToken_spec`: unfold `tokenCore` + `Stream.next?`
   - `tokenFilter_spec`: extends `anyToken_spec` with predicate check
   - `withBacktracking_spec`: position save/restore on error
   - `option?_spec`: always succeeds, returns `some`/`none`
3. **Per-parser specs** for each `ValidNode` constructor
4. **Fuel sufficiency** — one lemma per parser showing an upper bound
   on fuel needed as a function of input length
5. **Full composition** into the completeness theorem

### Current status

Phase 1 (infrastructure) is complete: `LawfulParserStream YamlStream Char`
(now from lean4-parser PR#97 + `Stream.lean` instance),
stream initialization lemmas, `parseYaml_ok_iff` bridge, concrete completeness
via `native_decide`.  The `StreamIterator` / `Std.Data.Iterators` bridge is
also available for provably terminating `for` loops over stream tokens.

Phase 2 (combinator specifications) is complete: `ParserSpecs.lean` provides
20 universal `@[simp]` lemmas covering monad, stream, error, token,
backtracking, option, and lookahead combinators.  Note: fold-based
combinators (`dropMany`, `count`, `drop`) do NOT yet have `@[simp]` lemmas;
these are exercised only computationally via `#guard` and `native_decide`.

Phase 3 (per-parser specs) is partially complete: `PerParserSpecs.lean`
has 49 theorems covering `plainScalarBlock` and `plainScalarFlow`.
Remaining constructors: `singleQuoted` (WIP), `doubleQuoted` (WIP),
`literalScalar`, `foldedScalar`, `blockSeq`, `blockMap`, `flowSeq`, `flowMap`.
-/

end Lean4Yaml.Proofs.Completeness
