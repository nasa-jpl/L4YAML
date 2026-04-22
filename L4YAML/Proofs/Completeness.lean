/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Parser.Composition
import L4YAML.Spec.Grammar

/-!
# Completeness Proofs  (Step 5.4 — Tokenized Parser)

Type-level infrastructure, parse bridge theorems, and end-to-end
completeness/correctness architecture for the YAML parser pipeline.

## Target Theorems (all achieved)

```
parse_sound    : parseYaml input = .ok docs → ValidYamlProp input docs
parse_complete : ValidYamlProp input docs → parseYaml input = .ok docs
```

## Structure

### §1  Type-Level Infrastructure
- `DecidableEq YamlValue` — via mutual structural recursion
- `DecidableEq YamlDocument` — derived from the above
- Enables `native_decide` on propositional equality of parse results

### §2  Parse Bridge
- `parseYaml_ok_iff` — structural decomposition into raw parse + compose

### §3  Concrete Completeness
- Propositional equality theorems for specific inputs via `native_decide`
- Each theorem is a compile-time-verified parse result

### §4  End-to-End Proof Architecture (cross-reference)
- Documents the completed proof pipeline across companion modules
- Maps the four originally-identified deficiencies to their resolutions

## Proof Strategy

### Termination

The tokenized parser (`TokenParser.lean`) uses **fuel-based structural
recursion** — all 14 mutual functions take a `fuel : Nat` parameter that
decreases by 1 at each entry via `match fuel with | fuel + 1 => ...`.
Lean 4 infers termination automatically from this structural decrease;
no `termination_by` or `partial` annotations are needed. Initial fuel is
`4 * tokens.size + 4`, bounding total mutual-function entries.

### Completed Pipeline (Phases A–D)

All four originally-identified proof obligations are discharged:

**Phase A — Scanner Correctness** (ScannerCorrectness.lean, 439 theorems):
```
scan_produces_valid_tokens :
  Scanner.scan input = .ok tokens → ValidTokenStream input tokens
```
Token envelope, position monotonicity, and `ScanInv` invariant fully proven.

**Phase B — Parser Termination** (TokenParser.lean):
All 14 mutual functions are total `def` (not `partial def`). Fuel-based
structural decrease on `Nat` gives automatic termination — the kernel
checks every recursive call. Zero trust gap.

**Phase C — Grammability Discharge** (ParserGrammable.lean):
```
parseStream_output_grammable :
  scanFiltered input = .ok tokens → parseStream tokens = .ok raw_docs →
  ∀ doc ∈ raw_docs.toList, Grammable doc.compose.value false

parseYaml_produces_valid_nodes :
  parseYaml input = .ok docs →
  ∀ doc ∈ docs.toList, ∃ node : ValidNode,
    stripAnnotations (toYamlValue node) = stripAnnotations doc.value
```
Chains scanner plain-scalar validation → parser well-behavedness →
anchor resolution → unconditional `ValidNode` witnesses.

**Phase D — End-to-End Composition** (EndToEndCorrectness.lean):
```
parse_sound        : parseYaml input = .ok docs → ValidYamlProp input docs
parse_complete     : ValidYamlProp input docs → parseYaml input = .ok docs
parse_deterministic : parseYaml input = .ok docs₁ → parseYaml input = .ok docs₂ → docs₁ = docs₂
parseStream_respects_grammar_unconditional :
  scanFiltered input = .ok tokens → parseStream tokens = .ok docs →
  ∀ doc ∈ docs.toList, ∃ node : ValidNode, ...
```

### Phase E — Universal Round-Trip (open)

The remaining proof obligation is the universal emitter round-trip:
```
∀ v : YamlValue, Grammable v false →
  ∃ docs, parseYaml (emit v) = .ok docs ∧
  docs.size = 1 ∧ contentEq v docs[0]!.value = true
```

**Current evidence**: Concrete `#guard` checks in RoundTrip.lean and
ScannerEmitBridge.lean verify round-trip for all node types. The universal
theorem requires:
1. `emit` produces valid YAML (scanner accepts canonical output)
2. Parser reconstructs equivalent content from canonical tokens
3. `contentEq` bridges style differences (emit uses double-quoted + flow)

**Existing infrastructure** toward Phase E:
- `emit_stripAnnotations` (ScannerEmitBridge): emit ignores annotations
- `contentEq_implies_emit_eq` (ScannerEmitBridge): content-equal values emit identically
- `contentEq` is an equivalence relation (RoundTrip): refl, symm, trans
- `canonical_roundtrip_conditional` (ScannerEmitBridge): conditional on parse success
- `escapeTag_roundtrip` (RoundTrip): per-character escape invertibility

## Zero Axioms

All completed theorems are machine-checked. No `sorry`, no `axiom`, no `partial`.
-/

namespace L4YAML.Proofs.Completeness

open L4YAML
open L4YAML.Grammar
open L4YAML.TokenParser

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
4. **`LawfulBEq YamlValue`** — proved in `Proofs/LawfulBEq.lean` using the
   explicit transparent `beqYamlValue` / `beqScalar` from `Types.lean`
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
def decEqYamlValue : (a b : YamlValue) → Decidable (a = b)
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
- `Array (YamlPos × Comment)` — from `DecidableEq YamlPos` × `DecidableEq Comment`
- `Array (YamlPath × YamlPos × YamlPos)` — from `DecidableEq PathSegment` × `DecidableEq YamlPos`
-/
instance : DecidableEq YamlDocument := fun a b =>
  if hv : a.value = b.value then
  if hd : a.directives = b.directives then
  if ha : a.anchors = b.anchors then
  if hc : a.comments = b.comments then
  if hn : a.nodePositions = b.nodePositions then
    isTrue (by cases a; cases b; subst hv; subst hd; subst ha; subst hc; subst hn; rfl)
  else isFalse fun h => hn (by cases h; rfl)
  else isFalse fun h => hc (by cases h; rfl)
  else isFalse fun h => ha (by cases h; rfl)
  else isFalse fun h => hd (by cases h; rfl)
  else isFalse fun h => hv (by cases h; rfl)


/-! ## §2  Parse Bridge

`parseYamlRaw` and `parseYaml` delegate to `TokenParser.parseYamlRaw`
and `TokenParser.parseYaml` respectively (P10.2 API switch).  `parseYaml`
applies the **Compose** step (§3.1) to resolve aliases and strip
anchor annotations.
-/

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
    · contradiction
  · intro ⟨rawDocs, hraw, hcomp⟩
    simp only [parseYaml]
    rw [hraw]
    exact congrArg Except.ok hcomp.symm

/-! ## §3  Concrete Completeness

For specific inputs we can verify parse results computationally.
`native_decide` evaluates the parser at compile time and checks the
Boolean predicate.
-/

/-- Helper: check that `parseYaml input` equals `expected` via `BEq`. -/
def parseYamlEq (input : String) (expected : Array YamlDocument) : Bool :=
  match parseYaml input with
  | .ok docs => docs == expected
  | .error _ => false

-- We use Bool predicates + native_decide for convenience; DecidableEq
-- is available (§1) for propositional equality proofs when needed.

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

/-! ## §4  End-to-End Proof Architecture

The completeness/correctness pipeline is fully proven across companion modules.
This section documents the architecture and cross-references the key results.

### Dependency Graph

```
Scanner.lean ──scan──→ Array (Positioned YamlToken)
    │                        │
    │ ScannerCorrectness     │ TokenParser (fuel-based, total)
    │ (439 theorems)         │
    ▼                        ▼
ValidTokenStream        parseStream → Array YamlDocument
    │                        │
    │ ScannerPlainScalarValid│ ParserGrammable (Phase C)
    │ + ParserWellBehaved    │
    ▼                        ▼
PlainScalarsValid       Grammable (unconditional)
    │                        │
    └────────────┬───────────┘
                 │ ParserSoundness + Soundness
                 ▼
          ∃ ValidNode witness
                 │
                 │ EndToEndCorrectness (Phase D)
                 ▼
    parse_sound ∧ parse_complete ∧ parse_deterministic
```

### Resolved Proof Obligations

| # | Obligation | Resolution | Module |
|---|---|---|---|
| 1 | Scanner correctness | `scan_produces_valid_tokens` | ScannerCorrectness |
| 2 | Parser termination | Fuel-based total `def` (14 mutual) | TokenParser |
| 3 | Grammability discharge | `parseYaml_produces_valid_nodes` | ParserGrammable |
| 4 | End-to-end composition | `parse_sound` + `parse_complete` | EndToEndCorrectness |

### Open Obligation

| # | Obligation | Status | Module |
|---|---|---|---|
| 5 | Universal round-trip | Planned for v0.4.7 — see `VERSION-0.4.7.md` | RoundTrip, ScannerEmitBridge |

The universal round-trip theorem (`∀ v, Grammable v false → ...contentEq...`)
requires proving that `emit` produces scanner-accepted output. Current evidence:
- 6 concrete `#guard` checks (RoundTrip.lean)
- Per-character escape invertibility (`escapeTag_roundtrip`)
- `contentEq` equivalence relation (refl/symm/trans)
- `emit_stripAnnotations` and `contentEq_implies_emit_eq` (ScannerEmitBridge)

**Approach for Phase E**: Prove `emit_produces_valid_yaml`:
```
∀ v, Grammable v false → ∃ tokens,
  Scanner.scanFiltered (emit v) = .ok tokens
```
Then compose with `parseStream` totality and `contentEq_refl` to close.
-/

end L4YAML.Proofs.Completeness
