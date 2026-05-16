# Initiative 4 — Intrinsic Foundations

**Status**: Phase 1 — Design **closed**. Phase 2 — Algebra library
**closed** on `feature/intrinsic-foundations` (branched from `main`):
all six clusters landed (foundation, small-independents, surface
combinators, schema, equivalence, idempotence capstone). The 23-item
inventory remains frozen; the Item 4 stress test confirmed
Guardrail 2 closure. Phase 3 — Stage C (scanner) on indexed types:
sub-plan decomposed into 6 sessions; **Steps 1–3 landed** with
`lake build` green (385 jobs, 0 sorries in `L4YAML/Indexed/`,
`L4YAML/Scanner/IndexedScanner.lean`,
`L4YAML/Proofs/Scanner/IndexedWhitespace.lean`, and
`L4YAML/Proofs/Scanner/IndexedIndent.lean`; the staging files are
unimported from `L4YAML.lean` per Guardrail 1). The Step 2 →
Step 3 deferred obligation (skip-loop termination + count = column
delta) closed in `IndexedWhitespace.lean` before any Step 3
production was added. See §Phase 2 status table and §Phase 3
sub-plan below.

**Driver**: Initiative 3 was stopped 2026-05-03 (see
`Blueprint/07-initiative-3-append-only.md` §Stop assessment).
The two root causes — late algebra (Lesson 5) and extrinsic data
(Observation 6) — call for a foundational refactor that reverses
both. This initiative builds the foundations *before* attacking
Tier 2 again.

**Convention**: phases are numbered (Phase 1, 2, 3, …) within this
initiative. The letter convention used in earlier initiatives
(I, J for previous numbered initiatives) had no documented meaning
and is not continued here.

---

## Motivation

<details><summary>Why Initiative 4 exists — Initiative 3's stop assessment surfaced two root causes (late algebra, extrinsic data) that this initiative directly reverses.</summary>

### What Initiative 3 demonstrated

<details><summary>134 commits, 7 sorries, predicates ballooning to 17–24 conjuncts — the stop traces to algebraic laws inlined as predicate conjuncts and spec datatypes that don't carry source provenance.</summary>

Initiative 3 traded `setIfInBounds` (in-place placeholder rewrite)
for an append-only `(tokens, pendingKeys)` pair plus a one-shot
`linearise` post-pass. The architectural intent was to trivialise
filter-monotonicity. The implementation delivered that property at
the scanner level, but the proof corpus did not converge:

- 134 commits between 2026-04-26 and 2026-05-03.
- 7 sorries remaining when the initiative was stopped, with the
  cascade-stitching layer assessed to require another 700–1000
  lines of new infrastructure across 3–5 more cadence steps.
- Each cadence step strengthened one of the bundled return contracts
  (`EmitScansInFlow`, `EmitListScansInFlow`, `EmitPairListScansInFlow`)
  rather than discharging an existing sorry. The first commit that
  discharged without strengthening was the 24th sub-step.
- The `Emit*ScansInFlow` predicates ended at 17–24 conjuncts each.

The Initiative 3 stop assessment (Blueprint 07 §1–§7) attributes
this to two underlying causes:

1. **Algebraic laws were inlined as predicate conjuncts.** Properties
   like bracket-balance composition, `expandKind` neutrality on
   bracket delta, `insertBeforeIdx` monotonicity under `saveSimpleKey`
   ordering, splice-streamEnd commutation — every one is a single
   named lemma about an algebraic structure. Each was instead
   bolted onto a bundled return contract, forcing every consumer to
   re-destructure and every producer to re-discharge it locally.

2. **Specification datatypes don't carry source provenance.**
   `YamlValue` and `Scalar` describe abstract structure but not the
   source string they came from, the source range, the line/column,
   or the scalar style. Every roundtrip proof has to reconstruct
   the value-source relationship as a byte-level claim, which is
   the bulk of the work and the source of the predicate explosion.

</details>

### What Initiative 4 reverses

<details><summary>Algebra-first foundations and indexed types reverse both root causes; Initiative 3's six lessons become the procedural guardrails.</summary>

Both root causes:

- **Algebra first**: a frozen library of 23 named algebraic lemmas
  is the foundation of every subsequent layer. Phase 1 enumerates
  it; Phase 2 proves it; phases beyond freeze it.
- **Indexed types**: the L1 representation graph is parameterised by
  the input string. Two values from different sources have
  different *types* and cannot be confused. Source range, scalar
  style, and (where relevant) anchor identity live in the type, not
  in a side-channel ghost predicate.

The Initiative 3 lessons (Blueprint 07 §7) form the procedural
guardrails:

- **No parallel state** (Lesson 1).
- **Cap predicate budget at design time** (Lesson 2).
- **Discharge before strengthening** (Lesson 3).
- **The cascade is the gate, not the body** (Lesson 4).
- **Algebra first, ghost predicates last** (Lesson 5).
- **Spec datatypes carry source provenance** (Lesson 6).

</details>

</details>

---

## Proposed architecture

<details><summary>Four layers (L0–L3) aligned to YAML 1.2.2 §3.1, three bidirectional stages, indexed types, hybrid Subtype/tactic pre-/postconditions, and a bundled LoadConfig.</summary>

### Four layers

<details><summary>L0 (native records), L1 (representation graph), L2 (token stream), L3 (character stream) — with the algebra library underneath.</summary>

L4YAML's architecture aligns with YAML 1.2.2 §3.1's three-stage
information model. Adding the application layer (L0) gives four
layers total:

```
                               ┌────────────────────────────┐
   L0  Native Lean records     │  user-defined types        │
                               │  (User, Config, …)         │
   ↕   Stage A                 │                            │
       (Represent / Construct) │                            │
                               │                            │
   L1  Representation graph    │  RepGraph input range      │  ← indexed
                               │                            │
   ↕   Stage B                 │                            │
       (Serialize / Compose)   │                            │
                               │                            │
   L2  Event/token stream      │  TokenStream input         │  ← indexed
                               │                            │
   ↕   Stage C                 │                            │
       (Present / Parse)       │                            │
                               │                            │
   L3  Character stream        │  String                    │  ← input root
                               └────────────────────────────┘
                               │  Algebra library           │  ← Phase 2
                               │  (23 frozen lemmas)        │
                               └────────────────────────────┘
```

</details>

### Three stages, each bidirectional

<details><summary>Stage A/B/C forward and backward functions; YAML 1.2.2's 211 rules distribute by grammatical level (`b-`/`s-`/`c-`/`ns-` vs `l-`/`s-l-` vs tag/schema).</summary>

| Stage | Forward | Backward |
|---|---|---|
| **A** (L0 ↔ L1) | `represent : α → RepGraph input range` (with `[ToYaml α]`) | `construct : RepGraph input range → α` (with `[FromYaml α]`) |
| **B** (L1 ↔ L2) | `serialize : RepGraph input range → TokenStream input` | `compose : TokenStream input → Option (RepGraph input range)` |
| **C** (L2 ↔ L3) | `present : TokenStream input → String` | `parse : String → Option (TokenStream input)` |

Each stage is verified in both directions against the YAML 1.2.2
production rules ([1]–[211]). The 211 rules distribute across
stages by their grammatical level:

- **Stage C rules**: characters, line breaks, indentation,
  whitespace, scalar lexing — roughly rules touching `b-`/`s-`/`c-`/
  `ns-` productions.
- **Stage B rules**: nodes, blocks, flows, document structure —
  roughly rules touching `l-`/`s-l-`/`l-block-`/`c-flow-` productions.
- **Stage A rules**: tags, schemas, the representation graph —
  the application-level rules.

</details>

### Indexed type discipline

<details><summary>`RepGraph` parameterised by source string + byte range; two graphs from different inputs have different types and cannot be compared at L1.</summary>

The L1 representation graph is parameterised by the source string
and the byte range it occupies:

```lean
-- Sketch (final shape resolved in Phase 1).
inductive RepGraph (input : String) (range : Range input) : Type where
  | scalar (range : Range input) (content : String) (style : ScalarStyle) : RepGraph input range
  | sequence (range : Range input) (items : Array (Σ r, RepGraph input r)) : RepGraph input range
  | mapping  (range : Range input) (pairs : Array (Σ rk rv, RepGraph input rk × RepGraph input rv)) : RepGraph input range
  | alias    (range : Range input) (name : AnchorName) : RepGraph input range
```

Two graphs from different inputs have different types and cannot be
compared at the L1 level. Construction at the application layer (L0)
happens via `ToYaml` / `FromYaml`; the L1 graph is never constructed
ad-hoc. Application code that wants a "free-floating" YAML value
constructs at L0 and converts down through Stage A.

`TokenStream input` is indexed similarly. `Token`s carry positions
that are offsets into `input`; mismatched indexing is caught by the
type system.

</details>

### Pre/post conditions: refinement types + tactic

<details><summary>Hybrid `Subtype` for input/output contracts plus a `decide_pre` tactic for routine discharge — replaces ghost predicates entirely.</summary>

Settled choice: hybrid `Subtype` + tactic. Each stage function
carries its precondition in the input subtype and its
postcondition in the output subtype:

```lean
def parse (s : String) : Subtype (TokenStream s ∧ ValidScan s) := by
  ...
```

Routine preconditions discharge via a `decide_pre` tactic that
unfolds the standard predicates and dispatches to `decide` /
`omega` / `simp`. Non-routine preconditions surface as call-site
obligations the user discharges explicitly.

The combination of indexed types + Subtype-encoded contracts
**replaces ghost predicates entirely**. A property that Initiative 3
expressed as `EmitScansInFlow v` becomes either:

- A structural predicate on the indexed type (decidable by induction
  on the value), or
- A subtype refinement on the result of the stage function.

There is no free-standing `Prop`-valued predicate threaded through
existential bundles.

</details>

### LoadConfig: bundled configuration

<details><summary>Single `LoadConfig` struct threading `EqMode` (cycle handling) and `DuplicateKeyPolicy` through parse/compose/construct; default `{}` is spec-strict.</summary>

Settled choice: bundled into a single `LoadConfig` structure
threaded through `parse`, `compose`, and `construct`.

```lean
structure LoadConfig where
  eqMode             : EqMode := .strict
  duplicateKeyPolicy : DuplicateKeyPolicy := .error

inductive EqMode where
  | strict                  -- error on cycle (default)
  | identity                -- cycles compare by anchor name
  | depthBounded (n : Nat)  -- terminates at depth n
  | bisim                   -- requires client-supplied bisimulation witness

inductive DuplicateKeyPolicy where
  | error                  -- parse error (libyaml default)
  | first                  -- keep first occurrence
  | last                   -- keep last (Python yaml default)
  | merge (f : YamlValue → YamlValue → YamlValue)
```

`LoadConfig` is threaded as an explicit parameter through `parse`,
`compose`, and `construct`. The default value (`{}`) gives
spec-strict behaviour (error on cycle, error on duplicate).

</details>

</details>

---

## Properties this delivers

<details><summary>Six explicit success criteria P1–P6 (ghost predicates eliminated, compositional proofs, spec-faithful, roundtrip lawful, sorry-free at boundaries, predicate budget capped).</summary>

| # | Property | Mechanism |
|---|---|---|
| P1 | Ghost predicates eliminated | Indexed types carry source-relationship; refinement types carry pre/post; algebra library carries laws. Nothing left to put in a free-standing `Prop`. |
| P2 | Compositional proofs | Each lemma reuses the algebra library; new theorems compose existing lemmas rather than restating them. |
| P3 | Spec-faithful, layer by layer | YAML 1.2.2's 211 rules verified in both directions, layer at a time. |
| P4 | Roundtrip lawful | For any `α` with `[ToYaml α]` and `[FromYaml α]` instances satisfying the round-trip law, `construct ∘ compose ∘ parse ∘ present ∘ serialize ∘ represent = some` (with the `LoadConfig` defaults). |
| P5 | Sorry-free at each phase boundary | Each phase's DONE criterion includes "no sorries in this phase's deliverable." Lesson 3: discharge before strengthening. |
| P6 | Predicate-budget capped | The algebra library is frozen at end of Phase 1. No new algebraic content past freeze without re-opening Phase 1. |

These six properties are the explicit success criteria for
Initiative 4. Failure to deliver any one of them at its phase
boundary triggers a stop-and-reassess (mirroring the Initiative 3
sorry-budget gate that should have been enforced in J.4).

</details>

---

## Worked example

<details><summary>`{a: 1}` walked through all four layers in both directions; ends with how Initiative 3's 24-conjunct `EmitScansInFlow` collapses to ≤30 lines of structural induction.</summary>

Input: `{a: 1}` (6 bytes, single line).

This walks the input through all four layers in both directions,
showing how the indexed types eliminate the ghost-predicate work
that Initiative 3's `EmitScansInFlow` was carrying.

### Stage C (L3 ↔ L2): present / parse

<details><summary>`parse "{a: 1}"` returns a `TokenStream "{a: 1}"` whose token positions are verifiably offsets into the input; the "scanning succeeded" fact lives in the subtype.</summary>

`parse "{a: 1}"` returns:

```lean
{ tokens := [
    ⟨pos 0, .flowMappingStart⟩,
    ⟨pos 1, .key⟩,
    ⟨pos 1, .scalar "a" .plain⟩,
    ⟨pos 2, .valueIndicator⟩,
    ⟨pos 4, .scalar "1" .plain⟩,
    ⟨pos 5, .flowMappingEnd⟩
  ] : TokenStream "{a: 1}" }
```

The `TokenStream input` indexing means:
- Each token's position is verifiably an offset into `"{a: 1}"`.
- The `parse` function's signature is
  `(s : String) → Subtype (validScan s)`; the subtype proof is
  the verification of YAML 1.2.2 rules `[1]`–`[~63]`.
- No `EmitScansInFlow` ghost predicate. The "scanning succeeded"
  fact lives in the subtype.

</details>

### Stage B (L2 ↔ L1): compose / serialize

<details><summary>`compose tokens` produces a `RepGraph` whose outer mapping range is the whole input and each sub-scalar carries its own 1-byte range.</summary>

`compose tokens` produces:

```lean
RepGraph "{a: 1}" (Range.mk 0 6) := .mapping (Range.mk 0 6) #[
  ⟨ Range.mk 1 2, Range.mk 4 5,
    .scalar (Range.mk 1 2) "a" .plain,
    .scalar (Range.mk 4 5) "1" .plain ⟩
]
```

Each sub-graph carries its own range. The outer mapping's range is
`[0, 6)` (the whole input); each sub-scalar's range is its 1-byte
position. The `compose` function's type ensures these ranges are
well-formed offsets into the input.

</details>

### Stage A (L1 ↔ L0): construct / represent

<details><summary>`construct (cfg := {})` produces `Map.mk [("a", 1)] : Map String Int` via the existing `FromYamlType Int` instance.</summary>

If the user has `[FromYaml (Map String Int)]` (derived via
`ToYaml`/`FromYaml` typeclass machinery from Phase 5), then
`construct (cfg := {})` returns the application value:

```lean
Map.mk [("a", 1)] : Map String Int
```

The `FromYamlType Int` instance (already present at
`Schema/FromToYaml.lean:85`) handles the scalar-to-int conversion
via `Schema.resolve`.

</details>

### How `EmitScansInFlow v` collapses

<details><summary>Initiative 3's 24-conjunct ∃-tuple collapses to a ≤30-line structural induction over `m`, chaining algebra-library lemmas — the test of whether Initiative 4 delivers what it claims.</summary>

In Initiative 3, the predicate `EmitScansInFlow v` for
`v = .flowMapping #[(.scalar "a" .plain, .scalar "1" .plain)]`
was a 24-conjunct existential ∃-tuple including:

- chain witness (`ScanChainGrew`, `FlowMonoChain`)
- 8 scanner-state preservation conjuncts
- pendingKey size monotonicity + per-index preservation
- new-kind disjunction
- bundled bracket-balance + flowEntry-prefix
- per-pair `qs` locator with 6 sub-conjuncts
- conditional save-time monotonicity

In Initiative 4, the corresponding statement is:

```lean
theorem mapping_scans (m : RepGraph input range) (h : m.isMapping) :
    parse (present m).toString = some (TokenStream.ofGraph m) := by
  -- Structural induction on m, dispatched by the algebra library:
  -- — concatenation lemma (Item 9: char/string decomposition)
  -- — token-stream concat monoid (Item 10)
  -- — position monoid + ordered (Item 7 + 13)
  -- — mapping commutativity is *not* in play here (we present in
  --   sequential order; Item 1 is for the ≈ equivalence relation)
  ...
```

The 24 conjuncts disappear because:
- Source-position information is in `range`, not a ghost predicate.
- Bracket balance is a structural property of `RepGraph` (sequences
  and mappings are balanced by the inductive type's constructors).
- Save-time monotonicity is a property of the indexed `Range` type
  (ranges of sub-graphs are nested in the parent's range).

The proof becomes ≤ 30 lines of structural induction over `m`,
chaining algebra-library lemmas. **This is the test of whether
Initiative 4 delivers what it claims.**

</details>

</details>

---

## Algebra library — frozen inventory (23 items)

<details><summary>The 23 named lemmas (Items 0–23) that form the foundation; frozen at end of Phase 1, with any new item triggering a Phase 1 re-open.</summary>

The library is enumerated in this section and **frozen at end of
Phase 1**. No new items past freeze without re-opening Phase 1.

### From the original sketch (Items 0–11)

<details><summary>Items 0–11: immutable data, mapping commutativity, sequence non-commutativity, equivalence relation, idempotence, set-uniqueness, anchors/aliases isomorphism, monoids (position/indent/string/token/fuel).</summary>

| # | Name | Encoding |
|---|---|---|
| **0** | Immutable data | Design constraint, not a lemma. All L1/L2 types are `structure`/`inductive`; state threading is purely functional; no `IO`, no monadic mutation. |
| **1** | Mapping commutativity at L1 | Setoid law. Two mappings with permuted key/value pairs are `≈`-equivalent. (Pairs with Item 3.) |
| **2** | Sequence non-commutativity | Counterexample / no-equational-law marker. Sequences are list-equal under `=`, not under any permutation `≈`. |
| **3** | Equivalence relation `≈` over L1 | `instance : Equivalence (≈)` with reflexivity, symmetry, transitivity. Cycle-handling via `EqMode` parameter (see LoadConfig). |
| **4** | Idempotence `load ∘ dump ∘ load = load` | Theorem at L1. Counterexample at L3 (presentation drift) proven separately. |
| **5** | Set-uniqueness on mapping keys | Conditional on `DuplicateKeyPolicy`. Under `.first`/`.last`/`.merge`, mapping is normalised; under `.error`, parser is partial on duplicates. |
| **6** | Graph isomorphism (anchors/aliases) | **Realised concretely via Item 12 (AnchorMap).** The coalgebraic structure on `RepGraph` is the `AnchorMap`'s insert/find/empty laws. Soundness: `dump ∘ load` preserves the `AnchorMap` reachability up to `≈`. |
| **7** | Position monoid (ordered) | `YamlPos.advance` left-id + assoc. Combined with Item 13's `Ord/LE` instances → ordered monoid. |
| **8** | Indent stack as free monoid | Push/pop laws; identity = empty stack. |
| **9** | Character/string decomposition | `String.toList`, `++`, prefix/suffix laws. Reuses Mathlib where applicable. |
| **10** | Token-stream concat monoid | Token arrays form a free monoid under concat; `scan` as `foldM` over chars. |
| **11** | Parse-side fuel monoid | Fuel composes additively; `parseLoop n` ∘ `parseLoop m` = `parseLoop (n + m)` modulo termination. |

</details>

### From in-scope file inventory (Items 12–17, verified)

<details><summary>Items 12–17 already present in the codebase (verified): AnchorMap, YamlPos order, surface combinator laws, ToYaml/FromYaml typeclasses, schema resolution, token discriminators.</summary>

| # | Name | Source | Encoding |
|---|---|---|---|
| **12** | AnchorMap algebra | `Spec/Types.lean:633–721` | `find?_insert`, `find?_insert_ne`, `find?_empty`. Provides the alias-resolution coalgebra mechanism for Item 6. |
| **13** | YamlPos total order | `Spec/Types.lean:127–134` | `Ord`, `LT`, `LE` instances on `YamlPos.offset`. Composes with Item 7 → ordered monoid. |
| **14** | Surface grammar combinator algebra | `Surface/Combinators.lean:32–82` | Kleene-like laws on `GSeq`, `GAlt`, `GStar`, `GPlus`, `GOpt`: `GStar (GStar P) = GStar P`, `GPlus P = GSeq P (GStar P)`, `GOpt P = GAlt P GEps`, `GSeq` associativity. Currently stated implicitly; Phase 2 names them. |
| **15** | ToYaml / FromYaml typeclass laws | `Schema/FromToYaml.lean:42–107+` | `FromYamlType`, `FromYaml`, `ToYaml` typeclasses already exist with the bridge instance `[FromYamlType α] : FromYaml α`. Round-trip law: `fromYaml? ∘ toYaml = some` for each user instance. |
| **16** | Schema resolution determinism | `Schema/Schema.lean:245–305` | `resolveImplicit` / `resolveScalar` / `resolve` are total deterministic. Resolution precedence (null → bool → int → float → str) is canonical. Lemma: "resolution is a function." |
| **17** | Token discriminator algebra | `Token/Token.lean:241–280` | `YamlToken.isVirtual`, `canStartNode`, `isFlowIndicator` partition tokens into disjoint classes. Exhaustiveness laws cut case-split boilerplate. |

</details>

### From `Proofs/Foundation/` (Items 18–23, already proven)

<details><summary>Items 18–23 are pre-existing in-tree theorems (stripAnchors / adaptForFlowContext idempotence, List/string algebra, LawfulBEq hierarchy) folded into the inventory directly.</summary>

These are pre-existing in-tree theorems that align with the
algebra-first principle and are folded into the inventory directly:

| # | Name | Source | Encoding |
|---|---|---|---|
| **18** | `stripAnchors` idempotence | `Proofs/Foundation/ValueAlgebra.lean:69–94` | `v.stripAnchors.stripAnchors = v.stripAnchors`. |
| **19** | `adaptForFlowContext` idempotence | `Proofs/Foundation/ValueAlgebra.lean:140–174` | Style adaptation idempotence. |
| **20** | `stripAnchors ∘ adaptForFlowContext` commutativity | `Proofs/Foundation/ValueAlgebra.lean:100–136` | `strip ∘ adapt = adapt ∘ strip`. |
| **21** | `(strip ∘ adapt)` pipeline idempotence | `Proofs/Foundation/ValueAlgebra.lean:184–190` | `(strip ∘ adapt) ∘ (strip ∘ adapt) = strip ∘ adapt`. |
| **22** | `List.dropWhile` idempotence + `reverse-trim-reverse` idempotence | `Proofs/Foundation/StringProperties.lean:71–91` | Foundational list/string algebra for whitespace handling. |
| **23** | LawfulBEq hierarchy | `Proofs/Foundation/LawfulBEq.lean:42–110` | `LawfulBEq` instances for `ScalarStyle`, `ChompStyle`, `CollectionStyle`, `BlockScalarMeta`, `Scalar`, `YamlValue`. Reflexivity + `eq_of_beq`. |

</details>

### Closure principle

<details><summary>List is final at end of Phase 1; additional algebraic content must either decompose into existing items or trigger a Phase 1 re-open. Procedural enforcement of Lessons 2 + 5.</summary>

The list above is final at end of Phase 1. Any additional algebraic
content discovered during Phases 3–6 must either:

1. Decompose into existing items, OR
2. Trigger a *re-opening of Phase 1* (a deliberate design re-review,
   not a quiet conjunct addition).

This is the procedural enforcement of Lesson 2 (cap predicate
budget) and Lesson 5 (algebra first, ghost predicates last).

</details>

</details>

---

## Phased plan (milestone-gated, no week estimates)

<details><summary>Six phases (Design → Algebra → Stage C → Stage B → Stage A → Capstone) each gated by DONE criteria; missed criteria force stop-and-reassess.</summary>

Per-phase DONE criteria replace week-based scope gates. If a
phase's criterion isn't met, **stop and reassess** before
committing to the next phase. This is the procedural fix for the
Initiative 3 failure where J.3 ran past its sorry-budget without
formal reassessment.

### Phase 1 — Design  *(closed)*

<details><summary>Design deliverable complete: blueprint written, algebra inventory frozen, LoadConfig settled, indexed-type signatures drafted, worked example walked, branch protocol fixed, D1–D5 resolved.</summary>

**DONE criteria** (all met):
- (i) `Blueprint/08-initiative-4-intrinsic-foundations.md` written and reviewed.
- (ii) Algebra library inventory **frozen** (this document, §Algebra library).
- (iii) `LoadConfig` shape settled; `EqMode` and `DuplicateKeyPolicy` enums final.
- (iv) `RepGraph input range` and `TokenStream input` indexed-type signatures drafted (no proofs).
- (v) Worked example walked through all four layers.
- (vi) Branch protocol settled: `feature/append-only` archived as `archive/initiative-3-stopped`; Initiative 4 implementation lands on `feature/intrinsic-foundations` off `main`.

All five open decisions D1–D5 resolved (see §Decisions table and
§What this document settles).

</details>

### Phase 2 — Algebra library  *(closed on `feature/intrinsic-foundations`)*

<details><summary>Prove all 23 algebra items in `L4YAML/Algebra/`; define `LoadConfig` and indexed types. All six clusters landed (foundation, small-independents, surface combinators, schema, equivalence, idempotence capstone). Phase 2 complete; 23-item inventory frozen.</summary>

**Goal**: prove all 23 inventoried items in a dedicated
`L4YAML/Algebra/` directory.

**DONE criteria**:
- (i) Every item in §Algebra library has a named theorem or instance
  declaration; sorry count = 0 in `L4YAML/Algebra/`.
- (ii) Items 18–23 migrated from `Proofs/Foundation/` to
  `L4YAML/Algebra/` (no semantic change; namespace move only).
- (iii) `LoadConfig` types defined.
- (iv) Indexed types `RepGraph` and `TokenStream` defined as
  `inductive`/`structure` with no scanning/parsing semantics yet.

**Status (foundation + schema cluster landed)**:

| # | Criterion | State |
|---|---|---|
| (i) | All 23 items proved sorry-free in `L4YAML/Algebra/` | **done** — Items 1–23 landed plus Item 0 design constraint. Item 4 (Idempotence capstone) wraps the inventory; sorry count in `L4YAML/Algebra/` = 0; full `lake build` passes 383 targets. |
| (ii) | Items 18–23 moved with namespace rename | **done** — `L4YAML/Algebra/Value.lean` (18–21), `L4YAML/Algebra/StringList.lean` (22), `L4YAML/Algebra/LawfulBEq.lean` (23). All downstream imports updated atomically (Guardrail 1). Sorry count in `L4YAML/Algebra/` = 0. |
| (iii) | `LoadConfig` types defined | **done** — `L4YAML/Config/LoadConfig.lean` defines `EqMode`, `DuplicateKeyPolicy`, `LoadConfig`. Threading into `parse`/`compose`/`construct` is Phase 3+. |
| (iv) | Indexed type signatures drafted | **done** — `L4YAML/Indexed/Range.lean` (`Range input`), `L4YAML/Indexed/RepGraph.lean` (`RepGraph input range` mutual inductive with `RepGraphChild`/`RepGraphPair`), `L4YAML/Indexed/TokenStream.lean` (`TokenStream input` with `IxToken input`). All compile sorry-free. |

**Reflections** (foundation chunk):

1. **D1(b) refinement during implementation**. The settled wording
   was “dependent pair `Σ (r : Range input), RepGraph input r`”
   for nested ranges. Lean 4's nested-inductive elaboration
   rejects `Sigma` whose second component references the inductive
   being defined (kernel error: *“nested inductive datatypes
   parameters cannot contain local variables”*). Resolution:
   realise the same type-level content via a **mutual inductive**
   with sibling types `RepGraphChild input` (single-graph existential
   pack) and `RepGraphPair input` (key/value pair at independent
   ranges). Semantically identical to the Σ-pair encoding; the
   syntactic shape is just the form Lean's elaborator accepts. This
   does **not** trigger a Phase 1 re-open (D1(b) was implementation
   guidance, not a load-bearing API claim).

2. **Migration shape held**. The "namespace move only" promise of
   DONE (ii) survived first contact: every external consumer
   (3 import sites, 1 `open` statement) flipped in the same commit
   as the file moves, satisfying Guardrail 1. The non-inventory
   helpers in `Proofs/Foundation/StringProperties.lean`
   (FoldResult lemmas, validPlainFirst preservation) stayed in place
   and now `import L4YAML.Algebra.StringList` for the two list
   lemmas they share with Item 22.

3. **`Proofs/Foundation/` is now legitimately mixed**. After the
   migration, `Proofs/Foundation/` holds only `CharClass.lean` and
   `StringProperties.lean` — neither is in the algebra inventory,
   both are *consumers* of the algebra. Renaming or relocating that
   directory is **not** a Phase 2 task; it is deferred to whenever
   the scanner cutover (Phase 3) decides where these consumers fit.

4. **Algebra closure check passed for migrated items**. Items 18–23
   each compile against the existing `Spec/Types.lean` and
   `Proofs/Parser/ParserGrammableBase.lean` imports with no
   additional algebraic content beyond the inventory. The closure
   principle (Guardrail 2) is therefore intact for the migrated
   subset; the test for Items 0–17 happens as each lands.

**Reflections** (first algebra cluster — Items 7, 8, 9, 12, 13):

5. **Item 7 design choice — abstract monoid, not scanner-advance**.
   The Item 7 wording in the inventory was “`YamlPos.advance`
   left-id + assoc”. The concrete scanner advancement
   (`ScannerState.advance` in `Scanner/State.lean`) is *not* a
   monoid op — it resets `col` after newlines, so it has no left
   identity at the type level. We therefore split the responsibility:
   `YamlPos.add` (in `L4YAML/Algebra/Position.lean`) is the
   componentwise-additive monoid op with `zero = ⟨0, 0, 0⟩`,
   and the scanner's `advance` remains in `Scanner/State.lean`
   as a *concrete consumer* of positions. The algebra states the
   monoid laws on the abstract op; the scanner's correctness
   theorems will reference `add` when composing token positions.
   This is consistent with how Items 18–23 separate algebraic
   content from parser pipeline.

6. **Item 8 representation choice — `List α`, not `Array α`**.
   The scanner's concrete indent stack is `Array IndentEntry`
   (`Scanner/State.lean:75`), but the algebra is stated on the
   abstract `List α` carrier so the free-monoid laws reduce to
   core Lean's `List.append_assoc` / `List.nil_append` /
   `List.append_nil` without any `Array`-specific reasoning.
   Phase 3's scanner cutover bridges the two via the trivial
   `Array.toList`/`Array.mk` isomorphism. The Item 8 file
   exposes `push`, `pop`, `top?` with `cons` as the underlying
   primitive — push/pop laws then hold by `rfl`.

7. **Item 9 — no Mathlib dependency**. The original inventory
   wording mentioned Mathlib's `String.toList` lemmas. L4YAML
   pulls in `importGraph` and `DocGen4` only; we therefore
   re-state the relevant laws against **core Lean 4.30**'s
   `String.toList_append` and `String.length_append`. No new
   algebraic content beyond the inventory.

8. **Item 12 migration — `Spec/Types.lean` shrinks by ~90 lines**.
   The full `AnchorMap` definition, `insert`/`find?`/`empty`
   operations, and the three laws (plus the
   `list_findSome?_filter_preserves` helper) moved verbatim from
   `Spec/Types.lean:630–721` to
   `L4YAML/Algebra/AnchorMap.lean`. The namespace changed from
   `L4YAML.AnchorMap` to `L4YAML.Algebra.AnchorMap`. Grep
   confirmed the only consumer outside `Spec/Types.lean` was a
   docstring reference in `Indexed/RepGraph.lean` — no atomic
   call-site update was needed (Guardrail 1 trivially satisfied).
   `Spec/Types.lean` now contains only a forwarding comment
   pointing at the new location.

**Reflections** (second algebra cluster — Items 10, 11, 17):

9. **Item 10 representation choice — `List τ`, not `Array τ`**. The
   inventory wording said "token *arrays* form a free monoid".
   Following the Item 8 precedent (Reflection 6), the algebra is
   stated on the abstract `List τ` carrier so the free-monoid laws
   reduce to core Lean's `List` lemmas with no `Array`-specific
   reasoning. The scanner's concrete `Array (Positioned YamlToken)`
   and the indexed `TokenStream input` (in
   `L4YAML/Indexed/TokenStream.lean`) are isomorphic to `List` via
   `Array.toList`/`Array.mk`, and Phase 3's scanner cutover bridges
   the two through that trivial isomorphism. Choosing `List`
   uniformly across Items 8 and 10 means the indent-stack and
   token-stream algebra share the same equational kernel.

10. **Item 11 — total + partial composition, not just one**. The
    Phase 1 wording "modulo termination" is realised as **two**
    iteration-composition laws living side-by-side:
    `iterate_add` (total `step : α → α`, unconditional) and
    `iterateOpt_add` (partial `step : α → Option α`, threaded
    through `Option.bind`). The partial form is the one the
    parser will actually rewrite onto in Phase 4 (each
    `parseNode`/`parseBlockSequenceLoop` rule is a partial step
    after stripping `ParseState` and `Except`); the total form is
    kept so abstract reasoning about fuel composition that
    doesn't need failure-threading stays simple. This is the
    "ghost predicates last" principle applied at the lemma level —
    the conditional form does not assume any intermediate
    invariant, leaving per-rule progress to Phase 4. The
    blueprint estimate of ~80 LOC was light by ~100 (final 187
    LOC) because of the dual statement; closure (Guardrail 2) is
    nonetheless intact — every theorem is a `Nat.iterate` /
    `Option.bind` fact, not new algebra.

11. **Item 17 — classifiers, not a partition**. The Phase 1
    wording said `isVirtual`/`canStartNode`/`isFlowIndicator`
    "partition tokens into disjoint classes". Verifying against
    `Token/Token.lean:241–270`, two of the three pairs overlap:
    `isVirtual ∩ canStartNode = {blockSequenceStart,
    blockMappingStart}` and `canStartNode ∩ isFlowIndicator =
    {flowSequenceStart, flowMappingStart}`. Only
    `isVirtual ∩ isFlowIndicator = ∅` is genuinely empty. The
    file therefore exposes them as *classifiers* — three
    independent decidable predicates with per-constructor `rfl`
    simp lemmas — and proves only the disjointness that actually
    holds (`not_virtual_of_flow`, `not_flow_of_virtual`). This is
    parallel to the Item 7 refinement (Reflection 5):
    implementation contradicted inventory wording, so the
    wording was refined rather than the implementation forced to
    match a false claim. Closure (Guardrail 2) holds — every
    theorem is a per-constructor evaluation or a Bool-level
    case-split over those evaluations.

12. **Item 17 LOC overrun, by design**. The blueprint estimate
    was ~100 LOC; the file landed at 311 LOC because every one
    of the 22 `YamlToken` constructors contributes one `rfl`
    simp lemma per discriminator (22 × 3 = 66 lemmas) so
    downstream `simp` calls discharge case-splits without
    needing `cases t`. The alternative — stating only the
    "positive" cases and relying on `cases <;> rfl` at use sites
    — saves LOC here but pushes the case-split into every
    consumer. The case-split-per-constructor form is the
    intended consumer interface for Phase 3 (scanner state
    machine) and Phase 4 (parser dispatch). Closure (Guardrail
    2) holds; no new algebra introduced.

**Reflections** (third algebra cluster — Item 14):

13. **Item 14 — relation equivalence, not relation equality**. The
    inventory wording reads `GStar (GStar P) = GStar P`,
    `GPlus P = GSeq P (GStar P)`, `GOpt P = GAlt P GEps`, which on
    its surface asks for *relation* equalities. Two relations
    `R₁ R₂ : SurfPos → SurfPos → Prop` are pointwise-equivalent
    iff `∀ s s', R₁ s s' ↔ R₂ s s'` (the relation extensionality
    principle). `funext` + `propext` would lift each such `Iff`
    to a strict `=`, but the `Iff` form is what every downstream
    rewrite actually consumes — proofs case-split on a grammar
    witness and re-pack it on the other side, which is exactly
    an `Iff`. The file therefore states each law as
    `∀ s s', R₁ s s' ↔ R₂ s s'` and leaves the lift to `=` to
    any consumer that needs it. Closure (Guardrail 2) holds —
    every law is structural induction over the existing
    `GSeq`/`GAlt`/`GStar`/`GPlus`/`GOpt`/`GSeq3`/`GEps`
    constructors.

14. **Item 14 — term-mode `match` over tactic-mode `cases` for
    indexed inductives**. The seven surface combinators are
    *indexed* inductives — their indices (`SurfPos` start- and
    end-positions) constrain which constructors fire. Lean's
    tactic-mode `cases h with | ctor a b c ...` required the
    user to know exactly how many name-slots each constructor
    consumes *after* index unification, which differed per
    constructor and (in this codebase's observed cases) per
    constructor inside the same inductive. Term-mode
    `match h with | .ctor _ _ ... =>` sidesteps that ambiguity:
    the pattern literally mirrors the constructor's full
    signature, and the underscore convention discharges
    name-slot mismatches for free. The bulk of the file is
    therefore in term mode, with tactic mode used only where
    index unification needs to substitute back into the goal
    type (`opt_iff_alt_eps`'s `.none`/`.right` branches and the
    inductive `star_star` / `star_append`). This is a
    proof-style refinement, not a soundness or closure concern.

**Reflections** (fourth algebra cluster — Items 15, 16):

15. **Item 16 — `unfold` doesn't reduce literal `match`-on-string**.
    `resolveScalar` is a top-level `match tag? with | some "tag:yaml.org,2002:bool" => ...`.
    With `tag? = some "tag:yaml.org,2002:bool"` substituted in,
    `unfold resolveScalar` exposes the body but leaves the outer
    `match` un-reduced — Lean's elaborator treats string-literal
    patterns as decidable equalities that aren't normalised by
    plain unfold. Two paths through this: (a) `simp [resolveScalar]`
    drives the outer match by definitional equality and works on
    every arm; (b) `show (match isBool content with | ...)` rewrites
    the goal to the inner-only match shape, after which a single
    `rw [h]` discharges the remaining `isBool content`. We picked
    (b) for the seven tag-precedence lemmas because it leaves the
    `simp` set minimal and the proof script literally mirrors the
    intended reduction sequence (outer-match-by-rfl, inner-match-by-rewrite).
    This is a proof-style refinement, not a soundness concern.

16. **Item 15 — class statement only, no instances**. Per D2
    (Blueprint 08 §What this document settles), `LawfulRoundTrip`
    is a separate typeclass carrying the law
    `∀ a, fromYaml? (toYaml a) = .ok a`. Phase 2's deliverable is
    the **statement**; Phase 5's `FromToYaml` cutover discharges
    instances per primitive type (`Int`, `Nat`, `Bool`, `String`,
    `Float`, …). Co-locating an instance here would either fix the
    semantics prematurely (e.g. `Int`'s instance has to commit to
    the precedence ordering's behaviour on decimal vs. octal vs.
    hex round-trips) or invite ghost-style conjuncts back into the
    file. Keeping the class isolated preserves Guardrail 2: Item 15
    is one line of statement, Item 16 is the precedence laws, and
    the round-trip law-discharge sits at the Phase 5 boundary.

17. **Bridge theorem `fromYaml_via_resolve` is `rfl`, but worth
    naming**. The bridge `fromYaml? = fromYamlType? ∘ resolve` for
    types with `[FromYamlType α]` is true *definitionally* (it's
    just the instance body in `Schema/FromToYaml.lean:63–64`).
    Stating it as a `theorem` and explicitly pinning the implicit
    instance argument (`@fromYaml? α (instFromYamlOfFromYamlType)`)
    gives Phase 5 a named rewrite hook: the first line of every
    `LawfulRoundTrip Int` (or `Nat`, `Bool`, …) proof can
    `rw [fromYaml_via_resolve]` rather than `unfold fromYaml?`,
    which keeps the proof robust against future overlap-instance
    additions on `FromYaml`. Closure (Guardrail 2) holds — the
    theorem adds no new algebraic content.

18. **Item 16 LOC came in around blueprint estimate**. The file
    landed at 265 LOC vs. the blueprint estimate of ~200 LOC. The
    overrun is 5 `resolveImplicit` precedence lemmas + 7
    `resolveScalar` tag-precedence lemmas + 6 `resolve` /
    `resolveList` / `resolvePairs` constructor unfoldings = 18
    rfl/simp-driven lemmas, each ~5–8 lines. The constructor
    unfoldings (`resolve_scalar`, `resolve_alias`, the four
    `resolveList` / `resolvePairs` cases) were not in the original
    blueprint sketch but are required so Phase 4 / Phase 5 proofs
    walk `YamlValue` without re-unfolding `resolve` by hand.
    Closure (Guardrail 2) holds — every unfolding is `rfl`.

**Reflections** (fifth algebra cluster — Items 1, 2, 3, 5, 6):

19. **Item 3 — `refl`/`symm`/`trans` as inductive constructors over
    a derived-equivalence layer**. There are two stylistic choices
    for stating `YamlEquiv`: (a) derive it as the smallest
    equivalence containing a single `mapping_perm` axiom, lifted
    through structural congruence; (b) bake `refl`/`symm`/`trans`
    in as primitive constructors of the inductive. (a) is cleaner
    in a typeclass-driven setting (the `Equivalence` instance
    follows from one auxiliary lemma per direction). (b) is
    cheaper to *use*: the `Equivalence` instance is one line
    (`⟨refl, symm, trans⟩`) and downstream proofs case-split on
    constructors directly. We picked (b) for Phase 2 because the
    one-line `Equivalence` instance is exactly what Phase 4's
    `EqMode.strict` consumer needs. Closure (Guardrail 2) holds —
    no structural-congruence lifting beyond `mapping_perm`.

20. **Item 2 — `decide` discharges string inequality at the
    bottom of the chain**. The Item 2 counterexample resolves to
    `"a" = "b"` after three `injection` steps. `decide` closes that
    leaf goal in one line because `String` has a `DecidableEq`
    instance pulled in automatically. The chain (`sequence` ≠ →
    `Array` ≠ → `List` cons inj → `alias` injection → string ≠)
    is verbose (six lines) but mechanical; using `injection` instead
    of `simp` keeps the proof legible because each step exposes the
    *next* injectivity obligation rather than `simp`-collapsing
    them into one opaque chain. This pattern carries over to any
    future no-equational-law counterexample (e.g. sequence-style
    differences if we later want to assert block vs. flow are
    `=`-distinct).

21. **Item 5 — `dedupFirst` idempotence via `dedupFirst_of_noDup`**.
    The standard idempotence proof for first-occurrence dedup is:
    (a) prove `noDup_dedupFirst` (the output is already de-duped);
    (b) prove `dedupFirst_of_noDup` (an already-de-duped list is
    fixed by `dedupFirst`); (c) compose. Step (b) is the
    interesting one — it needs `List.filter_eq_self.mpr` and the
    fact that `LawfulBEq YamlValue` (Item 23) lets us turn `k' ≠ k`
    into `(k' == k) = false` via `beq_eq_false_iff_ne`. The proof
    cost of having `LawfulBEq YamlValue` already discharged was
    significant: without it, the filter-condition reduction would
    require additional case-analysis on the `BEq` instance. This
    is a concrete payoff of Initiative 4's algebra-first ordering
    (Items 23 first, Item 5 later).

22. **Item 6 — typeclass shape only, deferring `Bisimulation`
    instances to Phase 4**. Per D3, `Bisimulation` is the witness
    typeclass for `EqMode.bisim`. Phase 2's deliverable is the
    typeclass *shape* (carrier `α`, relation `isBisim`, symmetry
    law). Instances at `RepGraph input range` land in Phase 4
    with the indexed-type cutover. `anchorReachable` is the one
    concrete fact Item 6 needs from Item 12 (AnchorMap) — its
    `iff`-form `anchorReachable m name v ↔ m.find? name = some v`
    is `rfl`. Closure (Guardrail 2) holds — Item 6's algebraic
    content lives in Item 12's `find?_insert` / `find?_insert_ne`
    / `find?_empty` laws; this file adds only the *interface* by
    which Phase 4's parser will consume them.

23. **Item 5 LOC blew through estimate; rest came in under**. The
    blueprint estimate for the entire cluster was ~250 LOC; the
    file landed at 352 LOC (40% over). The overrun is concentrated
    in Item 5 (`dedupFirst` + idempotence proof = 95 lines vs.
    ~50 estimated) — the auxiliary lemmas `nodup_filter` and
    `not_mem_keys_filter` cost 35 lines together because filtering
    a pair list while reasoning about the **key projection** needs
    explicit `List.mem_map ↔ ∃ x, x ∈ filter` round-trips. Items
    1 + 2 + 3 came in under estimate (~70 LOC total for the
    equivalence relation + counterexample) and Item 6 was ~30
    lines. Closure (Guardrail 2) holds — no item exceeds its
    stated content.

**Reflections** (sixth algebra cluster — Item 4, Idempotence capstone):

24. **Item 4 is one line on top of Item 21.** The L1 statement
    `canonicalize ∘ canonicalize = canonicalize` reduces literally
    to `stripAnchors_adaptForFlowContext_pipeline_idempotent`
    (Item 21, proved in `Algebra/Value.lean`). The Phase 2 stress
    test passes because the capstone *factors through* the
    cluster-21 packaging — `unfold canonicalize; exact …` is the
    entire proof. The capstone file's 462 LOC is therefore not
    the Item 4 proof itself but the **invariance corollaries**
    (resolution preservation, anchor stripping, key-uniqueness,
    abstract law) that connect Item 4 to Items 5, 6, 12, 15, 16.
    The closure stress test is *passed by construction*: no
    primitive outside Items 0–23 appears anywhere in the file.

25. **Schema-resolution invariance needed a fresh `resolveList_eq_map`
    helper that mirrors the parser's anchor-resolution one.** The
    pattern `where`-clause helper → `List.map` form is already used
    twice in the codebase (`stripList_eq_map`/`adaptList_eq_map` in
    `ParserGrammableBase.lean`, and `resolveList_eq_map` for
    `YamlValue.resolveAliases`). Item 4 §4 added a third instance
    for `Schema.resolve.resolveList` / `resolvePairs`. The pattern
    is becoming canonical: every where-clause-recursive function on
    `YamlValue` benefits from this rewrite when invariance under a
    metadata-only transform is being proved. Worth considering a
    macro or `@[simp]` framework in Phase 4 to avoid repeating the
    three-line `by induction l ⋯` boilerplate.

26. **The abstract `LawfulRoundTrip₁` predicate is intentionally
    parametric over the dump-target type.** Phase 5 will instantiate
    `T := String` (parse + dump). Stating the law as
    `∀ s : T, load (dump (load s)) = load s` rather than the
    constructor-by-constructor L1 round-trip lets Phase 5 specialise
    *once* per dump format (presentation drift at L3 means each
    style choice produces a different `dump`, but they all factor
    through the same L1 stable form). The Phase 2 file ships the
    statement and a trivial L1 instance (`load = canonicalize`,
    `dump = id`); Phase 5 fills in the real instances.

27. **Capstone LOC came in at 462 vs. 400 estimate (~15% over).**
    The overrun is concentrated in §4 (resolve invariance =
    ~80 lines per direction × 2 directions = ~160 LOC) and the
    closure documentation tables (§8 = ~40 LOC including the items-
    used summary). The Item 4 proof itself (§2) is 6 lines. The
    capstone's *value* is not in lines-of-proof but in the
    cross-cluster wiring it documents — every downstream consumer
    that needs "round-trip preserves X" now has a one-line lemma to
    rewrite with.

28. **Guardrail 2 stress test verdict: pass.** The L1 round-trip
    idempotence is provable using only Items 0–23. No 24th
    primitive is needed; Phase 1 remains closed. This is the
    formal closure check the Phase 2 plan called for: the
    algebra inventory is **complete with respect to the L1
    round-trip statement**. Phase 5's L3 statement (presentation
    drift counterexample) will be a separate matter, but the L1
    half is now algebraically discharged.

**Out of scope**: any scanner/parser code. The algebra library does
not depend on `Scanner/`, `Parser/`, or any J.3-era infrastructure.

#### Phase 2 closure note

<details><summary>All six clusters landed; the 23-item inventory is closed. Phase 3 (Scanner cutover on indexed types) is the next milestone.</summary>

All six algebra clusters are now **landed**: foundation (Items
18–23, Item 12), the small-independents pair (Items 7, 8, 9, 10,
11, 13, 17), the surface-combinator laws (Item 14), the schema
laws (Items 15, 16), the equivalence + collection laws (Items 1,
2, 3, 5, 6), and the **Idempotence capstone** (Item 4) in
`L4YAML/Algebra/Idempotence.lean`. The capstone passed the
Guardrail 2 stress test: the L1 statement
`load ∘ dump ∘ load = load` is provable using only Items 0–23,
with no 24th primitive needed.

**Phase 2 DONE-criteria (i)–(iv) are all `done`.** Sorry count in
`L4YAML/Algebra/` is 0; full `lake build` passes 383 targets.
The 23-item inventory remains **frozen** and **closed**.

**Next milestone**: Phase 3 — Stage C (scanner) on indexed types,
decomposed into six sessions (sub-plan in §Phase 3). **Steps 1–3
landed**: indexed-type extensions (Reflections 29–31), the
character/whitespace layer with bidirectional spec proofs
(Reflections 32–35), and the indentation / line-break dispatch
layer (Reflections 36–38) — the latter also closing the Step 2
deferred termination + count = column-delta obligation in
`IndexedWhitespace.lean`. **Step 4a landed** (Reflections 39–40):
quoted scalars (single + double) and a single-line plain scalar
recogniser, plus the deferred `skipToContent_progress` closure.
**Step 4b landed** (Reflections 41–42): block scalars
(literal + folded with `FoldState` + chomping) and multi-line
continuation for quoted + plain scalars. The Step 4a deferrals
(a)–(c) are closed; (d) hex-escape value correctness and
(e) full content-correctness are explicitly carried into Step 5.
**Step 5a landed** (Reflections 43–45): top-level dispatcher
(`scanNextTokenIx_*` family, `scanLoopIx`, `scanIx`) over
`ScannerStateIx input` (indent stack + simple-key + flow level +
directive bookkeeping). `SimpleKeyStateIx` is indexed on `input`
and carries an `IxCursor`, so placeholder-overwrite at the saved
key position needs no separate bound proof. The dispatcher's
offset-monotonicity chain was initially mediated by `emitAtSafe`
(a defensive emit that performs the bound check at runtime).
**Step 5b.1a landed** (Reflection 46): the 7 `collect*Ix`
helper-loop offset-monotonicity lemmas + `skipDocEndWhitespaceIx`
proven; all 10 `emitAtSafe` call sites replaced with `emitAt` +
inline-proof; `emitAtSafe` deleted. `scanYamlDirectiveIx` and
`scanTagDirectiveIx` gained an `hStart` parameter (caller-supplied
bound) discharged by `scanDirectiveIx` via the directive-name
collect-loop + `skipWhitespace` monotonicity chain.
**Step 5b.1b.i landed** (Reflection 47): the per-dispatcher
monotonicity cluster (5b.1b) was further split into
5b.1b.i–iv after first reading turned up ~12 missing
state-helper preservation lemmas behind the blueprint's
"single-line chain" framing. 5b.1b.i lands those helpers in a
new `Proofs/Scanner/IndexedDispatch.lean` file:
`IxCursor.advanceN_offset_monotonic` plus, on `ScannerStateIx`,
`emit_cursor` / `emitAt_cursor` / `emitAtCursor_cursor` /
`overwriteAtCursor_cursor` / `advance_cursor` /
`advance_offset_monotonic` / `advanceN_cursor` /
`advanceN_offset_monotonic` / `pushSequenceIndentIx_cursor` /
`pushMappingIndentIx_cursor` / `unwindIndentsLoopIx_cursor` /
`unwindIndentsIx_cursor` / `saveSimpleKeyIx_cursor` /
`scanValuePrepareIx_cursor` / `skipSpacesS_cursor` /
`skipSpacesS_offset_monotonic` / `skipWhitespaceS_cursor` /
`skipWhitespaceS_offset_monotonic` / `skipToContentS_cursor` /
`skipToContentS_offset_monotonic`. The cursor-level lemmas for
`consumeLineBreak` / `skipCommentText` / `skipToContent` already
existed in `IndexedWhitespace.lean` and `IndexedIndent.lean` —
5b.1b.i lifts them through `ScannerStateIx`.
**Step 5b.1b.ii landed** (Reflection 48): ten per-dispatcher
offset-monotonicity lemmas added to
`Proofs/Scanner/IndexedDispatch.lean` —
`scanBlockEntryIx_offset_monotonic`, `scanKeyIx_offset_monotonic`,
`scanValueIx_offset_monotonic`, `scanFlowEntryIx_offset_monotonic`
(Pattern A — always `.ok`); `scanDocumentStartIx_offset_monotonic`,
the four `scanFlow{Sequence,Mapping}{Start,End}Ix_offset_monotonic`
(Pattern B — state-returning); `scanDocumentEndIx_offset_monotonic`
(Pattern C — `Except` with early- and late-`throw` branches). The
do-block desugaring blocks `split at h` until `pure_bind` and
`if_pos`/`if_neg` peel the outer wrapper.
**Step 5b.1b.iii landed** (Reflection 49): five per-dispatcher
offset-monotonicity lemmas for the node-property + directive
dispatchers —
`scanAnchorOrAliasIx_offset_monotonic`,
`scanTagIx_offset_monotonic`,
`scanYamlDirectiveIx_offset_monotonic`,
`scanTagDirectiveIx_offset_monotonic`,
`scanDirectiveIx_offset_monotonic`. Chains thread through the
5b.1a `collect*LoopIx_offset_monotonic` helpers
(`collectAnchorNameLoopIx`, `collectTagHandleLoopIx`,
`collectTagSuffixLoopIx`, `collectVerbatimTagLoopIx`,
`collectDirectiveNameLoopIx`, `collectVersionMajorLoopIx`,
`collectVersionMinorLoopIx`) and `skipWhitespace_offset_monotonic`.
The directive helpers are stated relative to the explicit
`cAfterWS` parameter (`cAfterWS.pos.offset ≤ s'.cursor.pos.offset`)
since the dispatcher overwrites the input state's cursor anyway;
`scanDirectiveIx` chains through them via the leading
`advance` + `collectDirectiveNameLoopIx` + `skipWhitespace`. The
new Reflection 49 captures the term-level `let`-block obstacle:
`split at h` does not see through `let`/`have` bindings buried
under `unfold`, so we either pre-emit `simp only at h` (to
zeta-reduce) before `split`, or peel each `if` with
`by_cases hc` + `rw [if_pos hc / if_neg hc] at h`.

**Step 5b.1b.iv-pre landed** (Reflection 50): tokens-size growth
infrastructure for the dispatcher layer. Added 6 simp lemmas for
`emit` / `emitAt` / `emitAtCursor` / `overwriteAtCursor` / `advance`
/ `advanceN` token-side effects, plus 10 `_tokens_size_le` chain
lemmas for the 5b.1b.ii / 5b.1b.iii dispatchers
(`scanBlockEntryIx`, `scanKeyIx`, `scanValueIx`, `scanFlowEntryIx`,
the four `scanFlow*` start/end, `scanDocumentStartIx`,
`scanDocumentEndIx`, `scanAnchorOrAliasIx`, `scanTagIx`,
`scanYamlDirectiveIx`, `scanTagDirectiveIx`, `scanDirectiveIx`).

**Step 5b.1b.iv-cont landed** (Reflection 51): the seven top-level
chain lemmas — `scanNextTokenIx_preprocess` (only one that uses the
R50 nested-`split` skeleton without do-block early-return),
`scanNextTokenIx_dispatchStructural`/`dispatchFlowIndicators`/
`dispatchBlockIndicators` (do-blocks with early `return some _`),
`scanNextTokenIx_dispatchContent` (always-state return with three
scalar-`Option` matches and dependent `hBS`/`hDQ`/`hSQ` witness
binders), `scanNextTokenIx` (the per-iteration chain), and
`scanLoopIx_tokens_size_le` (fueled top-level, induction on fuel).
Two new techniques landed: (1) `by_cases hg + rw [if_pos / if_neg]`
threaded with `cases hF : f s with | error => cases h | ok v => ...`
to peel do-block guards explicitly (the `__do_jp` join-point chain
otherwise blocks `split at h`); (2) `split at h` (not `cases : ...
with`) is the right tactic for matches with dependent witness binders
(`match hBS : f s with`), because `cases` introduces a name that
`rw` can't substitute through the witness-dependent motive.
Reflection 51 captures both fixes.

**Step 5b.2 landed** (Reflection 52): tab-in-indentation hardening
for `scanBlockEntryIx` and `scanKeyIx`. `IndexedState.lean` gained
the indexed analogues of the legacy `hasTabInPrecedingWhitespace`
backward-scan; `IndexedDispatch.lean` gained the `tabInIndentation`
throw branch in both indicator scans (in block context only). The
monotonicity proofs (`_offset_monotonic` + `_tokens_size_le` for
both scans) were re-derived; the key new technique was three
`inFlow`-preservation simp lemmas (`emit_inFlow`, `advance_inFlow`,
`pushMappingIndentIx_inFlow`, all rfl-trivial) plus three
corresponding `flowLevel` lemmas, which let
`simp only [if_pos hi, advance_inFlow, emit_inFlow,
pushMappingIndentIx_inFlow] at h` collapse the post-pushMapping/
emit/advance `!s.inFlow` guard against the *original* `s.inFlow`
with a single `by_cases hi` on the original flag. Reflection 52
generalises: **when the same flag gates both a let-binding side
effect and a subsequent guard, add a preservation simp lemma for
each intermediate operation.**

**Step 5b.3 landed** (Reflection 53): `scanValueIx` was split
into the legacy four-stage chain `scanValueClearKeyIx /
scanValueValidateIx / scanValuePrepareIx / scanValueTabCheckIx` so
each stage carries one provable property — clear-key is a pure
state transformation, validate is `Except ScanError Unit` (five
violation cases per §7.4 / §7.4.2 / §8.2.1 / T833 / §8.2.2 [197]),
prepare resolves placeholders or pushes mapping indent (already
landed in Step 5b.1b.i), and tab-check enforces §6.1 against the
*original* `s.cursor.pos.col` + `s.currentIndent`. The two existing
`scanValueIx_*` monotonicity proofs needed structural updates:
`subst h` after `simp only [Except.ok.injEq] at h` no longer fits
once the do-block contains two `Except`-throwing calls (the
elaborated term carries `have s_kc := scanValueClearKeyIx s; do …`
with a `have`-binder that blocks `rw`/`subst` over the
sub-expressions). The legacy pattern — `simp only [bind,
Except.bind] at h; split at h; cases h | ...` — peels each
`.error`-branch as `cases h` (contradiction) and leaves the
all-`.ok` branch with the constructed state to `simp` over emit/
advance preservation lemmas. Two new helper lemmas landed
(`scanValueClearKeyIx_cursor` `@[simp]`,
`scanValueClearKeyIx_tokens_size_le`); the same commit fixed
unrelated breakage in `Proofs/Scanner/IndexedScalar.lean` and
`Proofs/Scanner/IndexedIndent.lean` that the prior
spec-traceability refactor had introduced (quoted-loop /
parseBlockHeader nested-if shapes, the `'#'` literal → `match …
isCommentBool d` form) but that the `lake build` cache had hidden.

**Step 5b.4 landed** (Reflection 54): the hex-escape
value-correctness obligation carried from Step 4a was discharged
as four lemmas in `Proofs/Scanner/IndexedScalar.lean`'s Layer
E1.4 — `hexDigitValue_lt_16` (digit bound for hex chars),
`hexStringValue_empty` / `hexStringValue_push` (foldl snoc law
lifted to `List.foldl` via `String.foldl_eq_foldl_toList` +
`String.toList_push` + `List.foldl_append`), `hexStringValue_lt_pow`
(`16^n` bound via `String.push_induction`), and
`parseHexEscapeIx_decoded` packaging the parser spec
(`ch = Char.ofNat (hexStringValue digits)` with the `< 0x110000`
guard already discharged). The proof-shape lesson: the simp
combination that pushes Bool-Or disjuncts into Nat-`≤` conjuncts
leaves the hypothesis as `(d ∨ u) ∨ l` (Lean's `||` is
left-associative) with `Nat.le` conjunctions inside. `rcases ... with
⟨_,_⟩ | ⟨_,_⟩ | ⟨_,_⟩` fails because it tries to destruct `Nat.le`
via `Nat.le.refl`. Plain `cases h with | inl … | inr …` (two nested
levels) routes around it.

**Step 5b.5 landed** (Reflection 55): the block-scalar auto-detect
indent loop now carries the lower-bound lemma
`autoDetectBlockScalarIndentLoopIx_ge_min` plus its entry-point
wrapper `autoDetectBlockScalarIndentIx_ge_min` in
`Proofs/Scanner/IndexedScalar.lean`'s new "Layer F.1" section. Both
state `minContentIndent ≤ result`, which is the spec-mandated bound
that downstream block-scalar content-correctness proofs (Step 5b.6)
will need to mediate against the YAML 1.2.2 content-indent rule
([162]). The proof shape: induction on `fuel` (zero ⇒ EOF-style
guard, `split <;> omega`; succ ⇒ three nested `split`s — the
`let (probeAfterSp, _) := skipSpaces probe` prod destructure, the
`match probeAfterSp.peek?` arm, and finally the inner
`if isLineBreakBool ch`). The recursive branch is closed by
`apply ih` because the IH is universally quantified over `maxWSCol`
(the running max-whitespace-column accumulator).

**Step 5b.6 landed** (Reflection 56): the block-scalar
content-correctness obligation discharged as six lemmas in
`Proofs/Scanner/IndexedScalar.lean`'s new "Layer F.2 — Block-scalar
content correctness" section. `applyChomp` (chomp indicator [160])
gets four spec-traceability lemmas: `applyChomp_keep` (identity,
`rfl`), `applyChomp_strip` (`= stripTrailingNewlines raw`, `rfl`),
and the two `applyChomp_clip_of_endsWith` / `_of_not_endsWith` arms
discharged by `simp [applyChomp, h]`. `foldBlockContent` (fold
machine [170]–[181]) gets two base-case lemmas: `foldBlockContentGo_nil`
(empty input list, `rfl`) and `foldBlockContent_empty` (the wrapper
on `""`, `rfl`). All six proofs are definitional unfolds — the
correctness theorems pin each Lean function branch to its spec rule
and serve as named anchors that downstream Steps 5b.7 (quoted
multi-line) and 5b.8 (plain multi-line) can cite when reasoning
about the block-scalar pipeline `parseBlockHeaderLoopIx →
blockHeaderToBodyIx → autoDetectBlockScalarIndentIx →
collectBlockScalarLoopIx → applyChomp → foldBlockContent`.

**Step 5b.7 landed** (Reflection 57): the quoted multi-line
content-correctness obligation discharged as nine spec-traceability
lemmas in `Proofs/Scanner/IndexedScalar.lean`'s new "Layer F.3 —
Quoted multi-line content correctness" section.
`foldQuotedNewlinesIx` (§6.5 [73] / [74]) gets two branch-mapping
lemmas: `foldQuotedNewlinesIx_of_blank_lines` (when
`emptyCount > 0`, the folded replacement is
`String.ofList (List.replicate emptyCount '\n')` per `b-l-trimmed`
[71]) and `foldQuotedNewlinesIx_of_single_break` (when
`emptyCount = 0`, the replacement is `String.singleton spaceChar`
per `b-as-space` [70]). `collectDoubleQuotedLoopIx` (§7.3.1
[111]–[116]) gets three branch lemmas — `_zero`, `_closing`,
`_linebreak`; `collectSingleQuotedLoopIx` (§7.3.2 [122]–[125])
gets four — `_zero`, `_doubled` (the `''` quoted-quote escape
`[123]`), `_closing_some` / `_closing_none` (single `'` followed by
non-`'` or by EOF), and `_linebreak`. The proof shape mirrors
Step 5b.6 — `rfl` for base cases, `unfold + rw + simp` for branches
that don't recurse, and the **`conv => lhs;` scoped unfold** for
the three branches whose RHS is another `collectXxxQuotedLoopIx`
call (otherwise plain `unfold` rewrites both sides and `simp`
expands the RHS into the full match-cascade — see Reflection 57).

**Step 5b.8 landed** (final Step-5b sub-step): the plain multi-line
content-correctness obligation discharged as 12 spec-traceability
lemmas in `Proofs/Scanner/IndexedScalar.lean`'s new "Layer F.4 —
Plain multi-line content correctness" section. `collectPlainScalarLoopIx`
(§7.3.3 [131]–[135]) is the most branch-heavy collector in the
scanner: each of its 11 outcomes — `_zero`, `_eof`, `_comment`,
`_colon_terminate`, `_colon_continue`, `_flow_indicator`,
`_linebreak_flow`, `_linebreak_block_none`, `_linebreak_block_some`,
`_whitespace`, `_not_plain_safe`, `_content` — gets a named branch
lemma. The threaded `content ++ folded` composition (what
`ns-plain-multi-line(n,c)` [134] describes) is visible in the two
line-break branches: `_linebreak_flow` reuses `foldQuotedNewlinesIx`
(Layer F1, §6.5 [73] / [74]) in flow context; `_linebreak_block_some`
threads `handleBlockLineBreakIx`'s folded prefix in block context.
Proof shape mirrors Step 5b.7 — `rfl` for `_zero`, `unfold + rw`
for `_eof`, `unfold + rw + simp` for the five non-recursive
terminator branches, and **`conv => lhs; unfold …` for the five
RHS-recursive branches** (`_colon_continue`, `_linebreak_flow`,
`_linebreak_block_some`, `_whitespace`, `_content` — direct
application of Reflection 57, no new failure modes encountered).
Each branch lemma takes the cascade-prefix predicates as explicit
hypotheses (e.g. `isCommentBool ch = false` to skip the `#` branch);
downstream consumers prove these from the concrete character at
the cursor.

**Step 5c landed** (the final pre-cutover step in Phase 3): the
indexed presenter and corpus-roundtrip theorem land as two new
staging files. `L4YAML/Scanner/IndexedPresenter.lean` (~121 LOC,
new) defines `renderToken : IxToken input → String` —
constructor-level dispatch from token to source contribution —
and `present : TokenStream input → String` as the fold
`ts.tokens.foldl (· ++ renderToken ·) ""`. The hybrid render is
necessary because the indexed scanner's indicator-token convention
(`emit` followed by `advance`, so the token's `[start, stop)`
range is zero-width at the position *before* the indicator
character) makes a pure source-span fold lose the single-character
indicators; `renderToken` re-injects the literal `[`/`]`/`{`/`}`/
`,`/`-` characters (and the `---`/`...` document markers) and
omits the implicit `key`/`value` tokens. Content tokens
(`scalar`, `anchor`, `alias`, `tag`, `comment`, `versionDirective`,
`tagDirective`) keep the source-span extraction via
`String.Pos.Raw.extract` (the Lean 4.30 raw-offset extract API,
since the new `String.extract` requires validated `s.Pos`
positions that the IxToken's `Nat`-offsets don't carry directly).

`L4YAML/Proofs/Scanner/IndexedRoundtrip.lean` (~158 LOC, new)
exhibits the roundtrip law on a 19-entry fixed corpus via
`native_decide`: `roundtripOk input` is the `Bool`-valued check
`match scanIx input with | .ok ts => present ts == input | .error _ => false`,
and each `theorem roundtrip_xxx : roundtripOk "…" = true := by
native_decide` line evaluates both `scanIx` (the full
indexed-scanner pipeline, fueled) and `present` on the concrete
input via Lean's native-code evaluator. The corpus covers the
empty input, single/multi-character plain scalars at root, empty
and one-/two-/three-/four-element flow sequences, empty and
one-/two-key flow mappings, and three nesting patterns
(`[[]]`/`[{}]`/`{[]}`/`[[],[]]`/`[a,[b,c]]`/`[{a},b]`/`{a,{b}}`).
A closing `scanIx_present_of_roundtripOk` lemma turns
`roundtripOk input = true` into the existential form
`∃ ts, scanIx input = .ok ts ∧ present ts = input` — the
Blueprint's `scanIx (present ts) = .ok ts` statement follows by
rewriting `present ts = input` on the LHS.

**Step 6a landed** (Reflection 61): the indexed parser state
record and navigation primitives land in a single staging file,
`L4YAML/Parser/ParseStateIx.lean` (304 LOC, sorry-free). The
file is a 1-to-1 mirror of legacy `Parser/State.lean` with the
type-level change `tokens : Array (Positioned YamlToken)
→ tokens : Indexed.TokenStream input`, plus the cascading
substitutions `Positioned.val → IxToken.token` and
`Positioned.pos → IxToken.start`. Everything else — anchor map,
tag handles, position-tracking state, `NodeProperties`, tag
resolution, `parseNodeProperties`, `emptyNode`,
`applyNodeFinalization`, `validateNodeProps` — ports verbatim
modulo the `input` type parameter, because those helpers only
manipulate `YamlValue` and `YamlPath` state that is shared
between the two parsers. The one departure from legacy form
that *did* require rewriting accessor bodies is the
`Inhabited`-instance issue: legacy `peek?` uses
`ps.tokens[ps.pos]!` (Array bang-index) which needs
`Inhabited (Positioned YamlToken)` (derived in legacy via
`deriving Inhabited`), but `IxToken input` cannot derive
`Inhabited` because its `startLEStop` and `stopLEInput` fields
are proofs with no canonical default. Rewrote the accessors
around `Indexed.TokenStream.get?` returning `Option (IxToken
input)`, with `peek?` / `peekPos?` derived via `.map (·.token)`
/ `.map (·.start)`. Added a new `peekIx?` accessor that
returns the full `IxToken input` (token + positions + bound
proofs in one shot) — Step 6b will use it for the parser
functions that needed both token and position. Staging
namespace `L4YAML.TokenParser.Indexed` (matches the Step 5b/5c
`L4YAML.Scanner.Indexed` convention).

**Step 6b landed** (Reflection 62): the 18-function mutual block
plus stream/document driver land in two staging files,
`L4YAML/Parser/FuelIx.lean` (~61 LOC) and
`L4YAML/Parser/TokenParserIx.lean` (~647 LOC), both sorry-free.
`FuelIx` is a direct port of `Parser/Fuel.lean` — same arithmetic
(`4 * tokens.size + 4`), only the container type swaps to
`Indexed.TokenStream input`. `TokenParserIx` is a near-verbatim
clone of `Parser/TokenParser.lean`'s mutual block + stream/document
layer, with three structural changes: every function carries an
`{input : String}` implicit so the state `ParseStateIx input` is
dependently typed; token accessors switch from `Positioned.val` /
`Positioned.pos` to `IxToken.token` / `IxToken.start`; the one
random-access site in `parseBlockMappingEntryValue` rewrites
`ps.tokens[i]!` to `ps.tokens.get? i` followed by `match`, on the
same `Inhabited (IxToken input)` constraint Step 6a's
`validateNodeProps` worked around (Reflection 61). All
`@[yaml_spec ...]` attributes from the legacy parser are
reproduced verbatim — the `yaml_spec` env extension keys entries
by fully-qualified `declName`, so `L4YAML.TokenParser.parseNode`
and `L4YAML.TokenParser.Indexed.parseNode` coexist without
collision (Reflection 62). Top-level entry-point is
`parseStreamIx : Indexed.TokenStream input → Except ScanError
(Array YamlDocument)`; the output type stays plain (no `input`
parameter) because the L2 → L1 step of the four-stage pipeline
produces a `YamlDocument` that is no longer tied to the source
string.

**Step 6c.1 landed** (Reflection 63): the `NodeProofs` half of the
original Step 6c scope (`AG` AnchorsGrow propagation + `AAR`
AllAliasesResolve propagation through `parseNode` and all 17 sub-parser
helpers) lands in a single staging file
`L4YAML/Proofs/Parser/IndexedNodeProofs.lean` (~1,814 LOC), sorry-free
on first build. Translation is **purely structural** — none of the
AG/AAR lemmas touch `ps.tokens` (they reason only about anchor-array
growth and alias resolution against the anchor map), so the indexed
proofs are a mechanical substitution of `ParseState → ParseStateIx
input` plus the namespace shift `L4YAML.TokenParser →
L4YAML.TokenParser.Indexed`. The one structural correction over the
naive cp+sed approach: the `ParseNodeAG` and `ParseNodeAAR` predicate
definitions had to take `input : String` as an **explicit** parameter
(legacy: `def ParseNodeAG (n : Nat) : Prop`; indexed: `def ParseNodeAG
(input : String) (n : Nat) : Prop`). With `input` implicit, Lean
cannot synthesise it at the `(h_ih : ParseNodeAG n)` hypothesis site
because the predicate returns `Prop` (no `input` in the result type to
unify against), and hypothesis parameters are resolved before later
`(ps : ParseStateIx input)` arguments are seen (Reflection 63).
**WfaProofs** is **not** in the 6c scope — it consumes three WellBehaved
lemmas directly (`parseNode_wb_all`, `parseNodeContent_wb`,
`parseNodeProperties_tokens`), and translating it standalone would
require porting a non-trivial fragment of `ParserWellBehaved.lean`
(4,797 LOC) ahead of its natural home. The Blueprint sub-plan ladder
above is updated to reflect this: WfaProofs is folded into 6d (where
WB lives), the 6c row is checked off as 6c.1 NodeProofs only.

**Step 6d.1a landed** (Reflection 64): the **supporting infrastructure**
half of `IndexedWellBehaved.lean` (~210 LOC) — indexed twins of the
`flowNesting` / `PlainScalarsValid` / `FlowAwarePSV` / `FlowContextPSV`
/ `FlowBracketsMatched` predicates from
`Proofs.Production.ScannerPlainScalarValid`, plus the four
`flowNestingIx_go_*` step lemmas (`_oob`, `_step`, `_ge_target`,
`_split`). The predicates are structurally identical to the legacy
`Array (Positioned YamlToken)` versions; only `.val` (token-kind
accessor on `Positioned`) becomes `.token` (the corresponding accessor
on `IxToken`). Discovery during this session: the full
`ParserWellBehaved.lean` port (~4,797 LOC) is **not** a pure mechanical
substitution like 6c.1 was. Three structural surprises (Reflection 64)
reshape 6d.1 into 6d.1a + 6d.1b — see Reflection 64 for the full
write-up; in short: (i) `Indexed.TokenStream input` wraps
`Array (IxToken input)`, introducing a `.tokens` indirection that
breaks the `ps.tokens = tokens` `Eq.trans` chains in §5f; (ii) the
indexed `ParseStateIx.peek?` is implemented via
`Option.map IxToken.token ps.peekIx?`, so the `peek_some_bounded`
bridge tactic has a different proof shape than the legacy version;
(iii) the §5 C2 chain invokes a scanner-side
`scan_flow_aware_psv` producer keyed on `Array (Positioned YamlToken)`
that needs an indexed twin before C2 closes.

**Step 6d.1b landed** (Reflection 65): the pre-mutual-block §5
sections of `ParserWellBehaved.lean` ported into
`IndexedWellBehaved.lean` (~613 LOC delta, growing 210 → 823 LOC, +
14 LOC `GetElem` instance in `Indexed/TokenStream.lean`). Option B
bridging was settled: a new `GetElem (TokenStream input) Nat
(IxToken input)` instance lets `tokens[i]'h` indexing work uniformly
on `TokenStream` parameters; the 5 supporting predicates re-target
to `Indexed.TokenStream input` with no functional change. Ported:
foundation switchover, §5 C2 Infrastructure (5 lemmas including
`peek_some_bounded_ix` with the new three-`Option`-rewrite proof
shape that resolves Reflection 64 point 2), §5a flowNesting step
lemmas (6 lemmas), §5b Scannable monotonicity (2 verbatim ports),
§5d Scannable for tag/anchor (1 verbatim port), §5d′
applyNodeFinalization preservation (4 lemmas), §5e′
parseNodeProperties preservation (4 lemmas + verbatim port of the
`unfold_loop_at` elaborator). Discovery (Reflection 65): Option B
lets §5b/§5d/§5d′ port **verbatim** (no token-shape dependency at
all), and §5a/§5e′ need only one-line `h_bridge` normalizations
between `tokens[i]` (TokenStream indexing) and `tokens.tokens[i]`
(Array indexing) — far smaller than Option A's ~150 `.tokens`
accessor insertions would have been.

**Next session**: Step 6d.1c — extend `IndexedWellBehaved.lean`
with the structurally hard remainder of the C2 chain. ~4,000 LOC
remaining: the §5e mutual `ParseNodeWB` block (~600 LOC) + §5e″
sub-parser well-behavedness for 11 sub-parsers (~1,500 LOC) + §5e₂
preservation helpers (~100 LOC) + §5f parseDocument scannability
(~150 LOC) + §5g parseStream output scannability (~150 LOC) + the
§5f position monotonicity chain (~1,500 LOC). Plus the §5c
scanner-side `scan_flow_aware_psv` bridge — recommended Option β
(axiom-bridge with a forward-reference axiom discharged later).
The mutual block is the structural core, but the indexed
`parseNode`'s mutual-recursion shape mirrors legacy exactly (see
`Parser/TokenParserIx.lean`), so the strong-induction proof should
port mechanically modulo state-type substitution. Estimated 2–3
sessions. Then 6d.2 (IndexedWfa, ~1 session) and 6d.3 (Correctness
+ Completeness + Grammable, ~1 session) close out 6d. The one
surviving Phase-3 carry-forward is **5b.6's fold-machine invariant
for non-empty input** (`foldBlockContentGo_preserves`), explicitly
deferred to the load-pipeline step that will quote it against
canonicalised input.

</details>

#### Algebra + foundation files landed

<details><summary>Table of landed files (Items 7–23 except 18–22 still pending in their original form, plus indexed types + LoadConfig) with LOC and number of downstream imports added.</summary>

| File | Items | LOC | Imports added downstream |
|---|---|---|---|
| `L4YAML/Algebra/Value.lean` | 18–21 | ~200 | 3 (was `Proofs.Foundation.ValueAlgebra`) |
| `L4YAML/Algebra/LawfulBEq.lean` | 23 | ~265 | 1 (`L4YAML.lean` root) |
| `L4YAML/Algebra/StringList.lean` | 9, 22 | ~120 | 1 (`StringProperties.lean`) |
| `L4YAML/Algebra/Position.lean` | 7, 13 | ~135 | 1 (`L4YAML.lean` root) |
| `L4YAML/Algebra/Indent.lean` | 8 | ~110 | 1 (`L4YAML.lean` root) |
| `L4YAML/Algebra/AnchorMap.lean` | 12 | ~125 | 1 (`L4YAML.lean` root); `Spec/Types.lean` shrinks by ~90 lines |
| `L4YAML/Algebra/TokenStream.lean` | 10 | ~145 | 1 (`L4YAML.lean` root) |
| `L4YAML/Algebra/Fuel.lean` | 11 | ~185 | 1 (`L4YAML.lean` root) |
| `L4YAML/Algebra/Token.lean` | 17 | ~310 | 1 (`L4YAML.lean` root) |
| `L4YAML/Algebra/Combinators.lean` | 14 | ~235 | 1 (`L4YAML.lean` root) |
| `L4YAML/Algebra/Schema.lean` | 15, 16 | ~265 | 1 (`L4YAML.lean` root) |
| `L4YAML/Algebra/Equivalence.lean` | 1, 2, 3, 5, 6 | ~350 | 1 (`L4YAML.lean` root) |
| `L4YAML/Algebra/Idempotence.lean` | 4 | ~460 | 1 (`L4YAML.lean` root) |
| `L4YAML/Config/LoadConfig.lean` | n/a | ~70 | 0 (new file; consumers in Phase 3+) |
| `L4YAML/Indexed/Range.lean` | n/a | ~150 | 0 (extended in Phase 3 Step 1) |
| `L4YAML/Indexed/RepGraph.lean` | n/a | ~120 | 0 |
| `L4YAML/Indexed/TokenStream.lean` | n/a | ~135 | 0 (extended in Phase 3 Step 1) |
| `L4YAML/Indexed/CharStream.lean` | n/a | ~250 | 1 (`L4YAML.lean` root; new in Phase 3 Step 1, monotonicity lemmas added in Step 2) |
| `L4YAML/Scanner/IndexedScanner.lean` | n/a | ~950 | 0 (staging — Guardrail 1; new in Phase 3 Step 2; +Layer D dispatch in Step 3; +Layer E scalar tier in Step 4a; +Layer F1/F2/F3 multi-line + block scalars in Step 4b) |
| `L4YAML/Scanner/IndexedState.lean` | n/a | ~335 | 0 (staging — Guardrail 1; new in Phase 3 Step 5a: `ScannerStateIx input`, indexed `SimpleKeyStateIx`, indent-stack ops, `emit/emitAt/emitAtCursor/overwriteAtCursor`; `emitAtSafe` removed in Step 5b.1a after the static monotonicity chain landed; Step 5b.2: `hasTabInPrecedingWhitespaceLoop` + `hasTabInPrecedingWhitespace` — indexed analogues of the legacy backward-scan, used by `scanBlockEntryIx` to enforce §6.1) |
| `L4YAML/Scanner/IndexedDispatch.lean` | n/a | ~1050 | 0 (staging — Guardrail 1; new in Phase 3 Step 5a: helper recogniser loops, simple-key save/resolve, block + flow indicator scans, document markers, directives, anchor/alias, tag, dispatch family, `scanLoopIx`, `scanIx`; Step 5b.1a: 8 helper-loop `*_offset_monotonic` lemmas, 10 `emitAtSafe`→`emitAt` replacements with inline proofs, `hStart` parameter on directive helpers; Step 5b.2: `tabInIndentation` throws added to `scanBlockEntryIx` and `scanKeyIx` — the former in block context when `hasTabInPrecedingWhitespace`, the latter when the cursor sits on `'\t'` immediately after consuming `?`; Step 5b.3: `scanValueIx` split into the legacy four-stage chain — `scanValueClearKeyIx` (clear spurious simple key when explicit `?` is pending), `scanValueValidateIx` (five `throw` cases: §7.4 / §7.4.2 / §8.2.1 / T833 / §8.2.2 [197]), `scanValuePrepareIx` (Step 5b.1b.i — placeholder overwrite or push mapping indent), `scanValueTabCheckIx` (§6.1 against the *original* col + indent)) |
| `L4YAML/Proofs/Scanner/IndexedWhitespace.lean` | n/a | ~405 | 0 (staging — Guardrail 1; new in Phase 3 Step 2; +`consumeLineBreak_strict` in Step 4a) |
| `L4YAML/Proofs/Scanner/IndexedIndent.lean` | n/a | ~355 | 0 (staging — Guardrail 1; new in Phase 3 Step 3; +`skipToContentLoop_progress` / `skipToContent_progress` in Step 4a) |
| `L4YAML/Proofs/Scanner/IndexedScalar.lean` | n/a | ~1158 | 0 (staging — Guardrail 1; new in Phase 3 Step 4a; +F1/F2/F3 monotonicity proofs in Step 4b; Step 5b.4: new "Layer E1.4 — Hex-escape value-correctness" section — `hexDigitValue_lt_16`, `hexStringValue_empty` `@[simp]`, `hexStringValue_push`, `hexStringValue_lt_pow`, `parseHexEscapeIx_decoded`; Step 5b.5: new "Layer F.1 — Auto-detected block-scalar indent ≥ `minContentIndent`" section — `autoDetectBlockScalarIndentLoopIx_ge_min` + `autoDetectBlockScalarIndentIx_ge_min`; Step 5b.6: new "Layer F.2 — Block-scalar content correctness" section — `applyChomp_keep` / `applyChomp_strip` / `applyChomp_clip_of_endsWith` / `applyChomp_clip_of_not_endsWith` / `foldBlockContentGo_nil` / `foldBlockContent_empty` pinning the chomp [160] + fold-machine [170]–[181] spec semantics; Step 5b.7: new "Layer F.3 — Quoted multi-line content correctness" section — `foldQuotedNewlinesIx_of_blank_lines` / `foldQuotedNewlinesIx_of_single_break` (§6.5 [73] / [74]), `collectDoubleQuotedLoopIx_zero` / `_closing` / `_linebreak` (§7.3.1 [111]–[116]), `collectSingleQuotedLoopIx_zero` / `_doubled` / `_closing_some` / `_closing_none` / `_linebreak` (§7.3.2 [122]–[125]); the three RHS-recursive lemmas use `conv => lhs; unfold …` to avoid `unfold` rewriting both sides of the goal — see Reflection 57; Step 5b.8: new "Layer F.4 — Plain multi-line content correctness" section — 12 branch-mapping lemmas covering every outcome of `collectPlainScalarLoopIx` (§7.3.3 [131]–[135]): `_zero`, `_eof`, `_comment`, `_colon_terminate`, `_colon_continue`, `_flow_indicator`, `_linebreak_flow`, `_linebreak_block_none`, `_linebreak_block_some`, `_whitespace`, `_not_plain_safe`, `_content`; the five RHS-recursive branches reuse the `conv => lhs; unfold …` pattern from Reflection 57) |
| `L4YAML/Scanner/IndexedPresenter.lean` | n/a | ~121 | 0 (staging — Guardrail 1; new in Phase 3 Step 5c: `renderToken : IxToken input → String` — per-constructor dispatch from token to source contribution — and `present : TokenStream input → String` = `ts.tokens.foldl (· ++ renderToken ·) ""`; virtual tokens (`streamStart`/`streamEnd`/`placeholder`/`block*Start`/`blockEnd`/implicit `key`/`value`) render to `""`, single-character indicators (`flow*Start`/`flow*End`/`flowEntry`/`blockEntry`) render to their literal character, `documentStart`/`documentEnd` render to `---`/`...`, and content tokens (`scalar`/`anchor`/`alias`/`tag`/`comment`/`versionDirective`/`tagDirective`) render via `String.Pos.Raw.extract input ⟨start⟩ ⟨stop⟩` — the Lean 4.30 raw-offset extract API, chosen over the new `String.extract` because `IxToken`'s positions are plain `Nat` offsets without the `Pos.Raw.IsValid` proof; `present_empty` simp lemma; `@[simp] theorem present_empty (input : String) : present (TokenStream.empty input) = "" := rfl` lands as a sanity check on the empty stream) |
| `L4YAML/Proofs/Scanner/IndexedRoundtrip.lean` | n/a | ~158 | 0 (staging — Guardrail 1; new in Phase 3 Step 5c: `roundtripOk : String → Bool` Bool-valued check `match scanIx input with | .ok ts => present ts == input | .error _ => false`; 19 corpus theorems `roundtrip_xxx : roundtripOk "…" = true := by native_decide` covering the empty input, plain scalars at root (`x`/`abc`/`hello`), empty/one-/two-/three-/four-element flow sequences (`[]`/`[x]`/`[x,y]`/`[a,b,c]`/`[a,b,c,d]`), empty/one-/two-key flow mappings (`{}`/`{a}`/`{a,b}`), nested patterns (`[[]]`/`[{}]`/`[a,[b,c]]`/`[{a},b]`/`{a,{b}}`/`[[],[]]`/`{[]}`); closing `scanIx_present_of_roundtripOk` lemma turns `roundtripOk input = true` into the existential `∃ ts, scanIx input = .ok ts ∧ present ts = input` form, from which the Blueprint's `scanIx (present ts) = .ok ts` statement follows by rewriting `present ts = input` on the LHS) |
| `L4YAML/Parser/FuelIx.lean` | n/a | ~61 | 0 (staging — Guardrail 1; new in Phase 3 Step 6b: indexed twin of legacy `Parser/Fuel.lean`; `initialFuelIx : Indexed.TokenStream input → Nat := fun ts => 4 * ts.tokens.size + 4`; arithmetic byte-identical to legacy, container type swaps to `Indexed.TokenStream input`; namespace `L4YAML.TokenParser.Indexed`) |
| `L4YAML/Parser/TokenParserIx.lean` | n/a | ~647 | 0 (staging — Guardrail 1; new in Phase 3 Step 6b: indexed twin of legacy `Parser/TokenParser.lean`; 18-function mutual block (`set_option maxHeartbeats 400000 in mutual`, structural recursion on `fuel`) — `parseNodeContent`, `parseNode`, `parseBlockSequence`, `parseBlockSequenceLoop`, `parseImplicitBlockSequence`, `parseImplicitBlockSequenceLoop`, `parseBlockMapping`, `parseBlockMappingEntryValue`, `handleBlockMappingKeyEntry`, `handleBlockMappingValueEntry`, `parseBlockMappingLoop`, `parseFlowSequence`, `parseFlowSequenceLoop`, `parseFlowMapping`, `parseFlowMappingValue`, `parseExplicitKey`, `parseFlowMappingLoop`, `parseSinglePairMapping`; stream/document layer outside the mutual block — `StreamState` + `StreamState.validNextToken`, `parseDirectives`, `prepareDocumentState`, `parseDocument`, `parseStreamLoop`, `parseStreamIx`; top-level entry `parseStreamIx {input : String} (tokens : Indexed.TokenStream input) (trackPositions : Bool := false) : Except ScanError (Array YamlDocument)` — output type plain `Array YamlDocument` since the L2 → L1 step of the four-stage pipeline erases the type-level binding to `input`; departures from legacy — every function carries `{input : String}` implicit, token accessors swap from `Positioned.val`/`Positioned.pos` to `IxToken.token`/`IxToken.start`, random-access reads in `parseBlockMappingEntryValue` use `ps.tokens.get?` + `match` rather than `[i]!` to avoid the `Inhabited (IxToken input)` constraint that proof-field-bearing `IxToken` cannot satisfy (Reflection 61); all `@[yaml_spec ...]` attributes reproduced verbatim — the env extension keys by fully-qualified `declName` so `L4YAML.TokenParser.parseNode` and `L4YAML.TokenParser.Indexed.parseNode` coexist without collision; namespace `L4YAML.TokenParser.Indexed`) |
| `L4YAML/Proofs/Parser/IndexedWellBehaved.lean` | n/a | ~823 | 0 (staging — Guardrail 1; namespace `L4YAML.Proofs.Indexed.WellBehaved` — at cutover renamed back to `L4YAML.Proofs.ParserWellBehaved`. Grew incrementally across two sub-steps. **6d.1a (~210 LOC, initial check-in)**: 5 supporting predicates (`flowNestingIx`, `PlainScalarsValidIx`, `FlowContextPSVIx`, `FlowAwarePSVIx`, `FlowBracketsMatchedIx`) — indexed twins of the eponymous predicates in `Proofs.Production.ScannerPlainScalarValid`; plus the four `flowNestingIx_go_*` step lemmas (`_oob`, `_step`, `_ge_target`, `_split`) — mechanical ports of the legacy `flowNesting_go_*` proofs. Initially keyed on `Array (IxToken input)`. **6d.1b (~613 LOC delta, growing to 823 LOC)**: Option B bridging settled (Reflection 65) — predicates re-targeted to `Indexed.TokenStream input` with the new `GetElem` instance in `Indexed/TokenStream.lean`. Pre-mutual-block §5 sections of legacy `ParserWellBehaved.lean` ported: §5 C2 Infrastructure (5 lemmas including `peek_some_bounded_ix` with a new three-`Option`-rewrite proof shape resolving Reflection 64 point 2), §5a flowNesting step lemmas (6 lemmas — `flowNestingIx_split_step` / `_pos_after_flow_start` / `_after_flow_start_eq` / `_after_flow_end` / `_non_flow_step` / `_beyond_size`), §5b Scannable monotonicity (2 verbatim ports), §5d Scannable for tag/anchor (1 verbatim port), §5d′ applyNodeFinalization preservation (4 lemmas re-targeted onto indexed `applyNodeFinalization`), §5e′ parseNodeProperties preservation (4 lemmas + verbatim port of the `unfold_loop_at` elaborator + the file-local `advance_tokens_eq_ix` `@[simp]` lemma). **What's deferred to Step 6d.1c (~4,000 LOC remaining)**: §5e mutual `ParseNodeWB` block (~600 LOC), §5e″ sub-parser WB for 11 sub-parsers (~1,500 LOC), §5e₂ preservation helpers (~100 LOC), §5f parseDocument scannability (~150 LOC), §5g parseStream output scannability (~150 LOC), §5f position monotonicity chain (~1,500 LOC), and §5c scanner-side bridge (`scan_flow_aware_psvIx` — recommended Option β axiom-bridge). Reflections 64 + 65 document the design choices) |
| `L4YAML/Proofs/Parser/IndexedNodeProofs.lean` | n/a | ~1,814 | 0 (staging — Guardrail 1; new in Phase 3 Step 6c.1: indexed twin of legacy `Proofs/Parser/ParserNodeProofs.lean` (1,781 LOC); namespace `L4YAML.Proofs.Indexed.NodeProofs` — at cutover renamed back to `L4YAML.Proofs.ParserNodeProofs`. Re-proves `AG` (AnchorsGrow) propagation through `parseNode` and all 17 sub-parser helpers (`parseBlockSequenceLoop`/`parseBlockSequence`/`parseImplicitBlockSequenceLoop`/`parseImplicitBlockSequence`/`parseBlockMappingEntryValue`/`handleBlockMappingKeyEntry`/`handleBlockMappingValueEntry`/`parseBlockMappingLoop`/`parseBlockMapping`/`parseExplicitKey`/`parseFlowMappingValue`/`parseSinglePairMapping`/`parseFlowSequenceLoop`/`parseFlowSequence`/`parseFlowMappingLoop`/`parseFlowMapping`/`parseNodeProperties`/`parseNodeContent`), culminating in `parseNode_ag_all : ∀ n, ParseNodeAG input n` by strong induction on fuel; and `AAR` (AllAliasesResolve) propagation through the same family, culminating in `parseNode_aar_all : ∀ n, ParseNodeAAR input n`. Helper extractors `parseNode_anchors_grow` and `parseNode_aliases_resolve'` exposed for downstream callers. Structural changes from legacy (3, all mechanical): state-type substitution `ParseState → ParseStateIx input` with `variable {input : String}` at file scope, accessor-namespace shift `ParseState.X → ParseStateIx.X` for advance/tryConsume/addAnchor, **explicit** `input : String` parameter on the `ParseNodeAG` and `ParseNodeAAR` predicate definitions — implicit `input` causes "don't know how to synthesize implicit argument `input`" errors at `(h_ih : ParseNodeAG n)` hypothesis sites because the predicate returns `Prop` with no `input` in the result type to unify against, and hypothesis parameters are resolved before the later `(ps : ParseStateIx input)` arguments can supply context (Reflection 63). Only one heartbeat override needed adjustment — `parseSinglePairMapping_ag` bumped from 800,000 to 1,600,000 to absorb the 17-arm `split <;> first | contradiction | skip` cascade under the new `ParseStateIx input` dependent-type unification. Bridge lemma `any_name_implies_findSome_isSome'` copied into the indexed namespace to keep the cutover atomic. **Status**: Step 6c's `IndexedWfa` half **deferred to Step 6d** — `WfaProofs` consumes three WB lemmas directly that don't have indexed twins yet) |
| `L4YAML/Parser/ParseStateIx.lean` | n/a | ~304 | 0 (staging — Guardrail 1; new in Phase 3 Step 6a: indexed twin of legacy `Parser/State.lean`, parameterised by `input : String`; structure `ParseStateIx (input : String)` carries `tokens : Indexed.TokenStream input` + `pos : Nat` cursor + auxiliary state (`anchors`, `tagHandles`, `trackPositions`, `currentPath`, `nodePositions`); explicit `Inhabited (ParseStateIx input)` instance built from `Indexed.TokenStream.empty input` since `IxToken input`'s proof fields prevent deriving; navigation API in staging namespace `L4YAML.TokenParser.Indexed` — `mk'`, `hasMore`, `peekIx?` (new — returns `Option (IxToken input)` rolling token + positions + bound proofs into one accessor), `peek?` / `peekPos?` derived via `peekIx?.map (·.token)` / `peekIx?.map (·.start)`, `advance`, `lastPos?` (rewritten around `get? (ps.pos - 1)` since `Array.get?`-based form avoids the `Inhabited (IxToken input)` constraint that `[i]!` indexing demands), `currentLine`, `expect`, `tryConsume`, `addAnchor`; node-property scaffolding ported verbatim from legacy — `NodeProperties`, `resolveTag`, `parseNodeProperties` `@[yaml_spec "6.9" 96]`, `emptyNode` `@[yaml_spec "7.2" 105/106]`, `applyNodeFinalization`, `validateNodeProps`) |
| `L4YAML/Proofs/Scanner/IndexedDispatch.lean` | n/a | ~1620 | 0 (staging — Guardrail 1; new in Phase 3 Step 5b.1b.i: `IxCursor.advanceN_offset_monotonic`; `ScannerStateIx` cursor-preservation lemmas for `emit*`/`overwriteAtCursor`/`advance*`/`pushSequenceIndentIx`/`pushMappingIndentIx`/`unwindIndentsLoopIx`/`unwindIndentsIx`/`saveSimpleKeyIx`/`scanValuePrepareIx`; `skipSpacesS`/`skipWhitespaceS`/`skipToContentS` offset-monotonicity lifts; Step 5b.1b.ii: 10 per-dispatcher offset-monotonicity lemmas — `scanBlockEntryIx`/`scanKeyIx`/`scanValueIx`/`scanFlowEntryIx`/`scanDocumentStartIx`/`scanDocumentEndIx`/`scanFlowSequenceStartIx`/`scanFlowSequenceEndIx`/`scanFlowMappingStartIx`/`scanFlowMappingEndIx`; Step 5b.1b.iii: 5 per-dispatcher offset-monotonicity lemmas — `scanAnchorOrAliasIx`/`scanTagIx`/`scanYamlDirectiveIx`/`scanTagDirectiveIx`/`scanDirectiveIx`; Step 5b.1b.iv-pre: 6 tokens-size simp lemmas — `skipToContentS_tokens`/`skipSpacesS_tokens`/`skipWhitespaceS_tokens`/`advance_tokens`/`advanceN_tokens`/`emit_tokens_size`/`emitAt_tokens_size`/`emitAtCursor_tokens_size`/`overwriteAtCursor_tokens_size`; 6 indent/key helper `_tokens_size_le` lemmas — `unwindIndentsLoopIx`/`unwindIndentsIx`/`pushSequenceIndentIx`/`pushMappingIndentIx`/`saveSimpleKeyIx`/`scanValuePrepareIx`; 12 dispatcher `_tokens_size_le` lemmas — `scanBlockEntryIx`/`scanKeyIx`/`scanValueIx`/`scanFlowEntryIx`/`scanFlowSequenceStartIx`/`scanFlowSequenceEndIx`/`scanFlowMappingStartIx`/`scanFlowMappingEndIx`/`scanDocumentStartIx`/`scanDocumentEndIx`/`scanAnchorOrAliasIx`/`scanTagIx`/`scanYamlDirectiveIx`/`scanTagDirectiveIx`/`scanDirectiveIx`; Step 5b.1b.iv-cont: 7 top-level pairs (`_offset_monotonic` + `_tokens_size_le`) for `scanNextTokenIx_preprocess`/`scanNextTokenIx_dispatchStructural`/`scanNextTokenIx_dispatchFlowIndicators`/`scanNextTokenIx_dispatchBlockIndicators`/`scanNextTokenIx_dispatchContent`/`scanNextTokenIx` plus `scanLoopIx_tokens_size_le`; Step 5b.2: 6 `flowLevel`/`inFlow` preservation simp lemmas — `emit_flowLevel`/`advance_flowLevel`/`pushSequenceIndentIx_flowLevel`/`pushMappingIndentIx_flowLevel`/`emit_inFlow`/`advance_inFlow`/`pushMappingIndentIx_inFlow` — used to collapse the post-advance `!s.inFlow` tab-check guard against the *original* `s.inFlow`, then `scanBlockEntryIx`/`scanKeyIx` `_offset_monotonic` + `_tokens_size_le` pairs re-derived with the new throw branches; Step 5b.3: 2 new `scanValueClearKeyIx` helper lemmas (`_cursor` `@[simp]` + `_tokens_size_le`), `scanValueIx_offset_monotonic` and `_tokens_size_le` re-proved with the legacy `simp only [bind, Except.bind] at h; split at h; cases h | …` pattern; same commit fixed cache-hidden breakage in `Proofs/Scanner/IndexedScalar.lean` (quoted/parse-header-loop `split at h` shapes, `blockHeaderToBodyIx` `by_cases hp` for the `match`-inside-`if` condition) and `Proofs/Scanner/IndexedIndent.lean::skipToContent_at_content` (`'#'` literal → `isCommentBool ch`)) |

</details>

</details>

### Phase 3 — Stage C (scanner) on indexed types

<details><summary>Re-implement scanner to produce `TokenStream input` directly; legacy deleted in the cutover commit; bidirectional verification of Stage-C YAML 1.2.2 rules.</summary>

**Goal**: replace `Scanner/Scanner.lean` and friends with a
scanner that produces `TokenStream input` directly, verified
against YAML 1.2.2 rules in both directions (`present` and
`parse`).

**DONE criteria**:
- (i) Scanner re-implemented atomically (no parallel state with the
  legacy scanner; legacy deleted in the cutover commit).
- (ii) Every Stage-C YAML 1.2.2 rule (rules touching characters,
  whitespace, indentation, line breaks, scalar lexing) verified in
  both directions.
- (iii) Sorry count = 0 in `L4YAML/Scanner/` and
  `L4YAML/Proofs/Scanner/`.
- (iv) End-to-end test: `parse (present ts) = some ts` for any
  `ts : TokenStream input`, on a corpus of test inputs.

**Critical guardrail** (Lesson 1): legacy scanner deleted in the
cutover commit. No "dual-write" interim state.

#### Reflections

<details><summary>R29 — The cursor type is the scanning-side analogue of `Range` (Phase 3 Step 1).</summary>

29. **The cursor type is the scanning-side analogue of `Range`.**
    Phase 2 framed `Range input` as a *static* byte interval — the
    span a finished token or sub-graph occupies. Step 1 introduces
    `IxCursor input` as a *moving* read head: a `YamlPos` carrying
    a bound proof `pos.offset ≤ input.utf8ByteSize`. The two types
    are *not* the same and should not be conflated: a cursor with
    `offset = n` and a range `[n, n)` describe the same byte
    position, but cursors carry line/col while ranges do not. The
    `rangeBetween : (c₁ c₂ : IxCursor input) → Range input` bridge
    is the only place these two views meet — Step 2's scanner will
    use it once per emitted token. Worth recording as a design
    constraint: do not collapse `IxCursor` into `Range × {line, col}`
    or vice versa.

</details>

<details><summary>R30 — `Nat.min` discharges the `advance` bound without a deep stdlib lemma.</summary>

30. **`Nat.min` discharges the `advance` bound without a
    deep stdlib lemma.** The natural bound proof for
    `advance` is "if `pos.offset < utf8ByteSize`, then
    `String.Pos.Raw.next` of that position has `byteIdx ≤
    utf8ByteSize`." This is a true fact about Lean's UTF-8
    implementation but its proof requires unfolding stdlib
    internals. Step 1 sidesteps it by clamping the next offset
    via `Nat.min nextOffset utf8ByteSize` — the bound proof
    becomes `Nat.min_le_right`. The clamping is semantically a
    no-op (the unclamped `next` already respects the bound) but
    moves the obligation off the scanner type and into Step 2's
    correctness proofs, where it pays off as a single rewrite once
    rather than a side-condition on every advance. Pattern to
    reuse in Step 2: prove `nextOffsetClamped c = (String.Pos.Raw.next
    input ⟨c.pos.offset⟩).byteIdx` whenever `c.hasMore = true`,
    and use that lemma to bridge to legacy-scanner reasoning.

</details>

<details><summary>R31 — Step 1's API surface is sized for Step 2's first cluster.</summary>

31. **Step 1's API surface is sized for Step 2's first cluster.**
    The temptation was to add `peekBack?`-with-proof, range
    intersection, cursor monotonicity, etc. — anything that *might*
    be needed later. The discipline observed: include only
    operations whose semantics are obvious *now* (peek, advance,
    rangeBetween, emitToken, push, append, last?), and let Step 2
    grow the surface with operations whose shape depends on actual
    use sites. The `@[simp]` lemmas are likewise minimal — five in
    `CharStream.lean` and four in `TokenStream.lean`, all of them
    one-step rewrites. Monotonicity of `advance` on `offset` is
    *not* here, even though it is obviously true, because the
    bound's `Nat.min` form makes the cleanest formulation
    use-site-dependent (Reflection 30).

</details>

<details><summary>R32 — The `Nat.min`-clamp obligation cleared at first use, exactly as planned (Phase 3 Step 2).</summary>

32. **The `Nat.min`-clamp obligation cleared at first use, exactly
    as planned.** Reflection 30 predicted Step 2 would need the
    bridge from `nextOffsetClamped` to the unclamped `next`. The
    actual shape of the proof was simpler than the predicted
    "rewrite lemma": `advance_offset_lt_of_hasMore` proves the strict
    inequality `c.pos.offset < c.advance.pos.offset` directly,
    chaining `String.Pos.Raw.byteIdx_lt_byteIdx_next` (stdlib) with
    a one-line `Nat.min` case split via `simp only [Nat.min_def];
    split <;> omega`. No intermediate "unclamping" lemma needed.
    The stdlib lemma `String.Pos.Raw.byteIdx_lt_byteIdx_next` is
    *unconditional* (no `¬ atEnd` precondition) because `next`
    always adds `Char.utf8Size_pos > 0` — this saves a side
    condition. Lesson for future bound-discharging tricks: try the
    direct strict-inequality form before reaching for an
    "unclamping" intermediate.

</details>

<details><summary>R33 — Pattern-matching on `Char` literals defeats `split`; use `if/else` on `==` instead.</summary>

33. **Pattern-matching on `Char` literals defeats `split`; use
    `if/else` on `==` instead.** First draft of `consumeLineBreak`
    used `match c.peek? with | some '\n' => ... | some '\r' => ...
    | _ => c`. Splitting through the literal patterns made the
    proof obligations carry concrete `Char` values that `simp` and
    `rfl` couldn't always reduce — `'\r'` was displayed as
    `'\x0d'` and the match wouldn't unfold definitionally.
    Restructured to `match c.peek? with | some ch => if ch == '\n'
    then ... else if ch == '\r' then ... else c | none => c`.
    Every proof became straightforward: `simp [consumeLineBreak,
    hp, hLF, hCR]` for the case lemmas, nested `by_cases hX :
    ch = '\n'` for the monotonicity. **Rule for Step 3+: never
    pattern-match on `Char` literals in scanner code; always use
    `==` and let `if/else` carry the case structure.**

</details>

<details><summary>R34 — `by_contra` is not in stdlib for this Lean version; use `if h : ... then ... else ...` for decidable contradictions.</summary>

34. **`by_contra` is not in stdlib for this Lean version (v4.30.0-rc2)
    — use `if h : ... then ... else ...` for decidable
    contradictions.** The `peekIs*_implies_hasMore` proofs initially
    tried `by_contra hbound; ...` which the elaborator rejected as
    "unknown tactic". The replacement `if h' : c.pos.offset <
    input.utf8ByteSize then exact h' else ...` is term-mode-friendly
    and lets the `else` branch derive a contradiction using
    `Decidable` instances directly. **Rule: until Mathlib lands in
    the dependency tree, write contradictions as if-then-else with
    explicit `Decidable` dispatch.**

</details>

<details><summary>R35 — Termination correctness was deferred from Step 2 to Step 3 — name it a scope shift, not an optimisation.</summary>

35. **Termination correctness was deferred from Step 2 to Step 3 —
    name it a scope shift, not an optimisation.** The "skip-loops
    end at non-whitespace or EOF" lemma was within Step 2's stated
    cluster (bidirectional spec proofs for the character/whitespace
    layer). It is provable in Step 2 via fuel induction with
    `advance_offset_lt_of_hasMore` and `input.utf8ByteSize -
    c.pos.offset ≤ fuel`; the proof is verbose, not infeasible.
    The defence — that Step 3's indent-stack invariant
    "count = offset delta ∧ terminates" subsumes termination and
    is thus the natural home — is *true*, but the right framing
    is "we chose to ship Step 2 before proving everything Step 2
    promised, and we paid for it by enlarging Step 3 in the
    blueprint." The Step 3 description was updated to call out
    this deferred obligation explicitly. **Lesson: when deferring
    a stated deliverable, the deferred-from doc should not call
    the deferral 'cheaper' — that wording rationalises scope
    reduction. Update the deferred-to doc to absorb the
    obligation, and label the move as what it is.**

</details>

<details><summary>R36 — Closing the Step 2 deferred obligation was easier than the blueprint sold.</summary>

36. **Closing the Step 2 deferred obligation was easier than the
    blueprint sold.** Termination + count-equals-column-delta
    closed in ~60 LOC in `IndexedWhitespace.lean` via two fuel-
    inductions and an `advance_indent_col_succ` helper. Both
    claims are inherently *single-line*: `skipSpacesLoop` only
    advances when `peekIsIndentChar c = true` (i.e.
    `c.peek? = some ' '`), so it stops at the first non-space —
    which includes `'\n'` and `'\r'`. The cursor therefore never
    crosses a line boundary inside one `skipSpaces` call, and
    `skipSpacesLoop_col_eq_count` proves *both* conjuncts:
    `(skipSpaces c).1.pos.col = c.pos.col + (skipSpaces c).2`
    *and* `(skipSpaces c).1.pos.line = c.pos.line`. Multi-line
    indentation is a composition concern handled at the next
    layer: `consumeLineBreak` resets `col` to 0 and bumps `line`;
    a fresh `skipSpaces` on the new line measures that line's
    indent in isolation. The column-delta form turned out *not*
    to need any `utf8Size` apparatus: `IxCursor.advance` already
    increments `col` by 1 for any non-LF/CR character and
    `isIndentCharBool = (· == ' ')`, so the column-delta-equals-
    count claim follows from the `advance` rule directly. The
    byte-offset analog
    (`(skipSpaces c).1.pos.offset = c.pos.offset + (skipSpaces c).2`)
    is *also* true within the single line (each ASCII space is 1
    byte) but would require `Char.utf8Size_eq_one_iff` to fire on
    `' '`; the indent-stack only consumes column delta, so the
    offset version is unneeded. The distinction between the two
    forms is purely proof-complexity, not expressivity — both say
    "count = how many spaces just got eaten on the current line".
    **Lesson (a partial walk-back of Reflection 35): the Step 3
    blueprint paragraph promised "count = offset delta ∧
    terminates", but the actually-useful invariant turned out to
    be "count = *column* delta ∧ terminates" — a strictly smaller
    obligation, equally expressive for the indent-stack's
    purposes. The deferred-to side should state the deliverable
    in its eventual form rather than the form initially expected.**

</details>

<details><summary>R37 — `let`-bindings opacify the body to `split` / `cases`.</summary>

37. **`let`-bindings opacify the body to `split` / `cases`.** The
    first draft of `skipToContentLoop` used
    `let c1 := skipWhitespace c; match c1.peek? with …`; `split`
    refused to decompose the match, reporting
    "Could not split an `if` or `match` expression in the goal"
    with the goal still wrapped in the `let`. Refactor: inline
    the call site — write `match (skipWhitespace c).peek? with …`
    directly (the function is pure; inlining is a no-op at
    runtime). The same shape appeared one level down in
    `skipSpacesLoop`'s `let (c', n) := … ; (c', n + 1)`
    destructure, which defeated `simp`/`rfl` closure on the true
    branch of helper lemmas — refactored to
    `let r := … ; (r.1, r.2 + 1)`. **Rule (sibling of Reflection
    33's Char-pattern rule): if the proof needs to decompose a
    function body via `split` or `cases`, the source must not
    hide structural decisions behind intermediate `let`-bindings
    or pattern-destructure. Inline.**

</details>

<details><summary>R38 — Progress is *not* a bidirectional spec lemma — it deserves its own deliverable, *and* its own explicit deferred-to paragraph.</summary>

38. **Progress is *not* a bidirectional spec lemma — it deserves
    its own deliverable, *and* its own explicit deferred-to
    paragraph.** Step 3's promised "bidirectional spec proofs"
    landed: single-step soundness/completeness for `s-indent`,
    `b-break`, `b-non-content`, and the cursor-local lemmas for
    `s-l-comments` (`skipToContent_atEnd`,
    `skipToContent_at_content`, offset-monotonicity,
    `skipCommentText_terminates`). The *global progress* property
    — that `skipToContent` terminates after finitely many
    recursive iterations with the cursor settled at EOF or a
    non-`s-l-comments` character — is a strict-fuel termination
    claim, *not* a bidirectional spec lemma. It is deferred to
    Step 4 where the dispatch-loop's fuel measure is the natural
    carrier. Unlike the Step 2 → Step 3 deferral (Reflection 35),
    this one *is* a scope distinction: bidirectional ≠ progress.
    The Step 4 description was updated with an explicit "Deferred
    from Step 3 (must close here)" paragraph that names the exact
    obligation (`(skipToContent c).peek?` settles), the missing
    auxiliary (`consumeLineBreak_strict` — offset strictly
    increases on LF/CR), and *why* Step 4 is the natural carrier
    (scalar recognisers depend on `skipToContent` settling at
    content before each scalar boundary). **Rule (procedural,
    sharpened from the Step 2 → Step 3 round-trip): a deferral
    is not complete until the deferred-to doc *explicitly* names
    the obligation. "The neighbouring paragraph implies it" is
    not enough — readers should not have to infer the obligation
    from surrounding context. If the deferred-to paragraph does
    not call out the deferred lemma by name and the rationale for
    deferral, the deferral has not been recorded; it has been
    forgotten in slow motion. Also: if a deferral crosses the
    bidirectional-vs-progress boundary, name the boundary — don't
    conflate "we didn't prove it" with "it doesn't belong in this
    step". And if it's the *same* kind of work as the surrounding
    step but you ran out of time, name *that* instead
    (Reflection 35).**

</details>

<details><summary>R39 — Nested namespaces don't shield short names from a populated parent namespace.</summary>

39. **Nested namespaces don't shield short names from a populated
    parent namespace.** Step 4a's new scalar recognisers
    (`processEscape`, `scanDoubleQuoted`, `collectPlainScalarLoop`,
    `trimTrailingWS`, …) share short names with the legacy
    `L4YAML.Scanner.*` definitions. The staging code lives in
    `L4YAML.Scanner.Indexed` — a *child* namespace — and the
    expectation was that an unqualified `processEscape` inside the
    child would resolve to the local definition. In practice the
    elaborator picked the legacy parent definition: the proof file
    transitively imports `L4YAML.Proofs.Foundation.CharClass →
    L4YAML.Scanner.Scanner → L4YAML.Scanner.Scalar`, which brings
    `L4YAML.Scanner.processEscape` into scope, and Lean's name
    resolution did not prefer the closer `L4YAML.Scanner.Indexed.processEscape`.
    Workaround: renamed every new scalar function with an `Ix`
    suffix (`processEscapeIx`, `scanDoubleQuotedIx`, etc.) so the
    short names no longer collide. The Step 6 cutover commit
    deletes the legacy and renames back. **Rule: when staging code
    in a child namespace of an existing namespace that the proof
    files will transitively import, do not reuse short names from
    the parent. A suffix (or moving the staging namespace to a
    *peer* of the existing one) is the cheap fix; the alternative —
    aggressive `_root_` qualification or per-callsite `open` —
    spreads through every proof file. The cost is paid once at
    rename time, not at every proof site.**

</details>

<details><summary>R40 — Inline values, not bind them, when a function will be split apart in proofs (Reflection 37, second iteration).</summary>

40. **Inline values, not bind them, when a function will be split
    apart in proofs (Reflection 37, second iteration).** Step 4a's
    `parseHexEscapeIx` originally had two consecutive
    `let`-bindings — `let (hex, c') := collectHexDigitsLoopIx c "" n`
    and `let val := hex.foldl (...) 0` — that obstructed `split` in
    the offset-monotonicity proof. `split` could not see past
    either binding to the `if` it gated; the proof reduced to four
    nested `split at h` calls with branches `split` could not
    enumerate, returning the same `Could not split…` error
    Reflection 37 catalogued. Refactor: factored the value
    computation out into `hexStringValue : String → Nat` (and the
    digit conversion into `hexDigitValue : Char → Nat`), and
    inlined the cursor access via `(collectHexDigitsLoopIx c "" n).2`
    (paying the cost of recomputing the loop in three branches; in
    practice Lean fuses these in the elaborated term). Now the
    body is `if pred1 then ... else if pred2 then ... else none` —
    two clean `split` levels, four bullets, done. **Rule (a
    sharpening of Reflection 37): if a function will be the subject
    of `split`-driven proofs, prefer projection-form
    (`expr.1`, `expr.2`, named helper calls) to `let`-bindings.
    `let` is fine for code clarity in isolation; in proof-heavy
    code paths it's a hidden cost. The signal: when `split at h`
    leaves the goal looking like `(have x := ... ; if ... then ...
    else ...) = ...`, the let-binding is the obstacle, not the
    `if`.**

</details>

<details><summary>R41 — A block-scalar dispatch is small if you push the chain into a named helper.</summary>

41. **A block-scalar dispatch is small if you push the chain into a
    named helper.** Step 4b's `scanBlockScalarIx` cores around a
    five-stage cursor chain: `c → c.advance → parseBlockHeaderLoopIx
    → skipWhitespace → optional comment → consumeLineBreak →
    collectBlockScalarLoopIx`. The naive proof rebuilt that chain
    inside the monotonicity tactic, with each `have hSW`, `have
    hComm`, `have hCLB` referring to the cursor produced by the
    previous step. The terms in those `have`s were already
    100+ characters long because `cAfterHeader`,
    `cAfterWS`, `cAfterComm` were not source-level names —
    Reflection 40's rule prohibits `let`-binding them. Factoring
    the post-header cursor into `blockHeaderToBodyIx : IxCursor →
    IxCursor` (a single named helper) and proving
    `blockHeaderToBodyIx_offset_monotonic` once collapsed the
    dispatcher proof to two chained `have`s.
    **Rule: when a `let`-binding ban (Reflection 40) forces the
    same long expression to appear five times in a proof, extract a
    named helper for the expression. The helper's monotonicity
    lemma is the same length the inline chain would be — but you
    write it once, and the caller's proof is small.** Cost: the
    helper has to handle the `if comment then ... else ...`
    branching internally; the payoff is that downstream proofs
    treat the helper as opaque.

</details>

<details><summary>R42 — Mathlib's `set` is not in the kernel; substitute named `have` blocks.</summary>

42. **Mathlib's `set` is not in the kernel; substitute named
    `have` blocks.** The first cut at the block-scalar dispatch
    proof used `set cHdr := ...`, `set cComm := ...`, `set cBreak
    := ...` to abbreviate the cursor chain. The build failed with
    "unknown tactic" at the first `set`: `Mathlib.Tactic.Set`
    isn't in scope of any module the staging proofs reach. Fix:
    rewrote the chain as named `have` lemmas (`have hSW : ... ≤
    ...`, `have hComm : ... ≤ ...`, …) — the same logical
    structure but referring to the long expressions by repetition
    rather than by abbreviation. Or — as Reflection 41 separately
    documents — factor the long expression into a named helper.
    **Rule: do not reach for Mathlib tactics in staging proofs
    that the cutover commit will re-home into the main proof
    corpus; the cutover commit's import surface must remain
    minimal. If you find yourself wanting `set` for legibility,
    that's a signal to extract a named helper (Reflection 41).**

</details>

<details><summary>R43 — Save the cursor, not the position, when later code needs the bound proof.</summary>

43. **Save the cursor, not the position, when later code needs the
    bound proof.** Step 5a's `SimpleKeyStateIx` originally held a
    raw `pos : YamlPos`. When `scanValuePrepareIx` came to overwrite
    placeholder tokens at that position, it needed
    `pos.offset ≤ input.utf8ByteSize` for the indexed-token bound —
    but that proof had been discarded at save-time. Two bad fixes
    surfaced: (a) add a `posBound` proof field to `SimpleKeyStateIx`
    (rebuilds the cursor's bound apparatus in a parallel structure);
    (b) defer the bound check to runtime at every overwrite site
    (defensive code that should be statically discharged). Real fix:
    index `SimpleKeyStateIx` on `input` and store an
    `IxCursor input`, which carries `posBound` natively. The save
    site (`saveSimpleKeyIx`) copies the current cursor; the resolve
    site (`scanValuePrepareIx`) overwrites tokens using the saved
    cursor's `posBound` directly via the new `overwriteAtCursor`
    helper. **Rule: when later code at site B needs a proof about a
    quantity captured at site A, capture the *quantity-with-proof*,
    not the bare quantity. For positions inside the scanner, that
    means `IxCursor input` (carries `posBound`), not `YamlPos`. Yes,
    this indexes the holder structure on `input`; the cost is
    justified because the alternative is a parallel-state bound
    field at every save site.**

</details>

<details><summary>R44 — `emitAtSafe` is a legitimate dispatcher-side fallback when the static proof is long but mechanical.</summary>

44. **`emitAtSafe` is a legitimate dispatcher-side fallback when the
    static proof is long but mechanical.** Step 5a's dispatch family
    (`scanAnchorOrAliasIx`, `scanTagIx`, `scanYamlDirectiveIx`, etc.)
    emits tokens at a `startPos` captured at function entry. The
    obligation `startPos.offset ≤ s.cursor.pos.offset` after the
    function's cursor chain is a five-to-eight-step monotonicity
    chain through `s.advance` → `collect*Ix` → `skipWhitespace` →
    further `collect*Ix` → … None of the steps is hard, but each
    needs a one-line monotonicity lemma plus the chaining. Inlining
    five `(by sorry)` was a non-starter (Step 5a was authorised as
    sorry-free); writing the eight or so `collect*Ix_offset_monotonic`
    lemmas during the same session bloats the step beyond its scope.
    Resolution: define `emitAtSafe : ScannerStateIx → YamlPos →
    YamlToken → ScannerStateIx`, a defensive emit that checks the
    bound at runtime and falls back to a zero-width token at the
    current cursor if it fails. In well-formed scans the fallback is
    never taken; Step 5b discharges the static obligation by
    chaining helper-loop monotonicity and substitutes `emitAt` for
    `emitAtSafe`. **Rule: when the static proof at a use site is
    mechanical-but-long and not the headline deliverable of the
    current step, define a `*Safe` defensive sibling that performs
    the check at runtime and falls back to a well-defined alternate
    branch. Document the carry-forward to the next step's plan. Do
    not use this for proofs that are genuinely hard or in proof
    files — `*Safe` belongs to *source* files where a runtime check
    has near-zero cost; in proof files, the legitimate moves are
    "extract a helper lemma" (Reflection 41) or "split the step".**
    The signal that `*Safe` is the right move: every site is the
    same proof template, the proof is offset-monotonicity through a
    fixed shape, and the dispatcher will be refactored in the next
    step anyway.

</details>

<details><summary>R45 — Forward-looking blueprint paragraphs are *deliverables*, not *session work items*.</summary>

45. **Forward-looking blueprint paragraphs are *deliverables*, not
    *session work items*.** The pre-Step-5a blueprint said: "Step 5
    — End-to-end `parse ∘ present = id`. Tie the per-rule
    bidirectional lemmas into a single corpus theorem … All staging
    proofs reach sorry-free at end of session." Reading this as a
    one-session work item conflated the *end-of-phase deliverable*
    (the corpus theorem) with the *next-session scope* (whatever
    fits cleanly between Step 4b and the corpus theorem). The
    realistic work cluster is at least three sessions: 5a — the
    dispatcher and state; 5b — dispatcher monotonicity + carried
    content-correctness; 5c — `present` + corpus. Step 4 had the
    same shape (it was authorised as one session and ended up as
    4a/4b); the pattern recurs and is not "scope creep" — it is the
    normal pace at which legacy infrastructure migrates. **Rule:
    when reading a blueprint paragraph that describes a phase-end
    deliverable, distinguish (i) the artifact named (a theorem, a
    corpus, a sorry-free file) from (ii) the work item *for this
    session* (a slice of code/proof that is locally complete and
    leaves the next session with a named handoff). If (i) is much
    larger than (ii), pre-commit to the split (5a / 5b / 5c) before
    starting work; do not inherit the phase-end framing as the
    session's scope. The user is amenable to splits when the
    rationale is "this is the natural decomposition", not "we ran
    out of time".**

</details>

<details><summary>R46 — Sub-steps within sub-steps: when a "plan" entry is really a backlog, order it and quote the ordering before starting.</summary>

46. **Sub-steps within sub-steps: when a "plan" entry is really
    a backlog, order it and quote the ordering before starting.**
    Step 5b's blueprint plan listed eight carry-forward clusters
    behind a single "Step 5b" header. Treating that header as a
    one-session work item would have repeated the Step-5a scope
    mistake (Reflection 45) one level deeper. The user asked
    "order the 8 clusters into a reasonable sub-step plan; start
    on the 1st sub-step" — which is the right framing: the
    *plan* is the work item, the *sub-step* is the session.
    Concretely: the headline cluster (dispatcher
    offset-monotonicity chain + `emitAtSafe`→`emitAt`) splits at
    the right seam between helper-loop lemmas (small, local,
    eight near-identical six-line proofs) and per-dispatcher
    lemmas (uniformly thin but each touches a different
    dispatcher); these become 5b.1a and 5b.1b. The remaining
    seven clusters each become one sub-step (5b.2–5b.8); they
    are independent and can be reordered if priorities shift.
    The cost of writing the sub-step ordering down before
    starting work is one paragraph; the benefit is that the
    "next session" handoff is unambiguous and the session can
    end cleanly when 5b.1a lands rather than tempting an
    over-reach into 5b.1b. **Rule: when a step's plan paragraph
    is itself a list of more than three items, order the items
    into named sub-steps in the blueprint *before* coding. The
    sub-step list is the working contract for the next several
    sessions; without it the temptation is to either over-reach
    (claiming multiple sub-steps when one suffices) or
    under-reach (leaving the carry-forward fuzzy). Apply this
    recursively: if a sub-step plan paragraph itself becomes a
    list of more than three items, sub-divide again.**

</details>

<details><summary>R47 — "Single-line chain" framing in a sub-step plan is a hypothesis to test before coding, not a sizing claim to trust.</summary>

47. **"Single-line chain" framing in a sub-step plan is a
    hypothesis to test before coding, not a sizing claim to
    trust.** The 5b.1b sub-step plan (written at end of 5b.1a)
    asserted that per-dispatcher monotonicity is "a single-line
    chain (the helper-loop lemmas from 5b.1a + the per-rule
    recogniser lemmas already proven in
    `Proofs/Scanner/IndexedScalar.lean`)." Reading the actual
    dispatchers at session start surfaced two things the framing
    missed: (a) `unfold + simp` only collapses to a single line
    once the state-level helpers (`emit`, `emitAt`,
    `pushMappingIndentIx`, `saveSimpleKeyIx`, `scanValuePrepareIx`,
    …) have `@[simp]` cursor-preservation lemmas — ~12 of them
    are missing; (b) `scanLoopIx` returns a `TokenStream`, not a
    state, so it doesn't admit a `cursor_offset_monotonic`
    statement at all — its monotonicity has to be expressed at
    the token level (every emitted token has `start.offset ≥`
    initial cursor's offset) and is *not* a one-line chain. Both
    discoveries happened in the first 20 minutes of reading and
    were trivially fixable by splitting 5b.1b into i (helpers),
    ii–iii (dispatcher chains), iv (loop) — but neither was
    visible from the 5b.1a-era plan paragraph. A complementary
    failure mode caught in the same pass: the plan listed
    `consumeLineBreak_offset_monotonic`,
    `skipCommentText_offset_monotonic`,
    `skipToContent_offset_monotonic` as *needed*, but a `grep`
    showed they already existed in `IndexedWhitespace.lean` and
    `IndexedIndent.lean`. The first-draft file contained
    re-proofs of these and failed to compile with "already
    declared" — a five-minute fix, but a five-minute fix that
    didn't need to happen. **Rule: when a sub-step plan
    paragraph contains size or shape claims ("single-line",
    "uniformly thin", "mechanical"), do not trust them as the
    session begins. The first action of the session is to
    read the actual code the sub-step touches and (a) `grep`
    for the supporting infrastructure the chain claims to use
    — confirm what exists and what is missing; (b) check that
    the result type of every named function admits the claimed
    statement form; (c) if either check fails, *update the
    plan before coding*, then proceed. Five minutes of reading
    saves a session-ending re-plan.**

</details>

<details><summary>R48 — `split at h` cannot peel a `do throw e; rest` block in an `Except` monad until `pure_bind` and the surrounding `if`/`match` have been rewritten.</summary>

48. **`split at h` cannot peel a `do throw e; rest` block in an
    `Except` monad until `pure_bind` and the surrounding
    `if`/`match` have been rewritten.** The Pattern-C draft of
    `scanDocumentEndIx_offset_monotonic` (5b.1b.ii) opened with
    `unfold ... at h; split at h` — and `split` failed because
    after `unfold`, the hypothesis `h` was not a top-level
    `if`/`match` but a `bind` expression: in Lean 4, `do
    if cond then throw e; rest` desugars to a bind where the
    immediate constructor is `Bind.bind`, not the `if` we wanted
    to dispatch on. The fix is two layers: (i) use
    `by_cases hd : cond` and `rw [if_pos hd] at h` / `rw [if_neg
    hd] at h` to peel the *outer* conditional (so the `then`
    branch produces a `throw`-bind that `simp [Bind.bind,
    Except.bind] at h` collapses to `.error _ = .ok s'` —
    discharged automatically); (ii) `simp only [pure_bind] at h`
    after the `if_neg` rewrite to flatten the residual
    `do let y ← pure (); k y` wrapper that the trailing match
    sits inside, so the *next* `split at h` sees the match
    directly. Once both wrappers are off, the inner `match
    probe.peek? with | none => pure () | some '#' => pure () |
    some ch => if ... then pure () else throw ...` is the
    target shape `split` was designed for. **Rule: when a proof
    targets a hypothesis of the form `<exception-monad
    do-block> = .ok x`, first reduce monad-laws (`pure_bind`,
    `Bind.bind`, `Except.bind`) and resolve top-level `if`s
    with `by_cases` + `if_pos`/`if_neg` so the hypothesis is
    syntactically a `match` or `if` before `split at h`. The
    diagnostic "Tactic `split` failed: Could not split an `if`
    or `match` expression in the type" almost always means a
    bind wrapper survives and needs `simp [pure_bind, Bind.bind,
    Except.bind]` first.** (See
    `scanDocumentEndIx_offset_monotonic` in
    `Proofs/Scanner/IndexedDispatch.lean`.)

</details>

<details><summary>R49 — `split at h` also cannot peel a term-level `let`-block until the lets are zeta-reduced.</summary>

49. **`split at h` also cannot peel a term-level `let`-block
    until the lets are zeta-reduced.** Reflection 48 covered
    `do`-block bind wrappers; R49 is the analogue for plain
    term-level `let`/`have` bindings. The 5b.1b.iii dispatchers
    (`scanAnchorOrAliasIx`, `scanTagIx`, `scanDirectiveIx`) are
    *not* `do`-blocks — they're chains of `let startPos := ...;
    let sAdv := s.advance; let ...; if cond then ... else ...`.
    After `unfold scanXIx at h`, the hypothesis looks like
    `(let ... let ... if cond then ... else ...) = .ok s'`, with
    the `if`/`match` buried under the let-binders. `split at h`
    fails with the same "Could not split an `if` or `match`
    expression in the type" diagnostic — but now there is no
    bind to flatten, just lets to zeta-reduce. Two fixes that
    work:
    (i) **`simp only at h`** with no arguments (default
    `zeta := true`) reduces every let-binding, lifting the
    outer `if`/`match` to the top so `split at h` reaches it.
    Used in `scanTagIx`, `scanDirectiveIx`.
    (ii) **`by_cases hc : <condition>` + `rw [if_pos hc] at h`
    / `rw [if_neg hc] at h`** to peel the conditional manually,
    one layer at a time. `rw` handles zeta through lets when
    matching the condition syntactically. Used in
    `scanAnchorOrAliasIx`. **Rule: when `split at h` fails on a
    term-level dispatcher unfold, the obstacle is almost always
    let-binders (not binds); `simp only at h` is the
    one-tactic fix, `by_cases` + `rw [if_pos/if_neg]` is the
    fine-grained alternative when one or both branches contain
    further structure to dispatch.** This pairs with R48 — both
    say "`split at h` only works when the hypothesis is already
    syntactically an `if`/`match` at the head, and `unfold`
    alone does not put it there." (See
    `scanAnchorOrAliasIx_offset_monotonic`,
    `scanTagIx_offset_monotonic`, and
    `scanDirectiveIx_offset_monotonic` in
    `Proofs/Scanner/IndexedDispatch.lean`.)

</details>

<details><summary>R50 — Inner-let `if` produces orthogonal sub-cases that 2-arm `split at h` skeletons miss (Phase 3 Step 5b.1b.iv-pre).</summary>

50. **Inner-let `if` produces orthogonal sub-cases that 2-arm
    `split at h` skeletons miss.** When a function body contains
    `let s := if cond then unwind s else s` followed by trailing
    matches, `simp only at h` zeta-reduces the let, exposing the
    inner `if` as a SEPARATE top-level conditional. A nested 2-arm
    `split at h ; · ... ; · split at h` then encounters MORE
    sub-cases than the surface syntax suggests, because the
    inner-let `if`'s `isTrue` arm contains the trailing `if errCond`
    and `match peek?`, and likewise for the `isFalse` arm. Two
    fixes: (i) `all_goals first | <success path> | (split at h;
    <inner>)` factors the trailing-content peeling into a single
    tactic invoked uniformly from each sub-case; (ii) case-exhaustive
    nested splits write out all sub-cases explicitly.
    R50 pairs with R49 (term-level `let`-block obstacle) and R48
    (do-block `let`-block obstacle): destructuring tactics don't
    peel through `let`-zeta'd intermediate state, and the *number*
    of surviving sub-cases after `split` depends on the zeta'd
    structure, not just the original surface syntax. **Rule: when a
    sub-step plan mentions a "single-line chain" or "5-way uniform"
    shape, count the let-zeta'd `if`s before estimating proof
    length, not the surface-syntax `if`s.** See full text in
    Step 5b.1b.iv-pre.

</details>

<details><summary>R51 — Do-block early-return needs `by_cases hg + rw [if_pos/if_neg] + cases hF`, not nested `split at h`; dependent matches need `split at h`, not `cases hF : f s` (Phase 3 Step 5b.1b.iv-cont).</summary>

51. **Two technical patterns the top-level dispatcher monotonicity
    proofs needed beyond R50's candidates.** The seven top-level
    chain lemmas (`scanNextTokenIx_preprocess`,
    `scanNextTokenIx_dispatch{Structural,FlowIndicators,
    BlockIndicators,Content}`, `scanNextTokenIx`,
    `scanLoopIx_tokens_size_le`) needed two new techniques that
    R48–R50 had not yet exposed:

    **(i) Do-block early-return is best peeled by
    `by_cases hg + rw [if_pos / if_neg] at h + cases hF : f s
    with`.** R50's preferred `simp only at h ; split at h` approach
    does not cleanly handle do-blocks like `do { if c then return
    some v ; if c2 then let s' ← g s ; return some s' ; ... }`. The
    Lean elaborator inserts `__do_jp` join-point chains that
    `simp [Bind.bind, Except.bind]` partially reduces but leaves
    residual `match pure PUnit.unit with ...` patterns that don't
    simplify further (the `match Except.ok x with | error => ... |
    ok v => f v` doesn't beta-reduce in `simp only`, only in `simp`
    with structural reduction). Instead, peel each guard with
    `by_cases hg : (c == 'X') = true` + `rw [if_pos hg / if_neg hg]
    at h`, then `cases hF : <scanner> s with | error e => rw [hF]
    at h; simp [...] at h | ok v => rw [hF] at h; simp [..., Pure.pure,
    Except.pure] at h; cases h; chain`. The `simp` with `Pure.pure`,
    `Except.pure` reduces `pure (some v) = .ok (some s')` to
    `v = s'`, which closes via `exact congrArg Except.ok h` or just
    `cases h`.

    **(ii) Dependent matches (`match hBS : f s with`) need
    `split at h`, not `cases hF : f s`.** `scanNextTokenIx_dispatchContent`
    has three scalar-`Option` matches with witness binders
    (`match hBS : scanBlockScalarIx ... with | some r => ...uses
    hBS for hBound ... | none => throw _`). Using `cases hF :
    scanBlockScalarIx ... with` followed by `rw [hF] at h` fails
    with "motive is not type correct" because the body of the
    `some r` arm depends on `hBS` (the witness equation), and
    rewriting the discriminant changes the implicit `hBS`'s type.
    The fix is `split at h` (which performs case analysis directly
    on the match in `h`) followed by `rename_i r hBS` to bind the
    witness in the proof's local scope, then `cases h` to
    substitute the constructed state. R51 generalises: **when a
    match has a `: x with`-style witness binder, `cases : x` fails
    on the resulting `rw`; use `split at h` instead.**

    Also incidental: alpha-equivalent terms with different bound
    names in `match` patterns (`| some s' => f s'` vs `| some t =>
    f t`) sometimes fail to unify across a private-helper
    `Application type mismatch` when one bound name shadows an
    outer free variable with the same name. Solution: rewrite the
    proof inline (no helper) when the helper's bound-name
    expectations diverge from the call site's. See full text in
    Step 5b.1b.iv-cont.

</details>

<details><summary>R52 — Post-advance guards on the *same* `inFlow` flag dispatch cleanly only after `flowLevel`/`inFlow` preservation simp lemmas are in scope (Phase 3 Step 5b.2).</summary>

52. **`scanBlockEntryIx` and `scanKeyIx` now carry the legacy's
    `tabInIndentation` throw; their monotonicity needed three new
    `inFlow`-preservation simp lemmas.** Both indicator scans have
    the shape

    ```
    do
      let s := if !s.inFlow then pushMappingIndentIx s c else s
      let s := s.emit YamlToken.key
      let s := s.advance
      if !s.inFlow then if let some '\t' := s.peek? then throw err
      .ok { s with … }
    ```

    The post-advance `if !s.inFlow` guards on the *post-pushMapping/
    emit/advance* state's `inFlow`, but `pushMappingIndentIx`, `emit`,
    and `advance` all preserve `flowLevel` (rfl on the structure
    update), so the post-state's `inFlow` is definitionally the
    *original* `s.inFlow`. The monotonicity proof wants to peel both
    `if !s.inFlow` guards with the same `by_cases hi : (!s.inFlow) =
    true`. Without preservation lemmas, simp leaves the inner
    condition as `(!(s.pushMappingIndentIx col).inFlow)`, and
    `if_pos hi` only fires on the outer occurrence; the inner if
    survives and `split at h` introduces a discordant
    `h✝ : (!(post).inFlow) = true` hypothesis that doesn't close.

    **Fix:** add `emit_flowLevel`/`advance_flowLevel`/
    `pushMappingIndentIx_flowLevel` (proofs: `rfl` or
    `unfold; split <;> rfl`) plus the corresponding `_inFlow` lemmas
    (each proved `unfold pushMappingIndentIx; split <;> rfl`), all
    tagged `@[simp]`. Then `simp only [if_pos hi, advance_inFlow,
    emit_inFlow, pushMappingIndentIx_inFlow] at h` chains: `if_pos hi`
    eliminates the outer if (so the post-state is now
    `pushMappingIndentIx s c`, not an `if`), the inFlow chain
    rewrites the inner condition's `((push s c).emit key).advance.inFlow`
    to `s.inFlow`, and `if_pos hi` then fires again on the inner if.
    What remains is the `match s.peek?` over the tab discriminant —
    `split at h` dispatches it cleanly.

    **Generalisable rule:** **when the same flag (e.g. `inFlow`)
    gates both a let-binding side effect *and* a subsequent guard,
    add a preservation simp lemma for each intermediate operation,
    so a single `by_cases` on the original flag collapses both ifs
    via `simp only [if_pos hi]`.** This is cheap (rfl-trivial
    lemmas), eliminates the "split-produces-discordant-hypothesis"
    failure mode, and keeps the proof linear instead of branching
    on case-shape that the elaborator already knows is impossible.

    **Aside on `@[inline]`:** `inFlow` is `@[inline]`, but Lean's
    elaborator keeps it as a projection at the term level — the
    inline expansion happens only at compile time. So the simp
    lemma's `(pushMappingIndentIx s col).inFlow = s.inFlow` does
    apply syntactically, despite the inline annotation.

</details>

<details><summary>R53 — Named-let do-blocks need `simp only [bind, Except.bind] at h; split at h; cases h`, not `simp only [Except.ok.injEq] at h; subst h`; and `lake build` cache hides upstream breakage until a downstream edit invalidates it (Phase 3 Step 5b.3).</summary>

53. **`scanValueIx`'s four-stage `do`-chain, and the cache-hidden
    breakage we paid for after `5994edce`.** Splitting `scanValueIx`
    from one-stage to four (`scanValueClearKeyIx /
    scanValueValidateIx / scanValuePrepareIx / scanValueTabCheckIx`)
    surfaced two distinct lessons.

    **Proof-shape lesson — `subst h` does not survive named-let
    do-blocks**. The Step 5b.1b.ii proof of `scanValueIx_*` was:

    ```lean
    unfold scanValueIx at h
    simp only [Except.ok.injEq] at h
    subst h
    show s.cursor.pos.offset ≤ _
    simp only [advance_cursor, emit_cursor, scanValuePrepareIx_cursor]
    exact IxCursor.advance_offset_monotonic _
    ```

    That worked while `scanValueIx` was a flat composition
    (`let s := scanValuePrepareIx s; let s := s.emit .value;
    let s := s.advance; .ok { s with … }`). After Step 5b.3 the
    definition is

    ```lean
    do
      let s_kc := scanValueClearKeyIx s
      scanValueValidateIx s_kc
      let s_prepared := scanValuePrepareIx s_kc
      let s_with_token := s_prepared.emit YamlToken.value
      let s_after_advance := s_with_token.advance
      scanValueTabCheckIx (s.cursor.pos.col : Int) s.currentIndent
                           s_after_advance
      .ok { s_after_advance with … }
    ```

    Two changes break the old proof. First, the elaborator renders
    `let s_kc := scanValueClearKeyIx s` (followed by no `do`-bind
    on `s_kc`) as `have s_kc := …; do …`. `simp only [Except.ok.injEq]
    at h` doesn't reduce the `do` block because the `do` block isn't
    `Except.ok`-shaped at the syntactic level — the `s_kc.scanValueValidateIx`
    and `scanValueTabCheckIx … s_after_advance` calls produce
    `Except` values that need bind-reduction first. Second, when
    `subst h` does fire (after a successful `injEq` rewrite), it
    tries to substitute through the `have`-bound variable names —
    but the lemmas in the goal refer to `scanValueClearKeyIx s`
    spelled out, and `rw [hV]` over `s.scanValueClearKeyIx.scanValueValidateIx`
    cannot find that pattern because the term has `s_kc.scanValueValidateIx`.

    **Fix — the legacy pattern**: `simp only [bind, Except.bind]
    at h` evaluates the do-block to a nested match, exposing the
    `.error` / `.ok` cases of each `Except`-throwing stage. Then
    `split at h` opens one match per throwing stage, `cases h`
    discharges each `.error` branch (since `h : .error e = .ok s'`
    is `False`), and the surviving `.ok`/`.ok` branch reduces to
    the constructed state which `simp only [advance_cursor,
    emit_cursor, scanValuePrepareIx_cursor, scanValueClearKeyIx_cursor]
    + IxCursor.advance_offset_monotonic _` closes. This is
    exactly the legacy `Proofs/Scanner/ScannerCorrectness.lean::
    scanValue_offset_lt` shape, translated 1:1 to the indexed
    types. **Generalisable rule**: whenever a `do`-block contains
    two or more `Except`-throwing calls and uses named `let`
    bindings between them, expect `simp only [bind, Except.bind]
    at h; split at h` as the proof skeleton, with `cases h` on
    each error branch.

    **Cache lesson — `lake build` reuses `.olean` files even when
    the originating source has been deleted/refactored**. Commit
    `5994edce` ("Spec traceability: per-character predicates +
    emission constants") changed the shape of several functions in
    `L4YAML/Scanner/IndexedScanner.lean` —
    `collectDoubleQuotedLoopIx`, `collectSingleQuotedLoopIx`,
    `parseBlockHeaderLoopIx`, `blockHeaderToBodyIx`, and
    `skipToContentLoop` — but `Proofs/Scanner/IndexedScalar.lean`
    and `Proofs/Scanner/IndexedIndent.lean` had no source edits,
    so the cached `.olean` files were re-used. The proofs *inside*
    those files referenced the old function shapes (`split at h`
    with four match branches for the old `some '"' | some '\\' |
    some ch | none`, `(ch == '#') = false` for the old comment
    test) and would have failed to recompile from scratch. The
    build reported "385/385" because nothing forced a recompile of
    the affected files.

    Step 5b.3 edited `IndexedDispatch.lean`, which transitively
    forces `IndexedScalar.lean` and `IndexedIndent.lean` to
    rebuild — at which point all six previously-cached proofs
    failed. The fix was mechanical (re-shape `split at h` to the
    new outer `some ch` / `none` split followed by nested
    `if`-cascade splits; switch `(ch == '#') = false` to
    `isCommentBool ch = false` via `unfold isCommentBool;
    simp [hHash]`; switch `(peek? == some '#')` to `by_cases hp :
    (match … isCommentBool d | none => false) = true; rw [if_pos
    hp]/[if_neg hp]`), but the deeper lesson is

    > **A successful `lake build` after a refactor only proves
    > "downstream files that were already compiled remain valid"
    > — it does *not* prove "every dependent file will recompile
    > cleanly." When changing a function's match/if structure (not
    > just renaming), force a downstream recompile (`touch` the
    > consumer, or temporarily flip a non-trivial import) before
    > calling the refactor complete.**

    This is dual to R47's pre-coding `grep` advice: there, we
    burned cycles writing lemmas that already existed; here, we
    shipped a commit whose stale-cache success masked latent
    incompatibility. Both failure modes have the same root —
    treating `lake build` as a proof-of-coherence rather than as
    a proof-of-cached-coherence.

</details>

<details><summary>R54 — `rcases` over an `Or` of `Nat.le` conjunctions destructures `Nat.le` itself and chokes; use plain `cases h with | inl … | inr …` instead (Phase 3 Step 5b.4).</summary>

54. **The hex-escape value-correctness proofs picked up a
    surprising `rcases` failure mode.** `hexDigitValue_lt_16` takes
    `h : isHexDigitBool ch = true` (a Bool disjunction over three
    UInt32 ranges) and needs to discharge each range. The natural
    first move:

    ```lean
    simp only [isHexDigitBool, Bool.or_eq_true, Bool.and_eq_true,
               decide_eq_true_eq, UInt32.le_iff_toNat_le] at h
    rcases h with ⟨hLo, hHi⟩ | ⟨hLo, hHi⟩ | ⟨hLo, hHi⟩
    ```

    fails with

    > `cases` failed with a nested error: Dependent elimination
    > failed: Failed to solve equation
    > `ch.val.toBitVec.toFin.1 = 97` at case `Nat.le.refl`

    The diagnosis took two iterations. First, the disjunction
    Lean produces is `(d ∨ u) ∨ l`, not the three-way disjunction
    the `|`-pattern syntax suggests — `||` is left-associative, so
    the simp result is `(0x30..0x39 ∨ 0x41..0x46) ∨ 0x61..0x66`.
    Second, and more importantly, **`rcases` aggressively
    destructs `Nat.le` along with `∧` and `∨`**. After the simp
    pass each disjunct is a conjunction of two `Nat.le` terms; the
    angle-bracket pattern tells `rcases` to split the conjunction,
    but `rcases` then looks one level deeper and tries to do
    dependent elimination on the underlying `Nat.le` (which has
    two constructors `refl` and `step`). The `refl` case requires
    unifying the two arguments — e.g. `ch.val.toBitVec.toFin.1`
    with `97` — which fails because the left-hand side is a
    variable expression.

    **Fix — plain `cases`**:

    ```lean
    cases h with
    | inr hLower => …
    | inl hDU =>
      cases hDU with
      | inl hDigit => …
      | inr hUpper => …
    ```

    `cases` on `Or` produces exactly two sub-goals carrying the
    intact conjunction — no further destruction. Then `hLower.1`
    / `hLower.2` extracts the `Nat.le` halves as raw facts that
    `omega` can consume. **Generalisable rule**: when `rcases`
    fails on `cases` with a `Nat.le.refl` reference, fall back to
    plain `cases` and explicit `.1` / `.2` projections; `rcases`'s
    convenience comes at the price of unwanted deep destruction.

    Two ancillary observations:
    - Each UInt32 literal needs an explicit `(0xNN : UInt32).toNat
      = NN` lemma (`by native_decide`) so `omega` has concrete
      Nat values. The literals survive simp as `UInt32.toNat 48`
      etc., which `omega` cannot evaluate further.
    - `simp only [decide_eq_true_eq, UInt32.le_iff_toNat_le]` is
      strong enough to do everything in one pass — including
      pushing the conjunction over `Or`. The earlier attempt to
      stay in Bool land (`(c.val ≥ 0x30) = true` plus a `decide`
      extraction lemma) hit a different elaboration anomaly where
      `(c.val ≥ 0x30) : Bool` does not surface as `decide …`
      cleanly. The Nat-first approach is more robust.

</details>

<details><summary>R55 — `split` after `unfold` fires on the *first* `match`/`if` it finds, including the implicit prod-destructure inside `let (a, b) := …`; count the nested constructs before placing bullets (Phase 3 Step 5b.5).</summary>

55. **The auto-detect-indent loop proof exposed a counting bug in
    nested `split` tactics.** `autoDetectBlockScalarIndentLoopIx`'s
    recursive body has the shape

    ```lean
    | fuel + 1 =>
      let (probeAfterSp, _) := skipSpaces probe
      match probeAfterSp.peek? with
      | some c =>
        if isLineBreakBool c then
          let maxWSCol' := if … then … else …
          autoDetectBlockScalarIndentLoopIx … fuel
        else
          if probeAfterSp.pos.col > minContentIndent then … else …
      | none => if maxWSCol > minContentIndent then … else …
    ```

    The natural proof is induction on `fuel`. After `unfold`, the
    `succ fuel` body has three nested splittable forms:
    1. The `let (probeAfterSp, _) := skipSpaces probe` prod
       destructure — `split` treats it as a `match` with **one**
       case.
    2. The `match probeAfterSp.peek?` arm — two cases (some/none).
    3. The inner `if isLineBreakBool ch` — two cases.

    My first attempt placed two bullets after a single outer
    `split` (anticipating some/none from the peek? match), then a
    nested `split` inside the "some" branch. The error message gave
    the game away: `case h_1` after the inner `split` carried both
    `x✝¹ : IxCursor input × Nat` (the prod from the let) **and**
    `x✝ : Option Char` (the peek? result) as hypotheses, with the
    goal still containing the full `if isLineBreakBool` if-then-else.
    Translation: the *outer* `split` had consumed the prod
    destructure (1 case), the *inner* `split` had consumed the
    peek? match (2 cases), and the `if isLineBreakBool` had never
    been split. So `apply ih` was looking at the whole if-then-else.
    Worse, the second top-level bullet (intended for the "none"
    case) saw "No goals to be solved" — because the outer split's
    single case was already consumed by the first top-level
    bullet's body.

    **Fix — three `split`s, two bullets**:

    ```lean
    | succ fuel ih =>
      unfold autoDetectBlockScalarIndentLoopIx
      split  -- (1) prod destructure (1 case)
      split  -- (2) peek? match (2 cases)
      · -- some ch
        split  -- (3) if isLineBreakBool ch (2 cases)
        · apply ih           -- true: recurse, IH ∀ maxWSCol'
        · split <;> omega    -- false: column bound
      · -- none — EOF
        split <;> omega
    ```

    Two consecutive `split`s with no intervening `·` is the
    idiomatic way to thread through a one-case match: the second
    `split` sees the still-open single goal and splits it again.

    **Generalisable rule**: before placing bullets after `split`,
    count *all* the splittable forms in the goal — including
    implicit prod-destructures from `let (a, b) := …`. The
    diagnostic-printed case label (`case h_1`/`h_2`) and the
    sequence of `x✝` hypotheses are reliable evidence of how many
    `split`s actually fired. A failing `apply` whose goal still
    contains the if-then-else you *thought* you had just split is
    the canonical signature of this bug.

    Two ancillary observations:
    - The IH for `autoDetectBlockScalarIndentLoopIx_ge_min` is
      universally quantified over `(probe, maxWSCol)` (via
      `induction fuel generalizing probe maxWSCol`). This is
      load-bearing: the recursive call carries an updated
      `maxWSCol'`, and the IH must absorb that.
    - The entry-point wrapper
      `autoDetectBlockScalarIndentIx_ge_min` is a one-liner
      because `autoDetectBlockScalarIndentIx` is a wrapper passing
      `0` for `maxWSCol` and `input.utf8ByteSize` for `fuel` — the
      loop lemma's universal quantification covers both.

</details>

<details><summary>R56 — Spec-traceability lemmas for pure `String → String` transformers are *definitional unfolds*; their value is the named anchor, not the proof shape (Phase 3 Step 5b.6).</summary>

56. **Block-scalar content correctness reduced to definitional unfolds.**
    `applyChomp` and `foldBlockContent` are pure `String → String`
    transformers — they take a fully-collected raw accumulator and
    apply a closed-form transformation (strip / clip / keep newlines;
    run the four-state fold machine). There is no cursor, no
    `IxCursor`-indexed reasoning, no monotonicity obligation. The
    "matches spec semantics" theorem is therefore a *definitional*
    statement, not a *computational* one.

    Concretely, all six Layer F.2 lemmas are one-line proofs:

    ```lean
    theorem applyChomp_keep (raw : String) :
        applyChomp .keep raw = raw := rfl
    theorem applyChomp_strip (raw : String) :
        applyChomp .strip raw = stripTrailingNewlines raw := rfl
    theorem applyChomp_clip_of_endsWith {raw : String}
        (h : raw.endsWith (String.singleton lineFeedChar) = true) :
        applyChomp .clip raw =
          stripTrailingNewlines raw ++ String.singleton lineFeedChar := by
      simp [applyChomp, h]
    theorem applyChomp_clip_of_not_endsWith {raw : String}
        (h : raw.endsWith (String.singleton lineFeedChar) = false) :
        applyChomp .clip raw = stripTrailingNewlines raw := by
      simp [applyChomp, h]
    theorem foldBlockContentGo_nil (acc : String) (st : FoldState)
        (pending : Nat) : foldBlockContentGo [] acc st pending = acc := rfl
    theorem foldBlockContent_empty : foldBlockContent "" = "" := rfl
    ```

    The temptation in a proof-heavy phase is to under-value a `rfl`
    or `simp` lemma — to read its shortness as triviality. That's
    backwards. The value is **not** the proof; it is the *named
    statement*. Once `applyChomp_clip_of_endsWith` exists, downstream
    consumers (Steps 5b.7, 5b.8 — quoted and plain multi-line) can
    cite it directly when reasoning about the pipeline
    `parseBlockHeaderLoopIx → blockHeaderToBodyIx →
    autoDetectBlockScalarIndentIx → collectBlockScalarLoopIx →
    applyChomp → foldBlockContent` without unfolding the case
    structure of `applyChomp` at each call site. The same is true of
    `applyChomp_keep` / `_strip` — they look definitional but they
    are *exactly the spec-rule statement*: each branch of `[160]`'s
    chomping indicator has its named theorem.

    **Generalisable rule**: when a function is a closed-form
    `String → String` (or any pure data transformer), look for *spec
    traceability* lemmas — one per branch of its operational
    structure — even if the proof of each is `rfl`. They are not
    busywork; they are the bridge between the implementation and the
    spec citation that downstream proofs will quote. The mistake is
    to skip them and re-derive the case split inline every time a
    larger proof passes through `applyChomp`.

    **Ancillary observation — `foldBlockContent` correctness has
    only two `rfl`-shaped lemmas because the interesting cases are
    *not* base cases.** The four-state fold machine has rich
    behaviour on non-empty input that *does not* reduce by `rfl`
    (the state transitions in the `c :: rest` arm involve nested
    `if`s and `match st with` branches). A full functional
    correctness theorem for `foldBlockContent` against the spec's
    folded-content extraction rule would need a list-induction proof
    that simultaneously tracks `FoldState`, `pending`, and the input
    structure — and even stating the spec side cleanly requires a
    separate reference implementation to compare against. Step 5b.6
    deliberately lands the *spec-traceability* fragment (named
    branches + base case) and leaves the full fold-machine
    invariant for a later pass when its consumers force the proof
    obligation. See the carried-forward note at the end of Step 5b.6.

</details>

<details><summary>R57 — `unfold` rewrites *every* occurrence of the symbol in the goal, including the RHS; for branch-mapping lemmas whose RHS is another call of the same recursive function, use `conv => lhs; unfold …` to scope the rewrite (Phase 3 Step 5b.7).</summary>

57. **A `simp` blow-up in a one-line branch-mapping proof, and the
    `conv => lhs;` rescue.** Step 5b.7 lands nine spec-traceability
    lemmas for the quoted multi-line fold/collect pipeline. Six
    follow the Step 5b.6 template directly — `rfl` for the
    `fuel = 0` base cases, and `unfold + rw [hPeek] + simp [hCond]`
    for the closing-delimiter branches where the RHS is a literal
    `some (content, c.advance)` value. The three *line-break-fold*
    / *doubled-quote* branches — `collectDoubleQuotedLoopIx_linebreak`,
    `collectSingleQuotedLoopIx_doubled`,
    `collectSingleQuotedLoopIx_linebreak` — initially looked like
    they'd follow the same shape:

    ```lean
    theorem collectDoubleQuotedLoopIx_linebreak ... :
        collectDoubleQuotedLoopIx c content (fuel + 1) =
          collectDoubleQuotedLoopIx (foldQuotedNewlinesIx c).2
            (trimTrailingWSIx content ++ (foldQuotedNewlinesIx c).1) fuel := by
      unfold collectDoubleQuotedLoopIx     -- ← lands a goal whose RHS
      rw [hPeek]                            --   is *also* unfolded!
      simp [hNotQuote, hNotEscape, hLineBreak]
    ```

    But the proof failed: `simp` left an unsolved goal where the
    RHS had been expanded into the full match-cascade
    (`match fuel with | 0 => none | succ => match (foldQuotedNewlinesIx c).snd.peek? with | …`).
    The cause: `unfold collectDoubleQuotedLoopIx` rewrites **every
    occurrence** of the symbol in the goal — including the
    `collectDoubleQuotedLoopIx (foldQuotedNewlinesIx c).2 …` call
    on the RHS that I wanted to keep frozen. With both sides
    unfolded, `simp` happily reduced the LHS's match all the way
    to the line-break branch (which itself contains another
    `collectDoubleQuotedLoopIx` invocation), and then *also* tried
    to reduce the RHS — but the RHS's `peek?` is on
    `(foldQuotedNewlinesIx c).snd`, an opaque term, so simp got
    stuck with two structurally-different presentations of "the
    same recursive call."

    **The fix is `conv => lhs; unfold …`** — a scoped `conv` block
    that descends into the LHS of the equality and applies `unfold`
    there only:

    ```lean
      conv => lhs; unfold collectDoubleQuotedLoopIx
      rw [hPeek]
      simp [hNotQuote, hNotEscape, hLineBreak]
    ```

    With the RHS untouched, `simp` proves the goal by reducing the
    LHS down to exactly the RHS expression. The repository already
    uses this shape elsewhere — `Proofs/Production/ScannerPlainScalarValid.lean::1537`
    has `conv => lhs; unfold flowNesting.go` for the same reason.
    (Note: `conv_lhs => …` is the Mathlib spelling and is *not*
    available in this Mathlib-free codebase — `conv => lhs; …` is
    the plain-Lean equivalent.)

    **Generalisable rule**: whenever a branch-mapping lemma's RHS
    contains another call to the function being unfolded, prefer
    `conv => lhs; unfold …` over plain `unfold …`. This applies
    not just to recursive functions but to any pattern where the
    same symbol appears on both sides of the goal and only one side
    should be reduced. The cost is one extra line; the payoff is
    that `simp` stays well-behaved instead of expanding the RHS
    into a syntactically distinct form that no further tactic can
    close. Diagnostic clue: when `simp` after `unfold` leaves an
    unsolved goal that contains a giant `match … with | …` cascade
    on the *right* of an equation whose original RHS was a small
    function application, the unfold scoped too widely.

    **Ancillary observation — six of the nine lemmas follow the
    Step 5b.6 template unchanged.** The `_zero` base cases are
    `rfl`. The `_closing` / `_closing_some` / `_closing_none`
    branches return literal `some (content, c.advance)` values that
    `simp` reduces directly. Only the three branches whose
    operational result is another call of the same loop need the
    `conv` scoping — they are the ones encoding "consume some
    delimiter, recurse on the rest" rather than "terminate with
    this value." This pattern recurred in Step 5b.8 (plain multi-line)
    exactly as predicted: five of `collectPlainScalarLoopIx`'s 11
    post-`peek?` outcomes need `conv => lhs; unfold …`
    (`_colon_continue`, `_linebreak_flow`, `_linebreak_block_some`,
    `_whitespace`, `_content`); the six terminating branches use
    plain `unfold`.

</details>

#### Phase 3 sub-plan (six sessions)

<details><summary>Phase 3 is ~30× the size of the Phase 2 capstone. It is decomposed into six sessions; only the final commit must be atomic per Guardrail 1.</summary>

The legacy scanner is ~3,100 LOC across 8 files in
`L4YAML/Scanner/`; the existing scanner proofs are ~17,000 LOC
across 18 files (14 carry sorries today, including the 10,637-line
`Proofs/Scanner/ScannerCorrectness.lean`). Doing the cutover in
one session is infeasible. Guardrail 1 ("no parallel state")
requires only that the **cutover commit** be atomic — *not* that
the whole phase fit in one commit. Steps 1–5 below land staging
code in `L4YAML/Indexed/` and (later) a `Scanner/Indexed*.lean`
namespace that the production build does **not** import. Step 6
performs the atomic cutover: rename, delete legacy, retarget every
downstream proof file in one push.

<details><summary>Step 1 — Indexed-type extensions <em>(landed)</em>.</summary>

**Step 1 — Indexed-type extensions** *(landed)*.
Grew the indexed substrate so steps 2–5 have the primitives they
need. Added operations on `Range input`, `IxToken input`,
`TokenStream input`, plus a new `IxCursor input` (position-tracked
byte cursor with `peek?`, `peekAt?`, `peekBack?`, `advance`,
`advanceN`, and bound proofs).
**Files**: `L4YAML/Indexed/Range.lean` (+ops), `L4YAML/Indexed/TokenStream.lean`
(+ops), new `L4YAML/Indexed/CharStream.lean`.
**Constraint observed**: type-level only — no scanning algorithm,
no character-class wiring. Nothing in `L4YAML/Scanner/` was
touched. **Sorry budget: 0 → 0**; full `lake build` passes 385
targets (up from 383 at Phase 2 close).

</details>

<details><summary>Step 2 — New scanner, character/whitespace layer <em>(landed)</em>.</summary>

**Step 2 — New scanner, character/whitespace layer** *(landed)*.
Built the lowest-level recognisers over `IxCursor input` in the
staging file `L4YAML/Scanner/IndexedScanner.lean` (namespace
`L4YAML.Scanner.Indexed`):

- **Layer A — character-class peeks**: `peekIsLineBreak`,
  `peekIsWhiteSpace`, `peekIsBlank`, `peekIsIndentChar` —
  uniform shape `match c.peek? with | some ch => isXBool ch | none => false`.
- **Layer B — whitespace runs**: `skipSpaces` (returns post-run
  cursor + count for indentation tracking) and `skipWhitespace`
  (consumes `s-white*` = spaces + tabs). Both use a fuel-driven
  recursive loop with `input.utf8ByteSize` as the safe upper bound.
- **Layer C — line break**: `consumeLineBreak` handles LF, CR-without-LF,
  and CRLF (the last collapsed to a single line bump, matching
  legacy `ScannerState.consumeNewline`). Uses `if/else` on `Char`
  equality rather than literal pattern matching to keep proof
  obligations decidable.

Bidirectional spec proofs landed in
`L4YAML/Proofs/Scanner/IndexedWhitespace.lean`:
- `peekIs*_iff` (4 lemmas): `peekIsX c = true ↔ ∃ ch, c.peek? = some ch ∧ isXProp ch` —
  the spec-runtime bridge for each predicate.
- `peekIs*_atEnd` (4): predicates evaluate to `false` at end-of-input.
- `peekIsIndentChar_implies_hasMore`, `peekIsWhiteSpace_implies_hasMore`:
  a successful peek implies `c.pos.offset < input.utf8ByteSize`.
- `skipSpaces_offset_monotonic`, `skipWhitespace_offset_monotonic` (+
  loop variants): byte offset only grows.
- `consumeLineBreak_{LF, CR_no_LF, CRLF_{offset,line,col}, atEnd,
  other_char, no_op, offset_monotonic}`: explicit characterisation
  of each `b-break` form plus monotonicity.

Plus two foundational lemmas added to `L4YAML/Indexed/CharStream.lean`
(promised in the Step 1 doc):
- `IxCursor.advance_offset_lt_of_hasMore` — strict offset
  progress when not at EOF; proved via `String.Pos.Raw.byteIdx_lt_byteIdx_next`
  + the `Nat.min` clamp.
- `IxCursor.advance_offset_monotonic` — the (non-strict) monotonicity
  used by every skip-loop monotonicity proof.

**Constraint observed**: `L4YAML.lean` does **not** import the new
staging files — confirmed by `grep -nE
"Scanner.IndexedScanner|Proofs.Scanner.IndexedWhitespace"`.
**Scope shift recorded**: termination correctness (skip-loops end
at non-whitespace or EOF) was *within* Step 2's stated cluster but
was *deferred to Step 3* — see Reflection 35 and the deferred-from
note in the Step 3 description below. The deferral was a scope
call, not an infeasibility: the lemma is provable in Step 2 by
fuel induction with `advance_offset_lt_of_hasMore`, and Step 3 has
been enlarged in the blueprint to absorb the obligation.
**Sorry budget: 0 → 0** in the staging files. Full `lake build`
passes (385 jobs total; lake-mode auto-discovers and builds the
staging files even though `L4YAML.lean` does not import them).

</details>

<details><summary>Step 3 — New scanner, indentation/line-break layer <em>(landed)</em>.</summary>

**Step 3 — New scanner, indentation/line-break layer** *(landed)*.
Extended the staging scanner (`L4YAML/Scanner/IndexedScanner.lean`)
with the comment-text and composite line-comment dispatch
recognisers, plus a new proof file
`L4YAML/Proofs/Scanner/IndexedIndent.lean` for the Step 3
bidirectional lemmas.

Productions added to `IndexedScanner.lean`:
- `skipCommentTextLoop` / `skipCommentText` — `[75] c-nb-comment-text`,
  the body of a `'#'`-introduced comment, consumed until line
  break or end-of-input. The leading `'#'` is consumed by the
  caller (Layer D).
- `skipToContentLoop` / `skipToContent` — `[79] s-l-comments`, the
  composite consumer of `s-white*`, optional `'#'`-comment, line
  break, then recurse. Body written without intermediate
  `let`-bindings so `split`/`cases` decompose cleanly (Reflection 37).

Deferred-from-Step-2 obligations *closed* in
`IndexedWhitespace.lean` before any Step 3 production was added:
- `skipSpacesLoop_terminates` / `skipSpaces_terminates`:
  `peekIsIndentChar (skipSpaces c).1 = false` — at fuel ≥
  `utf8ByteSize - offset`, the loop exits at a non-space or EOF.
- `skipWhitespaceLoop_terminates` / `skipWhitespace_terminates`:
  symmetric claim for `s-white*`.
- `advance_indent_col_succ`: advancing past an indent-char bumps
  `col` by 1 and leaves `line` unchanged.
- `skipSpacesLoop_col_eq_count` / `skipSpaces_col_eq_count`:
  `(skipSpaces c).1.pos.col = c.pos.col + (skipSpaces c).2 ∧
  (skipSpaces c).1.pos.line = c.pos.line` — the count returned by
  `skipSpaces` *is* the column delta. This is the form the
  indent-stack invariant consumes; the byte-offset analog would
  need the utf8Size apparatus, but the indent-stack only cares
  about column (Reflection 36).

Bidirectional spec lemmas for the four named productions:
- **`s-indent(n)`**: via `skipSpaces_col_eq_count` above.
- **`b-break`** / **`b-non-content`**: case lemmas
  `consumeLineBreak_{LF, CR_no_LF, CRLF_{offset,line,col},
  atEnd, other_char, no_op, offset_monotonic}` from Step 2 carry
  over unchanged. (The two productions have the same right-hand
  side; `b-non-content` is the label used in non-content
  positions such as inside `c-l-folded` headers.)
- **`s-l-comments`**: cursor-local characterisation —
  `skipCommentText_terminates` (settles at LF/EOF),
  `skipCommentText_offset_monotonic`,
  `skipToContentLoop_offset_monotonic`,
  `skipToContent_atEnd` (no-op at EOF),
  `skipToContent_at_content` (no-op at a non-`s-l-comments`
  character — the completeness direction of "scanner consumes
  nothing when there is nothing to consume").

**Constraint observed**: `L4YAML.lean` does **not** import the
new staging files — confirmed by
`grep -nE "Scanner.IndexedScanner|IndexedWhitespace|IndexedIndent"
L4YAML.lean` returning empty.
**Source refactor recorded**: `skipSpacesLoop`'s body was
rewritten from `let (c', n) := ...; (c', n+1)` to
`let r := ...; (r.1, r.2 + 1)` to make Prod-projection
reduction definitional — Reflection 37 generalises this as the
"avoid opaque let-bindings for proof-decomposed structures"
rule (a sibling of Reflection 33 on Char-literal patterns).
**Sorry budget: 0 → 0** in the staging files. Full `lake build`
passes 385 targets.
**Second-order deferral recorded** (honestly, not as
optimisation): the *global progress* claim for
`skipToContent` — "after finitely many iterations the cursor
settles at EOF or a non-`s-l-comments` character" — is a
strict-fuel termination result, *not* a bidirectional spec
lemma. It is deferred to Step 4 where the dispatch-loop's fuel
measure is the natural carrier. See Reflection 38.

</details>

<details><summary>Step 4a — New scanner, single-line scalar lexing + `skipToContent` progress closure <em>(landed)</em>.</summary>

**Step 4a — New scanner, single-line scalar lexing +
`skipToContent` progress closure** *(landed)*.

Step 4 was sized for two sessions per the blueprint
authorisation ("May span two sessions if the block-scalar
fold/chomp interaction proves recalcitrant"). Step 4a closed the
deferred progress obligation and landed the single-line scalar
recognisers; Step 4b *(also landed)* added block scalars and
multi-line continuation. The split was explicit because progress
+ quoted single-line is one coherent cluster (the scalar
recognisers that *call* `skipToContent` between scalars), while
block + fold is a separate state-machine cluster with its own
design discussion (chomping `[160]`, indent indicator `[163]`,
fold state `[170]`–`[181]`).

Deferred-from-Step-3 obligations *closed* in Step 4a (before any
Step 4 production code was added):
- `consumeLineBreak_strict` (in `IndexedWhitespace.lean`): when
  `c.peek? = some ch ∧ isLineBreakBool ch = true`, the offset
  strictly advances. Proof: case-split LF / CR-no-LF / CRLF on
  top of the existing `consumeLineBreak_{LF,CR_no_LF,CRLF_offset}`
  case lemmas plus `IxCursor.advance_offset_lt_of_hasMore`.
- `skipToContentLoop_progress` (in `IndexedIndent.lean`): given
  `fuel > utf8ByteSize - c.pos.offset`, the loop result is either
  `peek? = none` or `peek? = some ch` with `isWhiteSpaceBool ch =
  false ∧ isLineBreakBool ch = false ∧ ch ≠ '#'`. Proof: fuel
  induction; each non-settling iteration uses
  `consumeLineBreak_strict` (line-break branch) or `c.advance.pos.offset > c.pos.offset`
  followed by `consumeLineBreak` (after the `'#'`-comment + body).
- `skipToContent_progress` (entry-point form): the loop's
  `input.utf8ByteSize + 1` fuel exceeds
  `utf8ByteSize - c.pos.offset` for any cursor (since
  `c.posBound : c.pos.offset ≤ utf8ByteSize`).

Layer E additions to `IndexedScanner.lean` (suffixed `Ix` to
avoid shadowing the legacy short names — Reflection 39):
- **E1 — escapes**: `simpleEscapeChar` (18 single-char escapes),
  `hexDigitValue` / `hexStringValue`, `collectHexDigitsLoopIx`,
  `parseHexEscapeIx`, `processEscapeIx`. The split between
  `simpleEscapeChar` and the hex dispatch keeps the
  offset-monotonicity proof to three top-level cases.
- **E2 — double-quoted**: `collectDoubleQuotedLoopIx`,
  `scanDoubleQuotedIx`. Handles `"`, `\\` (via
  `processEscapeIx`), and content characters. In Step 4a the
  line-break path bailed as `none`; Step 4b replaced that with a
  fold-and-recurse path via `foldQuotedNewlinesIx` (Layer F1).
- **E3 — single-quoted**: `collectSingleQuotedLoopIx`,
  `scanSingleQuotedIx`. Handles the doubled-quote escape `''`.
  Step 4b added multi-line continuation through the same fold
  helper.
- **E4 — plain**: `colonTerminatesPlain` (helper for the `:`
  terminator rule), `collectPlainScalarLoopIx`, `scanPlainScalarIx`,
  `trimTrailingWSIx`. Termination conditions: EOF, `' #'`, `:` +
  blank / EOF / flow indicator, flow indicator (in flow context),
  document boundary (block). Step 4a was single-line; Step 4b
  added a `contentIndent` parameter and threaded line-break
  continuation through `foldQuotedNewlinesIx` (flow) or
  `handleBlockLineBreakIx` (block).

Step 4a bidirectional proofs in
`L4YAML/Proofs/Scanner/IndexedScalar.lean`:
- `collectHexDigitsLoopIx_offset_monotonic`,
  `parseHexEscapeIx_offset_monotonic`,
  `processEscapeIx_offset_monotonic`,
  `processEscapeIx_offset_lt` (strict — the escape indicator
  itself was consumed).
- `collectDoubleQuotedLoopIx_offset_monotonic`,
  `scanDoubleQuotedIx_offset_lt`.
- `collectSingleQuotedLoopIx_offset_monotonic`,
  `scanSingleQuotedIx_offset_lt`.
- `collectPlainScalarLoopIx_offset_monotonic`,
  `scanPlainScalarIx_offset_monotonic` (plain is total — no
  success guard).

**Constraint observed**: `L4YAML.lean` does **not** import the
new staging files — confirmed by `grep -nE
"Scanner.IndexedScanner|IndexedWhitespace|IndexedIndent|IndexedScalar"
L4YAML.lean` returning empty.
**Source refactor recorded**: `parseHexEscapeIx`'s original
`let (hex, c') := ...; let val := ...; if ...` body was
refactored to use `hexStringValue` and projection access — the
let-bindings obstructed `split` in proofs (Reflection 40, a
sharpening of Reflection 37).
**Sorry budget: 0 → 0** in the staging files. Full `lake build`
passes 385 targets (the staging files are auto-discovered).
**Deferred from Step 4a, closed in Step 4b**: (a) multi-line
quoted scalar continuation, (b) multi-line plain scalar including
the block-line-break handler, (c) block scalars — literal [170]
and folded [174] — with `FoldState` and chomping [160].
**Carried forward into Step 5**: (d) hex-escape value-correctness
proofs (that `hexStringValue` of a hex-digit string equals the
decoded `Nat`), and (e) bidirectional content-correctness proofs
(that the resolved scalar content matches the spec's substring
extraction).

</details>

<details><summary>Step 4b — New scanner, multi-line + block scalars <em>(landed)</em>.</summary>

**Step 4b — New scanner, multi-line + block scalars**
*(landed)*.

Three coupled work items, all landed:

1. **Multi-line quoted scalars (Layer F1)** — `s-double-multi-line(n)`
   [116] and `s-single-multi-line(n)` [125]. Continuation across
   an implicit line break: trim trailing whitespace on the current
   line, consume the line break + leading whitespace on the
   next, and fold (newline → space) per `b-l-folded` [73] /
   `s-flow-folded` [74]. Double-quoted additionally handles the
   `\\`-line-break escape (consume newline + skip whitespace,
   producing nothing in the resolved content). The fold logic
   lives in `foldQuotedNewlinesIx`, sharing `skipBlankLinesLoopIx`
   for the blank-line counter.

2. **Multi-line plain scalars (Layer F2)** — `ns-plain-multi-line(n,c)`
   [135] plus the auxiliary `s-ns-plain-next-line(n,c)` [134].
   The continuation indent check (`cAfterSp.pos.col ≥
   contentIndent`) and document-boundary termination
   (`---` / `...` at column 0) land in `handleBlockLineBreakIx`.
   `atDocumentBoundaryIx` / `atDocumentStartIx` /
   `atDocumentEndIx` mirror `Scanner/Document.lean`. `scanPlainScalarIx`
   grew a `contentIndent : Nat` parameter and the dispatcher
   (Step 5) is responsible for passing the correct floor:
   `s.col` in flow context, `max 0 (currentIndent + 1)` in block.

3. **Block scalars (Layer F3)** — literal `c-l+literal(n)` [170]
   and folded `c-l+folded(n)` [174]. The four-state fold machine
   (`FoldState`: `start` / `content` / `empty` / `more`) lives in
   `foldBlockContent` as a pure `String → String`. Chomping [160]
   (`strip` / `clip` / `keep`) is `applyChomp`. The pipeline:
   `parseBlockHeaderLoopIx` (chomp + indent indicator) →
   `blockHeaderToBodyIx` (whitespace + optional comment + line
   break) → `autoDetectBlockScalarIndentLoopIx` (when no explicit
   indent) → `collectBlockScalarLoopIx` (line-by-line, with
   `consumeExactSpacesIx` and `collectLineContentLoopIx`). The
   `parentIndent : Nat` parameter on `scanBlockScalarIx`
   substitutes for the indent-stack read that the dispatcher will
   wire in Step 5 — Step 4b keeps the indent-stack out of the
   scanner core; the *caller* supplies the parent indent.

Step 4b bidirectional proofs in `IndexedScalar.lean`:
- **F1**: `skipBlankLinesLoopIx_offset_monotonic`,
  `foldQuotedNewlinesIx_offset_monotonic`.
  The existing `collectDoubleQuotedLoopIx_offset_monotonic` /
  `collectSingleQuotedLoopIx_offset_monotonic` were updated to
  handle the new fold-and-recurse branch via
  `foldQuotedNewlinesIx_offset_monotonic`.
- **F2**: `handleBlockLineBreakIx_offset_monotonic` (success
  branch only — `none` is a no-progress case). The plain-scalar
  monotonicity was updated for the new `contentIndent` parameter
  and the flow / block fold sub-branches.
- **F3**: `consumeExactSpacesIx_offset_monotonic`,
  `collectLineContentLoopIx_offset_monotonic`,
  `parseBlockHeaderLoopIx_offset_monotonic`,
  `collectBlockScalarLoopIx_offset_monotonic`,
  `blockHeaderToBodyIx_offset_monotonic`,
  `scanBlockScalarIx_offset_monotonic`.

**Source refactor recorded**: Per Reflection 40, every helper
with a multi-`let` destructure that proofs would need to
`split` past was rewritten in projection form
(`(skipBlankLinesLoopIx ...).1`, `(consumeExactSpacesIx ...).2`,
…). `foldQuotedNewlinesIx`, `handleBlockLineBreakIx`,
`collectBlockScalarLoopIx`, and `scanBlockScalarIx`'s body were
all written this way from the outset.
**Source factor recorded**: `scanBlockScalarIx`'s post-header
cursor was extracted into `blockHeaderToBodyIx : IxCursor →
IxCursor` (Reflection 41) so the dispatcher's monotonicity proof
need not rebuild the five-stage chain inline.
**Sorry budget**: 0 → 0 in the staging files. Full `lake build`
passes 385 targets; the staging files remain unimported from
`L4YAML.lean` (Guardrail 1).

**Carried into Step 5**:
- Hex-escape value correctness: `hexStringValue` matches the
  intended `Nat` value of a hex-digit string.
- Block-scalar content correctness: `foldBlockContent` matches
  the spec's folded-content extraction; `applyChomp` matches
  `[160] c-chomping-indicator`'s semantics.
- Quoted multi-line content correctness: that the concatenated
  `content` matches `[111]`–`[116]` (double) and `[122]`–`[125]`
  (single) under the fold rules.
- Plain multi-line content correctness: that the threaded
  `content ++ folded` matches `[131]`–`[135]`.
- `autoDetectBlockScalarIndentLoopIx` correctness (terminates
  at the first non-empty line; respects `minContentIndent`).
- The dispatcher (Step 5) wires `scanBlockScalarIx`'s
  `parentIndent` parameter to the indent-stack and threads
  `inFlow` / `contentIndent` through `scanPlainScalarIx`.

</details>

<details><summary>Step 5a — Top-level dispatcher + scanner state <em>(landed)</em>.</summary>

**Step 5a — Top-level dispatcher + scanner state** *(landed)*.

Step 5 was sized against the legacy scanner code (~3,100 LOC) and
realistically does not fit in one session: it needs (i) an indexed
`ScannerStateIx`, (ii) the full dispatch family (`scanNextTokenIx_*`,
`scanLoopIx`, `scanIx`), (iii) a `present : TokenStream input →
String`, (iv) the roundtrip corpus theorem, plus (v) the
content-correctness obligations carried from Step 4b. Step 5a closes
the first two clusters; Step 5b/5c close the remainder.

Files added in Step 5a:
- `L4YAML/Scanner/IndexedState.lean` — `IndentEntryIx`,
  `SimpleKeyStateIx input` (indexed on `input`, carries an
  `IxCursor` so the saved-key position has its bound proof
  already discharged), and `ScannerStateIx input`. State-level
  accessors (`peek?`, `peekAt?`, `peekBack?`, `hasMore`,
  `currentPos`, `inFlow`, `isInFlowSequence`, `currentIndent`),
  navigation (`advance`, `advanceN`, `skipSpacesS`,
  `skipWhitespaceS`, `skipToContentS`), and token emission
  (`emit`, `emitAt`, `emitAtSafe`, `emitAtCursor`,
  `overwriteAtCursor`). Indent-stack ops (`unwindIndentsLoopIx`,
  `unwindIndentsIx`, `pushSequenceIndentIx`,
  `pushMappingIndentIx`).
- `L4YAML/Scanner/IndexedDispatch.lean` — helper recogniser
  loops (`collectAnchorNameLoopIx`, `collectTagHandleLoopIx`,
  `collectTagSuffixLoopIx`, `collectVerbatimTagLoopIx`,
  `collectDirectiveNameLoopIx`, `collectVersionMajor/MinorLoopIx`,
  `skipDocEndWhitespaceIx`); simple-key save (`saveSimpleKeyIx`)
  and candidate predicates (`isBlockEntryCandidateIx`,
  `isKeyCandidateIx`, `isJsonNodeTokenIx`, `isValueCandidateIx`);
  block-indicator scans (`scanBlockEntryIx`, `scanKeyIx`,
  `scanValuePrepareIx`, `scanValueIx`); document-marker scans
  (`scanDocumentStartIx`, `scanDocumentEndIx`); directives
  (`scanYamlDirectiveIx`, `scanTagDirectiveIx`, `scanDirectiveIx`);
  node properties (`scanAnchorOrAliasIx`, `scanTagIx`); flow
  indicators (`scanFlowSequenceStart/EndIx`,
  `scanFlowMappingStart/EndIx`, `scanFlowEntryIx`); and the full
  dispatch family (`scanNextTokenIx_preprocess`,
  `scanNextTokenIx_dispatchStructural/FlowIndicators/BlockIndicators/Content`,
  `scanNextTokenIx_checkBlockFlowIndent`, `scanNextTokenIx`)
  plus `scanLoopIx` and the top-level entry point `scanIx`.

**The simple-key state is indexed.** `SimpleKeyStateIx input`
carries the saved position as an `IxCursor input`, not as a raw
`YamlPos`. This lets `scanValuePrepareIx` overwrite placeholder
tokens at the saved position using the cursor's `posBound` —
no separate bound-tracking apparatus, no defensive checks at
the resolve site. (Reflection 43.)

**`emitAtSafe` is a deliberate defensive emit.** The dispatch
functions need `emitAt startPos ... hOrder` where `hOrder :
startPos.offset ≤ s.cursor.pos.offset` is a *chain* of helper
monotonicity proofs (one for each `collect*Ix`, plus
`skipWhitespace_offset_monotonic`, plus the per-rule
`scanDoubleQuotedIx_offset_lt` etc. from Step 4a/4b). The
chain is mechanical but lengthy. Rather than inline it (or
worse, leave the dispatcher with five `(by sorry)`s), Step 5a
defines `emitAtSafe : ScannerStateIx → YamlPos → YamlToken →
ScannerStateIx`, which performs the bound check at runtime and
falls back to a zero-width token at the current cursor on
failure. The fallback branch is never taken in well-formed
scans; Step 5b discharges the static obligation by chaining
the helper-loop monotonicity lemmas and replaces `emitAtSafe`
with `emitAt`. (Reflection 44.)

Step 5a bidirectional/monotonicity proofs: **none added in this
step**. The dispatch family is offset-monotonic by construction
(each branch either emits + advances, calls an offset-monotonic
sub-recogniser, or returns unchanged on EOF). The formal
monotonicity proofs are deferred to Step 5b.

**Constraint observed**: `L4YAML.lean` does **not** import the
new staging files — confirmed by `grep -nE
"Scanner.IndexedState|Scanner.IndexedDispatch" L4YAML.lean`
returning empty.
**Sorry budget: 0 → 0** in the staging files. Full `lake build`
passes 385 targets (the staging files are auto-discovered).
**Scope split recorded**: Step 5 was authorised as "one session"
in the original plan; Step 4's two-session precedent (4a/4b)
makes the split honest rather than ad-hoc. The blueprint Step 5
description was *forward-looking*: it stated the end-of-Phase-3
deliverable, not a per-session work item. Step 5a is the
dispatcher-and-state slice; 5b is the monotonicity-and-content
slice; 5c is the present-plus-corpus slice. (Reflection 45.)

</details>

<details><summary>Step 5b sub-step plan (nine sub-steps; per R46).</summary>

**Step 5b sub-step plan** (Reflection 46). Step 5b's eight
carry-forward clusters do not fit one session. The original
"dispatcher offset-monotonicity chain + `emitAtSafe`→`emitAt`"
cluster splits naturally into helper-loop monotonicity (5b.1a)
and per-dispatcher monotonicity (5b.1b). The remaining seven
clusters become 5b.2–5b.8. Total: nine sub-steps.

- **5b.1a — Helper-loop monotonicity + `emitAtSafe`→`emitAt`**
  *(landed)*. See subsection below.
- **5b.1b — Per-dispatcher monotonicity**. Reading 5b.1b for
  implementation revealed ~12 missing state-helper preservation
  lemmas (`emit_cursor`, `pushMappingIndentIx_cursor`,
  `saveSimpleKeyIx_cursor`, `skipToContentS_offset_monotonic`,
  etc.) behind the "single-line chain" framing of the dispatcher
  lemmas. Per Reflection 46 (apply sub-step ordering
  recursively), 5b.1b is split into four sub-steps:
  - **5b.1b.i — Preservation infrastructure** *(landed)*. State-level
    cursor-preservation + offset-monotonicity lemmas in a new
    `Proofs/Scanner/IndexedDispatch.lean`. See subsection below.
  - **5b.1b.ii — Simple-shape dispatcher monotonicity** *(landed)*.
    Ten `scan*Ix_offset_monotonic` lemmas for `scanBlockEntryIx`,
    `scanKeyIx`, `scanValueIx`, `scanDocumentStartIx`,
    `scanDocumentEndIx`, and the five `scanFlow*Ix`. See subsection
    below. (Pattern A — always `.ok`: 4; Pattern B — state-returning:
    5; Pattern C — early-/late-throw: 1, with Reflection 48's
    `pure_bind` / `if_pos` peeling trick.)
  - **5b.1b.iii — Node-property + directive dispatcher monotonicity**
    *(landed)*. Five `scan*Ix_offset_monotonic` lemmas for
    `scanAnchorOrAliasIx`, `scanTagIx`, `scanYamlDirectiveIx`,
    `scanTagDirectiveIx`, `scanDirectiveIx`. Chains thread through
    the 5b.1a `collect*LoopIx_offset_monotonic` helpers and
    `skipWhitespace_offset_monotonic`. The directive helpers are
    stated relative to the explicit `cAfterWS` parameter (since the
    dispatcher overwrites the input state's cursor with `cAfterTW`
    anyway); `scanDirectiveIx` then chains through them via the
    leading `advance` + `collectDirectiveNameLoopIx` + `skipWhitespace`.
    See subsection below; the `let`-block destructuring obstacle is
    Reflection 49.
  - **5b.1b.iv-pre — Tokens-size growth leaf helpers** *(landed)*.
    6 simp lemmas counting emit/overwrite/etc.'s effect on
    `tokens.size`, plus 6 indent/key helpers + 12 dispatcher
    `_tokens_size_le` lemmas — one for each of the 5b.1b.ii /
    5b.1b.iii dispatchers (`scanBlockEntryIx`, `scanKeyIx`,
    `scanValueIx`, `scanFlowEntryIx`, four `scanFlow*Ix`,
    `scanDocumentStartIx`, `scanDocumentEndIx`, `scanAnchorOrAliasIx`,
    `scanTagIx`, `scanYamlDirectiveIx`, `scanTagDirectiveIx`,
    `scanDirectiveIx`). These are the chain ingredients the
    eventual top-level claims feed off. See R50.
  - **5b.1b.iv-cont — Top-level dispatcher monotonicity** *(landed)*.
    14 lemmas across 6 dispatcher pairs (`scanNextTokenIx_preprocess`,
    `_dispatchStructural`, `_dispatchFlowIndicators`,
    `_dispatchBlockIndicators`, `_dispatchContent`, and the
    per-iteration `scanNextTokenIx`) — each producing
    `_offset_monotonic` + `_tokens_size_le` — plus the fueled
    `scanLoopIx_tokens_size_le`. The last is the only non-chain:
    `scanLoopIx` returns a `TokenStream` rather than state, so its
    claim is `s.tokens.size ≤ ts.size`, proven by induction on fuel,
    chaining `scanNextTokenIx_tokens_size_le` plus the terminal
    `unwindIndentsIx_tokens_size_le` + `emit streamEnd` growth.
    The stronger *"every emitted token has
    `start.offset ≥` initial cursor's offset"* claim is deferred to
    Step 5b.2 (it would require strengthening every leaf lemma to
    carry per-token offset bounds, not just final-cursor monotonicity).
    See Reflection 51 for the two technical patterns the proofs
    needed (`by_cases hg + rw [if_pos/if_neg] + cases h : f s` for
    do-block early-return; `split at h` (not `cases h : ...`) for
    matches with dependent witness binders).
- **5b.2 — Tab-in-indentation hardening** for `scanBlockEntryIx`
  and `scanKeyIx` (§6.1 [187]) *(landed)*.
  `scanBlockEntryIx` now throws `tabInIndentation` in block context
  when `s.hasTabInPrecedingWhitespace` (an indexed analogue of the
  legacy backward-scan, added to `IndexedState.lean` as
  `ScannerStateIx.hasTabInPrecedingWhitespace`); `scanKeyIx` now
  throws when the cursor sits on `'\t'` immediately after consuming
  `?` in block context. Both monotonicity proofs (`_offset_monotonic`
  + `_tokens_size_le`) were re-derived; the proofs needed three new
  `inFlow`-preservation simp lemmas (`emit_inFlow`, `advance_inFlow`,
  `pushMappingIndentIx_inFlow`) so `simp only [if_pos hi, …]` could
  collapse the post-advance `!s.inFlow` guard against the *original*
  `s.inFlow` (Reflection 52).
- **5b.3 — `scanValueIx` validation chain** *(landed)*. Split the
  simplified `scanValueIx` into the legacy's four-stage chain
  (`scanValueClearKeyIx` / `scanValueValidateIx` /
  `scanValuePrepareIx` / `scanValueTabCheckIx`). Three new defs in
  `Scanner/IndexedDispatch.lean` (clear-key pure transform, validate
  + tab-check `Except ScanError Unit`); `scanValueIx` rewritten as a
  `do`-block chaining all four. Existing `scanValueIx_offset_monotonic`
  / `_tokens_size_le` re-proved with the legacy `simp only [bind,
  Except.bind] at h; split at h; cases h | ...` pattern (the indexed
  proofs previously used `subst h` directly, which no longer fits
  once two `Except`-throwing stages appear). Two new helper lemmas
  landed (`scanValueClearKeyIx_cursor` `@[simp]`,
  `scanValueClearKeyIx_tokens_size_le`); a small unrelated breakage
  carried over from the prior char-predicate refactor in
  `Proofs/Scanner/IndexedScalar.lean` (quoted-loop `split at h` shapes,
  `parseBlockHeaderLoopIx` nested-if cascade,
  `blockHeaderToBodyIx_offset_monotonic`'s `'#'` literal → match form)
  and `Proofs/Scanner/IndexedIndent.lean::skipToContent_at_content`
  (`(ch == '#') = false` → `isCommentBool ch = false`) were fixed in
  the same commit. See Reflection 53.
- **5b.4 — Hex-escape value-correctness** *(landed)*. Four lemmas
  in `Proofs/Scanner/IndexedScalar.lean` (Layer E1.4): `hexDigitValue_lt_16`
  (digit bound for `isHexDigitBool ch = true`), `hexStringValue_empty` /
  `hexStringValue_push` (`String.foldl` snoc law via
  `String.foldl_eq_foldl_toList` + `String.toList_push` +
  `List.foldl_append`), `hexStringValue_lt_pow`
  (`String.push_induction` chaining the digit bound and snoc law),
  and `parseHexEscapeIx_decoded` packaging the escape spec — on
  success, `ch = Char.ofNat (hexStringValue digits)` with
  `hexStringValue digits < 0x110000` already discharged. The proof
  shape for `hexDigitValue_lt_16` had to avoid `rcases` over the
  three-way disjunction: after `simp only [isHexDigitBool,
  Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
  UInt32.le_iff_toNat_le]`, the hypothesis is `(d ∨ u) ∨ l` (Lean's
  `||` left-associativity) where each branch carries `Nat.le`
  conjunctions; `rcases` then aggressively tries to destruct the
  `Nat.le` via `Nat.le.refl` and fails with `ch.val.toBitVec.toFin.1
  = 97`. Plain `cases h with | inl … | inr …` (two nested levels)
  routes around it. See Reflection 54.
- **5b.5 — `autoDetectBlockScalarIndentLoopIx` correctness** *(landed)*.
  Carried-forward Step 4b obligation discharged as two lemmas in
  `Proofs/Scanner/IndexedScalar.lean`'s new "Layer F.1 — Auto-detected
  block-scalar indent ≥ `minContentIndent`" section:
  `autoDetectBlockScalarIndentLoopIx_ge_min` (loop body) +
  `autoDetectBlockScalarIndentIx_ge_min` (entry-point wrapper). Both
  state `minContentIndent ≤ result`, which downstream block-scalar
  content-correctness proofs (Step 5b.6) need as the spec-mandated
  lower bound. The proof: induction on `fuel`; base case is the
  `if maxWSCol > minContentIndent then maxWSCol else minContentIndent`
  guard (`split <;> omega`); the recursive case requires *three*
  nested `split`s — the `let (probeAfterSp, _) := skipSpaces probe`
  prod destructure (1 case), then the `match probeAfterSp.peek?`
  arm (some/none), then the inner `if isLineBreakBool ch`
  (recurse/bound). The IH is universally quantified over `maxWSCol`
  (since the loop carries a running max-whitespace-column), so
  `apply ih` closes the recursive branch regardless of which
  `maxWSCol'` the body computed. See Reflection 55.
- **5b.6 — Block-scalar content correctness** *(landed)*.
  Carried-forward Step 4b obligation discharged as six lemmas in
  `Proofs/Scanner/IndexedScalar.lean`'s new "Layer F.2 — Block-scalar
  content correctness" section. `applyChomp` (chomp indicator
  `[160]`) gets four arms — `applyChomp_keep` (identity, `rfl`),
  `applyChomp_strip` (`= stripTrailingNewlines raw`, `rfl`),
  `applyChomp_clip_of_endsWith` / `applyChomp_clip_of_not_endsWith`
  (both `simp [applyChomp, h]`); `foldBlockContent` (fold machine
  `[170]`–`[181]`) gets two base-case lemmas — `foldBlockContentGo_nil`
  (`rfl`) + `foldBlockContent_empty` (`rfl`). All six are
  *definitional unfolds* — the value here is binding each Lean
  function branch to its spec rule so downstream Steps 5b.7
  (quoted multi-line) and 5b.8 (plain multi-line) can cite by
  name when reasoning about the block-scalar pipeline. See
  Reflection 56.
- **5b.7 — Quoted multi-line content correctness** *(landed)*.
  Carried-forward Step 4b obligation discharged as nine
  spec-traceability lemmas in `Proofs/Scanner/IndexedScalar.lean`'s
  new "Layer F.3 — Quoted multi-line content correctness" section.
  `foldQuotedNewlinesIx` (§6.5 [73] / [74]) gets two branch-mapping
  lemmas — `foldQuotedNewlinesIx_of_blank_lines` (`emptyCount > 0`
  → `String.ofList (List.replicate emptyCount '\n')`, `b-l-trimmed`
  [71]) and `foldQuotedNewlinesIx_of_single_break`
  (`emptyCount = 0` → `String.singleton spaceChar`, `b-as-space`
  [70]). `collectDoubleQuotedLoopIx` (§7.3.1 [111]–[116]) gets
  three — `_zero` (`rfl`), `_closing` (closing `"` returns
  `(content, c.advance)`), `_linebreak` (line-break fold composes
  `trimTrailingWSIx content ++ folded`).
  `collectSingleQuotedLoopIx` (§7.3.2 [122]–[125]) gets four —
  `_zero`, `_doubled` (`''` doubled-quote escape `[123]` pushes one
  `'`), `_closing_some` / `_closing_none` (single `'` followed by
  non-`'` or EOF closes), `_linebreak` (same fold composition).
  Proof shape: `rfl` for `_zero`s, `unfold + rw + simp` for the
  non-recursive branches, **`conv => lhs; unfold …` for the three
  branches whose RHS is another `collectXxxQuotedLoopIx` call**
  (otherwise `unfold` rewrites both sides and `simp` expands the
  RHS into the full match-cascade). See Reflection 57.
- **5b.8 — Plain multi-line content correctness** *(landed)*.
  Carried-forward Step 4b obligation discharged as 12
  spec-traceability lemmas in `Proofs/Scanner/IndexedScalar.lean`'s
  new "Layer F.4 — Plain multi-line content correctness" section.
  `collectPlainScalarLoopIx` (§7.3.3 [131]–[135]) gets a named
  branch lemma for each of its 11 outcomes — `_zero` (fuel = 0),
  `_eof` (`peek? = none`), `_comment` (`#` after spaces),
  `_colon_terminate` / `_colon_continue` (`:` terminates per
  `colonTerminatesPlain` or continues with `content ++ spaces ++ ":"`,
  matching the in-flow / block split in `[132]`),
  `_flow_indicator` (flow context `,`/`]`/`}`),
  `_linebreak_flow` (flow context reuses `foldQuotedNewlinesIx`
  Layer F1 — §6.5 [73] / [74] — composing `content ++ folded`),
  `_linebreak_block_none` / `_linebreak_block_some` (block context
  consults `handleBlockLineBreakIx`: under-indent or document
  boundary terminates, else fold + `content ++ folded` per
  `ns-plain-multi-line(n,c)` [134]), `_whitespace` (accumulates
  into the `spaces` parameter), `_not_plain_safe` (terminates on
  flow-indicator/control character in plain-unsafe position), and
  `_content` (the plain-safe character push,
  `content ++ spaces ++ ch`). Proof shape mirrors Step 5b.7:
  `rfl` for `_zero`, `unfold + rw` for `_eof`,
  `unfold + rw + simp` for the five non-recursive terminators, and
  **`conv => lhs; unfold …` for the five RHS-recursive branches**
  (`_colon_continue`, `_linebreak_flow`, `_linebreak_block_some`,
  `_whitespace`, `_content` — direct reuse of Reflection 57; no
  new failure modes encountered).

</details>

<details><summary>Step 5b.1a — Helper-loop monotonicity + `emitAtSafe`→`emitAt` <em>(landed)</em>.</summary>

**Step 5b.1a — Helper-loop monotonicity + `emitAtSafe`→`emitAt`**
*(landed)*.

Eight monotonicity lemmas landed in
`L4YAML/Scanner/IndexedDispatch.lean` (between the helper-loop
defs and the `ScannerStateIx` namespace):

- `collectAnchorNameLoopIx_offset_monotonic`,
- `collectTagHandleLoopIx_offset_monotonic`,
- `collectTagSuffixLoopIx_offset_monotonic`,
- `collectVerbatimTagLoopIx_offset_monotonic`,
- `collectDirectiveNameLoopIx_offset_monotonic`,
- `collectVersionMajorLoopIx_offset_monotonic`,
- `collectVersionMinorLoopIx_offset_monotonic`,
- `skipDocEndWhitespaceIx_offset_monotonic`.

Each is six lines: `induction fuel` (base = `Nat.le_refl _`;
succ unfolds the loop, `split`s on `c.peek?` and the inner
predicate, and chains `advance_offset_monotonic` with the IH).
The chain matches the pattern used in
`Proofs/Scanner/IndexedWhitespace.lean::skipSpacesLoop_offset_monotonic`.

`IndexedDispatch.lean` now imports
`L4YAML.Proofs.Scanner.IndexedWhitespace` (for
`skipWhitespace_offset_monotonic`) and
`L4YAML.Proofs.Scanner.IndexedScalar` (for the per-rule
recogniser monotonicity lemmas
`scanDoubleQuotedIx_offset_lt`, `scanSingleQuotedIx_offset_lt`,
`scanPlainScalarIx_offset_monotonic`,
`scanBlockScalarIx_offset_monotonic`). The 10 `emitAtSafe` use
sites were replaced with `emitAt … hBound`, where `hBound`
discharges `startPos.offset ≤ sAfter.cursor.pos.offset` by a
let-bound `by` block (`show s.cursor.pos.offset ≤ <final>` to
align the goal with the lemma shape, then `Nat.le_trans` chains).
`scanYamlDirectiveIx` and `scanTagDirectiveIx` gained an
`hStart : startPos.offset ≤ cAfterWS.pos.offset` parameter;
`scanDirectiveIx` discharges it via the
`collectDirectiveNameLoopIx` + `skipWhitespace` chain.

`emitAtSafe` itself is deleted (it was the last carry-forward
out of Step 5a's compromise). `ScannerStateIx`'s emit API is
now `emit` (zero-width at cursor), `emitAt` (saved start, cursor
end, with explicit bound proof), `emitAtCursor` (zero-width at
saved cursor — uses cursor's own `posBound`), `overwriteAtCursor`
(for placeholder slots).

Sorry budget: **0 → 0** in the staging files. `lake build` passes
all 385 targets. `L4YAML.lean` does not import any
`Scanner.Indexed*` or `Proofs.Scanner.Indexed*` file — confirmed.

**Carried forward into Step 5b.1b**: per-dispatcher
monotonicity lemmas. First reading turned up the "single-line
chain" framing as too optimistic — see Reflection 47 and the
recursive split into 5b.1b.i–iv. The infrastructure half lands
in 5b.1b.i (below); the three dispatcher halves (5b.1b.ii,
5b.1b.iii, 5b.1b.iv) follow.

**Carried forward into Steps 5b.2–5b.8**: the remaining seven
clusters (tab-in-indent hardening, `scanValueIx` validation
chain, hex-escape value, `autoDetectBlockScalarIndentLoopIx`,
block-scalar fold/chomp, quoted multi-line, plain multi-line).

</details>

<details><summary>Step 5b.1b.i — Preservation infrastructure <em>(landed)</em>.</summary>

**Step 5b.1b.i — Preservation infrastructure** *(landed)*.

A new staging proof file `L4YAML/Proofs/Scanner/IndexedDispatch.lean`
(~200 LOC) lands the state-level lemmas the dispatcher
monotonicity chains will need.

One cursor-level lemma — `IxCursor.advanceN_offset_monotonic`
— was missing from `Indexed/CharStream.lean`'s primitive corpus
(the prior whitespace / indent proofs needed only single-step
`advance` and the various loop fuel-induction patterns). It is
the natural induction on `n` chaining `advance_offset_monotonic`.

`ScannerStateIx` cursor-preservation lemmas (12 total, each
`rfl` or a small `unfold + split`):

- Emit-family: `emit_cursor`, `emitAt_cursor`,
  `emitAtCursor_cursor`, `overwriteAtCursor_cursor`. All `rfl`
  (token push is a structure update on `tokens`, leaving
  `cursor` unspecified, which structurally preserves it).
- Navigation: `advance_cursor`, `advanceN_cursor` (both `rfl`).
- Navigation monotonicity: `advance_offset_monotonic`,
  `advanceN_offset_monotonic` (one-line lifts via the
  `IxCursor` lemmas).
- Indent-stack: `pushSequenceIndentIx_cursor`,
  `pushMappingIndentIx_cursor`, `unwindIndentsLoopIx_cursor`
  (induction on fuel), `unwindIndentsIx_cursor` (direct
  application). All `split <;> rfl` after `unfold` — emits push
  tokens but leave the cursor untouched.
- Simple-key plumbing: `saveSimpleKeyIx_cursor` (three branches,
  all `rfl`), `scanValuePrepareIx_cursor` (five branches; four
  `rfl`, one delegates to `pushMappingIndentIx_cursor`).

`ScannerStateIx` state-level skip lemmas (6 total):

- `skipSpacesS_cursor` / `skipSpacesS_offset_monotonic`,
- `skipWhitespaceS_cursor` / `skipWhitespaceS_offset_monotonic`,
- `skipToContentS_cursor` / `skipToContentS_offset_monotonic`.

Each `*_cursor` is `rfl`; each `*_offset_monotonic` is a one-line
`rw […_cursor]; exact …` lift through the matching cursor-level
lemma already in `IndexedWhitespace.lean` or `IndexedIndent.lean`.

What did **not** need to land: lemmas about `consumeLineBreak`,
`skipCommentText`, `skipToContent` at the cursor level — those
already exist in `Proofs/Scanner/IndexedWhitespace.lean`
(`consumeLineBreak_offset_monotonic`) and
`Proofs/Scanner/IndexedIndent.lean` (`skipCommentText_*`,
`skipToContent_*`). The first-pass plan for 5b.1b.i listed
these as missing; a grep before coding showed otherwise. See
Reflection 47 for the lesson.

Sorry budget: **0 → 0** in the staging files. `lake build` passes
all 385 targets. `L4YAML.lean` does not import any
`Scanner.Indexed*` or `Proofs.Scanner.Indexed*` file — confirmed.

**Carried forward into Step 5b.1b.ii**: per-dispatcher
monotonicity for the 10 simple-shape dispatchers. Pattern: for
each `scanXIx s = .ok s'`, prove `s.cursor.pos.offset ≤
s'.cursor.pos.offset` by `unfold` + `simp only` with the
preservation `@[simp]` lemmas above, then close with
`advance_offset_monotonic` (or `Nat.le_refl _` for the trivial
cases where no `advance` happens before the result is assembled
— `scanFlowEntryIx` etc.).

</details>

<details><summary>Step 5b.1b.ii — Simple-shape dispatcher monotonicity <em>(landed)</em>.</summary>

**Step 5b.1b.ii — Simple-shape dispatcher monotonicity** *(landed)*.

Ten per-dispatcher offset-monotonicity lemmas added to
`L4YAML/Proofs/Scanner/IndexedDispatch.lean` (after the
preservation infrastructure from 5b.1b.i), grouped by return shape:

- **Pattern A** (always `.ok`, `h : scanXIx s = .ok s'` hypothesis):
  `scanBlockEntryIx_offset_monotonic`, `scanKeyIx_offset_monotonic`,
  `scanValueIx_offset_monotonic`, `scanFlowEntryIx_offset_monotonic`.
  Each: `unfold` + `simp only [Except.ok.injEq] at h; subst h`,
  then `simp only [advance_cursor, emit_cursor, …_cursor]` chases
  the preservation lemmas, and `IxCursor.advance_offset_monotonic`
  closes. `scanBlockEntryIx` / `scanKeyIx` need a `split` on
  `!s.inFlow` (the indent-push branch); the others have no
  branching.
- **Pattern B** (returns `ScannerStateIx` directly, no hypothesis):
  `scanDocumentStartIx_offset_monotonic`,
  `scanFlowSequenceStartIx_offset_monotonic`,
  `scanFlowSequenceEndIx_offset_monotonic`,
  `scanFlowMappingStartIx_offset_monotonic`,
  `scanFlowMappingEndIx_offset_monotonic`. Each is three lines:
  `unfold`, `simp only [...]`, `exact IxCursor.advance_offset_monotonic _`
  (or `advanceN_offset_monotonic _ _` for `scanDocumentStartIx`).
- **Pattern C** (`Except` with early- and late-`throw` branches):
  `scanDocumentEndIx_offset_monotonic`. Uses `by_cases` on the
  `directivesPresent ∧ ¬documentEverStarted` guard, `rw [if_pos/if_neg]`
  to peel it, `simp only [pure_bind] at h` to flatten the outer
  `pure ()`-bind, then `split at h` on the trailing `probe.peek?`
  match (and inner `if isLineBreakBool ch`). The four non-throw
  arms all close by the same `advanceN_cursor` / `emit_cursor` /
  `unwindIndentsIx_cursor` chain; the two throw arms contradict
  `.ok s'` via `simp [Bind.bind, Except.bind] at h`. Written with
  `all_goals first | (...) | (...)` to keep the proof flat.

The `do throw e; rest` desugars to `(throw e).bind (fun _ => rest)`,
which `split` cannot directly destructure (the top-level shape is
a `bind`, not the `if` or `match` we wanted to dispatch on). The
fix is to first reduce `pure_bind` and rewrite the outer `if`
with `if_pos` / `if_neg` *before* `split`-ing the inner match —
see Reflection 48.

Sorry budget: **0 → 0** in the staging files. `lake build` passes
all 385 targets. `L4YAML.lean` does not import any
`Scanner.Indexed*` or `Proofs.Scanner.Indexed*` file — confirmed.

**Carried forward into Step 5b.1b.iii**: per-dispatcher
monotonicity for the five node-property + directive dispatchers
(`scanAnchorOrAliasIx`, `scanTagIx`, `scanYamlDirectiveIx`,
`scanTagDirectiveIx`, `scanDirectiveIx`). Same shape as 5b.1b.ii
but the chains thread through `collectAnchorNameLoopIx` /
`collectTagHandleLoopIx` / `collectDirectiveNameLoopIx` /
`skipWhitespace` (the 5b.1a helper-loop monotonicity lemmas).

</details>

<details><summary>Step 5b.1b.iii — Node-property + directive dispatcher monotonicity <em>(landed)</em>.</summary>

**Step 5b.1b.iii — Node-property + directive dispatcher
monotonicity** *(landed)*.

Five `scan*Ix_offset_monotonic` lemmas landed in
`L4YAML/Proofs/Scanner/IndexedDispatch.lean`, after the 5b.1b.ii
block:

- `scanAnchorOrAliasIx_offset_monotonic` — `if name.isEmpty then
  .error else .ok …`. The empty-name branch contradicts `.ok s'`;
  the non-empty branch chains
  `IxCursor.advance_offset_monotonic` →
  `collectAnchorNameLoopIx_offset_monotonic`.
- `scanTagIx_offset_monotonic` — `match s.advance.peek? with`
  three-arm dispatch (verbatim `<…>`, `!!suffix`, primary/secondary
  `!handle!suffix`). The verbatim arm has nested `if !foundClose`
  and `if uri.isEmpty` throws; both contradict `.ok s'`. Each arm
  closes by chaining two `advance_offset_monotonic`s with the
  relevant `collect*Loop_offset_monotonic`.
- `scanYamlDirectiveIx_offset_monotonic` — `do`-block with an
  early-throw guard on `seenYamlDirective` (same shape as
  `scanDocumentEndIx`, but the trailing match is the
  `!major.isEmpty && !minor.isEmpty` validation `if`).
- `scanTagDirectiveIx_offset_monotonic` — straight-line `do`-block
  (no throws on the success path). Closes by chaining
  `collectTagHandleLoopIx_offset_monotonic` → `skipWhitespace` →
  `collectTagSuffixLoopIx_offset_monotonic` → `skipWhitespace`.
- `scanDirectiveIx_offset_monotonic` — composes the previous two
  via the leading `s.advance` + `collectDirectiveNameLoopIx` +
  `skipWhitespace cAfterName`. The `name == "YAML"` and
  `name == "TAG"` arms apply
  `scanYamlDirectiveIx_offset_monotonic` /
  `scanTagDirectiveIx_offset_monotonic` directly; the reserved-
  directive `else` arm threads through the same head chain.

The directive helpers are stated relative to their explicit
`cAfterWS` parameter (`cAfterWS.pos.offset ≤ s'.cursor.pos.offset`)
rather than relative to `s.cursor`, since the dispatcher overwrites
the input state's cursor with `cAfterTW` unconditionally and never
uses `s.cursor` in its monotonic chain. This matches the call-site
hypothesis in `scanDirectiveIx`, which holds `cAfterWS :=
skipWhitespace cAfterName` and discharges
`startPos.offset ≤ cAfterWS.pos.offset` directly.

The new wrinkle versus 5b.1b.ii is *term-level `let`-blocks block
`split at h`*: the dispatcher bodies use chains of `let`/`have`
bindings before the outer `if`/`match`, so after `unfold … at h`
the conditional is buried under let-binders that `split` cannot
see through. Two fixes work:

1. **`simp only at h`** — zeta-reduces all lets so `split at h`
   reaches the outer conditional. Used in `scanTagIx`,
   `scanDirectiveIx`.
2. **`by_cases hc : <condition>` + `rw [if_pos hc] at h` /
   `rw [if_neg hc] at h`** — peels one `if` at a time. Required
   when the condition naming forces the order, used in
   `scanAnchorOrAliasIx`.

See Reflection 49.

Sorry budget: **0 → 0** in the staging files. `lake build` passes
all 385 targets. `L4YAML.lean` does not import any
`Scanner.Indexed*` or `Proofs.Scanner.Indexed*` file — confirmed.

**Carried forward into Step 5b.1b.iv**: top-level dispatcher
monotonicity for the five `scanNextTokenIx_*` sub-dispatchers
(`scanNextTokenIx_preprocess`, `scanNextTokenIx_dispatchStructural`,
`scanNextTokenIx_dispatchFlowIndicators`,
`scanNextTokenIx_dispatchBlockIndicators`,
`scanNextTokenIx_dispatchContent`,
`scanNextTokenIx_checkBlockFlowIndent`), `scanNextTokenIx`, and the
fueled top-level `scanLoopIx`. The last is the only non-chain: it
returns a `TokenStream`, not state, so its statement form is
*"every token emitted has `start.offset ≥` the initial cursor's
offset"* — proven by induction on fuel, using the per-step
`scanNextTokenIx_offset_monotonic`.

</details>

<details><summary>Step 5b.1b.iv-pre — Tokens-size growth leaf helpers <em>(landed)</em>.</summary>

**Step 5b.1b.iv-pre — Tokens-size growth leaf helpers** *(landed)*.

The chain ingredients for the eventual 5b.1b.iv-cont top-level
proofs landed: 6 simp lemmas counting `tokens.size` effects of
`emit` / `emitAt` / `emitAtCursor` / `overwriteAtCursor` /
`advance` / `advanceN`, then 6 indent/key helper
`_tokens_size_le` lemmas (`unwindIndentsLoopIx`,
`unwindIndentsIx`, `pushSequenceIndentIx`, `pushMappingIndentIx`,
`saveSimpleKeyIx`, `scanValuePrepareIx`), then 12 dispatcher
`_tokens_size_le` lemmas — one for each 5b.1b.ii / 5b.1b.iii
dispatcher (`scanBlockEntryIx`, `scanKeyIx`, `scanValueIx`,
`scanFlowEntryIx`, four `scanFlow*Ix` start/end,
`scanDocumentStartIx`, `scanDocumentEndIx`, `scanAnchorOrAliasIx`,
`scanTagIx`, `scanYamlDirectiveIx`, `scanTagDirectiveIx`,
`scanDirectiveIx`). The 2 directive helpers `scanYamlDirectiveIx`
/ `scanTagDirectiveIx` are stated relative to the explicit
`cAfterWS` cursor parameter (same shape as the 5b.1b.iii
cursor-form). `scanDirectiveIx_tokens_size_le` chains through them
without an inline `unfold scanYamlDirectiveIx at h` (that would
re-introduce the `seenYamlDirective` guard against `sAdv`, not
`s`); R49's chain-via-helper pattern carries over cleanly.

**Reflection 50 — *inner-let-`if` produces orthogonal sub-cases
that 2-arm `split at h` skeletons miss*.**
While attempting 5b.1b.iv's `scanNextTokenIx_preprocess_*` proof,
the standard 5b.1b.iii pattern (`unfold + simp only at h ;
split at h ; · simp at h ; · split at h ; · simp at h ; · …`)
broke on the inner `let s := if !s.inFlow && s.needIndentCheck
then …(unwind) else s` of the body. After `simp only at h`
zeta-reduces that let, the inner `if` survives as a *separate*
top-level conditional from the outer `if !hasMore`. A 2-arm
nested `split` only sees 2 cases at each level, but the inner
`isFalse`-of-outer arm now contains the inner `if`'s two
sub-cases (`isFalse.isTrue` / `isFalse.isFalse`), each of which
still holds the trailing-content `if errCond` plus the `match
s.peek?` — i.e. *four* surviving success paths, not one. The
proof skeleton aborts because the second `· split at h` lands in
`isFalse.isFalse` (no trailing splits) and `simp at h` makes no
progress.

Two fixes:
1. **`all_goals first | <succ path> | (split at h; <inner>)`** —
   factors the trailing-content `if` and `match peek?` peeling
   into a single tactic invoked from each of the 4 sub-cases.
2. **Case-exhaustive nested splits** — write out all four
   `isTrue / isFalse.isTrue / isFalse.isFalse.…` sub-cases by
   hand, each closing with `simp at h` (contradiction) or
   `simp only [Except.ok.injEq, Option.some.injEq,
   Prod.mk.injEq] at h ; obtain ⟨hsubst, _⟩ := h ; subst hsubst`
   followed by the leaf `_tokens_size_le` chain.

R50 pairs with R49 (term-level `let`-block obstacle) and R48
(do-block `let`-block obstacle): the family is "destructuring
tactics don't peel through `let`-zeta'd intermediate state, and
the *number* of surviving sub-cases after `split` depends on the
zeta'd structure, not just the original surface syntax". When a
sub-step plan mentions a "single-line chain" or "5-way uniform"
shape, *count the let-zeta'd `if`s* before estimating proof
length, not the surface-syntax `if`s.

Sorry budget: **0 → 0** in the staging files. `lake build`
passes all 385 targets. `L4YAML.lean` does not import any
`Scanner.Indexed*` or `Proofs.Scanner.Indexed*` file — confirmed.

**Carried forward into Step 5b.1b.iv-cont**: the seven top-level
chain lemmas. With the leaf `_tokens_size_le` helpers and R50's
two fix candidates in hand, the next session should fit in scope.

</details>

<details><summary>Step 5b.1b.iv-cont — Top-level dispatcher monotonicity <em>(landed)</em>.</summary>

**Step 5b.1b.iv-cont — Top-level dispatcher monotonicity** *(landed)*.

The seven top-level chains landed: six dispatcher pairs
(`_offset_monotonic` + `_tokens_size_le`) for
`scanNextTokenIx_preprocess`, `_dispatchStructural`,
`_dispatchFlowIndicators`, `_dispatchBlockIndicators`,
`_dispatchContent`, and the per-iteration `scanNextTokenIx`; plus
the fueled `scanLoopIx_tokens_size_le` (the only non-chain — it
returns a `TokenStream`, not state, so its claim is
`s.tokens.size ≤ ts.size`, proven by induction on fuel).

The proofs needed two new techniques beyond R50's two candidate
fixes:

1. **`by_cases hg + rw [if_pos / if_neg] at h + cases hF : f s with`**
   for do-block early-returns. R50's preferred approach (nested
   `split at h`) does not work cleanly on do-blocks with multiple
   `if c then return some v` early-returns, because the elaborator
   inserts `__do_jp` join-point chains that `simp [Bind.bind,
   Except.bind]` cannot fully collapse. Instead, peel each guard
   with `by_cases hg + rw [if_pos hg / if_neg hg] at h`, then for
   each production use `cases hF : <scanner> s with | error e => rw
   [hF] at h; simp [...] at h | ok v => rw [hF] at h; simp [...] at
   h; ...`. The `simp [Bind.bind, Except.bind, Pure.pure,
   Except.pure]` reduces `pure (some v) = .ok (some s')` to `v =
   s'`, which closes via `exact congrArg Except.ok h` or `cases h`.

2. **`split at h` (not `cases h : <expr>`) for dependent matches.**
   `scanNextTokenIx_dispatchContent` has three scalar-`Option`
   matches with dependent witness binders
   (`match hBS : scanBlockScalarIx ... with | some r => ... uses
   hBS to discharge hBound ...`). `cases h : <expr> with` introduces
   `h : <expr> = constructor`, but `rw [h] at body` fails with
   "motive is not type correct" because `body` depends on
   `hBS` (the original witness). The fix is to use `split at h`
   instead, which performs the case analysis directly on the match
   in `h` and introduces the witness in the proper scope via
   `rename_i r hBS`.

Reflection 51 captures both patterns together.

Sorry budget: **0 → 0** in the staging files. `lake build` passes
all 385 targets. `L4YAML.lean` does not import any
`Scanner.Indexed*` or `Proofs.Scanner.Indexed*` file — confirmed.

**Carried forward into Steps 5b.2–5b.8**: the seven Step-5b
clusters (tab-in-indent hardening, `scanValueIx` validation chain,
hex-escape value, `autoDetectBlockScalarIndentLoopIx`, block-scalar
fold/chomp, quoted multi-line, plain multi-line).

</details>

<details><summary>Step 5b.2 — Tab-in-indentation hardening <em>(landed)</em>.</summary>

**Step 5b.2 — Tab-in-indentation hardening** *(landed)*.

Both `scanBlockEntryIx` (the `-` block-entry indicator) and
`scanKeyIx` (the `?` explicit-key indicator) now carry the legacy's
§6.1 [187] `tabInIndentation` throw, mirroring
`L4YAML.Scanner.SimpleKey.scanBlockEntry` /
`L4YAML.Scanner.SimpleKey.scanKey` in `Scanner/SimpleKey.lean`.

**Source changes** (`L4YAML/Scanner/IndexedDispatch.lean`,
`L4YAML/Scanner/IndexedState.lean`):

- `IndexedState.lean` gained two new functions:
  - `hasTabInPrecedingWhitespaceLoop` (structurally recursive on
    fuel, scans backward through the contiguous whitespace run
    before the cursor; returns `true` iff at least one `\t`
    appears).
  - `hasTabInPrecedingWhitespace` (the entry point — calls the loop
    with `s.cursor.pos.offset` as both starting position and fuel).

  Both indexed analogues of `ScannerState.hasTabInPrecedingWhitespace`
  in `Scanner/Whitespace.lean`.

- `IndexedDispatch.lean::scanBlockEntryIx` now reads:
  ```
  do
    if !s.inFlow then
      if s.hasTabInPrecedingWhitespace then
        throw (.tabInIndentation s.cursor.pos.line s.cursor.pos.col)
    let s := if !s.inFlow then pushSequenceIndentIx s s.cursor.pos.col else s
    let s := s.emit YamlToken.blockEntry
    let s := s.advance
    .ok { s with simpleKeyAllowed := true }
  ```

  catching tabs in `-\t-`, `- \t-`, `-\t -`, etc. (any tab in the
  preceding whitespace run is forbidden in block context).

- `IndexedDispatch.lean::scanKeyIx` now reads:
  ```
  do
    let s := if !s.inFlow then pushMappingIndentIx s s.cursor.pos.col else s
    let line := s.cursor.pos.line
    let s := s.emit YamlToken.key
    let s := s.advance
    if !s.inFlow then
      if let some '\t' := s.peek? then
        throw (.tabInIndentation s.cursor.pos.line s.cursor.pos.col)
    .ok { s with simpleKeyAllowed := true, explicitKeyLine := some line,
                  simpleKey := { cursor := IxCursor.start input } }
  ```

  catching a tab immediately following `?` in block context (the
  tab would be indentation for the key content per §6.1).

**Proof changes** (`L4YAML/Proofs/Scanner/IndexedDispatch.lean`):

- Six new `flowLevel` / `inFlow` preservation simp lemmas added to
  the `ScannerStateIx` namespace, between
  `pushMappingIndentIx_cursor` and `unwindIndentsLoopIx_cursor`:
  `emit_flowLevel` (`rfl`), `advance_flowLevel` (`rfl`),
  `pushSequenceIndentIx_flowLevel` and `pushMappingIndentIx_flowLevel`
  (each `unfold pushXxxIndentIx; split <;> rfl`), `emit_inFlow`
  (`rfl`), `advance_inFlow` (`rfl`), `pushMappingIndentIx_inFlow`
  (`unfold pushMappingIndentIx; split <;> rfl`). These let
  `simp only [advance_inFlow, emit_inFlow, pushMappingIndentIx_inFlow]`
  collapse the post-pushMapping/emit/advance `inFlow` projection
  back to the original `s.inFlow`, so the post-advance tab-check
  guard can be dispatched against the *original* `s.inFlow` via
  `simp only [if_pos hi, …]`.

- `scanBlockEntryIx_offset_monotonic` and
  `scanBlockEntryIx_tokens_size_le` re-derived with the early-throw
  pattern from R51 (R50's preferred `split at h` cannot peel both
  the outer `if !s.inFlow` *and* the inner `if hasTab` cleanly):

  ```
  unfold scanBlockEntryIx at h
  by_cases hi : (!s.inFlow) = true
  · rw [if_pos hi] at h
    by_cases ht : s.hasTabInPrecedingWhitespace = true
    · rw [if_pos ht] at h          -- throw fires
      simp [Bind.bind, Except.bind] at h
    · rw [if_neg ht] at h
      simp only [pure_bind] at h
      rw [if_pos hi] at h          -- second `if !s.inFlow` for push
      simp only [Except.ok.injEq] at h
      subst h
      show s.cursor.pos.offset ≤ _
      simp only [advance_cursor, emit_cursor, pushSequenceIndentIx_cursor]
      exact IxCursor.advance_offset_monotonic _
  · rw [if_neg hi] at h            -- flow context: outer guard skipped
    simp only [pure_bind] at h
    rw [if_neg hi] at h
    simp only [Except.ok.injEq] at h
    subst h
    show s.cursor.pos.offset ≤ _
    simp only [advance_cursor, emit_cursor]
    exact IxCursor.advance_offset_monotonic _
  ```

- `scanKeyIx_offset_monotonic` and `scanKeyIx_tokens_size_le`
  re-derived with the more compact `simp only [if_pos hi,
  advance_inFlow, emit_inFlow, pushMappingIndentIx_inFlow]` chain
  (R52). The proof's block-context branch reads:

  ```
  by_cases hi : (!s.inFlow) = true
  · simp only [if_pos hi, advance_inFlow, emit_inFlow,
      pushMappingIndentIx_inFlow] at h
    split at h
    · simp [Bind.bind, Except.bind] at h     -- some '\t' arm
    · simp only [pure_bind, Except.ok.injEq] at h
      subst h
      show s.cursor.pos.offset ≤ _
      simp only [advance_cursor, emit_cursor, pushMappingIndentIx_cursor]
      exact IxCursor.advance_offset_monotonic _
  · ...
  ```

  The simp set chains `if_pos hi` (outer if), then the inFlow chain
  (post-pushMapping/emit/advance `inFlow` ↝ `s.inFlow`), then
  `if_pos hi` *again* (now firing on the inner if whose condition
  is now syntactically `(!s.inFlow) = true`), leaving only the
  `match s.peek?` over the tab discriminant.

Sorry budget: **0 → 0** in the staging files. `lake build` passes
all 385 targets. `L4YAML.lean` does not import any
`Scanner.Indexed*` or `Proofs.Scanner.Indexed*` file — confirmed.

**Carried forward into Steps 5b.3–5b.8**: the six remaining Step-5b
clusters (`scanValueIx` validation chain, hex-escape value,
`autoDetectBlockScalarIndentLoopIx`, block-scalar fold/chomp,
quoted multi-line, plain multi-line).

</details>

<details><summary>Step 5b.3 — <code>scanValueIx</code> validation chain <em>(landed)</em>.</summary>

**Step 5b.3 — `scanValueIx` validation chain** *(landed)*.

Three new defs lifted from `L4YAML/Scanner/SimpleKey.lean` into
`L4YAML/Scanner/IndexedDispatch.lean` (alongside the already-landed
`scanValuePrepareIx`):

- **`scanValueClearKeyIx`** (§8.2.2). Pure state transform that
  clears a spurious simple key when an explicit `?` is pending and
  either (a) the simple key was saved AT the `:` position itself on
  a different line from `?`, or (b) the simple key was saved on the
  `?` line and `:` is on a subsequent line in block context. The
  body matches on `s.explicitKeyLine`; both `some`-branch clears
  produce `{ s with simpleKey := { cursor := IxCursor.start input }
  }` (the indexed convention for "reset to default"). Never touches
  `tokens` or `cursor`.
- **`scanValueValidateIx`** (§8.2.2). `Except ScanError Unit`. Five
  separate `throw` cases mirroring the legacy verbatim, translated
  to indexed accessors: §7.4 block-context multiline implicit key;
  §7.4.2 flow-sequence multiline implicit key; §8.2.1 key at same
  indent as block sequence; T833 missing comma in flow mapping
  (uses `s.tokens.tokens[i]?` and `.token`); §8.2.2 [197] explicit
  value `:` must be at mapping indent level (two sub-checks for
  `sameLineExplicitValue` / `misindentedExplicitValue`).
- **`scanValueTabCheckIx`** (§6.1). `Except ScanError Unit` taking
  `origCol : Int` and `origIndent : Int` from the *pre-emit*
  state, then peeks the *post-advance* cursor for `'\t'`.

`scanValueIx` itself is rewritten as the legacy four-stage `do`-chain:

```lean
def scanValueIx ... := do
  let s_kc := scanValueClearKeyIx s
  scanValueValidateIx s_kc
  let s_prepared := scanValuePrepareIx s_kc
  let s_with_token := s_prepared.emit YamlToken.value
  let s_after_advance := s_with_token.advance
  scanValueTabCheckIx (s.cursor.pos.col : Int) s.currentIndent
                       s_after_advance
  .ok { s_after_advance with simpleKeyAllowed := true,
                              explicitKeyLine := none }
```

The two existing monotonicity proofs (`scanValueIx_offset_monotonic`
and `_tokens_size_le` in `Proofs/Scanner/IndexedDispatch.lean`)
were re-derived. The Step 5b.1b.ii style — `simp only [Except.ok.injEq]
at h; subst h` — no longer fits: the elaborated `do` carries
`have s_kc := scanValueClearKeyIx s; …` (a `have`-binder shadowing
the do-block let), so `rw` over the sub-expression names fails. The
fix is the legacy pattern:

```lean
unfold scanValueIx at h
simp only [bind, Except.bind] at h
split at h
· cases h                                                  -- validate threw
· split at h
  · cases h                                                -- tab-check threw
  · simp only [Except.ok.injEq] at h
    subst h
    show s.cursor.pos.offset ≤ _
    simp only [advance_cursor, emit_cursor, scanValuePrepareIx_cursor,
               scanValueClearKeyIx_cursor]
    exact IxCursor.advance_offset_monotonic _
```

Two new helper simp lemmas landed: `scanValueClearKeyIx_cursor`
`@[simp]` (every branch leaves `.cursor` untouched — `unfold;
split; · split; · rfl; · split <;> rfl; · rfl`) and
`scanValueClearKeyIx_tokens_size_le` (every branch leaves `.tokens`
untouched — `Nat.le_refl _` in all five leaves).

**Unrelated breakage swept in the same commit**: the prior
spec-traceability commit (`5994edce`) had left two proof files
broken under the `lake build` cache. After the staging recompile
chain was disturbed by Step 5b.3's edits, the cache invalidated and
the underlying breakage surfaced:

- `Proofs/Scanner/IndexedScalar.lean`:
  `collectDoubleQuotedLoopIx_offset_monotonic`,
  `scanDoubleQuotedIx_offset_lt`,
  `collectSingleQuotedLoopIx_offset_monotonic`,
  `scanSingleQuotedIx_offset_lt`,
  `parseBlockHeaderLoopIx_offset_monotonic`, and
  `blockHeaderToBodyIx_offset_monotonic`. All needed `split at h`
  shape updates: the quoted/header loops moved from
  `match c.peek? with | some 'X' => …` (4+ direct match branches) to
  `match c.peek? with | some ch => if isXBool ch then … else if …`
  (2 outer branches plus a nested if-cascade), so the proofs now
  open with an outer `some ch` / `none` split and then nest one
  `split at h` per `else if` level. `blockHeaderToBodyIx` further
  has `(peek? == some '#')` replaced by `(match peek? with | some d
  => isCommentBool d | none => false)`, which `split` opens as a
  match-then-if, requiring an explicit `by_cases hp : … = true`
  with `rw [if_pos hp]` / `rw [if_neg hp]` rather than two
  back-to-back `split`s.
- `Proofs/Scanner/IndexedIndent.lean::skipToContent_at_content`:
  `(ch == '#') = false` → `isCommentBool ch = false`. One-line fix
  (`unfold isCommentBool; simp [hHash]`), but the proof would not
  compile until the underlying simp shape was restated.

The reason `lake build` had shown 385/385 after `5994edce`: the
`.olean` cache for `IndexedScalar` / `IndexedIndent` predated the
predicate refactor — only `IndexedScanner.lean`'s `.olean` was
rebuilt by the prior commit, because nothing else's source had
changed yet. Step 5b.3 touched `IndexedDispatch.lean`, which
transitively forces `IndexedScalar.lean` to recompile, which is
when the breakage surfaced. See Reflection 53.

Sorry budget: **0 → 0** in the staging files. `lake build` passes
all 385 targets. `L4YAML.lean` does not import any
`Scanner.Indexed*` or `Proofs.Scanner.Indexed*` file — confirmed.

**Carried forward into Steps 5b.4–5b.8**: the five remaining
Step-5b clusters (hex-escape value,
`autoDetectBlockScalarIndentLoopIx`, block-scalar fold/chomp,
quoted multi-line, plain multi-line).

</details>

<details><summary>Step 5b.4 — Hex-escape value-correctness <em>(landed)</em>.</summary>

**Step 5b.4 — Hex-escape value-correctness** *(landed)*.

Discharges the Step 4a carry-forward: `hexStringValue` of a
hex-digit string equals the decoded `Nat` value (modulo the
overflow checks). Four lemmas land in
`L4YAML/Proofs/Scanner/IndexedScalar.lean` (new section
"Layer E1.4 — Hex-escape value-correctness", after the F3 block-
scalar proofs and before `end L4YAML.Scanner.Indexed`):

- **`hexDigitValue_lt_16`** — for every hex digit `ch` (i.e.
  `isHexDigitBool ch = true`), `hexDigitValue ch < 16`. Proof:
  `simp only [isHexDigitBool, Bool.or_eq_true, Bool.and_eq_true,
  decide_eq_true_eq, UInt32.le_iff_toNat_le] at h` pushes the
  Bool disjunction into a Nat-`≤` disjunction in one pass.
  `Char.toNat` then unfolds the goal's `ch.toNat` into
  `ch.val.toNat`, and the matching `simp only [Char.toNat,
  UInt32.le_iff_toNat_le]` pushes the `hexDigitValue`'s if-
  condition the same way. Six `(0xNN : UInt32).toNat = NN`
  facts (`by native_decide`) bridge the literal forms. The
  case-split uses plain `cases h with | inl … | inr …` —
  `rcases` aggressively destructs the underlying `Nat.le`
  conjuncts and fails (Reflection 54).
- **`hexStringValue_empty`** — `@[simp]`, `hexStringValue "" = 0`.
  One-line proof: `String.foldl_eq_foldl_toList` + `rfl`.
- **`hexStringValue_push`** — the snoc law:
  `hexStringValue (s.push ch) = hexStringValue s * 16 +
  hexDigitValue ch`. Proof: chain `String.foldl_eq_foldl_toList`,
  `String.toList_push`, `List.foldl_append`. Two `rfl` cleanups
  close it.
- **`hexStringValue_lt_pow`** — the `16^n` bound when every
  character is a hex digit: `(∀ c ∈ s.toList, isHexDigitBool c
  = true) → hexStringValue s < 16 ^ s.length`. Induction via
  `String.push_induction`. The push case rewrites with the
  snoc law and `String.length_push`, then chains
  `Nat.mul_le_mul_right 16 hb` (where `hb : hexStringValue b
  + 1 ≤ 16 ^ b.length` from the IH) so that `omega` can close
  `hexStringValue b * 16 + hexDigitValue ch < 16 ^ b.length *
  16` using `hch : hexDigitValue ch < 16`.
- **`parseHexEscapeIx_decoded`** — the parser spec: when
  `parseHexEscapeIx c n = some (ch, c')`,

  ```
  hexStringValue (collectHexDigitsLoopIx c "" n).1 < 0x110000
  ∧ ch = Char.ofNat (hexStringValue (collectHexDigitsLoopIx c "" n).1)
  ∧ c' = (collectHexDigitsLoopIx c "" n).2.
  ```

  Two `split at h` (one per nested `if`) plus
  `Option.some.injEq` / `Prod.mk.injEq` and a `rename_i hLt` to
  pick up the value-range hypothesis is the whole proof.

The Unicode-range guard `< 0x110000` is load-bearing only for
`n = 8` (`\U________`): for `n = 2` and `n = 4` the
`hexStringValue_lt_pow` bound gives `< 16^4 = 65536`, comfortably
below `0x110000`. The guard nevertheless stays in the parser for
the `n = 8` case and survives surrogate hex escapes
(`\ud800..\udfff`) as `Char.ofNat`'s `default` fallback rather
than a parser error — that's an existing semantic issue, not a
Step 5b.4 obligation.

Sorry budget: **0 → 0** in the staging files. `lake build` passes
all 385 targets. `L4YAML.lean` does not import any
`Scanner.Indexed*` or `Proofs.Scanner.Indexed*` file — confirmed.

**Carried forward into Steps 5b.5–5b.8**: the four remaining
Step-5b clusters (`autoDetectBlockScalarIndentLoopIx`,
block-scalar fold/chomp, quoted multi-line, plain multi-line).

</details>

<details><summary>Step 5b.5 — `autoDetectBlockScalarIndentLoopIx` correctness <em>(landed)</em>.</summary>

**Step 5b.5 — `autoDetectBlockScalarIndentLoopIx` correctness**
*(landed)*.

Discharges the Step 4b carry-forward: the block-scalar
auto-detect-indent loop chooses a content indent that is at least
the spec-mandated minimum. Two lemmas land in
`L4YAML/Proofs/Scanner/IndexedScalar.lean` (new section
"Layer F.1 — Auto-detected block-scalar indent ≥
`minContentIndent`", after the Layer E1.4 hex-escape proofs and
before `end L4YAML.Scanner.Indexed`):

- **`autoDetectBlockScalarIndentLoopIx_ge_min`** — for any `(probe,
  maxWSCol, minContentIndent, fuel)`,

  ```
  minContentIndent ≤
    autoDetectBlockScalarIndentLoopIx probe maxWSCol minContentIndent fuel.
  ```

  Proof: induction on `fuel` (`generalizing probe maxWSCol` so the
  IH absorbs the recursive call's updated `maxWSCol'`). Base case
  is the EOF-style `if maxWSCol > minContentIndent then maxWSCol
  else minContentIndent` — `split <;> omega` from either branch.
  Recursive case is three nested `split`s: (1) the
  `let (probeAfterSp, _) := skipSpaces probe` prod destructure
  (1 case), (2) `match probeAfterSp.peek?` (some/none), (3) inside
  `some ch`, `if isLineBreakBool ch`. The true (`isLineBreakBool ch
  = true`) recursive branch closes by `apply ih`; the false branch
  and the EOF branch both reduce to `split <;> omega` on the inner
  `if probeAfterSp.pos.col > minContentIndent` / `if maxWSCol >
  minContentIndent` guards. The proof-shape lesson — count the
  three nested splittables (the let-prod destructure is the
  unintuitive one) — is captured in Reflection 55.
- **`autoDetectBlockScalarIndentIx_ge_min`** — entry-point
  wrapper: `minContentIndent ≤ autoDetectBlockScalarIndentIx c
  minContentIndent`. One-line proof: unfold and apply the loop
  lemma with `maxWSCol := 0`, `fuel := input.utf8ByteSize`.

The lower-bound property is the spec-mandated invariant from
YAML 1.2.2 [162] (`c-l+literal`/`c-l+folded` indent rules): the
content indent of a block scalar must exceed the parent indent.
Since `autoDetectBlockScalarIndentIx` is called with
`minContentIndent = parentIndent + 1`, downstream content-
correctness proofs (Step 5b.6) will lift this lower bound into
the parent-indent strict inequality the spec demands.

The function deliberately does *not* return a `Char × IxCursor` or
similar — it returns a bare `Nat` (the chosen indent) — so the
"correctness" property is a bound on that `Nat`, not a
monotonicity or progress lemma. That matches the function's role
as a *probe* (the call site does not consume input; the actual
indent consumption happens later in `collectBlockScalarLoopIx`).

Sorry budget: **0 → 0** in the staging files. `lake build` passes
all 385 targets. `L4YAML.lean` does not import any
`Scanner.Indexed*` or `Proofs.Scanner.Indexed*` file — confirmed.

**Carried forward into Steps 5b.6–5b.8**: the three remaining
Step-5b clusters (block-scalar fold/chomp, quoted multi-line,
plain multi-line).

</details>

<details><summary>Step 5b.6 — Block-scalar content correctness <em>(landed)</em>.</summary>

**Step 5b.6 — Block-scalar content correctness** *(landed)*.

Carried-forward Step 4b obligation discharged in
`L4YAML/Proofs/Scanner/IndexedScalar.lean`'s new "Layer F.2 —
Block-scalar content correctness" section (~50 LOC, just before
the closing `end L4YAML.Scanner.Indexed`). Six lemmas pin the two
post-collection block-scalar transformers to their YAML 1.2.2 spec
rules:

`applyChomp` (chomp indicator `[160]`, §8.1.1.2) — four lemmas,
one per spec branch:
- `applyChomp_keep (raw : String) : applyChomp .keep raw = raw` —
  identity (`rfl`).
- `applyChomp_strip (raw : String) :
  applyChomp .strip raw = stripTrailingNewlines raw` — strip all
  trailing newlines (`rfl`).
- `applyChomp_clip_of_endsWith {raw : String}
  (h : raw.endsWith (String.singleton lineFeedChar) = true) :
  applyChomp .clip raw =
    stripTrailingNewlines raw ++ String.singleton lineFeedChar` —
  clip keeps exactly one when raw ended in `\n` (`simp [applyChomp, h]`).
- `applyChomp_clip_of_not_endsWith {raw : String}
  (h : raw.endsWith (String.singleton lineFeedChar) = false) :
  applyChomp .clip raw = stripTrailingNewlines raw` — clip keeps
  zero otherwise (`simp [applyChomp, h]`).

`foldBlockContent` (fold machine `[170]`–`[181]`, §8.1.3) — two
base-case lemmas:
- `foldBlockContentGo_nil (acc : String) (st : FoldState) (pending : Nat) :
  foldBlockContentGo [] acc st pending = acc` — empty input list,
  output is the accumulator (`rfl`).
- `foldBlockContent_empty : foldBlockContent "" = ""` — wrapper on
  the empty string (`rfl`).

All six are definitional unfolds; the value of the lemma is the
*named statement*, not the proof. Once these exist, downstream
multi-line consumers (Steps 5b.7 quoted, 5b.8 plain) can cite the
spec-rule mapping by name when reasoning about the block-scalar
pipeline `parseBlockHeaderLoopIx → blockHeaderToBodyIx →
autoDetectBlockScalarIndentIx → collectBlockScalarLoopIx →
applyChomp → foldBlockContent`. The rule about valuing
spec-traceability lemmas equally with computational ones — and
the explicit *non*-goal of proving the full fold-machine
invariant in this step — is captured in Reflection 56.

Sorry budget: **0 → 0** in the staging files. `lake build` passes
all 385 targets. `L4YAML.lean` does not import any
`Scanner.Indexed*` or `Proofs.Scanner.Indexed*` file — confirmed.

**Carried forward into Steps 5b.7–5b.8**: the two remaining
Step-5b clusters (quoted multi-line content correctness `[111]`–
`[116]` / `[122]`–`[125]`, plain multi-line content correctness
`[131]`–`[135]`). Also carried: the full fold-machine invariant
for `foldBlockContent` on non-empty input — when a downstream
proof forces the obligation, the lemma will need list-induction
simultaneously tracking `FoldState`, `pending`, and the input
structure against a reference implementation of the spec's folded
extraction.

</details>

<details><summary>Step 5b.7 — Quoted multi-line content correctness <em>(landed)</em>.</summary>

**Step 5b.7 — Quoted multi-line content correctness** *(landed)*.

Carried-forward Step 4b obligation discharged in
`L4YAML/Proofs/Scanner/IndexedScalar.lean`'s new "Layer F.3 —
Quoted multi-line content correctness" section (~120 LOC, just
before the closing `end L4YAML.Scanner.Indexed`). Nine lemmas pin
the three multi-line quoted-scalar helpers to their YAML 1.2.2
spec rules:

`foldQuotedNewlinesIx` (§6.5 [73] / [74]) — two branch-mapping
lemmas, one per arm of the `emptyCount > 0` conditional:
- `foldQuotedNewlinesIx_of_blank_lines {input : String}
  (c : IxCursor input)
  (h : (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).2 > 0) :
  foldQuotedNewlinesIx c =
    (String.ofList (List.replicate _ lineFeedChar),
     skipWhitespace _)` — `b-l-trimmed(n,c)` [71]
  (`unfold + simp [h]`).
- `foldQuotedNewlinesIx_of_single_break {input : String}
  (c : IxCursor input)
  (h : (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).2 = 0) :
  foldQuotedNewlinesIx c =
    (String.singleton spaceChar, skipWhitespace _)` —
  `b-as-space` [70] (`unfold + simp [h]`).

`collectDoubleQuotedLoopIx` (§7.3.1 [111]–[116]) — three lemmas:
- `collectDoubleQuotedLoopIx_zero (c : IxCursor input)
  (content : String) : collectDoubleQuotedLoopIx c content 0 = none` —
  fuel exhaustion (`rfl`).
- `collectDoubleQuotedLoopIx_closing` — closing `"` returns
  `some (content, c.advance)` (`unfold + rw [hPeek] + simp [hQuote]`).
- `collectDoubleQuotedLoopIx_linebreak` — line-break branch
  composes `trimTrailingWSIx content ++ (foldQuotedNewlinesIx c).1`
  and recurses on `(foldQuotedNewlinesIx c).2` (uses
  `conv => lhs; unfold …` because the RHS is another loop call).

`collectSingleQuotedLoopIx` (§7.3.2 [122]–[125]) — four lemmas:
- `collectSingleQuotedLoopIx_zero` — fuel exhaustion (`rfl`).
- `collectSingleQuotedLoopIx_doubled` — `''` quoted-quote escape
  [123] pushes one `'` and recurses on `c.advance.advance` (uses
  `conv => lhs; unfold …`).
- `collectSingleQuotedLoopIx_closing_some` — single `'` followed
  by non-`'` returns `some (content, c.advance)`
  (`unfold + rw [hPeek] + simp [hQuote, hPeekAdv, hNext]`).
- `collectSingleQuotedLoopIx_closing_none` — single `'` at EOF
  also returns `some (content, c.advance)` (same shape, with
  `hPeekAdv : c.advance.peek? = none`).
- `collectSingleQuotedLoopIx_linebreak` — same fold composition
  as the double-quoted line-break branch, same `conv` scope.

All nine proofs are definitional unfolds; the value of each lemma
is the *named statement*, not the proof shape. Once these exist,
downstream multi-line consumers and `present`/corpus proofs (Step
5c) can cite the spec-rule mapping by name when reasoning about
the quoted-scalar collectors. The three RHS-recursive branches
(`_linebreak` for both loops + `_doubled` for single-quoted)
use `conv => lhs; unfold …` instead of plain `unfold …`
because plain `unfold` rewrites *both* sides of the equality —
including the recursive call on the RHS — and the subsequent
`simp` then expands that RHS into the full match-cascade,
leaving an unsolvable goal. See Reflection 57.

Sorry budget: **0 → 0** in the staging files. `lake build` passes
all 385 targets. `L4YAML.lean` does not import any
`Scanner.Indexed*` or `Proofs.Scanner.Indexed*` file — confirmed.

**Carried forward into Step 5b.8**: the final Step-5b cluster —
plain multi-line content correctness `[131]`–`[135]`
(`collectPlainScalarLoopIx` with its inFlow/block context branch
and the `foldQuotedNewlinesIx` reuse). Also still carried: the
full fold-machine invariant for `foldBlockContent` on non-empty
input (Step 5b.6 carry-forward, unchanged).

</details>

<details><summary>Step 5b.8 — Plain multi-line content correctness <em>(landed)</em>.</summary>

**Step 5b.8 — Plain multi-line content correctness** *(landed)*.

Carried-forward Step 4b obligation discharged in
`L4YAML/Proofs/Scanner/IndexedScalar.lean`'s new "Layer F.4 —
Plain multi-line content correctness" section (~165 LOC, just
before the closing `end L4YAML.Scanner.Indexed`). 12 lemmas pin
every branch of `collectPlainScalarLoopIx` (§7.3.3 [131]–[135])
to its YAML 1.2.2 spec rule. This is the most branch-heavy
collector in the indexed scanner; each of its 11 post-`peek?`
outcomes plus the fuel-zero base case gets a named branch lemma.

Spec rules:
- `ns-plain(n,c)` [131] — top-level plain scalar production
- `nb-ns-plain-in-line(c)` [132] — in-line plain text (covered by
  the `_colon_terminate` / `_colon_continue` split, which makes the
  `colonTerminatesPlain` flow/block disambiguation visible)
- `s-ns-plain-next-line(n)` [133] — continuation onto next line
  (visible in the `_linebreak_*` branches' fold + indent check)
- `ns-plain-multi-line(n,c)` [134] — the threaded
  `content ++ folded` composition is what this rule describes;
  visible in `_linebreak_flow` (flow context, uses
  `foldQuotedNewlinesIx` from Layer F1) and
  `_linebreak_block_some` (block context, uses
  `handleBlockLineBreakIx` with `contentIndent` floor + document
  boundary check)
- `ns-plain-one-line(c)` [135] — single-line plain (the
  `_linebreak_block_none` branch terminates the loop without
  continuation when handle returns `none`)

The 12 lemmas:

- `collectPlainScalarLoopIx_zero (c content spaces inFlow contentIndent) :
  collectPlainScalarLoopIx c content spaces inFlow contentIndent 0 =
    (content ++ spaces, c)` — fuel exhaustion (`rfl`).
- `collectPlainScalarLoopIx_eof (hPeek : c.peek? = none) :
  collectPlainScalarLoopIx c content spaces inFlow contentIndent (fuel + 1) =
    (content ++ spaces, c)` — `peek? = none` (`unfold + rw [hPeek]`).
- `collectPlainScalarLoopIx_comment
  (hPeek : c.peek? = some ch)
  (hComment : isCommentBool ch = true)
  (hSpaces : spaces.length > 0) :
  ... = (content, c)` — `#` after at least one space terminates
  (`unfold + rw + simp [hComment, hSpaces]`).
- `collectPlainScalarLoopIx_colon_terminate
  (hMapVal : isMappingValueBool ch = true)
  (hColon : colonTerminatesPlain c inFlow = true) :
  ... = (content, c)` — `:` followed by blank/EOF (block) or
  `:` followed by flow-indicator (flow) terminates.
- `collectPlainScalarLoopIx_colon_continue
  (hMapVal : isMappingValueBool ch = true)
  (hColon : colonTerminatesPlain c inFlow = false) :
  ... = collectPlainScalarLoopIx c.advance
        (content ++ spaces ++ String.singleton ch) "" inFlow
        contentIndent fuel` — `:` mid-plain pushes literally and
  recurses (uses `conv => lhs; unfold …`).
- `collectPlainScalarLoopIx_flow_indicator (hFlowInd) :
  ... (inFlow := true) = (content, c)` — `,`/`]`/`}` in flow
  context terminates.
- `collectPlainScalarLoopIx_linebreak_flow (hLineBreak) :
  ... (inFlow := true) =
    collectPlainScalarLoopIx (foldQuotedNewlinesIx c).2
      (content ++ (foldQuotedNewlinesIx c).1) "" true
      contentIndent fuel` — flow-context line break delegates to
  `foldQuotedNewlinesIx` (Layer F1 — §6.5 [73] / [74]) and
  composes `content ++ folded` (uses `conv => lhs; unfold …`).
- `collectPlainScalarLoopIx_linebreak_block_none
  (hLineBreak) (hHandle : handleBlockLineBreakIx c contentIndent = none) :
  ... (inFlow := false) = (content, c)` — block-context line break
  terminates the loop when the continuation line is under-indented
  or hits a document boundary.
- `collectPlainScalarLoopIx_linebreak_block_some
  (hHandle : handleBlockLineBreakIx c contentIndent = some (folded, cAfterFold)) :
  ... (inFlow := false) =
    collectPlainScalarLoopIx cAfterFold (content ++ folded) ""
      false contentIndent fuel` — block-context line break recurses
  on `cAfterFold` with `content ++ folded`; this is the
  `ns-plain-multi-line(n,c)` [134] threading (uses
  `conv => lhs; unfold …`).
- `collectPlainScalarLoopIx_whitespace (hWhitespace) :
  ... = collectPlainScalarLoopIx c.advance content (spaces.push ch)
        inFlow contentIndent fuel` — whitespace accumulates into
  `spaces` (uses `conv => lhs; unfold …`).
- `collectPlainScalarLoopIx_not_plain_safe (hNotPlainSafe) :
  ... = (content, c)` — non-plain-safe character terminates.
- `collectPlainScalarLoopIx_content (hPlainSafe) :
  ... = collectPlainScalarLoopIx c.advance
        (content ++ spaces ++ String.singleton ch) "" inFlow
        contentIndent fuel` — the plain-safe content push (uses
  `conv => lhs; unfold …`).

All 12 proofs are definitional unfolds; the value of each lemma
is the *named statement*, not the proof shape. Once these exist,
downstream multi-line consumers and `present`/corpus proofs (Step
5c) can cite the spec-rule mapping by name when reasoning about
the plain-scalar collector. The five RHS-recursive branches
(`_colon_continue`, `_linebreak_flow`, `_linebreak_block_some`,
`_whitespace`, `_content`) use `conv => lhs; unfold …` instead
of plain `unfold …` to scope the rewrite to the LHS — direct
reuse of Reflection 57 from Step 5b.7; no new failure modes
encountered, so no new reflection. Each lemma takes its cascade-
prefix predicates as explicit hypotheses (e.g.
`isCommentBool ch = false` to skip the `#` branch); the
hypotheses match the structure of the `if … else if …` cascade
so that `simp` closes the goal mechanically after `rw [hPeek]`.

Sorry budget: **0 → 0** in the staging files. `lake build` passes
all 385 targets. `L4YAML.lean` does not import any
`Scanner.Indexed*` or `Proofs.Scanner.Indexed*` file — confirmed.

**Step 5b is now complete**: all eight sub-steps (5b.1a,
5b.1b.i–iv, 5b.2–5b.8) are landed. The only surviving carry-
forward is the full **fold-machine invariant for
`foldBlockContent` on non-empty input** (Step 5b.6 carry-forward,
explicitly deferred to the load-pipeline step that will quote it
against canonicalised input).

</details>

<details><summary>Step 5c — `present` + corpus theorem <em>(landed)</em>.</summary>

**Step 5c — `present` + corpus theorem** *(landed)*.
The final pre-cutover staging step landed as two new files. The
sorry budget is `0 → 0` in both files — every roundtrip theorem
discharges by `native_decide`.

### `L4YAML/Scanner/IndexedPresenter.lean` (~121 LOC, new)

Defines two functions in `namespace L4YAML.Scanner.Indexed`:

- `renderToken : IxToken input → String` — per-constructor
  dispatch. Returns:
  - `""` for virtual tokens (`streamStart`, `streamEnd`,
    `placeholder`, `blockSequenceStart`, `blockMappingStart`,
    `blockEnd`, and the implicit `key`/`value` tokens the scanner
    inserts for simple-key resolution and block-mapping value
    discovery).
  - The single literal character `[`/`]`/`{`/`}`/`,`/`-` for the
    flow brackets, flow entry separator, and block-entry indicator.
  - The three-character marker `---`/`...` for `documentStart`/
    `documentEnd`.
  - The source span `String.Pos.Raw.extract input ⟨tok.start.offset⟩
    ⟨tok.stop.offset⟩` for content tokens (`scalar`, `anchor`,
    `alias`, `tag`, `comment`, `versionDirective`, `tagDirective`).

- `present : TokenStream input → String` =
  `ts.tokens.foldl (init := "") fun acc tok => acc ++ renderToken tok`.

Plus a single sanity lemma:
- `@[simp] theorem present_empty (input : String) :
    present (TokenStream.empty input) = "" := rfl`.

The hybrid render is necessary because the indexed scanner's
indicator-token convention is `emit` (zero-width at cursor) +
`advance` — so the token's `[start, stop)` range is degenerate
at the position *before* the indicator character. A pure
source-span fold would lose every `[`/`]`/`{`/`}`/`,`/`-`. The
constructor-level dispatch re-injects them by literal.

The use of `String.Pos.Raw.extract` (rather than the new Lean 4.30
`String.extract`) sidesteps the `Pos.Raw.IsValid` proof that the
validated `s.Pos` API requires — `IxToken`'s positions are plain
`Nat`-wrapped offsets that don't carry a validity proof, and
`Pos.Raw.extract` accepts raw byte offsets directly.

### `L4YAML/Proofs/Scanner/IndexedRoundtrip.lean` (~158 LOC, new)

Defines:

- `roundtripOk : String → Bool` — the Bool-valued check
  `match scanIx input with | .ok ts => present ts == input | .error _ => false`.
  Returning `Bool` (rather than `Prop`) lets each corpus theorem
  state a closed-form `= true` equation without the dependent-
  `Prop` `Decidable` instance plumbing a `match`-shaped predicate
  would need.

- 19 corpus roundtrip theorems, each of the form
  `theorem roundtrip_xxx : roundtripOk "…" = true := by native_decide`.
  Both `scanIx` (the full indexed-scanner pipeline, fueled) and
  `present` (the fold) are fully computable on a fixed `String`,
  so `native_decide` compiles the goal to native code and
  evaluates it. The corpus:
  - `""` (empty)
  - Plain scalars at root: `"x"`, `"abc"`, `"hello"`
  - Empty/one-/two-/three-/four-element flow sequences:
    `"[]"`, `"[x]"`, `"[x,y]"`, `"[a,b,c]"`, `"[a,b,c,d]"`
  - Empty/one-/two-key flow mappings:
    `"{}"`, `"{a}"`, `"{a,b}"`
  - Nesting patterns:
    `"[[]]"`, `"[{}]"`, `"[a,[b,c]]"`, `"[{a},b]"`,
    `"{a,{b}}"`, `"[[],[]]"`, `"{[]}"`

- `scanIx_present_of_roundtripOk : ∀ input, roundtripOk input = true →
    ∃ ts, scanIx input = .ok ts ∧ present ts = input` — the
  closed-form consequence. The Blueprint's
  `scanIx (present ts) = .ok ts` statement follows by rewriting
  `present ts = input` on the LHS.

### Corpus scope and deferred work

The corpus is restricted to inputs whose token streams (i) cover
every byte of `input` with no inter-token whitespace, (ii) have
only implicit `key`/`value` tokens (no explicit `?`/`:` in
source), and (iii) use plain scalars only (no quoted, literal, or
folded scalars, no anchors/aliases/tags). Inputs that include
inter-token whitespace, explicit `?`/`:`, quoted/block scalars,
anchors/tags, comments, or document markers do *not* roundtrip
with the current presenter; extending the corpus to cover them
requires a richer presenter that interpolates gap bytes from the
input type-parameter and recovers explicit-vs-implicit key/value
distinctions. That refinement is the full bidirectional
`compose ∘ parse ∘ present ∘ serialize` roundtrip in Phase 4+.

### Status

`lake build` 385/385 green. Both new staging files build under
`lake build L4YAML.Scanner.IndexedPresenter` /
`lake build L4YAML.Proofs.Scanner.IndexedRoundtrip` (26-job
incremental). Neither file is imported by `L4YAML.lean` —
Guardrail 1 is preserved. Step 5 is now complete: 5a (state +
dispatch infrastructure), 5b (the eight correctness sub-steps),
and 5c (`present` + corpus) are all landed; the only surviving
carry-forward is Step 5b.6's fold-machine invariant for non-empty
input, explicitly deferred to the load-pipeline step.

### Reflection 58 — *`emit`-then-`advance` produces zero-width indicator tokens; `present` needs constructor-level dispatch, not pure source-span extraction.*

The natural design for `present : TokenStream input → String` is a
fold extracting each token's source span:
`ts.tokens.foldl (· ++ input.extract [t.start, t.stop)) ""`. This
works for content tokens (`scalar`, `anchor`, `alias`, `tag`,
`comment`, `versionDirective`, `tagDirective`) where the scanner
records the consumed range. But the indexed scanner emits
single-character indicator tokens by the convention `emit`
(zero-width at the cursor) followed by `advance` (cursor moves
past the character) — the token's recorded `[start, stop)` range
is therefore `[cursor.pos, cursor.pos)`, *before* the character.
A pure source-span fold yields the empty string for every
`[`/`]`/`{`/`}`/`,`/`-`/`---`/`...`, and the roundtrip fails on
even the simplest flow inputs like `"[]"`.

The fix is per-constructor dispatch in `renderToken`:

- **Virtual tokens** (`streamStart`, `streamEnd`, `placeholder`,
  `blockSequenceStart`, `blockMappingStart`, `blockEnd`, and the
  implicit `key`/`value` tokens) render to `""`.
- **Single-character indicators** (`flow*Start`, `flow*End`,
  `flowEntry`, `blockEntry`) render to the literal character.
- **Multi-character markers** (`documentStart`, `documentEnd`)
  render to `---`/`...`.
- **Content tokens** keep the source-span extraction (their
  `[start, stop)` is non-degenerate).

The `key`/`value` tokens are deliberately rendered to `""`
because the scanner emits them in both explicit (`?`/`:` written
in source) and implicit (simple-key resolution in flow context,
block-mapping value discovery) cases, with no constructor-level
distinction — distinguishing them requires inspecting the source
character at `tok.start.offset` and is deferred to a richer
presenter in Phase 4+.

The lesson generalises: **when a scanner emits-then-advances, the
token's recorded source position is the pre-consumption cursor,
not a post-consumption span.** Any downstream that wants to
reconstruct source from tokens must compensate. The alternative
would be for the scanner to advance *first* then emit (so
`[start, stop)` covers the consumed character), but that would
break the existing offset-monotonicity proofs in Step 5b.1b (which
assume emit doesn't move the cursor).

### Reflection 59 — *`Bool`-valued `roundtripOk` sidesteps dependent `Prop` `Decidable` plumbing for corpus theorems.*

The Blueprint's preferred statement for Step 5c was
`scanIx (present ts) = .ok ts` for each `ts ∈ corpus`. The
natural Lean encoding is a `Prop`:

```lean
def roundtripProp (input : String) : Prop :=
  match scanIx input with
  | .ok ts => present ts = input
  | .error _ => False
```

But this requires a `Decidable` instance on `roundtripProp` for
`native_decide` to evaluate it. The `match`-on-`Except` produces
a dependent `Prop` (the `ts` in the `.ok` branch has type
`TokenStream input`, which depends on `input`), and the standard
`unfold + split + infer_instance` skeleton doesn't construct the
instance cleanly — `split`'s case-split on `Except` doesn't
propagate the `input` dependency through the `Decidable` instance
search, and the result fails with an opaque "uses `sorry`" error.

The fix is to return `Bool` from the helper:

```lean
def roundtripOk (input : String) : Bool :=
  match scanIx input with
  | .ok ts => present ts == input
  | .error _ => false
```

`Bool` equality is trivially `Decidable` (the goal becomes
`roundtripOk "…" = true`), and `native_decide` evaluates the
function call by compiling to native code. The closed-form
existential `∃ ts, scanIx input = .ok ts ∧ present ts = input`
follows from `roundtripOk input = true` by a one-line `cases` +
`refine` proof (see `scanIx_present_of_roundtripOk`).

The lesson: **when the goal is to *exhibit* a property on
fixed inputs (not to *derive* it symbolically), prefer `Bool`-
valued helpers with `= true` equations over `Prop`-valued
predicates with custom `Decidable` instances.** `native_decide` is
designed for `Decidable` `= true` equations; the `Prop`-shaped
detour costs an instance-search hazard with no proof-engineering
benefit.

### Reflection 60 — *Lean 4.30's validated `String.Pos` requires `String.Pos.Raw.extract` for raw-offset extraction.*

In Lean 4.30, `String.Pos s` is a dependent structure indexed by
the source string `s`, with two fields: `offset : Pos.Raw` and
`isValid : offset.IsValid s`. The legacy `String.extract` (which
took `⟨n⟩ : String.Pos` from a `Nat`) no longer exists in the
same form — the new `String.extract` requires the validity
proof.

`IxToken`'s positions are `YamlPos` values with a `Nat` `offset`
field and no UTF-8 validity proof. Constructing
`String.Pos input` from a `Nat` offset requires synthesising
`offset.IsValid input`, which is a non-trivial proposition
(`offset` must point at a UTF-8 boundary).

The fix is to use `String.Pos.Raw.extract` (in
`Init.Data.String.Basic`) directly: it takes
`(@& String) → (@& Pos.Raw) → (@& Pos.Raw) → String` — raw
byte offsets, no validity check — and returns the substring (or
`""` if `start ≥ stop` or the offsets aren't on character
boundaries; the latter case won't trigger for IxToken positions
because the scanner only advances at character boundaries via
`advance` / `advanceN`, but the safety net of returning `""` is
nice to have).

The lesson: **when downstream code holds positions as plain
`Nat` offsets without a UTF-8-validity proof, use the
`String.Pos.Raw.*` API family rather than constructing
validated `String.Pos`.** This is a Lean 4.30-specific
adjustment; pre-4.30 code that wrote `String.extract input ⟨a⟩
⟨b⟩` migrates to `String.Pos.Raw.extract input ⟨a⟩ ⟨b⟩`.

</details>

<details><summary>Step 6 — Atomic cutover (prep-pass ladder 6a–6f).</summary>

**Step 6 — Atomic cutover**.

Originally framed as a single commit, but a scope check after Step
5c landed showed the Parser layer's dependency on the legacy scanner
API is substantial enough that the cutover must be staged. The
downstream surface is **1,348 LOC of Parser production code**
(`State.lean` 285, `TokenParser.lean` 790, `Composition.lean` 214,
`Fuel.lean` 59) and **~10,091 LOC of Parser proofs** (`WellBehaved`
4,797, `NodeProofs` 1,781, `WfaProofs` 1,692, plus
`Correctness`/`Completeness`/`Grammable` ~600 combined), all of
which consume `Array (Positioned YamlToken)` and index into it via
a `pos : Nat` cursor. The indexed scanner produces `Indexed.TokenStream
input` — dependently typed on `input : String` — so the type
substitution ripples through every parser function and every parser
proof.

**Strategic forks settled**:
- **Fork 1 — Parser-proof strategy: rebuild**. Re-prove parser
  correctness directly against the indexed `ParseStateIx`. The
  legacy parser-proof stack dies with the legacy scanner in the
  final cutover commit. Rejected alternative: *lift* (prove
  `parseStream ∘ TokenStream.toLegacy = parseStreamIx` and transfer
  legacy proofs via the adapter). Rebuild aligns with the Phase 3
  thesis that the indexed substrate **subsumes** the flat-array
  substrate, and avoids leaving an adapter equivalence in the
  production build forever.
- **Fork 2 — Staging vs. in-place: staging**. Continue the `*Ix.lean`
  staging-file pattern established by Step 5b (`IndexedDispatch`)
  and Step 5c (`IndexedPresenter`, `IndexedRoundtrip`): every Step 6
  sub-step lands in staging files that the legacy build does *not*
  import, keeping `lake build` green throughout 6a–6e. Only 6f
  promotes staging files to production names and deletes the legacy
  stack.

**Sub-step ladder**:

| Sub-step | Scope | New staging files | LOC added | Sessions |
|----------|-------|-------------------|-----------|----------|
| **6a** ✅ | `ParseStateIx` — state record holding `Indexed.TokenStream input` + cursor; re-implement navigation primitives (`hasMore`, `peek?`, `advance`, `expect`, `tryConsume`, `lastPos?`, `currentLine`). Production code only; no proofs. **Landed** in Step 6a commit (~304 LOC). | `Parser/ParseStateIx.lean` | ~304 (landed) | 1 (actual) |
| **6b** ✅ | `TokenParserIx` — clone the 18-function mutually-recursive parser block + stream/document layer over `ParseStateIx`; preserve fuel discipline (`4 * ts.tokens.size + 4`). Add `parseStreamIx : Indexed.TokenStream input → Except ScanError (Array YamlDocument)`. **Landed** in Step 6b commit (~708 LOC). | `Parser/TokenParserIx.lean`, `Parser/FuelIx.lean` | ~708 (landed) | 1 (actual) |
| **6c** ✅ | Re-prove **NodeProofs** (`AG` + `AAR` propagation) against `ParseStateIx`. Pure structural translation — none of the AG/AAR lemmas touch `ps.tokens`, so the substitution is `ParseState → ParseStateIx input` plus the new explicit `input : String` parameter on `ParseNodeAG` / `ParseNodeAAR` (Reflection 63). **Landed** in Step 6c.1 commit (~1,814 LOC). Step 6c's original **WfaProofs** scope is moved into 6d alongside `IndexedWellBehaved`, where its three WB-lemma dependencies (`parseNode_wb_all`, `parseNodeContent_wb`, `parseNodeProperties_tokens`) naturally live. | `Proofs/Parser/IndexedNodeProofs.lean` | ~1,814 (landed) | 1 (actual) |
| **6d.1a** ✅ | **WellBehaved supporting infrastructure** — indexed twins of `flowNesting`/`PlainScalarsValid`/`FlowAwarePSV`/`FlowContextPSV`/`FlowBracketsMatched` over `Array (IxToken input)`, plus the four `flowNestingIx_go_*` step lemmas (`_oob`/`_step`/`_ge_target`/`_split`) that the §5a bridge lemmas depend on. **Landed** in Step 6d.1a commit (~210 LOC, sorry-free). Discovery during this work-in-progress session — Reflection 64: the WellBehaved port is **not** a pure mechanical substitution because (i) `Indexed.TokenStream input` wraps `Array (IxToken input)`, introducing a `.tokens` indirection that breaks `ps.tokens = tokens` `Eq.trans` chains in §5f; (ii) the indexed `peek?` is `Option.map IxToken.token ps.peekIx?` rather than the legacy `tokens[pos]?.map (·.val)`, so the `peek_some_bounded` bridge tactic doesn't transfer; (iii) the §5 C2 chain invokes a scanner-side `scan_flow_aware_psv` producer that needs an indexed twin. Splitting 6d.1 into 6d.1a (infrastructure, this commit) + 6d.1b (full port, next session) keeps each commit `lake build` green per Guardrail 1. | `Proofs/Parser/IndexedWellBehaved.lean` | ~210 (landed) | 1 (actual) |
| **6d.1b** ✅ | **WellBehaved §5-§5e′ pre-mutual-block port** — Option B bridging settled and committed: a new `GetElem (TokenStream input) Nat (IxToken input)` instance in `Indexed/TokenStream.lean` lets predicates re-target from `Array (IxToken input)` to `Indexed.TokenStream input` with a uniform `tokens[i]'h` indexing shape. `IndexedWellBehaved.lean` grew from ~210 → ~823 LOC, covering the loosely-coupled, pre-mutual-block sections: foundation switchover (5 predicates), §5 C2 Infrastructure (5 lemmas including the new `peek_some_bounded_ix` proof shape — the indexed `peek?` factors through `peekIx?` → `TokenStream.get?` → underlying `Array.get?`), §5a flowNesting step lemmas (6 lemmas), §5b Scannable monotonicity (2 verbatim ports — purely `YamlValue`), §5d (1 verbatim port), §5d′ applyNodeFinalization preservation (4 lemmas re-targeted onto indexed `applyNodeFinalization`), §5e′ parseNodeProperties preservation (4 lemmas + verbatim port of the `unfold_loop_at` elaborator). **Landed** in Step 6d.1b commit (~613 LOC delta + 14 LOC `GetElem` instance, sorry-free, `lake build` 385/385 green). Discovery during this session — Reflection 65: Option B (GetElem instance + TokenStream parameters) lets the §5b/§5d/§5d′ proofs port **verbatim** (no token-shape dependency at all), and the §5a/§5e′ proofs need only an explicit `h_bridge : tokens[i] = tokens.tokens[i]` line to normalize `h`-hypotheses against the goal after the algebraic rewrites — much smaller diff than Option A's `.tokens` accessor pervasiveness would have been. **What's deferred**: the §5e mutual `ParseNodeWB` block (~600 LOC), §5e″ sub-parser well-behavedness (~1,500 LOC), §5e₂ token-array preservation (~100 LOC), §5f parseDocument scannability (~150 LOC), §5g parseStream output scannability (~150 LOC), §5f position monotonicity (~1,500 LOC), and §5c `scanFiltered_flow_aware_psv` (scanner-side dependency). All deferred to Step 6d.1c. | `Proofs/Parser/IndexedWellBehaved.lean` (extended), `Indexed/TokenStream.lean` (extended) | ~627 (landed) | 1 (actual) |
| **6d.1c** | **WellBehaved §5e + §5e″ + §5f + §5g port** — extend `IndexedWellBehaved.lean` with the structurally hard remainder of the C2 chain: the §5e mutual `ParseNodeWB` predicate + strong-induction proof; the §5e″ sub-parser well-behavedness theorems for the 11 mutually-recursive parser functions (`parseBlockSequenceLoop` / `parseBlockSequence` / `parseImplicitBlockSequenceLoop` / `parseImplicitBlockSequence` / `parseBlockMappingEntryValue` / `handleBlockMappingKeyEntry` / `handleBlockMappingValueEntry` / `parseBlockMappingLoop` / `parseBlockMapping` / `parseSinglePairMapping` / `parseExplicitKey` / `parseFlowMappingValue` / `parseFlowSequenceLoop` / `parseFlowSequence` / `parseFlowMappingLoop` / `parseFlowMapping`); §5f `parseDocument` scannability; §5g `parseStream` output scannability; the §5f position monotonicity chain. Plus the §5c bridge to an indexed `scan_flow_aware_psvIx` (or a deferred-axiom stand-in, depending on scanner-side readiness). The mutual block is the structural core — it states the combined `Scannable ∧ flowNesting-preservation` predicate and proves it for every sub-parser by strong induction on fuel. | `Proofs/Parser/IndexedWellBehaved.lean` (extended) | ~4,000 | 2–3 |
| **6d.2** | **WfaProofs** — `Proofs/Parser/IndexedWfa.lean` (~1,692 LOC), **moved here from the original Step 6c scope**. Re-proves `WellFormedAnchors`/`Scannable`/`AllAliasesResolve` preservation through `parseNode`. Consumes three WellBehaved lemmas directly (`parseNode_wb_all`, `parseNodeContent_wb`, `parseNodeProperties_tokens`), which is why it ships here rather than next to NodeProofs in 6c.1. Mechanical once 6d.1c's WB mutual block is sorry-free. | `Proofs/Parser/IndexedWfa.lean` | ~1,692 | 1 |
| **6d.3** | **Correctness + Completeness + Grammable** — `Proofs/Parser/{IndexedCorrectness,IndexedCompleteness,IndexedGrammable}.lean`. Composes the WB + Wfa chain to produce `parseStreamIx_output_valid_nodes`. Each file is purely a composition layer once 6d.1c + 6d.2 land. | `Proofs/Parser/IndexedCorrectness.lean`, `IndexedCompleteness.lean`, `IndexedGrammable.lean` | ~515 | 1 |
| **6e** | `IndexedComposition` — top-level `scanAndParseIx : String → Except _ (Array YamlDocument)` chaining `scanIx` then `parseStreamIx`. Exhibit end-to-end roundtrip on the Step 5c corpus via `native_decide` (extends `IndexedRoundtrip` with a parser-level check). | `Parser/IndexedComposition.lean`, `Proofs/Parser/IndexedComposition.lean` | ~250 | 1 |
| **6f** | **Atomic cutover commit**. Rename every staging `*Ix.lean` → production name (overwriting legacy: `IndexedScanner.lean` → `Scanner.lean`, `ParseStateIx.lean` → `State.lean`, `TokenParserIx.lean` → `TokenParser.lean`, etc.). Delete legacy `Scanner/{Scalar,Whitespace,Indent,SimpleKey,Document,NodeProperties,State}.lean`, all of `Proofs/Scanner/*` (~26,858 LOC across 23 files), and legacy `Proofs/Parser/{ParserWellBehaved,ParserCorrectness,ParserCompleteness,ParserGrammable,ParserNodeProofs,ParserWfaProofs,…}.lean`. Retarget `L4YAML.lean` imports. Single `lake build` green. | mass rename + delete | net **≈ −30,000** | 1 |

**Total**: 9–13 sessions for a clean rebuild + staged cutover. 6c
and 6d are the swing factors; if proof translation collapses to
mostly-mechanical substitution (rather than fresh strong-induction
arguments), those sub-steps run faster.

**Why this shape preserves Phase 3 invariants**:
- Every sub-step from 6a–6e compiles `lake build` green with no new
  `sorry`. The legacy stack stays live and untouched throughout.
- Sub-step 6f is the *only* commit that deletes legacy files, and
  it does so atomically with the staging-→-production rename. The
  ~30,000 LOC delete in one commit is large but mechanical: every
  file deleted in 6f has a staging counterpart that has been green
  for at least one prior commit.
- The `*Ix.lean` staging pattern is already proven at Phase 3 scale
  (`IndexedDispatch`, `IndexedPresenter`, `IndexedRoundtrip` all
  landed via the same discipline).

#### Step 6a — `ParseStateIx` staging *(landed)*

**Goal**: stand up the indexed parser state record and its
navigation primitives in a new staging file
`L4YAML/Parser/ParseStateIx.lean`. Production code only — no
proofs, no downstream imports. The legacy `Parser/State.lean`
remains untouched and continues to back the legacy parser.

**Scope (landed)**:
- `ParseStateIx (input : String)` — record holding
  `tokens : Indexed.TokenStream input` and a cursor `pos : Nat`,
  plus the same auxiliary state as legacy `ParseState`:
  `anchors`, `tagHandles`, `trackPositions`, `currentPath`,
  `nodePositions`. Explicit `Inhabited (ParseStateIx input)`
  instance built from `Indexed.TokenStream.empty input` (the
  derived instance won't work because `IxToken` carries proof
  fields — see reflection 61).
- Navigation primitives: `hasMore`, `peekIx?` (new — returns
  `Option (IxToken input)`), `peek?`, `peekPos?`, `advance`,
  `lastPos?`, `currentLine`. `peek?` and `peekPos?` are derived
  from `peekIx?` via `.map (·.token)` and `.map (·.start)`,
  consolidating the bound check.
- Token consumption helpers: `expect`, `tryConsume`.
- Constructor: `ParseStateIx.mk' : Indexed.TokenStream input →
  ParseStateIx input` (initial state, position 0, empty
  auxiliary state).
- Node-property scaffolding ported from legacy: `NodeProperties`,
  `resolveTag`, `parseNodeProperties` (`@[yaml_spec "6.9" 96]`),
  `emptyNode`, `applyNodeFinalization`, `validateNodeProps`.
  These manipulate `YamlValue` / `YamlPath` state, so they port
  verbatim modulo the `input` type parameter; they live in the
  state file rather than `TokenParserIx.lean` for symmetry with
  the legacy split (see `Parser/State.lean` module header).
- Total: **304 LOC, sorry-free**.

**Departures from legacy worth noting**:
- Legacy `peek?` reads `ps.tokens[ps.pos]!.val` (Array bang-index,
  which requires `Inhabited (Positioned YamlToken)`). The indexed
  twin can't bang-index `Array (IxToken input)` because `IxToken
  input` lacks an `Inhabited` instance (its `startLEStop` /
  `stopLEInput` fields are proofs that have no canonical default
  inhabitant). Rewrote the accessor chain around
  `Indexed.TokenStream.get?` instead, which sidesteps the
  `Inhabited` requirement entirely and is more proof-friendly
  (the `Option.map` shape rewrites with the indexed-substrate
  `get?` lemmas added in Phase 3 Step 1).
- `peekIx?` is new (returns the full `IxToken input` including
  start/stop and bound proofs). Legacy callers that did
  `match ps.peek?, ps.peekPos? with | some t, some p => …` had to
  defensively pattern-match two `Option`s; in the indexed parser
  a single `match ps.peekIx? with | some ix => …` covers both.
  Step 6b's `TokenParserIx` will use `peekIx?` when it needs both
  the token and its position simultaneously.

**Staging-namespace convention**: `L4YAML.TokenParser.Indexed`,
mirroring the Step 5b/5c `L4YAML.Scanner.Indexed` pattern. The
legacy `L4YAML.TokenParser.ParseState` and indexed
`L4YAML.TokenParser.Indexed.ParseStateIx` coexist without
collision while both are in the build.

**DONE**: `lake build` 385/385 green; sorry budget `0 → 0` in the
new file; no downstream imports added (the file is not referenced
from `L4YAML.lean`; lake auto-builds it because `lean_lib L4YAML`
globs submodules by default).

##### Reflection 61 — *Proof fields on `IxToken input` block `deriving Inhabited`; replace `[i]!` indexing with `get?` to keep the indexed parser state portable.*

Legacy `ParseState` uses `ps.tokens[ps.pos]!` (Array bang-index)
to read tokens after a manual bound check `ps.pos <
ps.tokens.size`. This pattern requires `Inhabited (Positioned
YamlToken)`, which legacy gets for free via `deriving Inhabited`
on `Positioned α`.

`IxToken input` cannot derive `Inhabited`:

```lean
structure IxToken (input : String) where
  start  : YamlPos
  token  : YamlToken
  stop   : YamlPos
  startLEStop  : start.offset ≤ stop.offset
  stopLEInput  : stop.offset ≤ input.utf8ByteSize
```

The last two fields are propositions about the first three —
they have no canonical default inhabitant without committing to
specific values for `start` / `stop` and proving the inequalities
hold. An explicit instance is possible (e.g., `start := stop := 0`
gives `startLEStop := Nat.le.refl` and `stopLEInput :=
Nat.zero_le _`), but it bakes in a "zero-positioned placeholder"
that has no semantic meaning for any non-empty token stream and
would weaken the disjointness guardrail.

Two ways to avoid the `Inhabited` requirement when porting
`ps.tokens[ps.pos]!`-shaped legacy code:

1. **`Indexed.TokenStream.get?` returning `Option (IxToken input)`** —
   pattern-match the `Option` or chain `.map` to project fields.
   This is the route taken for Step 6a's `peek?` / `peekPos?` /
   `lastPos?`. Trade-off: slightly more verbose at the call site,
   slightly more proof-friendly (the `Array.get?_eq_some` shape
   lemmas are well-stocked in the Lean stdlib).
2. **Roll the bang-index into a new `peekIx?` accessor** — return
   `Option (IxToken input)` once and derive `peek?` / `peekPos?`
   from it. Sidesteps repeating the bound check. Step 6a went
   this route as well: `peekIx?` is the primary accessor; the
   legacy-shape `peek?` and `peekPos?` are one-liners on top.
   This also gives `TokenParserIx` (Step 6b) a single accessor
   when it needs both the token's payload and its source position
   (which the 14 mutual functions repeatedly do for
   error-reporting and node-position tracking).

The lesson: **don't add `Inhabited (IxToken input)` instances
just to mirror legacy bang-index patterns — rewrite the indexing
shape instead.** The proof obligations on `IxToken` are
load-bearing for the indexed substrate's disjointness guardrail
(Phase 3 invariant: positions valid for one input cannot be
passed off as positions of another); introducing a "synthetic
zero" inhabitant would undermine the type-level discipline.

#### Step 6b — `TokenParserIx` + `FuelIx` staging *(landed)*

**Goal**: clone the mutually-recursive parser functions over
`ParseStateIx`. Output type is `Except ScanError (Array
YamlDocument)` (same as legacy — the parser produces a flat
document AST, not an indexed graph; the indexed-graph form is
Phase 4 RepGraph territory).

**Scope landed**:
- `Parser/FuelIx.lean` (~61 LOC) — `initialFuelIx ts := 4 *
  ts.tokens.size + 4`, keyed on `Indexed.TokenStream.size`. The
  formula matches `Parser/Fuel.lean` byte-for-byte; only the
  input type changes.
- `Parser/TokenParserIx.lean` (~647 LOC) — the full 18-function
  mutual block plus the stream-level grammar table and document
  driver:
  - **Mutual block** (`set_option maxHeartbeats 400000 in mutual`,
    structural recursion on `fuel`): `parseNodeContent`,
    `parseNode`, `parseBlockSequence`, `parseBlockSequenceLoop`,
    `parseImplicitBlockSequence`, `parseImplicitBlockSequenceLoop`,
    `parseBlockMapping`, `parseBlockMappingEntryValue`,
    `handleBlockMappingKeyEntry`, `handleBlockMappingValueEntry`,
    `parseBlockMappingLoop`, `parseFlowSequence`,
    `parseFlowSequenceLoop`, `parseFlowMapping`,
    `parseFlowMappingValue`, `parseExplicitKey`,
    `parseFlowMappingLoop`, `parseSinglePairMapping`.
  - **Stream/document layer** (outside the mutual block):
    `StreamState` + `StreamState.validNextToken`,
    `parseDirectives`, `prepareDocumentState`, `parseDocument`,
    `parseStreamLoop`, `parseStreamIx`.
- Top-level entry: `parseStreamIx {input : String} (tokens :
  Indexed.TokenStream input) (trackPositions : Bool := false) :
  Except ScanError (Array YamlDocument)`.

**Departures from legacy `Parser/TokenParser.lean`**:
- Every function carries an `{input : String}` implicit parameter
  so the state type `ParseStateIx input` is dependently typed.
- Token accessor: `IxToken.token` (was `Positioned.value`) and
  `IxToken.start` (was `Positioned.pos`).
- Random-access reads in `parseBlockMappingEntryValue` use
  `ps.tokens.get?` (returning `Option`) rather than `[i]!`.
  Reason: `IxToken input` carries the `startLEStop` /
  `stopLEInput` proof fields, which block deriving `Inhabited`,
  which `[i]!` requires. The match-on-`Option` rewrite is the
  same pattern Step 6a applied in `validateNodeProps`. See
  Reflection 61 (Step 6a) for the underlying constraint.
- All `@[yaml_spec ...]` attributes from the legacy parser are
  reproduced verbatim on the indexed twins. They're keyed by
  fully-qualified `declName`, so the two namespaces coexist
  without collision; at Step 6f cutover the legacy entries get
  deleted and the indexed entries become canonical.

**Namespace**: `L4YAML.TokenParser.Indexed` — keeps per-rule
function names unqualified (`parseNode`, `parseFlowSequence`, …)
without colliding with the legacy `L4YAML.TokenParser`
declarations. Only the top-level entry-point gets a suffix
(`parseStreamIx`) so external callers can distinguish the two
parsers during the staging period.

**Output type**: plain `Array YamlDocument` (no `input`
parameter). This is the L2 → L1 step of the four-stage pipeline,
where the type-level binding to `input` is erased — exactly the
shape downstream stages (`Compose`, `Serialize`) expect.

**Smoke testing**: deferred to Step 6e per the Step 6b plan
(behavioural parity with the legacy parser on the Step 5c corpus
sits naturally in `IndexedComposition.lean` next to the
`scanAndParseIx` entry point).

**DONE criteria**: `lake build` green (385/385 jobs); sorry
budget `0 → 0`; Guardrail 1 preserved (`L4YAML.lean` does not
import either file).

##### Reflection 62 — *`@[yaml_spec ...]` attributes are keyed by fully-qualified `declName`, so indexed and legacy twins coexist without collision; copy them verbatim.*

**Why:** `Spec/YamlSpec.lean` registers `yaml_spec` as a builtin
attribute backed by a `SimplePersistentEnvExtension` whose entries
are `Name × YamlSpecRef`. The `add` handler does
`modifyEnv fun env => yamlSpecExt.addEntry env (declName, ref)` —
keying purely on the fully-qualified name of the *decorated*
declaration. That means `L4YAML.TokenParser.parseNode` and
`L4YAML.TokenParser.Indexed.parseNode` register independent
entries even when both carry `@[yaml_spec "7.5" 161 …]`. Before I
checked, I almost stripped the indexed copies of their attributes
on the assumption they'd duplicate-key against the legacy parser
in `#yaml_spec_coverage`. They don't — both entries surface as
distinct declarations under the same production rule.

**How to apply:** when cloning a legacy file into a staging
namespace (`L4YAML.TokenParser.Indexed`, `L4YAML.Scanner.Indexed`,
…), preserve `@[yaml_spec ...]` annotations verbatim on every
function. The coverage report will list both the legacy and the
indexed declaration under each production rule during the
staging period; at the cutover commit (Step 6f / scanner Step 6),
the legacy declarations are deleted and the indexed entries become
the canonical (singleton) coverage. Symmetrically, do not
duplicate the *attribute definition* across namespaces — the
extension is a single environment-wide table keyed by
declaration name.

#### Step 6c.1 — Indexed NodeProofs *(landed)*

**Goal**: re-prove the `AG` (AnchorsGrow) and `AAR`
(AllAliasesResolve) propagation lemmas — every sub-parser preserves
`AG ps ps'` and every successful `parseNode` outputs a value whose
aliases all resolve against the (possibly grown) anchor map — against
the indexed parser stack landed in Step 6a/6b.

**Original Step 6c scope** was both `ParserNodeProofs.lean` (1,781
LOC) and `ParserWfaProofs.lean` (1,692 LOC). During scoping it
surfaced that `ParserWfaProofs` consumes three lemmas
(`parseNode_wb_all`, `parseNodeContent_wb`,
`parseNodeProperties_tokens`) directly from `ParserWellBehaved.lean`
(4,797 LOC, scheduled for Step 6d), so translating WfaProofs alongside
NodeProofs would have required porting a non-trivial WB fragment
*before* its natural home. We split Step 6c: 6c.1 lands NodeProofs
this session (no WB dependency), and the WfaProofs translation moves
into Step 6d alongside `IndexedWellBehaved` where the WB lemmas
naturally live (sub-plan ladder updated, see 6d row).

**Scope (landed in Step 6c.1)**:
- `L4YAML/Proofs/Parser/IndexedNodeProofs.lean` (~1,814 LOC,
  sorry-free) — indexed twin of `ParserNodeProofs.lean`. Reparented
  onto `ParseStateIx input` and the indexed `parseNode` in
  `L4YAML.TokenParser.Indexed`. Namespace
  `L4YAML.Proofs.Indexed.NodeProofs` (matches the Step 5b/5c
  `L4YAML.Scanner.Indexed` convention; renamed to
  `L4YAML.Proofs.ParserNodeProofs` at cutover).

**Structural changes from legacy** (3, all mechanical):
1. **State type substitution** — `(ps : ParseState)` →
   `(ps : ParseStateIx input)` everywhere in theorem signatures and
   `variable` declarations. The `{input : String}` implicit is
   threaded via a single `variable {input : String}` declaration at
   the top of the file (active before all theorems).
2. **Accessor namespace** — `ParseState.advance` →
   `ParseStateIx.advance`; same for `tryConsume`, `addAnchor`. The
   bodies of the helper theorems (e.g., `AG.advance`, `AG.tryConsume`)
   use the new `ParseStateIx.X` accessors directly.
3. **Predicate signatures** — `def ParseNodeAG (n : Nat) : Prop` →
   `def ParseNodeAG (input : String) (n : Nat) : Prop` (`input`
   **explicit**, not implicit — see Reflection 63). The 17 `_ag` and
   17 `_aar` sub-parser theorems that take `(h_ih : ParseNodeAG n)` /
   `(h_ih_aar : ParseNodeAAR n)` hypotheses all rewrite to
   `ParseNodeAG input n` / `ParseNodeAAR input n` at the hypothesis
   site.

**What did not need touching**:
- `AllAliasesResolve`, `WellFormedAnchors`, `AG`, `AAR.mono`,
  `aar_retag_*`, `aar_push`, `applyNodeFinalization_aar`,
  `emptyNode_aar`, `items_push_aar`, `pairs_push_aar`,
  `parseNode_aliases_resolve'` — all preserved verbatim modulo the
  state-type substitution.
- The bridge lemma `any_name_implies_findSome_isSome'` is copied into
  the indexed namespace (it was a self-contained Array lemma in the
  legacy file too; the staging copy avoids cross-importing the
  legacy `ParserNodeProofs` and keeps the 6f cutover clean).
- Every tactic block. The `unfold_loop_at` elab tactic was carried
  over without changes — it pattern-matches on `loop`-suffixed
  constants by name, not by their parser provenance.
- All `maxHeartbeats` overrides — except `parseSinglePairMapping_ag`,
  which was bumped from 800,000 to 1,600,000. The 17-arm cascade of
  `split <;> first | contradiction | skip` plus the bidirectional
  trans-chain construction (4 closing variants × 2 trans depths) hit
  `whnf` timeout in the indexed setting where each `ParseStateIx
  input` unification carries the `input : String` proof obligation.
  No other proof in the file needed adjustment, including the parallel
  `parseSinglePairMapping_aar` (which inherited the 800,000 bump from
  the legacy file).

**DONE criteria** (all met):
- `L4YAML/Proofs/Parser/IndexedNodeProofs.lean` builds via
  `lake build L4YAML.Proofs.Parser.IndexedNodeProofs` (41/41).
- `lake build` full: 385/385 green (legacy stack untouched).
- Sorry budget: 0 → 0 in the new staging file; legacy `EmitterScannability`
  carries 7 pre-existing sorries (untouched).

##### Reflection 63 — *Induction-hypothesis predicates with `input : String` must take it explicitly, not implicitly: the predicate returns `Prop` so there's no result-type slot for Lean to unify `input` against at hypothesis sites.*

**Why**: The legacy `ParseNodeAG` predicate is
`def ParseNodeAG (n : Nat) : Prop := ∀ (ps : ParseState) ..., AG ps ps'`.
The indexed twin needs `(ps : ParseStateIx input)`, so `input` becomes
a free variable in the body. The naive translation makes it implicit
via the file-scope `variable {input : String}` — Lean then sees a
predicate of type `{input : String} → Nat → Prop`. At every theorem
that takes `(h_ih : ParseNodeAG n)` as a hypothesis (17 such theorems
in the AG family + 17 in the AAR family), Lean must elaborate
`ParseNodeAG n` to a fully-applied `Prop`. To do that it needs to
synthesise the implicit `input`, but `ParseNodeAG` is a *definition*
returning `Prop` — there is no place in the result type where `input`
appears that could constrain it from the goal. **And** the
elaboration order is "all parameter types resolved before the proof
is processed", so a later parameter like `(ps : ParseStateIx input)`
doesn't help: Lean cannot peek forward to take `input` from the type
of a not-yet-introduced parameter. Result: `error: don't know how to
synthesize implicit argument 'input'` at every hypothesis site.

**How to apply**: When porting an induction-hypothesis-style predicate
to indexed types, make the type parameter **explicit**:
`def ParseNodeAG (input : String) (n : Nat) : Prop := …`. Hypothesis
sites then read `(h_ih : ParseNodeAG input n)` — the explicit `input`
fixes the value before the elaborator needs it. This is symmetric to
how function signatures fix dependent-typed arguments: the rule
generalises beyond predicates to any auxiliary `Prop` / `Type`
definition that has a structural parameter (e.g., `input : String`,
`tokens : Array …`, a state record) but whose result discards that
parameter. *Look for it whenever you have a predicate whose definition
takes a structural parameter that does not appear in its return type
— that's the danger signature.* This is the third "implicit-vs-explicit
parameter" finding in the indexed port: Reflection 61 (proof
fields blocking `Inhabited`) and Reflection 62
(`@[yaml_spec ...]` keyed by `declName`) were both about types and
attributes; this one is about predicate-level induction hypotheses.

##### Reflection 64 — *A wrapping container type (`TokenStream input` around `Array (IxToken input)`) reshapes a "purely mechanical" port: equalities that compose in the legacy setting via `Eq.trans` now type-check only after explicit `.tokens` projection, and any tactic that pattern-matches on the wrapped accessor (`peek?`) needs a different shape.*

**Why**: The legacy `ParseState.tokens : Array (Positioned YamlToken)`
is a *flat* array, so a theorem returning `ps'.tokens = ps.tokens`
and a hypothesis `h : ps.tokens = tokens` compose with a single
`Eq.trans` — both sides are the same `Array` type. In the indexed
setting, `ParseStateIx.tokens : Indexed.TokenStream input`, where
`TokenStream input := { tokens : Array (IxToken input) }` is a
single-field wrapper. A naive mechanical port keeps the supporting
predicates (`flowNesting`, `PlainScalarsValid`, …) over
`Array (IxToken input)` and writes hypotheses as `ps.tokens.tokens
= tokens` (TokenStream → Array bridge), which type-checks one
hypothesis at a time but **breaks composition**: a theorem
returning `ps'.tokens = ps.tokens` (TokenStream equality) no
longer chains with `Eq.trans` against `ps.tokens.tokens = tokens`
(Array equality) — the middle type differs. Trying to fix this by
inserting `.tokens.tokens` everywhere cascades: 139+ sites need
adjustment, and several `simp` / `subst` tactics that depended on
the un-wrapped shape break in non-obvious ways.

Separately, the indexed `ParseStateIx.peek?` is implemented as
`Option.map IxToken.token ps.peekIx?` (the indexed
peek returns `Option (IxToken input)` carrying the bound proof; the
non-indexed `peek?` drops the bound via `Option.map`). The legacy
`ParseState.peek?` is `tokens[pos]?.map (·.val)`. The
`peek_some_bounded` bridge — which proves
`ps.peek? = some tok → ps.pos < ps.tokens.size ∧
(ps.tokens[ps.pos]'h).val = tok` — uses `unfold ParseState.peek?
at h; split at h; …`. That tactic cannot split the indexed `h :
Option.map IxToken.token ps.peekIx? = some tok` because the
`Option.map` wrapper has to be peeled (e.g., via
`Option.map_eq_some`) before the underlying `peekIx?` can be
case-analysed.

**How to apply**: When porting proofs against a substrate that
*wraps* a previously-flat data structure, the mechanical-substitution
mental model breaks twice — at equality-chain composition and at
tactics keyed on the un-wrapped accessor. Treat the port as a
**bridging design problem**, not a `cp + sed`. The two viable
strategies are:

1. **Push the wrapper down**: make the supporting predicates take
   the wrapper type (`Indexed.TokenStream input`) and add a
   `GetElem` instance so legacy `tokens[i]'h` notation still
   compiles. Eliminates the equality-chain mismatch; smaller diff
   in the proof bodies; one new instance.
2. **Bridge at every use site**: keep the predicates over the
   un-wrapped array and insert `.tokens` accessors at every
   wrapped use site. More edits; cascading `Eq.trans` adjustments;
   pattern-matching tactics still need new shapes.

Pick strategy 1 (recommended). Two-session split: 6d.1a
(infrastructure: supporting predicates + step lemmas; this commit)
+ 6d.1b (full C2 + position-monotonicity port against the
strategy-1 bridging). *This is the second "container-vs-naked" port
finding in the indexed cutover: Reflection 61 was about proof
fields blocking `Inhabited`; this one is about a single-field
wrapper breaking `Eq.trans` chain composition.*

**Process lesson**: when copy-substitution on a large legacy file
produces 100+ errors after the obvious passes, **stop and
diagnose the structural delta**, do not iterate per-error fixes.
The Step 6d.1a infrastructure-only commit landed in one session;
the WIP attempt at the full port would have produced an unlandable
commit (broken file + 100+ errors). Splitting on the first
structural surprise — and committing the infrastructure clean — is
faster overall than driving error counts down for half a session
and then aborting.

##### Reflection 65 — *Choosing the right `@[simp]` cardinality for a `GetElem` bridge lemma matters: an over-eager bridge auto-fires inside `simp [h]` calls and de-syncs hypothesis and goal forms, even when the bridge itself is `rfl`.*

**Why**: Step 6d.1b implemented Option B (Reflection 64) — a new
`GetElem (TokenStream input) Nat (IxToken input)` instance on
`Indexed.TokenStream` plus a `getElem_eq_tokens_getElem :
ts[i]'h = ts.tokens[i]'h` bridge lemma. The first attempt marked
the bridge `@[simp]`, reasoning that `tokens[i]` and
`tokens.tokens[i]` are definitionally equal anyway, so the
auto-rewriting should be invisible. It wasn't.

Concretely, in `flowNestingIx_pos_after_flow_start` the proof has
a hypothesis `h : (tokens[i]'hi).token = .flowSequenceStart` and a
goal (after the algebraic `rw` chain via `flowNestingIx_split_step`
+ `flowNestingIx_go_step` + `flowNestingIx_go_ge_target`) of the
shape `(match (tokens.tokens[i]'hi).token with | .flowSequenceStart
=> depth + 1 | … ) = depth + 1`. The `simp [h]` tactic should
substitute `h`'s LHS into the goal. With `@[simp]
getElem_eq_tokens_getElem` registered, `simp` first normalizes both
sides: it rewrites `tokens[i]` to `tokens.tokens[i]` in *h itself*
(via the simp lemma) before applying `h` as a rewrite — but the
goal already has `tokens.tokens[i]`. The result was Lean reporting
the goal *unchanged* because `simp` had already canonicalized `h`'s
LHS to a form that *did* match the goal, but then the
`tokens.tokens[i]` form in `h` lost its inferred bound proof
relationship to the goal's `hi'` (where `hi : i < tokens.size` and
`hi' : i < tokens.tokens.size` are different `Prop` terms despite
being defeq).

Removing the `@[simp]` attribute and writing an explicit
`have h_bridge : (tokens[i]'hi) = (tokens.tokens[i]'hi') := …`
before the `rw [h_bridge] at h` line made the proof go through
cleanly. The bridge is invoked at exactly one site per theorem
(6 sites in §5a + 1 in §5e′ helpers), where its rewriting
direction is unambiguous.

**How to apply**: When introducing a `GetElem` instance + bridge
lemma to thread a wrapper type through proofs, prefer the
**non-`@[simp]` form** of the bridge. Reasons:

1. **The bridge is `rfl`** — Lean's elaborator already unifies the
   two forms in type-checking. The simp lemma adds nothing new for
   elaboration; it only changes *which* form `simp` canonicalizes
   to. That choice is wrong roughly as often as it's right.
2. **`simp [h]` calls** apply `h` as a rewrite, but they also
   pre-normalize via registered `@[simp]` lemmas. If the bridge
   pre-rewrites `h` into a form that no longer matches the goal's
   bound-proof structure, the `simp [h]` becomes a silent no-op.
3. **The fix per site is one line** — `have h_bridge : … := …`
   followed by `rw [h_bridge] at h`. Less code than diagnosing
   why `simp` didn't fire.

This is the indexed port's third "auto-firing simp lemma misfires"
finding: Reflection 51 (auto-firing `@[simp]` on a structural
projection breaks pattern recognition), Reflection 58
(`@[simp]` on `OfNat` coercions interferes with `decide`-style
goals), and now Reflection 65 (`@[simp]` on a `GetElem` bridge
breaks `simp [h]` calls that should substitute a hypothesis).

**Pattern**: every time you reach for `@[simp]` on a bridge lemma
between two definitionally-equal forms, ask: "is one of those
forms strictly preferable as the canonical form, in every site
where the bridge could fire?" If the answer is *no, both forms are
used naturally in different proofs*, leave the `@[simp]` off and
invoke the bridge by name where needed.

#### Step 6d.1a — Indexed WellBehaved supporting infrastructure *(landed)*

**Goal**: stage the indexed supporting predicates and `flowNestingIx.go`
step lemmas that the full `IndexedWellBehaved` port (6d.1b) will
rest on.

**Scope (landed in Step 6d.1a, ~210 LOC, sorry-free)**:
- `Proofs/Parser/IndexedWellBehaved.lean` (initial check-in):
  - `flowNestingIx` — indexed twin of
    `ScannerPlainScalarValid.flowNesting`, structurally identical
    over `Array (IxToken input)` with `.token` instead of `.val`.
  - `PlainScalarsValidIx` / `FlowContextPSVIx` / `FlowAwarePSVIx` /
    `FlowBracketsMatchedIx` — indexed twins of their legacy
    counterparts.
  - `flowNestingIx_go_oob` / `_go_step` / `_go_ge_target` /
    `_go_split` — the four algebraic step lemmas that the §5a
    bridge lemmas (`flowNestingIx_split_step`,
    `_pos_after_flow_start`, `_after_flow_start_eq`,
    `_after_flow_end`, `_non_flow_step`, `_beyond_size`) need.
    Pre-landing them here keeps Step 6d.1b focused on the C2-chain
    substitution rather than on the underlying algebraic facts.

**Why split 6d.1 into 6d.1a + 6d.1b**: discovery during the Step
6d.1 work-in-progress session (Reflection 64). The port of
`ParserWellBehaved.lean` (~4,797 LOC) is **not** a pure mechanical
substitution like Step 6c.1's `IndexedNodeProofs`:

1. **TokenStream vs Array indirection.** `Indexed.TokenStream input`
   is a single-field wrapper around `Array (IxToken input)` (see
   `L4YAML/Indexed/TokenStream.lean`). `ParseStateIx.tokens :
   Indexed.TokenStream input` therefore needs an extra `.tokens`
   accessor (or a `GetElem` instance) to bridge with the
   `Array (IxToken input)` parameters that the supporting
   predicates (`flowNestingIx`, `PlainScalarsValidIx`, …) take.
   Legacy `ParseState.tokens : Array (Positioned YamlToken)` had no
   such indirection, so the WB proofs intermix `ps.tokens = tokens`
   (Array equality) and `ps'.tokens = ps.tokens` (Array equality)
   freely. In the indexed setting these are two different types
   (TokenStream vs Array), and the `Eq.trans` chains in the
   position-monotonicity proofs (§5f) need explicit `.tokens`
   accessor insertion to compose.

2. **`peek?` shape divergence.** The indexed
   `ParseStateIx.peek? : ParseStateIx input → Option YamlToken` is
   defined as `Option.map IxToken.token ps.peekIx?` (see
   `L4YAML/Parser/ParseStateIx.lean`), where `peekIx?` returns the
   bound-carrying `Option (IxToken input)`. The legacy
   `ParseState.peek?` is a plain `tokens[pos]?.map (·.val)`. The
   `peek_some_bounded` bridge lemma in §5 — which proves
   `ps.peek? = some tok → ps.pos < ps.tokens.size ∧
   (ps.tokens[ps.pos]'h).val = tok` — uses `unfold
   ParseState.peek?; split at h; …`. That tactic doesn't apply to
   the indexed `peek?` because the `Option.map` wrapper has to be
   peeled before the underlying `peekIx?` can be `split`. The
   indexed bridge needs a different proof shape (likely two
   `Option.map_eq_some` unfolds).

3. **Scanner-side `scan_flow_aware_psv` dependency.** The §5
   C2-bridge proofs (`scalar_from_token_scannable`,
   `scalar_from_flow_token_scannable`) themselves do not need a
   scanner producer — but `parseStream_output_scannable` invokes
   `scan_flow_aware_psv input scanned_tokens` from
   `Proofs.Production.ScannerPlainScalarValid` to obtain the
   `FlowAwarePSV` precondition. That producer is keyed on
   `Array (Positioned YamlToken)`. The indexed C2 chain needs an
   indexed producer (`scan_flow_aware_psvIx`) emitting
   `FlowAwarePSVIx ts.tokens` for the indexed scanner's output —
   itself a scanner-side port that either (a) front-loads into
   Step 6d.1b, or (b) front-loads into an earlier scanner-side
   Step 6d.0 if the scope grows past one session.

**Status**: `lake build` 385/385 green, sorry budget 0 → 0.

#### Step 6d.1b — Indexed WellBehaved §5-§5e′ pre-mutual-block port *(landed)*

**Goal**: settle the TokenStream-vs-Array bridging strategy
(Reflection 64), then port the loosely-coupled, pre-mutual-block
sections of `ParserWellBehaved.lean` to the indexed substrate.

**Bridging strategy chosen (Option B)**: a new `GetElem (TokenStream
input) Nat (IxToken input)` instance in `L4YAML/Indexed/TokenStream.lean`
lets `tokens[i]'h` indexing work uniformly on `TokenStream` parameters,
eliminating the `Eq.trans`-chain breakage that Option A's `.tokens`
accessor pervasiveness would have introduced. The 5 supporting
predicates (`flowNestingIx`, `PlainScalarsValidIx`,
`FlowContextPSVIx`, `FlowAwarePSVIx`, `FlowBracketsMatchedIx`)
re-target from `Array (IxToken input)` to `Indexed.TokenStream
input` with no functional change to their bodies.

**Scope (landed in Step 6d.1b, ~613 LOC delta in `IndexedWellBehaved.lean`
+ 14 LOC `GetElem` instance, sorry-free)**:

- **Foundation switchover**:
  - `GetElem (Indexed.TokenStream input) Nat (IxToken input) (fun ts
    i => i < ts.size)` instance + `getElem_eq_tokens_getElem` bridge
    lemma (non-`@[simp]` to avoid destabilizing downstream proofs).
  - Predicate parameter type switch: 5 predicates now keyed on
    `Indexed.TokenStream input`; the internal `flowNestingIx.go`
    stays on `Array (IxToken input)` so the algebraic step lemmas
    keep their simple form.

- **§5 C2 Infrastructure** (5 lemmas):
  - `ScalarScannable_strengthen` — verbatim from legacy (`Scalar` is
    not indexed by `input`).
  - `scalar_from_token_scannable_ix`,
    `scalar_from_flow_token_scannable_ix` — token-typed bridge
    lemmas re-targeted onto `TokenStream` + `IxToken.token`.
  - `empty_scalar_scannable` — verbatim (purely `YamlValue`-typed).
  - `peek_some_bounded_ix` — **new proof shape** (Reflection 64
    point 2): the indexed `peek?` factors through `peekIx?` →
    `TokenStream.get?` → underlying `Array.get?`. The new proof
    `unfold`s those three layers and applies
    `Option.map_eq_some_iff` + `Array.getElem?_eq_some_iff`,
    landing in three `Option`-rewriting steps rather than the
    legacy single `getElem!_pos` pass.

- **§5a flowNesting step lemmas** (6 lemmas):
  `flowNestingIx_split_step`, `_pos_after_flow_start`,
  `_after_flow_start_eq`, `_after_flow_end`, `_non_flow_step`,
  `_beyond_size`. Each proof needs one extra `h_bridge :
  (tokens[i]'hi) = (tokens.tokens[i]'hi')` line to normalize the
  hypothesis form against the goal after the algebraic rewrites
  via `flowNestingIx_split_step` + `flowNestingIx_go_step` +
  `flowNestingIx_go_ge_target`.

- **§5b Scannable monotonicity** (2 lemmas):
  `Scannable_true_implies_false`, `Scannable_any_implies_false`.
  Verbatim ports — purely on `YamlValue` and `Scannable`; no
  token-shape dependency.

- **§5d Scannable for tag/anchor modification** (1 lemma):
  `Scannable_attach_props`. Verbatim port — purely `YamlValue`-
  typed.

- **§5d′ applyNodeFinalization preservation** (4 lemmas):
  `applyNodeFinalization_scannable_ix`, `_tokens_ix`, `_pos_ix`,
  `_trackPositions_ix`. Re-targeted onto the indexed
  `applyNodeFinalization` in `Parser/ParseStateIx.lean`.

- **§5e′ parseNodeProperties preservation** (4 declarations +
  1 file-local `@[simp]` + verbatim `unfold_loop_at_ix` elaborator):
  `parseNodeProperties_tokens_ix`,
  `parseNodeProperties_flowNesting_ix`, plus the helper
  `advance_preserves_flowNestingIx`,
  `advance2_preserves_flowNestingIx`, and the file-local
  `advance_tokens_eq_ix` `@[simp]` lemma (named `_eq_ix` to avoid
  the `ParseStateIx` structure-namespace collision discovered in
  Step 6d.1a's WIP work).

**Discovery — Reflection 65**: Option B (GetElem instance +
TokenStream parameters) lets §5b/§5d/§5d′ port **verbatim** (these
sections have no token-shape dependency at all), and §5a/§5e′ need
only a one-line `h_bridge` normalization between
`(tokens[i]'hi)` (TokenStream indexing) and `(tokens.tokens[i]'hi')`
(Array indexing). This is a much smaller diff than Option A's
~150 `.tokens` accessor insertions would have produced, and it
matches the parser-state-touching shape uniformly across the
chain. The `@[simp]` `getElem_eq_tokens_getElem` bridge lemma was
initially attempted but caused destabilization in `simp [h]` calls
where `h` contained `tokens[i]` and the goal had `tokens.tokens[i]`
— removing the `@[simp]` attribute and using a manual `h_bridge`
line per site was cleaner.

**What's deferred to Step 6d.1c** (~4,000 LOC remaining):
- **§5e mutual `ParseNodeWB` block** (~600 LOC): the combined
  `Scannable ∧ flowNesting-preservation ∧ tokens-preservation`
  predicate, the `parseNodeWB_apply` projection helpers, and the
  strong-induction `parseNode_wb_all` theorem over fuel.
- **§5e″ sub-parser well-behavedness** (~1,500 LOC): 11
  mutually-recursive sub-parser WB theorems
  (`parseBlockSequenceLoop_wb` through `parseFlowMapping_wb`).
- **§5e₂ token-array preservation** (~100 LOC): helper lemmas for
  the §5f scannability proofs.
- **§5f parseDocument scannability** (~150 LOC).
- **§5g parseStream output scannability** (~150 LOC).
- **§5f position monotonicity chain** (~1,500 LOC):
  `ParseNodePosMono` + 11 sub-parser monotonicity theorems.
- **§5c `scanFiltered_flow_aware_psv`**: scanner-side dependency
  that needs an indexed twin (`scan_flow_aware_psvIx`) or a bridge
  lemma from `FlowAwarePSV ts.tokens` to `FlowAwarePSVIx ts`.

**Status**: `lake build` 385/385 green, sorry budget 0 → 0.

#### Step 6d.1c — Indexed WellBehaved §5e mutual block + §5f/§5g + position monotonicity *(planned)*

**Goal**: complete the `IndexedWellBehaved.lean` port — the §5e
mutual `ParseNodeWB` block, §5e″ sub-parser well-behavedness, §5e₂
preservation helpers, §5f parseDocument scannability, §5g parseStream
output scannability, the §5f position monotonicity chain, and the
§5c scanner-side bridge — against the §5-§5e′ infrastructure landed
in 6d.1b.

**Scope** (~4,000 LOC of porting):

- **§5e mutual block** — define `ParseNodeWB tokens n` over
  `Indexed.TokenStream input` and the indexed `parseNode`; prove
  `parseNodeWB_apply`, `parseNode_scannable_false`,
  `parseNode_scannable_true`, `parseNode_flowNesting`,
  `parseNode_tokens` (the 4 single-projection extractors); and the
  big `parseNode_wb_all` strong-induction theorem. The
  mutually-recursive structure carries to the indexed parser
  verbatim modulo state-type substitution: indexed `parseNode` in
  `Parser/TokenParserIx.lean` has the exact same 14-function
  mutual-block shape as legacy `parseNode`.

- **§5e″ sub-parser WB** — port the 11 sub-parser well-behavedness
  theorems. The `_h_fpsv : FlowAwarePSV tokens` precondition becomes
  `_h_fpsv : FlowAwarePSVIx tokens`. The `tryConsume_tokens` /
  `tryConsume_flowNesting` / `tryConsume_with_path_*` helper lemmas
  need indexed twins; their proofs are likely verbatim modulo state
  type.

- **§5e₂ preservation helpers** — `parseDirectives_tokens` and
  `parseNode_tokens_preserved` ports.

- **§5f parseDocument scannability** —
  `prepareDocumentState_tokens_preserved`,
  `parseDocument_tokens_preserved`, `parseDocument_value_cases`,
  `parseDocument_scannable`.

- **§5g parseStream output scannability** — `expect_tokens`,
  `parseStreamLoop_docs_from_parseDocument`,
  `parseStream_doc_from_parseDocument`,
  `parseStream_output_scannable`.

- **§5f position monotonicity** — `ParseNodePosMono` predicate +
  the 11 sub-parser position-monotonicity theorems. ~1,500 LOC of
  proofs that need to thread through the same indexed parseNode
  mutual recursion as the §5e block, but for the position field
  rather than the value/flowNesting.

- **§5c scanner-side bridge** — either:
  - **Option α (front-load)**: write an indexed
    `scan_flow_aware_psvIx : Scanner.scanFilteredIx input ts → FlowAwarePSVIx ts`
    that ports the scanner-side `scan_flow_aware_psv` chain in
    `Proofs/Production/ScannerPlainScalarValid.lean`. Estimated ~1
    session of scanner-side work.
  - **Option β (axiom-bridge)**: state
    `axiom scan_flow_aware_psvIx_axiom : …` in
    `IndexedWellBehaved.lean` as a forward reference, prove it
    later. Keeps 6d.1c sorry-free but introduces a temporary axiom
    that must be discharged before Phase 3 close-out.

  Recommended: **Option β** (axiom-bridge) to keep 6d.1c focused
  on the parser-side port; the scanner-side bridge lands as its
  own follow-up Step 6d.1d (or rolls into Step 6f cutover prep).

**DONE criteria**: `IndexedWellBehaved.lean` covers the entire
`ParserWellBehaved.lean` surface (legacy 4,797 LOC vs landed scope),
sorry-free (modulo Option β's temporary axiom, if chosen), `lake
build` green. Estimated 2–3 sessions.

#### Step 6d.2 — Indexed Wfa *(planned)*

**Scope**: `Proofs/Parser/IndexedWfa.lean` (~1,692 LOC) — **moved
here from the original Step 6c scope**. Re-proves
`WellFormedAnchors`/`Scannable`/`AllAliasesResolve` preservation
through `parseNode`. Consumes three WellBehaved lemmas directly
(`parseNode_wb_all`, `parseNodeContent_wb`,
`parseNodeProperties_tokens`), which is why it ships in 6d
alongside `IndexedWellBehaved` rather than next to NodeProofs in
6c.1. Mechanical once those WB dependencies are in place.

**DONE criteria**: sorry-free, `lake build` green. Estimated 1
session.

#### Step 6d.3 — Indexed Correctness + Completeness + Grammable *(planned)*

**Scope**:
- `Proofs/Parser/IndexedCorrectness.lean` (~170 LOC): parsed
  output satisfies the grammar spec (`ValidNode` witness).
- `Proofs/Parser/IndexedCompleteness.lean` (~230 LOC): grammable
  values have grammar witnesses (the soundness roundtrip).
- `Proofs/Parser/IndexedGrammable.lean` (~115 LOC): composes
  correctness + completeness to discharge the `h_grammable`
  obligation.

**Risk** (carried over from previous draft): `ParserWellBehaved`'s
per-rule strong-induction tactics may quote `Array.get?_some` /
`Array.size_set` shape lemmas that have different statements for
`TokenStream`. Where the indexed substrate lacks a needed lemma,
it goes into `Indexed/TokenStream.lean` (not the proof file). If a
missing lemma cannot be stated without extending Phase 1's algebra,
**stop and re-open Phase 1** (Guardrail 2).

**DONE criteria**: all three files sorry-free, `lake build` green.
Estimated 1 session.

#### Step 6e — `IndexedComposition` + end-to-end roundtrip *(planned)*

**Goal**: wire the indexed scanner and indexed parser into a
top-level `scanAndParseIx : String → Except ScanError (Array
YamlDocument)` and exhibit the full pipeline on the Step 5c
corpus.

**Scope**:
- `Parser/IndexedComposition.lean` — defines `scanAndParseIx`
  by chaining `scanIx` then `parseStreamIx`.
- `Proofs/Parser/IndexedComposition.lean` — for each input in the
  Step 5c corpus (extended to cover parser-relevant inputs like
  `"a: b"`, `"- x"`, etc. as the parser-side corpus matures),
  `scanAndParseIx input = .ok docs` for the expected `docs`. By
  `native_decide`.

**Design notes**:
- The composition's signature matches legacy `scanAndParse` so
  that the 6f cutover only needs to rename the file and update
  the `L4YAML.lean` import — no signature changes ripple into
  external callers.
- This sub-step is the parser-level analogue of Step 5c
  (`IndexedRoundtrip`): a corpus-exhibited end-to-end property
  with no symbolic reasoning, gated by the `native_decide` budget.

**DONE criteria**: both files sorry-free, `lake build` green,
corpus covers at least 5 parser-relevant inputs end-to-end.

#### Step 6f — Atomic cutover commit *(planned)*

**Goal**: in a single commit, promote every staging `*Ix.lean`
file to its production name, delete the legacy scanner and parser
stacks, and retarget `L4YAML.lean` imports.

**Mechanics**:
1. Rename: `Scanner/IndexedScanner.lean` → `Scanner/Scanner.lean`
   (overwrites legacy), `Scanner/IndexedDispatch.lean` →
   `Scanner/Dispatch.lean`, `Scanner/IndexedPresenter.lean` →
   `Scanner/Presenter.lean`, `Parser/ParseStateIx.lean` →
   `Parser/State.lean` (overwrites legacy), `Parser/TokenParserIx.lean`
   → `Parser/TokenParser.lean`, `Parser/FuelIx.lean` →
   `Parser/Fuel.lean`, `Parser/IndexedComposition.lean` →
   `Parser/Composition.lean`. Same for the `Proofs/Parser/Indexed*.lean`
   staging files → production names.
2. Delete: legacy `Scanner/{Scalar,Whitespace,Indent,SimpleKey,Document,NodeProperties}.lean`
   (the legacy `Scanner/Scanner.lean` and `Parser/{State,TokenParser,Fuel,Composition}.lean`
   are overwritten by step 1, so they don't need explicit deletion).
   Delete all of `Proofs/Scanner/*.lean` (~26,858 LOC across 23 files)
   and legacy `Proofs/Parser/{ParserWellBehaved,ParserCorrectness,ParserCompleteness,ParserGrammable,ParserNodeProofs,ParserWfaProofs,…}.lean`.
3. Retarget `L4YAML.lean`'s import list: remove obsolete imports,
   confirm all `Indexed*` references are updated to bare names.

**DONE criteria**: `lake build` 100% green in this single commit;
sorry budget unchanged from 6e (carry-forward only); the cutover
commit message body explicitly states the net LOC delta
(≈ −30,000 expected).

</details>

<details><summary>Sub-plan guardrails.</summary>

**Sub-plan guardrails**:
- Each of steps 1–5 (and each Step 6 sub-step 6a–6e) commits with
  `sorry: N → 0` (or `0 → 0`) in the *new* indexed/staging files;
  the legacy sorry count is untouched (the legacy scanner still
  has open sorries today; those are obsoleted, not fixed, by Step
  6f).
- Step 6f must show `lake build` green in the cutover commit
  message body.
- If any step surfaces a missing algebra item, **stop and re-open
  Phase 1** (Guardrail 2). Do not quietly add a 24th item.

</details>

</details>

</details>

### Phase 4 — Stage B (parser) on indexed types

<details><summary>Re-implement parser to consume `TokenStream input` and produce `RepGraph input range`; integrate `LoadConfig` and `AnchorMap`; bidirectional verification of Stage-B rules.</summary>

**Goal**: replace the parser with one that consumes `TokenStream input`
and produces `RepGraph input range`, verified bidirectionally.

**DONE criteria**:
- (i) Parser re-implemented atomically; legacy deleted in cutover.
- (ii) Every Stage-B YAML 1.2.2 rule (nodes, blocks, flows, document
  structure) verified in both directions (`compose`, `serialize`).
- (iii) `LoadConfig` integrated: `EqMode` and `DuplicateKeyPolicy`
  threaded through the parser.
- (iv) `AnchorMap` (Item 12) integrated for alias resolution.
- (v) Sorry count = 0 in `L4YAML/Parser/` and
  `L4YAML/Proofs/Parser/`.

</details>

### Phase 5 — Stage A (document) + ToYaml / FromYaml

<details><summary>Lift `ToYaml`/`FromYaml` typeclasses onto indexed `RepGraph`; round-trip law proved per instance; extend the derived-instance generator.</summary>

**Goal**: lift the `ToYaml` / `FromYaml` typeclasses to operate on
indexed `RepGraph` and verify the round-trip law for every primitive
instance + a derived-instance generator (similar to Lean's existing
`deriving`).

**DONE criteria**:
- (i) `ToYaml`, `FromYaml`, `FromYamlType` typeclasses migrated to
  consume / produce indexed types.
- (ii) Round-trip law `fromYaml? ∘ toYaml = some` proven for every
  instance in `Schema/FromToYaml.lean`.
- (iii) Derived-instance generator (analogous to current
  `Schema/Deriving.lean`) extended for indexed types.
- (iv) Sorry count = 0 in `L4YAML/Schema/`.

</details>

### Phase 6 — Capstone: end-to-end roundtrip

<details><summary>Prove `construct ∘ compose ∘ parse ∘ present ∘ serialize ∘ represent = some` end-to-end; re-attack Tier 2 emitter-scannability from the new foundation.</summary>

**Goal**: prove the end-to-end roundtrip theorem.

**DONE criteria**:
- (i) Theorem
  `∀ (α : Type) [ToYaml α] [FromYaml α] [LawfulRoundTrip α] (a : α),`
  `construct (cfg := {}) (compose (parse (present (serialize (represent a))))) = some a`
  proven sorry-free.
- (ii) Tier 2 emitter-scannability (the original Initiative 3
  motivation) re-attacked from the new foundation; proof corpus
  updated to use indexed types.
- (iii) `Blueprint/04-capstones.md` updated to point at the new
  capstone proofs.


</details>

</details>

---

## Critical guardrails (procedural, from Initiative 3 lessons)

<details><summary>Five enforceable rules (No parallel state, Closed algebra inventory, Discharge before strengthening, Cascade-first design, Sorry budget per phase); each violation triggers stop-and-reassess.</summary>

These are enforceable rules, not aspirational principles. Violating
any one of them is a stop-and-reassess trigger.

### Guardrail 1 — No parallel state

<details><summary>Every use site of an old type/function flips in the same commit as its replacement — no transitional dual-write period. (Lesson 1.)</summary>

When a new type or function lands, every use site of the old
type/function flips in the **same commit**. No transitional
"dual-write" period. (Lesson 1: the J.2 dual-write became permanent.)

</details>

### Guardrail 2 — Algebra inventory is closed

<details><summary>The 23 items are the complete list; adding a 24th forces a deliberate Phase 1 re-open. Quiet additions during later phases are forbidden. (Lessons 2 + 5.)</summary>

The 23 items in §Algebra library are the complete list. Adding
a 24th item triggers a re-opening of Phase 1 (a deliberate design
re-review). Quiet additions during Phase 3+ are forbidden. (Lesson
2 + Lesson 5.)

</details>

### Guardrail 3 — Discharge before strengthening

<details><summary>Every cadence step's commit message must show `sorry: N → N − 1` (a discharge) or `sorry: N → N` (pure infrastructure). No commit may strengthen a predicate without a concurrent discharge. (Lesson 3.)</summary>

Every cadence step's commit message must show one of:
- `sorry: N → N − 1` (a discharge), OR
- `sorry: N → N` (pure infrastructure, no semantic claim added).

A commit that strengthens a predicate without a concurrent discharge
is not allowed. (Lesson 3.)

</details>

### Guardrail 4 — Cascade-first design

<details><summary>For any Tier 1 cascade-discharging step: first commit drafts the cascade discharge, second designs the supporting predicate, third lands the discharge. (Lesson 4.)</summary>

For any cadence step that aims to discharge a Tier 1 cascade
theorem (e.g. `scanFiltered_emit*_nonempty_structure`), the step's
**first** commit drafts the cascade discharge in pseudocode; the
**second** commit designs whatever predicate or lemma is needed; the
**third** commit lands the discharge. (Lesson 4: Initiative 3
designed predicates first and discovered the cascade didn't fit.)

</details>

### Guardrail 5 — Sorry budget per phase

<details><summary>Per-phase budget: 0 sorries at every phase boundary (Phases 2–6). In-flight sorries fine; the boundary is hard 0.</summary>

- Phase 2 budget: 0 (algebra library is the foundation).
- Phase 3 budget: 0 at phase end.
- Phase 4 budget: 0 at phase end.
- Phase 5 budget: 0 at phase end.
- Phase 6 budget: 0 at phase end.

In-flight sorries during a phase are fine, but the phase boundary
is a hard 0. (Initiative 3's Phase J.3 had no enforced
phase-boundary budget; it accumulated 19 → 7 across the entire
phase, never hitting 0.)

</details>

</details>

---

## Risks

<details><summary>Five risks with mitigations: indexed-type friction, algebra inventory closed too early, ToYaml/FromYaml law-discharge cost, late-discovered cascade, Tier 2 re-attack difficulty.</summary>

### Risk 1 — Indexed-type ergonomic friction

<details><summary>Dependent-type elaboration may force `show`/annotations; mitigated by the Phase 1 worked-example test — >5 annotations or any `show` for routine paths reopens the type design.</summary>

Lean's elaboration of dependent types occasionally requires
explicit type annotations or `show` tactics. If `RepGraph input range`
becomes painful to construct, application code may pile up
type-coercion boilerplate.

**Mitigation**: Phase 1 worked-example (above) walks one full
construction. If it requires more than 5 explicit type annotations
or any `show` for routine paths, the type design is reopened at end
of Phase 1.

</details>

### Risk 2 — Algebra inventory closed too early

<details><summary>Phase 3 may surface a missed algebra item; mitigated by a Phase 1 stress test — attempt a 30-line `mapping_scans` proof using only the 23 items, otherwise expand and re-freeze.</summary>

If Phase 3's scanner work surfaces an algebra item we missed at
freeze, every subsequent phase has to either decompose into
existing items (forced, possibly awkward) or re-open Phase 1.

**Mitigation**: Phase 1 *deliberately includes* a "stress test" —
attempt to write a 30-line proof of the `mapping_scans` claim from
the worked example using only the 23 inventoried items. If that
proof requires content outside the inventory, the inventory is
incomplete and freezes only after that content is added.

</details>

### Risk 3 — `ToYaml` / `FromYaml` law-discharge cost

<details><summary>Every instance must discharge the round-trip law; derived generator must produce instance + proof. Mitigated by starting from a manual `Int` proof — reopen typeclass design if it exceeds 100 lines.</summary>

Every `[ToYaml α]` / `[FromYaml α]` instance must discharge the
round-trip law. For derived instances (Phase 5), the derivation
generator must produce both the instance *and* the law-discharge
proof. This is structurally similar to Lean's `deriving` machinery
but with proof obligations.

**Mitigation**: Phase 5 starts with a single primitive instance
(`Int`) and proves the law manually before generalising. If the
manual proof exceeds 100 lines, the typeclass design is reopened.

</details>

### Risk 4 — Initiative-3-style cascade discovered late

<details><summary>An analogue of the Initiative 3 cascade may lurk at Stage A↔B or B↔C boundaries; mitigated by an explicit Phase 1 cascade audit that drafts the equivalent of `scanFiltered_emit*_nonempty_structure` at each boundary.</summary>

The cascade-stitching layer that broke Initiative 3 may have an
analogue at Stage B / Stage A boundaries that we don't notice
until Phase 4 / 5.

**Mitigation**: Phase 1 includes an explicit cascade audit: for
each stage boundary (A↔B, B↔C), draft the equivalent of
`scanFiltered_emit*_nonempty_structure` in Initiative-4 form and
verify it composes from the algebra library + indexed types. If
any cascade can't be drafted, Phase 1 is not done.

</details>

### Risk 5 — "Re-attack Tier 2" is harder than it looks

<details><summary>Tier 2 emitter-scannability is non-trivial regardless of foundation; mitigated by promoting Tier 2 to a required Phase 6 deliverable (criterion ii), not aspirational.</summary>

The original Initiative 3 driver (Tier 2 emitter-scannability) was
the gate. Initiative 4 promises to deliver it from a stronger
foundation, but the actual proof of `parse (emit v) = ok v` for
arbitrary `v` is non-trivial regardless of foundation choice.

**Mitigation**: Phase 6's DONE criterion (ii) makes Tier 2 a
required deliverable, not aspirational. If it's not provable in
Initiative 4, the foundation choice is wrong and we stop again.

</details>

</details>

---

## Decisions (D1–D5)

<details><summary>Summary table of all five resolved Phase-1 decisions (indexed type shape, LawfulRoundTrip shape, EqMode.bisim witness, Algebra namespace structure, per-phase test corpus).</summary>

All five Phase-1 decision points are resolved. The full rationale and
the chosen option for each appears in §What this document settles,
what it leaves open below. Summary:

| # | Topic | Resolution |
|---|---|---|
| **D1** | Indexed type shape | `range` as separate parameter; nested via dependent pair; `AnchorMap input` as separate parameter. |
| **D2** | `LawfulRoundTrip α` shape | Separate typeclass. |
| **D3** | `EqMode.bisim` witness | `Bisimulation` typeclass. |
| **D4** | `L4YAML/Algebra/` namespace | One file per item-cluster (per §Initial implementation order). |
| **D5** | Per-phase test corpus | Existing `yaml-test-suite` runner with stage-tag filters. |

</details>

---

## Initial implementation order (sketch for Phase 2 onward)

<details><summary>File-by-file landing order for Phase 2 (17 files): position → indent → string → tokenstream → fuel → anchormap → combinators → schema → token → value → lawfulbeq → equivalence → idempotence, then indexed-type substrate, then LoadConfig.</summary>

Once Phase 1 closes, Phase 2 lands these files in approximately this
order (internal sequencing of Phase 2; not part of the phase
DONE criteria):

1. `L4YAML/Algebra/Position.lean` (Items 7, 13)
2. `L4YAML/Algebra/Indent.lean` (Item 8)
3. `L4YAML/Algebra/StringList.lean` (Item 9, plus Item 22 migration)
4. `L4YAML/Algebra/TokenStream.lean` (Item 10)
5. `L4YAML/Algebra/Fuel.lean` (Item 11)
6. `L4YAML/Algebra/AnchorMap.lean` (Item 12 migration from `Spec/Types.lean`)
7. `L4YAML/Algebra/Combinators.lean` (Item 14)
8. `L4YAML/Algebra/Schema.lean` (Items 15, 16)
9. `L4YAML/Algebra/Token.lean` (Item 17)
10. `L4YAML/Algebra/Value.lean` (Items 18–21 migration)
11. `L4YAML/Algebra/LawfulBEq.lean` (Item 23 migration)
12. `L4YAML/Algebra/Equivalence.lean` (Items 1, 2, 3, 5, 6 — depends on AnchorMap)
13. `L4YAML/Algebra/Idempotence.lean` (Item 4)
14. `L4YAML/Indexed/Range.lean` (indexed-type infrastructure for D1)
15. `L4YAML/Indexed/RepGraph.lean` (Item 0 + indexed RepGraph type)
16. `L4YAML/Indexed/TokenStream.lean` (indexed TokenStream type)
17. `L4YAML/Config/LoadConfig.lean` (LoadConfig + EqMode + DuplicateKeyPolicy)

Files 1–13 are pure algebra. Files 14–17 are the type substrate
that Phase 3+ build on. Phase 2 is done when all 17 files compile
sorry-free and the closure check (any algebraic statement decomposes
into Items 0–23) passes.

</details>

---

## Estimated effort

<details><summary>Deliberately not in weeks; gated by per-phase DONE criteria. Phase 1: days. Phase 2: bounded by 23 items. Phases 3–6: scale with 211×2 YAML rule verifications.</summary>

**Deliberately not stated in weeks.** Initiative 3's effort estimates
were inaccurate by ≈30%; week-based gates encouraged commit-forward
behaviour past the sorry budget. Initiative 4 is gated by per-phase
DONE criteria. Each phase is "done when the criteria are met."

If a calendar reference is needed for planning purposes:

- Phase 1 (this document): days, not weeks.
- Phase 2 (algebra library): scope is bounded by the 23 items;
  estimate ≈ 1 named theorem per item × 17 files ≈ a contained piece
  of work. The library is the foundation; over-investing here is
  cheaper than under-investing.
- Phase 3, 4, 5, 6: each is gated by 0-sorry at boundary. Effort
  scales with the YAML 1.2.2 rule count; each rule is bidirectional
  so effective work = 211 × 2 = 422 verifications, distributed
  across the three stages. If a phase's verification productivity
  is low, the algebra library is incomplete and Phase 1 reopens.

The procedural rule that replaces calendar estimates: **at any phase
boundary, if the DONE criteria are not met, stop and reassess
before committing to the next phase.**

</details>

---

## What this document settles, what it leaves open

<details><summary>Settled choices from the 2026-05-03 conversation plus resolutions for D1–D5 (indexed type shape, LawfulRoundTrip typeclass, EqMode.bisim, Algebra namespace, test corpus).</summary>

**Settled** (decided in conversation 2026-05-03):
- Numeric phase indexing (not letter-based).
- Branch protocol (archive `feature/append-only`; new branch from `main`).
- Indexed `RepGraph` / `TokenStream` types (not annotation, not wrapper).
- Hybrid pre/post conditions: `Subtype` + `decide_pre` tactic.
- `linearise` cut; replaced by purely functional state threading
  on the legacy `setIfInBounds` shape (Item 0).
- Bottom-up phase ordering (algebra → types → stage C → stage B
  → stage A → capstone).
- `LoadConfig` bundles `EqMode` + `DuplicateKeyPolicy`.
- Algebra library inventory frozen at 23 items.

**Resolved during Phase 1**:

- **D1: final shape of indexed type**
  - (a) `range` is a **separate parameter** of `RepGraph`, not a field.
    Type-level disjointness of sub-graphs from different inputs is a
    critical guardrail against the ghost-predicate problem.
  - (b) Nested ranges encoded via **dependent pair** `Σ (r : Range input), RepGraph input r`.
    Slow elaboration is mitigated by keeping the dependent pair shallow
    (one level per constructor) and by `@[reducible]` aliases where the
    `Σ` would otherwise appear in user-facing signatures.
  - (c) Anchors use a **separate type parameter** `AnchorMap input`.
    `AnchorMap` is the coalgebra structure for graph isomorphism (Item 6);
    indexing it by `input` keeps cross-input alias confusion out of the
    type system.

- **D2: `LawfulRoundTrip α` typeclass shape** — **separate typeclass**.
  Clean separation of concerns: the round-trip law is a property of
  the instances, not of the types themselves. Gives the derivation
  generator a clear target for proof generation.

- **D3: `EqMode.bisim` witness shape** — **`Bisimulation` typeclass**.
  Most abstract and flexible: clients choose their bisimulation
  witness shape while presenting a common interface to the parser.

- **D4: `L4YAML/Algebra/` namespace structure** — **one file per
  item-cluster**, per the §Initial implementation order list. Keeps
  related content together while avoiding monolithic files.

- **D5: test corpus per phase** — **existing `yaml-test-suite` runner**,
  with tag filters per stage. Phase 3 must pass `tags: scan`,
  Phase 4 must pass `tags: parse`, Phase 5 must pass `tags: load`.

</details>

---

## Cross-references

<details><summary>Pointers to Blueprint 07 §Stop assessment, YAML 1.2.2 §3.1, Blueprint 02 §Append-only token stream, Blueprint 04 capstones.</summary>

- **`Blueprint/07-initiative-3-append-only.md` §Stop assessment** —
  the retrospective that motivated this initiative.
- **YAML 1.2.2 §3.1** — the three-stage information model
  (Native ↔ Representation ↔ Serialization ↔ Presentation) that
  this document's four-layer architecture aligns with.
- **`Blueprint/02-architecture.md` §Append-only token stream** —
  the *original* architecture choice that Initiative 3 challenged
  and Initiative 4 takes a different direction on.
- **`Blueprint/04-capstones.md`** — Tier 2 emitter-scannability,
  the original driver. Phase 6 DONE criterion (ii) re-attacks it.

</details>
