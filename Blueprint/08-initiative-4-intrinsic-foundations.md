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
offset-monotonicity chain is mediated by `emitAtSafe` (a defensive
emit that performs the bound check at runtime); the static
monotonicity proof is the headline Step 5b deliverable.
**Next session**: Step 5b — discharge the dispatcher offset-
monotonicity chain (helper-loop monotonicity for the `collect*Ix`
family, then chain through each `scan*Ix`); also pick up the
deferred Step 4 content-correctness obligations
((d) hex-escape value, (e) multi-line content for quoted +
plain, block-scalar `foldBlockContent` + `applyChomp`).
**Then Step 5c**: `present` + corpus theorem.

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
| `L4YAML/Scanner/IndexedState.lean` | n/a | ~260 | 0 (staging — Guardrail 1; new in Phase 3 Step 5a: `ScannerStateIx input`, indexed `SimpleKeyStateIx`, indent-stack ops, `emit/emitAt/emitAtSafe/emitAtCursor/overwriteAtCursor`) |
| `L4YAML/Scanner/IndexedDispatch.lean` | n/a | ~720 | 0 (staging — Guardrail 1; new in Phase 3 Step 5a: helper recogniser loops, simple-key save/resolve, block + flow indicator scans, document markers, directives, anchor/alias, tag, dispatch family, `scanLoopIx`, `scanIx`) |
| `L4YAML/Proofs/Scanner/IndexedWhitespace.lean` | n/a | ~405 | 0 (staging — Guardrail 1; new in Phase 3 Step 2; +`consumeLineBreak_strict` in Step 4a) |
| `L4YAML/Proofs/Scanner/IndexedIndent.lean` | n/a | ~355 | 0 (staging — Guardrail 1; new in Phase 3 Step 3; +`skipToContentLoop_progress` / `skipToContent_progress` in Step 4a) |
| `L4YAML/Proofs/Scanner/IndexedScalar.lean` | n/a | ~630 | 0 (staging — Guardrail 1; new in Phase 3 Step 4a; +F1/F2/F3 monotonicity proofs in Step 4b) |

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

**Reflections** (Phase 3 Step 1 — indexed-type extensions):

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

**Reflections** (Phase 3 Step 2 — character/whitespace layer):

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

**Carried forward into Step 5b** (was Step 5b/5c in the new
split, but most belongs in 5b):
- Dispatcher offset-monotonicity chain: prove
  `collect*Ix_offset_monotonic` (anchor name, tag handle, tag
  suffix, verbatim tag, directive name, version major/minor) +
  `skipDocEndWhitespaceIx_offset_monotonic`, then chain through
  each dispatcher (`scanAnchorOrAliasIx_offset_monotonic`,
  `scanTagIx_offset_monotonic`,
  `scanYamlDirectiveIx_offset_monotonic`,
  `scanTagDirectiveIx_offset_monotonic`,
  `scanDirectiveIx_offset_monotonic`,
  `scanNextTokenIx_*_offset_monotonic`,
  `scanLoopIx_offset_monotonic`).
- Replace `emitAtSafe` use sites with `emitAt` once the chain
  exists.
- Hex-escape value-correctness (carried from Step 4a):
  `hexStringValue` of a hex-digit string equals the decoded
  `Nat` value (mod overflow checks).
- Block-scalar content correctness (carried from Step 4b):
  `foldBlockContent` matches the spec's folded-content
  extraction; `applyChomp` matches `[160]`'s semantics.
- Quoted multi-line content correctness (carried from Step 4b):
  the concatenated `content` matches `[111]`–`[116]` /
  `[122]`–`[125]` under the fold rules.
- Plain multi-line content correctness (carried from Step 4b):
  the threaded `content ++ folded` matches `[131]`–`[135]`.
- `autoDetectBlockScalarIndentLoopIx` correctness.
- `scanValueIx`'s validation chain (the legacy splits this
  into `scanValueClearKey` / `scanValueValidate` /
  `scanValuePrepare` / `scanValueTabCheck`; Step 5a landed
  only `scanValuePrepareIx` and a simplified driver).
- Tab-in-indentation check for `scanBlockEntryIx` and
  `scanKeyIx` (§6.1 hardening).

**Step 5c — `present` + corpus theorem** *(planned)*.
After Step 5b is sorry-free, build:
- `present : TokenStream input → String` — render an indexed
  token stream back to YAML source.
- A small fixed corpus of test inputs (mirror the existing
  scanner test harness in `L4YAML/Tests/`).
- The corpus roundtrip theorem: for each `ts ∈ corpus`,
  `scanIx (present ts) = .ok ts`.
- All staging proofs reach sorry-free at end of session.

**Step 6 — Atomic cutover**.
A single commit:
1. Rename `Scanner/IndexedScanner.lean` → `Scanner/Scanner.lean`
   (overwriting the legacy file) and likewise for every staging
   proof file.
2. Delete every legacy file replaced by the cutover (`Scanner/Scalar.lean`,
   `Scanner/Whitespace.lean`, `Scanner/Indent.lean`,
   `Scanner/SimpleKey.lean`, `Scanner/Document.lean`,
   `Scanner/NodeProperties.lean`, `Scanner/State.lean`, and the
   ~17,000 LOC of `Proofs/Scanner/*` that no longer apply).
3. Retarget every downstream import (`Parser/`, `Spec/`,
   `Output/`, `Proofs/Parser/`, `Proofs/RoundTrip/`, etc.) to the
   new scanner API.
4. Update `L4YAML.lean` import list.
5. Full `lake build` must pass in this single commit.

**Sub-plan guardrails**:
- Each of steps 1–5 commits with `sorry: N → 0` (or `0 → 0`) in
  the *new* indexed/staging files; the legacy sorry count is
  untouched (the legacy scanner still has open sorries today;
  those are obsoleted, not fixed, by step 6).
- Step 6 must show `lake build` green in the cutover commit
  message body.
- If any step surfaces a missing algebra item, **stop and re-open
  Phase 1** (Guardrail 2). Do not quietly add a 24th item.

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
