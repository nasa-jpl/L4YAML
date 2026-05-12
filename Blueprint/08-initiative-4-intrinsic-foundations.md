# Initiative 4 — Intrinsic Foundations

**Status**: **Design phase**, on `main`. No code changes yet.
This document is the deliverable of *Phase 1 — Design*; subsequent
phases land on a fresh feature branch off `main` once Phase 1 closes.

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

### What Initiative 3 demonstrated

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

### What Initiative 4 reverses

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

---

## Proposed architecture

### Four layers

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

### Three stages, each bidirectional

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

### Indexed type discipline

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

### Pre/post conditions: refinement types + tactic

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

### LoadConfig: bundled configuration

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

---

## Properties this delivers

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

---

## Worked example

Input: `{a: 1}` (6 bytes, single line).

This walks the input through all four layers in both directions,
showing how the indexed types eliminate the ghost-predicate work
that Initiative 3's `EmitScansInFlow` was carrying.

### Stage C (L3 ↔ L2): present / parse

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

### Stage B (L2 ↔ L1): compose / serialize

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

### Stage A (L1 ↔ L0): construct / represent

If the user has `[FromYaml (Map String Int)]` (derived via
`ToYaml`/`FromYaml` typeclass machinery from Phase 5), then
`construct (cfg := {})` returns the application value:

```lean
Map.mk [("a", 1)] : Map String Int
```

The `FromYamlType Int` instance (already present at
`Schema/FromToYaml.lean:85`) handles the scalar-to-int conversion
via `Schema.resolve`.

### How `EmitScansInFlow v` collapses

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

---

## Algebra library — frozen inventory (23 items)

The library is enumerated in this section and **frozen at end of
Phase 1**. No new items past freeze without re-opening Phase 1.

### From the original sketch (Items 0–11)

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

### From in-scope file inventory (Items 12–17, verified)

| # | Name | Source | Encoding |
|---|---|---|---|
| **12** | AnchorMap algebra | `Spec/Types.lean:633–721` | `find?_insert`, `find?_insert_ne`, `find?_empty`. Provides the alias-resolution coalgebra mechanism for Item 6. |
| **13** | YamlPos total order | `Spec/Types.lean:127–134` | `Ord`, `LT`, `LE` instances on `YamlPos.offset`. Composes with Item 7 → ordered monoid. |
| **14** | Surface grammar combinator algebra | `Surface/Combinators.lean:32–82` | Kleene-like laws on `GSeq`, `GAlt`, `GStar`, `GPlus`, `GOpt`: `GStar (GStar P) = GStar P`, `GPlus P = GSeq P (GStar P)`, `GOpt P = GAlt P GEps`, `GSeq` associativity. Currently stated implicitly; Phase 2 names them. |
| **15** | ToYaml / FromYaml typeclass laws | `Schema/FromToYaml.lean:42–107+` | `FromYamlType`, `FromYaml`, `ToYaml` typeclasses already exist with the bridge instance `[FromYamlType α] : FromYaml α`. Round-trip law: `fromYaml? ∘ toYaml = some` for each user instance. |
| **16** | Schema resolution determinism | `Schema/Schema.lean:245–305` | `resolveImplicit` / `resolveScalar` / `resolve` are total deterministic. Resolution precedence (null → bool → int → float → str) is canonical. Lemma: "resolution is a function." |
| **17** | Token discriminator algebra | `Token/Token.lean:241–280` | `YamlToken.isVirtual`, `canStartNode`, `isFlowIndicator` partition tokens into disjoint classes. Exhaustiveness laws cut case-split boilerplate. |

### From `Proofs/Foundation/` (Items 18–23, already proven)

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

### Closure principle

The list above is final at end of Phase 1. Any additional algebraic
content discovered during Phases 3–6 must either:

1. Decompose into existing items, OR
2. Trigger a *re-opening of Phase 1* (a deliberate design re-review,
   not a quiet conjunct addition).

This is the procedural enforcement of Lesson 2 (cap predicate
budget) and Lesson 5 (algebra first, ghost predicates last).

---

## Phased plan (milestone-gated, no week estimates)

Per-phase DONE criteria replace week-based scope gates. If a
phase's criterion isn't met, **stop and reassess** before
committing to the next phase. This is the procedural fix for the
Initiative 3 failure where J.3 ran past its sorry-budget without
formal reassessment.

### Phase 1 — Design  *(closed)*

<details>

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

### Phase 2 — Algebra library  *(in progress on `feature/intrinsic-foundations`)*

<details>
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

**Status (foundation chunk landed)**:

| # | Criterion | State |
|---|---|---|
| (i) | All 23 items proved sorry-free in `L4YAML/Algebra/` | **partial** — Items 18–23 migrated; Items 0–17 are next (see §Phase 2 next steps). |
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

**Out of scope**: any scanner/parser code. The algebra library does
not depend on `Scanner/`, `Parser/`, or any J.3-era infrastructure.

#### Phase 2 next steps (Items 0–17)

The §Initial implementation order list (below) gives the file
sequencing. The first cluster ready to land is:

1. `L4YAML/Algebra/Position.lean` — Items 7 (position monoid)
   and 13 (`YamlPos` total order). Source content already exists in
   `Spec/Types.lean:127–134`; this is migration + naming the monoid
   laws explicitly.
2. `L4YAML/Algebra/Indent.lean` — Item 8 (indent stack as free
   monoid). Pure new content; small (~50 LOC).
3. `L4YAML/Algebra/StringList.lean` *(extend)* — Item 9
   (character/string decomposition). Reuses Mathlib's
   `String.toList`/`++`/prefix/suffix laws where applicable.
4. `L4YAML/Algebra/AnchorMap.lean` — Item 12 migration from
   `Spec/Types.lean:633–721`. Already-proven theorems
   (`find?_insert`, `find?_insert_ne`, `find?_empty`); namespace
   move only.

Items 1, 2, 3, 5, 6 (`Equivalence.lean`) depend on AnchorMap and
are last. Item 4 (`Idempotence.lean`) is the capstone of Phase 2
itself: `load ∘ dump ∘ load = load`, proved via the algebra library
+ indexed types — this is the Phase 2 stress test for the closure
principle.

#### Algebra files landed in foundation chunk

| File | Items | LOC | Imports added downstream |
|---|---|---|---|
| `L4YAML/Algebra/Value.lean` | 18–21 | ~200 | 3 (was `Proofs.Foundation.ValueAlgebra`) |
| `L4YAML/Algebra/LawfulBEq.lean` | 23 | ~265 | 1 (`L4YAML.lean` root) |
| `L4YAML/Algebra/StringList.lean` | 22 | ~60 | 1 (`StringProperties.lean`) |
| `L4YAML/Config/LoadConfig.lean` | n/a | ~70 | 0 (new file; consumers in Phase 3+) |
| `L4YAML/Indexed/Range.lean` | n/a | ~60 | 0 |
| `L4YAML/Indexed/RepGraph.lean` | n/a | ~120 | 0 |
| `L4YAML/Indexed/TokenStream.lean` | n/a | ~80 | 0 |

</details>

### Phase 3 — Stage C (scanner) on indexed types

<details>
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

</details>

### Phase 4 — Stage B (parser) on indexed types

<details>
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

<details>
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

<details>
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

---

## Critical guardrails (procedural, from Initiative 3 lessons)

These are enforceable rules, not aspirational principles. Violating
any one of them is a stop-and-reassess trigger.

### Guardrail 1 — No parallel state

When a new type or function lands, every use site of the old
type/function flips in the **same commit**. No transitional
"dual-write" period. (Lesson 1: the J.2 dual-write became permanent.)

### Guardrail 2 — Algebra inventory is closed

The 23 items in §Algebra library are the complete list. Adding
a 24th item triggers a re-opening of Phase 1 (a deliberate design
re-review). Quiet additions during Phase 3+ are forbidden. (Lesson
2 + Lesson 5.)

### Guardrail 3 — Discharge before strengthening

Every cadence step's commit message must show one of:
- `sorry: N → N − 1` (a discharge), OR
- `sorry: N → N` (pure infrastructure, no semantic claim added).

A commit that strengthens a predicate without a concurrent discharge
is not allowed. (Lesson 3.)

### Guardrail 4 — Cascade-first design

For any cadence step that aims to discharge a Tier 1 cascade
theorem (e.g. `scanFiltered_emit*_nonempty_structure`), the step's
**first** commit drafts the cascade discharge in pseudocode; the
**second** commit designs whatever predicate or lemma is needed; the
**third** commit lands the discharge. (Lesson 4: Initiative 3
designed predicates first and discovered the cascade didn't fit.)

### Guardrail 5 — Sorry budget per phase

- Phase 2 budget: 0 (algebra library is the foundation).
- Phase 3 budget: 0 at phase end.
- Phase 4 budget: 0 at phase end.
- Phase 5 budget: 0 at phase end.
- Phase 6 budget: 0 at phase end.

In-flight sorries during a phase are fine, but the phase boundary
is a hard 0. (Initiative 3's Phase J.3 had no enforced
phase-boundary budget; it accumulated 19 → 7 across the entire
phase, never hitting 0.)

---

## Risks

### Risk 1 — Indexed-type ergonomic friction

Lean's elaboration of dependent types occasionally requires
explicit type annotations or `show` tactics. If `RepGraph input range`
becomes painful to construct, application code may pile up
type-coercion boilerplate.

**Mitigation**: Phase 1 worked-example (above) walks one full
construction. If it requires more than 5 explicit type annotations
or any `show` for routine paths, the type design is reopened at end
of Phase 1.

### Risk 2 — Algebra inventory closed too early

If Phase 3's scanner work surfaces an algebra item we missed at
freeze, every subsequent phase has to either decompose into
existing items (forced, possibly awkward) or re-open Phase 1.

**Mitigation**: Phase 1 *deliberately includes* a "stress test" —
attempt to write a 30-line proof of the `mapping_scans` claim from
the worked example using only the 23 inventoried items. If that
proof requires content outside the inventory, the inventory is
incomplete and freezes only after that content is added.

### Risk 3 — `ToYaml` / `FromYaml` law-discharge cost

Every `[ToYaml α]` / `[FromYaml α]` instance must discharge the
round-trip law. For derived instances (Phase 5), the derivation
generator must produce both the instance *and* the law-discharge
proof. This is structurally similar to Lean's `deriving` machinery
but with proof obligations.

**Mitigation**: Phase 5 starts with a single primitive instance
(`Int`) and proves the law manually before generalising. If the
manual proof exceeds 100 lines, the typeclass design is reopened.

### Risk 4 — Initiative-3-style cascade discovered late

The cascade-stitching layer that broke Initiative 3 may have an
analogue at Stage B / Stage A boundaries that we don't notice
until Phase 4 / 5.

**Mitigation**: Phase 1 includes an explicit cascade audit: for
each stage boundary (A↔B, B↔C), draft the equivalent of
`scanFiltered_emit*_nonempty_structure` in Initiative-4 form and
verify it composes from the algebra library + indexed types. If
any cascade can't be drafted, Phase 1 is not done.

### Risk 5 — "Re-attack Tier 2" is harder than it looks

The original Initiative 3 driver (Tier 2 emitter-scannability) was
the gate. Initiative 4 promises to deliver it from a stronger
foundation, but the actual proof of `parse (emit v) = ok v` for
arbitrary `v` is non-trivial regardless of foundation choice.

**Mitigation**: Phase 6's DONE criterion (ii) makes Tier 2 a
required deliverable, not aspirational. If it's not provable in
Initiative 4, the foundation choice is wrong and we stop again.

---

## Decisions (D1–D5)

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

---

## Initial implementation order (sketch for Phase 2 onward)

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

---

## Estimated effort

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

---

## What this document settles, what it leaves open

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

---

## Cross-references

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
