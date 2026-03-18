# Specification Gap Analysis: Remaining Sorry Theorems

**Date:** 2026-03-18 (updated)
**Status:** 322/322 build, 3 sorry warnings — see below.
**Progress:** Gap #8 Phase 1 complete (parser-level validation). Gap #9 proof infrastructure complete. Gap #8 now has 2 localized sorry helpers; original `parseStream_output_aliases_resolve` is fully proven. Revised phase plan: Phase 3 (scanner) → Phase 2 (parser sorrys).

## Overview

All algorithmic/structural theorems in the C2 proof chain are proved.
The remaining sorrys are in the **anchor/alias resolution** layer,
where the proof chain connects parser output (`Scannable`) to composed
output (`Grammable`). The composition theorem `compose_value_grammable`
requires two hypotheses:

| # | Theorem | Predicate | Status |
|---|---------|-----------|--------|
| 8 | `parseStream_output_aliases_resolve` | `AllAliasesResolve` | **Proven** (modulo 2 helper sorrys: `parseNode_anchors_grow`, `parseNode_aliases_resolve`) |
| 9 | `parseStream_output_anchors_wellformed` | `WellFormedAnchors` | **Sorry** — specification modeling gap (`∀ inFlow` too strong) |

---

## Gap #8: `AllAliasesResolve` — Alias Ordering

### Status: Phase 1 Complete

The parser now validates aliases at parse time (§7.1 compliance).
`parseNode` rejects `*name` unless `name ∈ ps.anchors`, producing
an `undefinedAlias` error. The top-level theorem is fully proven:

```lean
theorem parseStream_output_aliases_resolve
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h_parse : parseStream tokens = .ok docs) :
    ∀ doc ∈ docs.toList, AllAliasesResolve doc.value doc.anchors
```

**Proof chain:** `parseStream` → `parseStreamLoop_aliases_resolve` →
`parseDocument_aliases_resolve` → `parseNode_aliases_resolve`.

Two helper lemmas remain as `sorry`:
1. `parseNode_aliases_resolve` — core induction on fuel, showing every
   alias in the output tree passed the `ps.anchors.any` check
2. `parseNode_anchors_grow` — anchors only grow (monotonicity), needed  
   to lift from child-level to parent-level anchors

### Implementation Changes

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

### Why Phase 1 the Sorrys Are Small

Both remaining sorrys are structural induction proofs over `parseNode`:
- They unfold `parseNode` at fuel `k+1`, split on the token match, and
  for recursive cases (sequences, mappings) use the IH at fuel `≤ k`
- The alias branch is trivial: the `if` guard provides the witness
- The scalar/empty branches are trivial: no aliases in the tree
- The recursive branches need monotonicity (`parseNode_anchors_grow`)
  to lift child-level IH to parent-level anchors

### Remaining Phase Plan (revised: Phase 3 → Phase 2)

The original D → B → A ordering assumed Phase 2's parser-level mutual
induction would "template" Phase 3's scanner proof.  In practice the
two induction shapes are unrelated (14-function mutual induction vs.
`scanLoop` state-machine induction with 5-level dispatch), so Phase 2
provides no scaffolding for Phase 3.  Going scanner-first is better:

- **Phase 3 (next)**: Add `definedAnchors : Array String` to
  `ScannerState`.  Prove `scan_aliases_have_prior_anchors` — every
  `.alias name` token at position `i` has a prior `.anchor name` at
  `j < i`.  This is semantically correct §7.1 conformance at the
  scanner level.
- **Phase 2 (after Phase 3)**: Discharge `parseNode_aliases_resolve`
  and `parseNode_anchors_grow` using the scanner theorem as a
  precondition on the input token stream.  With
  `AliasesHaveAnchors tokens` established by the scanner, the parser
  proof becomes straightforward — no mutual induction over 14
  functions needed.

### Resolution Options

| Option | Effort | Impact | Recommended? |
|--------|--------|--------|--------------|
| **A. Scanner invariant proof** | High | Closes gap fully + proves §7.1 conformance | ✅ Ideal — semantically correct |
| **B. Parser-level tracking** | Medium | Closes gap fully at parser level | ✅ Template for Option A |
| **C. Precondition** | Low | Shifts burden to caller | ⚠️ Weakens theorem |
| **D. Parser-level validation** | Low (code) | Closes sorry by construction | ✅ Immediate result |

#### Option A: Scanner Invariant Proof (with `definedAnchors` field)

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

#### Option B: Parser-Level Tracking

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

#### Option C: Precondition

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

#### Option D: Scanner Validation

Modify `scanAnchorOrAlias` to reject aliases when the name is not in a
running set of defined anchors. This closes the gap by construction but
changes the scanner's behavior (it would now reject some inputs that the
YAML spec also rejects, so this is spec-compliant).

---

## Gap #9: `WellFormedAnchors` — Cross-Context Aliasing

### What We Need to Prove

```lean
theorem parseStream_output_anchors_wellformed
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h_scan_tokens : PlainScalarsValid tokens)
    (h_parse : parseStream tokens = .ok docs) :
    ∀ doc ∈ docs.toList, WellFormedAnchors doc.anchors
```

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

### Where the Gap Comes From

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

### Concrete Counterexample

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

### Is This a YAML Spec Problem?

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

### Why `∀ inFlow` Exists

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

### Resolution Options

| Option | Effort | Impact | Changes spec? |
|--------|--------|--------|---------------|
| **A. Context-aware `WellFormedAnchors`** | Medium | Closes gap precisely | Yes — new predicate |
| **B. Style-flexible `Grammable`** | Medium | Closes gap at right level | Yes — weaker Grammable |
| **C. Precondition on input** | Low | Restricts to "nice" YAML | Yes — new precondition |
| **D. Accept and document** | None | Gap remains | No |

#### Option A: Context-Aware `WellFormedAnchors`

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

#### Option B: Style-Flexible `Grammable`

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

#### Option C: Precondition on Input

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

#### Option D: Accept and Document

Leave both sorrys with documentation explaining the gap. The final
theorem would have `sorry` annotations but the documentation makes clear
that:
- All algorithmic proof obligations are discharged.
- The two remaining gaps are at the specification/modeling interface.
- The gaps affect only YAML documents with cross-context aliasing of
  plain scalars containing flow indicators — a nearly-nonexistent
  corner case in practice.

---

## Interaction Between the Two Gaps

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

## Diagnosis Summary

| Aspect | Gap #8 (Aliases Resolve) | Gap #9 (Anchors Well-Formed) |
|--------|--------------------------|------------------------------|
| **Root cause** | Scanner doesn't prove anchor-before-alias ordering | `∀ inFlow` quantifier too strong for cross-context aliasing |
| **YAML spec clear?** | ✅ Yes — §7.1 requires preceding anchor | ⚠️ Partially — spec allows cross-context aliasing but doesn't address serialization-level implications |
| **Our formalization clear?** | ✅ Yes — `AllAliasesResolve` is correct | ✅ Yes — `adaptForFlowContext` in `addAnchor` makes stored values universally grammable |
| **Is the predicate correct?** | ✅ Yes | ✅ Yes — now satisfiable via `adaptForFlowContext` |
| **Counterexample to provability?** | None (should be provable) | ~~Yes — `&a value{braces}` + `[*a]`~~ **Resolved**: `addAnchor` converts to `.doubleQuoted` |
| **Category** | Formalization gap | ~~Specification modeling gap~~ → **Resolved at runtime** |
| **Proof status** | Three-phase plan (D → B → A) | Helper lemmas all proven; loop invariant needed |

---

## Decisions

### Gap #8: Three-Phase Plan (D → B → A)

Gap #8 is resolved in three phases.  Phase 1 is complete.  The
remaining phases are reordered: scanner first (Phase 3), then parser
sorrys (Phase 2), because the scanner theorem trivializes the parser
proof:

#### Phase 1: Option D — Parser-Level Alias Validation

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

#### Phase 2: Parser-Level Sorrys (after Phase 3)

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

#### Phase 3: Option A — Scanner-Level `definedAnchors` Field

**Goal:** Prove YAML §7.1 conformance at the scanner level — the
semantically correct result.

Add `definedAnchors : Array String` to `ScannerState`. This is
preferred over logical ghost state because ghost state artificially
papers over the fact that the scanner's semantic state is incomplete.
The `definedAnchors` field is genuinely part of the scanner's
responsibility — tracking which anchors have been defined in the
current document is information the scanner *should* have.

**Implementation:**
1. Add `definedAnchors : Array String` to `ScannerState`
2. `scanAnchorOrAlias` with `isAnchor = true`: push `name` to
   `definedAnchors`
3. `scanAnchorOrAlias` with `isAnchor = false`: check
   `name ∈ definedAnchors` (reject if absent — §7.1 conformance)
4. `scanDocumentStart` / `scanDocumentEnd`: reset `definedAnchors`
   (document-scoped per §7.1)
5. ~15 preservation lemmas (mechanical — most functions don't touch
   the field; 5-level dispatch decomposition helps)
6. `scanLoop` induction: thread `definedAnchors` monotonicity

**Outcome:** A standalone scanner theorem:
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

### Gap #9: Option B′ — `adaptForFlowContext` in `addAnchor` ✅ IMPLEMENTED

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

**Remaining work for Gap #9:** The helper lemmas are fully proven.
Discharging the actual `parseStream_output_anchors_wellformed` sorry
requires threading `adaptForFlowContext_grammable_forall` through the
parse loop invariant — showing that `addAnchor`'s call to
`adaptForFlowContext` means `ps.anchors` satisfies `WellFormedAnchors`
at document end. This requires a loop invariant over `parseStreamLoop`
and `parseDocument` connecting individual `addAnchor` calls to the
final anchor array.
