# Specification Gap Analysis: Remaining Sorry Theorems

**Date:** 2026-03-17
**Status:** 322/322 build, 2 sorry warnings — both analyzed here.

## Overview

All algorithmic/structural theorems in the C2 proof chain are proved.
The 2 remaining sorrys are in the **anchor/alias resolution** layer,
where the proof chain connects parser output (`Scannable`) to composed
output (`Grammable`). The composition theorem `compose_value_grammable`
requires two hypotheses that our proof chain cannot currently discharge:

| # | Theorem | Predicate | Gap Type |
|---|---------|-----------|----------|
| 8 | `parseStream_output_aliases_resolve` | `AllAliasesResolve` | **Formalization gap** — scanner omits provable invariant |
| 9 | `parseStream_output_anchors_wellformed` | `WellFormedAnchors` | **Specification modeling gap** — `∀ inFlow` quantifier is too strong |

---

## Gap #8: `AllAliasesResolve` — Alias Ordering

### What We Need to Prove

```lean
theorem parseStream_output_aliases_resolve
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h_parse : parseStream tokens = .ok docs) :
    ∀ doc ∈ docs.toList, AllAliasesResolve doc.value doc.anchors
```

`AllAliasesResolve v anchors` requires: for every `.alias name` node
in the value tree `v`, there exists an entry with key `name` in the
`anchors` array. This ensures alias resolution will succeed.

### Where the Gap Comes From

**This is a formalization gap, not a YAML spec gap.**

YAML 1.2.2 §7.1 is explicit:

> "An alias node is denoted by the `*` indicator, followed by the
> alias's name. The alias refers to the most recent **preceding** node
> having the same anchor."

The word "preceding" establishes a clear ordering requirement: every
alias must have a prior anchor with the same name.

Our implementation does not validate this:

1. **Scanner** (`scanAnchorOrAlias`): Emits `.anchor name` or `.alias name`
   tokens unconditionally — it does not check whether a prior `.anchor`
   with matching name exists.

2. **Parser** (`parseNode`): When encountering `.alias name`, immediately
   returns `YamlValue.alias name` without checking `ps.anchors`.

3. **Anchor accumulation** (`applyNodeFinalization` → `addAnchor`): When
   encountering `.anchor name`, adds `(name, resolved_value)` to
   `ps.anchors`. This happens during document parsing, so the anchor
   map grows monotonically.

The proof chain has no theorem connecting "`.alias name` token implies
prior `.anchor name` token" — and no theorem connecting "prior `.anchor
name` token implies `name ∈ ps.anchors` at the point of alias processing."

### Why This Is Not a YAML Spec Problem

The YAML spec is unambiguous: §7.1 forbids forward aliases. A conforming
scanner that accepts the input has already validated that every alias
name has been anchored. The gap is that our scanner doesn't prove this
property about its output.

### Resolution Options

| Option | Effort | Impact | Recommended? |
|--------|--------|--------|--------------|
| **A. Scanner invariant proof** | High | Closes gap fully | ✅ Ideal but expensive |
| **B. Parser-level tracking** | Medium | Closes gap fully | ✅ Practical |
| **C. Precondition** | Low | Shifts burden to caller | ⚠️ Weakens theorem |
| **D. Scanner validation** | Low (code) | Closes gap but changes behavior | ⚠️ Behavior change |

#### Option A: Scanner Invariant Proof

Prove from the scanner's state machine that for every `.alias name`
token at position `i`, there exists a `.anchor name` token at position
`j < i`. This is a substantial proof (the scanner has ~1000 lines of
state machine logic) but is **semantically correct** — it captures what
the YAML spec requires.

Estimated work: New inductive invariant over the scanner loop, tracking
the set of defined anchor names. Similar in spirit to `FlowContextPSV`
but over anchor names rather than flow nesting.

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
- Resolving #9 alone (fixing `WellFormedAnchors`) would reduce sorrys
  from 2 to 1.
- Both can be resolved independently.

However, the two gaps share one structural feature: they both involve
the **anchor/alias pipeline** that crosses scanner → parser → composition
boundaries. Any refactoring of anchor handling affects both.

---

## Diagnosis Summary

| Aspect | Gap #8 (Aliases Resolve) | Gap #9 (Anchors Well-Formed) |
|--------|--------------------------|------------------------------|
| **Root cause** | Scanner doesn't prove anchor-before-alias ordering | `∀ inFlow` quantifier too strong for cross-context aliasing |
| **YAML spec clear?** | ✅ Yes — §7.1 requires preceding anchor | ⚠️ Partially — spec allows cross-context aliasing but doesn't address serialization-level implications |
| **Our formalization clear?** | ✅ Yes — `AllAliasesResolve` is correct | ❌ No — `WellFormedAnchors` over-constrains with `∀ inFlow` |
| **Is the predicate correct?** | ✅ Yes | ❌ Too strong |
| **Counterexample to provability?** | None (should be provable) | Yes — `&a value{braces}` + `[*a]` |
| **Category** | Formalization gap | Specification modeling gap |

---

## Recommended Path Forward

### Priority 1: Fix Gap #9 (specification modeling)

Gap #9 has a **genuine counterexample** — the theorem as stated is false
for some valid YAML documents. This must be addressed by changing either
the predicate or the theorem statement.

**Recommended: Option B (Style-Flexible Grammable)** or **Option C
(Precondition)**. Option B is more principled; Option C is more practical.

### Priority 2: Fix Gap #8 (formalization)

Gap #8 is a true theorem — it's provable in principle, we just haven't
proved it. The most practical approach is **Option B (Parser-Level
Tracking)**: extend the `_wb` chain with an anchors-cover-aliases
conclusion.

### Alternative: Hybrid Approach

If full proofs for both gaps are too expensive, consider:
1. Fix #9 with Option C (precondition) — low effort, immediate progress
2. Fix #8 with Option C (precondition) — low effort
3. Add a comment to the final theorem listing the two preconditions and
   explaining they are YAML spec requirements, not implementation artifacts
