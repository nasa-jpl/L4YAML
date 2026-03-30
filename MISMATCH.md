# Code/Proof Architecture Mismatch in lean4-yaml-verified

## The Concept

In software engineering, Garlan, Allen, and Ockerbloom (1995) identified
**architecture mismatch**: when independently-developed components make
conflicting assumptions about how they will interact, composing them
into a system fails or requires costly adaptation. Their examples involved
event models, data formats, and control flow assumptions that clashed
at integration time despite each component being individually correct.

We have discovered an analogous phenomenon in **formal verification of
software**: a **code/proof architecture mismatch**. The scanner code and
the grammar specification are both internally consistent, but their
structural decomposition boundaries are incompatible — making it
impossible to prove the desired property without introducing a new
abstraction layer that bridges the gap.

We propose the term **code/proof mismatch** for this class of problem.

## How it Differs from Classical Architecture Mismatch

Classical architecture mismatch arises from composing **existing black-box
components** that were designed independently. The fix is typically an
adapter, wrapper, or glue code — a *syntactic* bridge between two APIs.

Code/proof mismatch arises when **formalizing properties of a single
system**. The code already works. The grammar specification already
defines the language. But the proof that connects them requires
decomposing both along compatible boundaries — discovering that the
natural decomposition of the code (token-by-token scanning) and the
natural decomposition of the grammar (nested document → node → content
productions) do not align.

| Aspect | Architecture Mismatch (1995) | Code/Proof Mismatch (this work) |
|--------|-----------------------------|---------------------------------|
| Domain | Component integration | Formal verification |
| Parties | Two or more independent components | Code structure vs. specification structure |
| Symptoms | Runtime failures, deadlocks, data corruption | Unprovable theorems, sorry obligations that resist discharge |
| Root cause | Incompatible assumptions about interaction protocols | Incompatible decomposition granularity between code and grammar |
| Fix | Adapters, wrappers, glue code | New proof-level abstractions that bridge the boundary gap |

The key difference: in classical architecture mismatch, you're composing
**what exists**. In code/proof mismatch, you're **discovering what
abstractions you need** to write properties and prove them. The mismatch
is not between two implementations but between an implementation's
structure and a specification's structure, as seen through the lens of
proof.

## The Specific Mismatch

### Scanner token boundaries vs. grammar production boundaries

The YAML scanner (`scanNextToken`) processes input in **token steps**:

```
Token N                          Token N+1
┌────────────────────────────────┬────────────────────────────────┐
│ preprocessing │ content scan   │ preprocessing │ content scan   │
│ (whitespace)  │ (e.g., "[")   │ (whitespace)  │ (e.g., "a")   │
└───────────────┴────────────────┴───────────────┴────────────────┘
```

The YAML grammar (`SBlockNode.flowInBlock`) requires **three-part
productions** that span token boundaries:

```
┌──────────────────────────────────────────────────────────────────┐
│ SSeparate        │ SFlowNode content  │ SSLComments              │
│ (ws BEFORE)      │                    │ (break/ws AFTER)         │
└──────────────────┴────────────────────┴──────────────────────────┘
       ↑                                        ↑
  From token N's preprocessing            From token N+1's preprocessing
```

**The trailing `SSLComments` of token N is consumed during token N+1's
preprocessing.** This means no single token step has all three parts
available simultaneously.

### Concrete examples of the mismatch

1. **Flow indicators** (`[`, `]`, `{`, `}`, `,`): After scanning `[`,
   the grammar position is mid-content. No `SLYamlStream` constructor
   can represent "stream with one open bracket" — the grammar requires
   the matching `]` and trailing comments before a document is complete.

2. **Document suffix** (`...`): `SLDocumentSuffix` requires
   `SCDocumentEnd + SSLComments`. After scanning `...`, we have
   `SCDocumentEnd` at column 3, but the trailing newline that would
   form `SSLComments` is not consumed until the next token's
   preprocessing.

3. **Block indicators** (`-`, `?`, `:`): Block collections like
   `- a\n- b` span ≥4 `scanNextToken` calls. There is no per-token
   grammar production for "one entry of a block sequence" — the grammar
   requires the complete `SBlockSeqEntries` as a unit.

### Why it went undetected through 4 layers of planning

The v0.4.6 plan grew incrementally as each layer exposed new gaps:

| Phase | What was planned | What was discovered |
|-------|-----------------|-------------------|
| **Original** | 3 layers to discharge 1 sorry (`scan_content_gives_stream`) | — |
| **Layer 1** | Per-scanner-function `_prod` theorems | `n=0, c=.blockIn` existential trick needed |
| **Layer 2** | Compose scalars into `SBlockNode` hierarchy | `SBlockNode.flowInBlock` needs loop-level context (Reflection #2: "the `SSeparate` comes from preprocessing, `SSLComments` from post-content — neither is available to the content function") |
| **Layer 3** | Thread `SLYamlStream` through `scanLoop` | `SLYamlStream` is NOT an append structure (Reflection #1); `GConsumeAll`/`SSLComments` shortcuts all fail |
| **Layer 4a–b** | Leaf `_prod` theorems + preprocessing coupling | Foundations complete, no issues |
| **Layer 4c** | Per-dispatch sorry lemmas for `scanNextToken` | **Mismatch discovered**: the sorry lemmas are unprovable because `SLYamlStream sp_start sp'` requires complete grammar productions, but each token step only has partial context |

**The mismatch was foreshadowed** by Layer 2 Reflection #2 ("needs
loop-level context") and Layer 3 Reflection #1 ("`SLYamlStream` is not
an append structure"). But these were treated as complexity management
issues, not as structural impossibility. The escalation through 4a → 4b
→ 4c was driven by assuming that enough machinery would eventually close
the gap — when in fact the gap was architectural.

## Resolution: The Lagging Grammar Accumulator

The fix requires a new proof-level abstraction: a **grammar accumulator
whose position lags behind the scanner** by exactly one `SSLComments`
worth.

### Current (broken) invariant

```
∀ token step:
  SLYamlStream sp_start sp  ∧  ScannerSurfCorr sc sp
  ────────────────────────────────────────────────────
            grammar and scanner at SAME position
```

This is unprovable because after scanning token N's content, the grammar
needs N's trailing `SSLComments` (which hasn't been consumed yet) to
close N's `SBlockNode` production.

### Proposed (lagging) invariant

```
∀ token step:
  SLYamlStream sp_start sp_gram  ∧
  PendingNode sp_gram sp_scan    ∧   -- open grammar gap
  ScannerSurfCorr sc sp_scan
  ─────────────────────────────────
  grammar lags scanner by one SSLComments
```

At each step:
1. **Preprocessing** of token N+1 consumes whitespace → this provides
   the `SSLComments` needed to **close token N's node**
2. The closed node extends `SLYamlStream` from `sp_gram` to `sp_mid`
3. **Content dispatch** of token N+1 advances scanner to `sp_scan'`
4. A new `PendingNode sp_mid sp_scan'` is opened

At EOF (preprocessing returns `none`):
- The final `PendingNode` is closed with `SSLComments` from the EOF gap
- `SLYamlStream sp_start sp_final` where `sp_final.chars = []`

### What `PendingNode` must track

The pending grammar state between tokens must capture all information
needed to close a `SBlockNode` / `SLDocumentSuffix` / etc. once the
trailing `SSLComments` becomes available:

- **Document-level state**: do we have an open document? If so, via `---`
  (explicit) or bare? Are we between documents (after `...`)? Between
  prefix and content?
- **Node-level content**: the actual `SFlowNode`, `SCLLiteral`, etc.
  produced by the current token's `_prod` theorem
- **Separation context**: the `SSeparate` from preprocessing, needed
  by `SBlockNode` constructors
- **Block collection nesting**: for multi-token block sequences/mappings,
  the partial `GStar (SBlockSeqEntry n)` accumulated so far

This is substantially more complex than the current `SLYamlStream`-only
accumulator, but it correctly models the scanner's token-by-token
execution.

## Reflections on Code/Proof Mismatch

1. **Mismatches manifest as sorry obligations that resist discharge.**
   The 5 per-dispatch sorry lemmas in StreamAccum.lean are individually
   well-typed and appear reasonable. They only become visibly unprovable
   when you attempt the proof and realize the postcondition requires
   information that won't exist until the next iteration.

2. **Escalating machinery is a diagnostic signal.** The progression
   from "1 sorry, 3 layers" to "1 sorry, 4 layers with sublayers a–d"
   should have triggered a review of the invariants, not just addition
   of more infrastructure. In hindsight, each new sublayer was working
   around the same fundamental misalignment rather than addressing it.

3. **The grammar is not wrong; the code is not wrong.** Both the YAML
   grammar specification and the scanner implementation are correct.
   The mismatch is in the **interface between them** — the assumption
   that scanner token steps can be mapped one-to-one onto grammar
   productions. The resolution requires a new abstraction (the lagging
   accumulator) that lives entirely in the proof layer.

4. **This is not unique to YAML.** Any scanner/parser that processes
   tokens with leading and trailing context (whitespace, comments,
   separators) will have this boundary misalignment relative to a
   grammar that bundles leading/trailing context with content. The
   pattern likely applies to any verified scanner proving grammar
   conformance.

## Postscript: The Converse — When Boundaries Are Right

The resolution of the mismatch (sub-layers 4d and 4e) produced an
unexpected positive result that is worth documenting alongside the
negative lesson.

Sub-layer 4e was expected to be the **hardest part** of the entire
proof effort. Block collections (`- a\n- b`) span multiple
`scanNextToken` calls, requiring a nested accumulator to track
partially-built `SBlockSeqEntries` and `SBlockMapEntries` across
iterations. The README estimated it at "High" difficulty with "novel
inductive design."

In practice, 4e was completed quickly and mechanically. The `BlockStack`
inductive (3 constructors: `nil`, `seqLevel`, `mapLevel`) slotted into
the existing composition layer with only parameter additions. All six
proven composition theorems reproved with the same `unfold/split`
skeleton used in 4c and 4d. The sorry lemma signatures gained one extra
existential variable (`sp_block'`) and one extra hypothesis (`h_stack`).
No proof content changed.

This was possible because the 4d resolution — the lagging invariant —
had established the **right abstraction boundary**. Specifically:

1. **Orthogonal concerns compose.** The lagging invariant separated
   "immediate token lag" (`PendingNode`) from "grammar accumulation"
   (`SLYamlStream`) from "scanner correspondence" (`ScannerSurfCorr`).
   Adding a fourth concern ("block nesting depth" via `BlockStack`)
   required no restructuring — it inserted between `SLYamlStream` and
   `PendingNode` as an independent component. The four-part state
   (`SLYamlStream ∧ BlockStack ∧ PendingNode ∧ ScannerSurfCorr`)
   is a product of independent concerns, not a monolithic invariant.

2. **Evidence-free inductives are rewrite-resilient.** All three
   iterations (4c, 4d, 4e) kept the accumulator types evidence-free
   (tracking positions only, not grammar witnesses). This meant each
   rewrite only changed type signatures and existential unpacking in
   the composition layer — never proof content. The cost of adding
   `BlockStack` was proportional to the number of *type signatures*
   that mentioned position variables, not the number of *proofs*.

3. **The composition layer is structurally invariant.** The
   `unfold scanNextToken; simp only [bind, Except.bind]; split`
   pattern that decomposes `scanNextToken` into 5 dispatch paths is
   determined by the *code's* control flow, not by the *invariant's*
   structure. Changing the invariant from a triple to a quad changed
   what gets passed to each sorry lemma, but not how many sorry
   lemmas exist or how the delegation works. This is a hallmark of
   correct abstraction: the composition structure is stable under
   refinement of the components it composes.

**The lesson is the converse of the mismatch:** architecture mismatch
makes simple properties impossible to prove (the 4c sorry obligations
were provably unprovable). But once the abstraction boundaries are
correctly aligned, even the "hardest" extensions become mechanical
(4e slotted in without restructuring). The cost of finding the right
boundary (4c's failure → MISMATCH.md → 4d's redesign) was high, but
the ongoing cost of working within it is low. This suggests that in
verified systems, **investing in abstraction boundary design has
superlinear returns** — a correct boundary not only resolves the
current mismatch but makes future extensions cheap.

This also provides a **diagnostic criterion**: if adding a new concern
to a proof requires restructuring existing proofs rather than extending
them, the abstraction boundary may be misaligned. Conversely, if a new
concern slots in as an independent component with only type-signature
changes to the composition layer, the boundary is likely correct.

## References

- D. Garlan, R. Allen, J. Ockerbloom. "Architectural Mismatch: Why
  Reuse Is So Hard." *IEEE Software*, 12(6):17-26, November 1995.
