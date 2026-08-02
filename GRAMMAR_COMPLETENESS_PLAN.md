# Grammar Completeness Plan — `parse_iff_grammar` (capstone 7.7)

> Formerly `VERSION-0.4.8.md`; renamed 2026-08-01 (VERSION-named docs
> are retired release-campaign records — this is the **open** plan).
> The campaign, when executed, ships as release v0.4.8. All line pins
> below re-verified against the code on 2026-08-01.

**Goal:** Prove the grammar completeness theorem — that every string in the YAML 1.2.2 formal language parses successfully — and close the biconditional.

```lean
theorem parse_iff_grammar (input : String) :
    (∃ docs, parseYaml input = .ok docs) ↔ InYamlLanguage input
```

Both directions:
- **Forward** (v0.4.6, proven): `parseYaml input = .ok docs → InYamlLanguage input`
- **Converse** (this plan, target): `InYamlLanguage input → ∃ docs, parseYaml input = .ok docs`

## Status (as of 2026-08-01): NOT STARTED — UNBLOCKED

| Step | Status | Notes |
|---|---|---|
| 0. Scanner audit for directive handling | ✅ done 2026-08-01 | findings under Fix B: mid-stream leniency **confirmed reachable** |
| 1. Remove `directiveDrop` / `scannerDrop` constructors from `SLYamlStream` | ❌ open | both still present in [Surface/Document.lean](L4YAML/Surface/Document.lean) (lines 165, 175) |
| Fix A: eliminate `scannerDrop` (flow indicator grammar evidence) | ❌ open | blocking lemma `SFlowNode_context_lift` not proven |
| Fix B: eliminate `directiveDrop` (orphaned directive resolution) | ❌ open | audit done; recommended path = strengthen the scanner (option c) |
| 5. Prove the converse `grammar_completeness` | ❌ open | depends on Steps 0–4 |
| 6. Assemble `parse_iff_grammar` biconditional | ❌ open | depends on Step 5 |

**Blocker cleared (2026-07-04):** v0.4.7 is complete — `universal_roundtrip` is
fully proven (proof-status SSOT:
[Blueprint/04-capstones.md](Blueprint/04-capstones.md)). This plan is now the
only open proof frontier (capstone slot 7.7, `parse_iff_grammar`).

**Where the obligations live:** `StreamAccum.lean` is **sorry-free** — 0
`sorry` tactics; its ~28 `sorry` mentions are docstring narrative, mostly
inside the §6 Gap Analysis block now explicitly marked *historical*
(`StreamAccum.lean:3201–3320`). The obligations this plan addresses
(`SFlowNode_context_lift`, `h_closable` construction for `pendingFlow`,
orphaned-directive resolution) are real but live only as prose: in v0.4.6
they were "discharged" **via the over-approximation constructors this plan
removes**, so eliminating the constructors reopens exactly those
obligations, minus the escape hatch. (The BOM col≠0 edge case formerly
listed alongside them is genuinely closed:
`bom_noWhitespace_ssbcomment` at
[L4YAML/Proofs/Production/PreprocessProduction.lean:262](L4YAML/Proofs/Production/PreprocessProduction.lean)
builds `SSBComment.withSep` from the column-independent
`SSeparateInLine.startOfLine`.)

**Estimated effort:** ~150–600 LoC for Phase 1; the bulk lands in
[Production/StreamAccum.lean](L4YAML/Proofs/Production/StreamAccum.lean) (currently 3,322 lines).

---

## Motivation

Version 0.4.6 proved **acceptance strictness** — if the parser accepts an input, the input is in the YAML language:

```lean
theorem parse_strict_proof : parseYaml input = .ok docs → InYamlLanguage input
theorem scan_strict_proof  : scan input = .ok tokens   → InYamlLanguage input
```

The converse — that every YAML-language string is accepted — is missing. Together these would establish a **biconditional**: the parser accepts **exactly** the YAML 1.2.2 language — no more, no less. This is the strongest correctness statement possible for a parser: soundness (forward), completeness (converse), and their conjunction.

1. **Spec-conformance is bidirectional.** Without the converse, the parser could silently reject valid YAML inputs. v0.4.6 proves it doesn't accept *invalid* inputs; this plan proves it doesn't reject *valid* ones.

2. **Closes the formal verification story.** The biconditional `parse ↔ grammar` is the gold standard for parser correctness in the formal-methods literature. Combined with v0.4.7's round-trip theorem: the parser accepts exactly the right inputs, and for the emitter's output subset, the parsed result matches the original.

3. **Enables refactoring confidence.** Any scanner/parser refactor that preserves the biconditional is provably behaviour-preserving. Without completeness, a refactor could accidentally narrow the accepted language.

---

## The Over-Approximation Problem

`InYamlLanguage` is defined via `SLYamlStream`
([Surface/Document.lean:136](L4YAML/Surface/Document.lean); `InYamlLanguage`
at :186), which has **5 constructors**:

```lean
inductive SLYamlStream : SurfPos → SurfPos → Prop where
  | single           : GStar SLDocumentPrefix → GOpt SLAnyDocument → GStar SLDocumentSuffix → ...
  | suffixContinue   : SLYamlStream s s₁ → GPlus SLDocumentSuffix → ...
  | implicitContinue : SLYamlStream s s₁ → GStar SLDocumentPrefix → GOpt SLAnyDocument → ...
  | directiveDrop    : SLYamlStream s s₁ → GPlus SLDirective s₁ s' → SLYamlStream s s'
  | scannerDrop      : SLYamlStream s s₁ → SSLComments s₂ s' → SLYamlStream s s'
```

The first three correspond directly to YAML 1.2.2 §9.1 production [211]. The last two — `directiveDrop` (line 165) and `scannerDrop` (line 175) — are **over-approximations** added during the v0.4.6 `scan_strict` proof to accommodate scanner behaviour that doesn't map cleanly to spec productions:

- **`directiveDrop`**: absorbs orphaned directives (e.g., `%YAML 1.2` without a following document).
- **`scannerDrop`**: opaque gap matcher for characters consumed by the scanner (e.g., incomplete flow indicators) that don't fit a clean grammar production.

### Consequence for the converse

The over-approximation constructors make `InYamlLanguage` **weaker** than "parseable YAML":

```
parseable inputs ⊂ InYamlLanguage inputs
```

A string can satisfy `InYamlLanguage` (via `scannerDrop`) without being parseable — e.g., an unclosed flow sequence `[1, 2` may be accepted by `InYamlLanguage` through `scannerDrop` but rejected by `parseYaml` with an unmatched-bracket error.

**The converse theorem is therefore false under the current definition.** The fix: remove the over-approximation constructors, making `InYamlLanguage` exactly characterize the parseable YAML language.

---

## Approach: Eliminate Over-Approximation Constructors

Rather than creating a parallel `StrictInYamlLanguage` definition, we **remove `directiveDrop` and `scannerDrop` directly from `SLYamlStream`**, reducing it to its 3 spec-conforming constructors:

- No duplication of grammar definitions
- The existing `InYamlLanguage` becomes the biconditional target
- Every existing theorem using `InYamlLanguage` is automatically strengthened
- `scan_strict_proof` is *harder* to prove (no escape hatches), but the theorem itself is *stronger*

### Impact analysis (verified 2026-08-01)

- **Definition site (must change):** `L4YAML/Surface/Document.lean` — remove the two constructors from the `SLYamlStream` inductive.
- **Construction sites (must fix):** all 8 are in `Proofs/Production/StreamAccum.lean` — 1 `scannerDrop` (line 481) + 7 `directiveDrop` (lines 505, 1138, 1162, 1334, 1346, 2794, 2814).
- **Nothing else breaks:** a library-wide sweep found **no case analysis on `SLYamlStream` anywhere** — not even in `StreamAccum.lean`, which only *constructs* it. `DocumentProduction.lean` applies the three spec constructors in helper lemmas and threads values opaquely; every other file threads existentials. Removing constructors therefore breaks exactly the 8 construction sites.
- Corollary for Step 5: the converse proof will introduce the library's **first** case analysis (rule inversion) of `SLYamlStream`.

---

## Dependency Map

### Usage site 1: `PendingNode.close_with_ssl` — `scannerDrop` (line 481)

The `pendingFlow` arm uses `scannerDrop`:

```lean
| pendingFlow =>
    exact SLYamlStream.scannerDrop sp_start sp_block sp_scan sp_mid h_stream h_ssl
```

**Root cause**: `PendingNode.pendingFlow` (`StreamAccum.lean:134–136`) stores only `h_stream : SLYamlStream sp_start sp_block` — there is an opaque gap `sp_block → sp_scan` where flow indicators (`[`, `{`, `]`, `}`, `,`) were scanned, with no grammar evidence retained.

**Fix required**: `pendingFlow` must carry grammar evidence for the gap — see Fix A.

### Usage site 2: `PendingNode.close_with_ssl` — `directiveDrop` (line 505)

The `pendingDirective` arm uses `directiveDrop`:

```lean
| @pendingDirective _ h_dir_acc _ _ =>
    exact SLYamlStream.directiveDrop sp_start sp_block sp_mid
      h_stream (h_dir_acc sp_mid h_ssl)
```

**Root cause**: when directives are encountered without a following `---`, the scanner accumulates them but they never form a document; `directiveDrop` absorbs them. (`pendingDirective`'s own docstring, `StreamAccum.lean:120–122`: "Does NOT carry h_closable — cannot close directives without `---`".)

**Fix required**: see Fix B.

### Usage sites 3–8: `accum_structural_pending` / `accum_step_structural` / `accum_step_block`

All `pendingDirective` transition cases use `directiveDrop`, in the same pattern, **6 times** across 3 lemmas (`accum_structural_pending` lines 1138/1162, `accum_step_structural` lines 1334/1346, `accum_step_block` lines 2794/2814) — always the `pendingDirective` case, in both col=0 and col≠0 sub-cases.

Note: these sites construct `directiveDrop` **directly**, not via `close_with_ssl` — but the fix is shared: once the directive-without-`---` case is resolved, the same construction replaces `directiveDrop` at all 7 sites.

### Summary: two independent fixes

| Fix | Constructor | Usage sites | Root cause |
|-----|-------------|-------------|------------|
| **A** | `scannerDrop` | 1 (line 481) | `pendingFlow` lacks grammar evidence for flow indicators |
| **B** | `directiveDrop` | 7 (lines 505, 1138, 1162, 1334, 1346, 2794, 2814) | orphaned directives not mapped to grammar productions |

---

## Fix A: Eliminating `scannerDrop` — Flow Indicator Grammar Evidence

### Current state

`PendingNode.pendingFlow` (`StreamAccum.lean:134–136`) is used when the scanner processes flow indicators. It carries only the stream at block level:

```lean
| pendingFlow (sp_start sp_block sp_scan : SurfPos)
    (h_stream : SLYamlStream sp_start sp_block) :
    PendingNode sp_start sp_block sp_scan
```

The gap `sp_block → sp_scan` is opaque; at close time, `scannerDrop` absorbs it.

### Required change

Add an `h_closable` field, matching the pattern of `pendingContent` (`StreamAccum.lean:93–97`):

```lean
| pendingFlow (sp_start sp_block sp_scan : SurfPos)
    (h_closable : ∀ sp_mid,
      SSLComments sp_scan sp_mid →
      SLYamlStream sp_start sp_mid) :
    PendingNode sp_start sp_block sp_scan
```

Then at dispatch time (in `accum_step_flow`, §1c, `StreamAccum.lean:1451`), construct the closure by composing:
1. `SFlowSequence` / `SFlowMapping` evidence from `_prod` theorems
2. `SBlockNode.flowInBlock` wrapping (`Surface/Node.lean:89`)
3. Stream extension via `implicitContinue`

### Blocking issue

Recorded as root cause 1 in `StreamAccum.lean`'s §6 Gap Analysis
(`:3264–3272` — the block is marked *historical* because the file's sorries
were discharged, but they were discharged **via** `scannerDrop`; this
obligation is what remains once the escape hatch is removed):

> Blocked on 4i: `_prod` theorems give `SFlowNode 0 .blockIn` but `flowInBlock` needs `SFlowNode (n+1) .flowOut`.

The existing `_prod` theorems (Phase B/C coupling proofs) produce grammar evidence with context parameter `n=0, ctx=blockIn`. But `SBlockNode.flowInBlock` requires `SFlowNode (n+1) .flowOut`. A **context parameter lifting lemma** is needed:

```lean
theorem SFlowNode_context_lift (n : Nat) (ctx : Context) :
    SFlowNode 0 .blockIn sp sp' → SFlowNode (n+1) .flowOut sp sp'
```

This is provable because flow content parsing doesn't depend on block indent level — the grammar rules for `SFlowSequence`, `SFlowMapping`, and `SFlowNode` (`Surface/Node.lean:291/349/245`) are insensitive to `n` and `ctx` at the character level.

### Estimated scope

- Context lifting lemma: ~200 lines (one mutual induction over flow grammar types)
- `h_closable` construction in `accum_step_flow`: ~100 lines
- `pendingFlow` definition change: ~10 lines
- `close_with_ssl` pendingFlow arm: ~5 lines (delegates to `h_closable`)
- **Total: ~300–500 lines**

---

## Fix B: Eliminating `directiveDrop` — Orphaned Directive Resolution

### Scanner behaviour — audit result (2026-08-01, Step 0 done)

Post-reorg locations: the scan pipeline lives in
`L4YAML/Scanner/Scanner.lean` (dispatchers
`scanNextToken_dispatchStructural` at :293,
`scanNextToken_dispatchContent` at :366) and directives are scanned by
`scanDirective` in `L4YAML/Scanner/Document.lean:243` (guard
`c == '%' && s.col == 0` at `Scanner/Scanner.lean:307–309`).

The "directives require `---`" rule is enforced only **partially**. The
error constructor exists — `ScanError.directiveWithoutDocument`
(`Token/Token.lean:316`) — and fires in two situations:

1. **EOF after directives**: `scanLoop` (`Scanner/Scanner.lean:495–497`)
   and `scanLoopFull` (`:555–556`) error when
   `directivesPresent && !documentEverStarted`.
2. **`...` after directives**: `scanDocumentEnd`
   (`Scanner/Document.lean:318–319`).

But the **mid-stream path is lenient**: if a directive is followed by
ordinary content (e.g. `%YAML 1.2\nfoo: bar`), `scanNextToken`
(`Scanner/Scanner.lean:444–449`) sets `documentEverStarted := true`
("Any non-directive, non-document-marker content means we're in a
document"), which suppresses check 1. No error fires; the directives are
orphaned. **This is exactly the path `directiveDrop` absorbs — it is
reachable, not dead code.**

### What the YAML spec says

YAML 1.2.2 §9.1.4 (production [205]): a directive document REQUIRES
`c-directives-end` (`---`). Orphaned directives are not valid YAML; the
lenient path is scanner leniency beyond the spec.

### Resolution options

- **(c) Strengthen the scanner — recommended.** Raise
  `directiveWithoutDocument` in the directive-then-content branch, making
  the lenient path an error like the EOF and `...` cases already are. The
  "close `pendingDirective` without `---`" path becomes unreachable, and
  `directiveDrop` is eliminated by an impossibility proof. Runtime
  behaviour changes only on spec-invalid inputs. ~100 lines of proof
  (plus the scanner change and its `_prod`/strictness lemma updates).
- **(b) Keep the leniency**: prove the parser also accepts
  directive-then-content inputs and extend grammar evidence
  (`SLDocumentPrefix` with directive absorption). ~500 lines, and the
  grammar then over-approximates the spec by design.

### Estimated scope

**Total: ~100–500 lines** depending on the option chosen.

---

## Implementation Plan

- **Step 0 (✅ done 2026-08-01)**: scanner directive audit — findings
  above; decision needed between options (b)/(c), recommendation (c).
- **Step 1**: delete `directiveDrop` and `scannerDrop` from
  `Surface/Document.lean`. The build breaks **only** at the 8
  construction sites in `StreamAccum.lean` (verified — no case analysis
  on `SLYamlStream` exists anywhere).
- **Step 2 (Fix A)**: prove `SFlowNode_context_lift`; change
  `pendingFlow` to carry `h_closable`; construct it at the
  `accum_step_flow` dispatch sites; update `close_with_ssl`.
- **Step 3 (Fix B)**: per the Step 0 decision — strengthen the scanner
  and prove the `pendingDirective` close path unreachable (option c), or
  construct directive-absorbing grammar evidence (option b).
- **Step 4**: full rebuild. `scan_strict_proof` / `parse_strict_proof`
  are automatically strengthened.
- **Step 5**: prove the converse:
  ```lean
  theorem grammar_completeness (input : String) (h : InYamlLanguage input) :
      ∃ docs, parseYaml input = .ok docs
  ```
  This inverts the 3-constructor `SLYamlStream` into scanner+parser
  success — the library's first rule inversion on this inductive.
- **Step 6**: assemble the biconditional from `parse_strict_proof` +
  `grammar_completeness`.

---

## Existing Infrastructure

### Forward direction (parse → grammar): v0.4.6

| Module | Role | LOC (2026-08-01) |
|--------|------|-----|
| `Proofs/Production/StreamAccum.lean` | Threads `SLYamlStream` through the scan loop (26 sub-layers) | 3,322 |
| `Proofs/Production/DocumentProduction.lean` | Composes stream/document-level productions | 261 |
| `Proofs/Scanner/ScanStrictCoupling.lean` | Bridges scanner state to surface positions | 497 |
| `Proofs/Coupling/ScalarCoupling.lean` | Scalar `_prod` theorems (double/single/plain/block) | 765 |
| `Proofs/Coupling/StructureCoupling.lean` | Flow/block indicator productions | 652 |
| `Proofs/Production/StructureProduction.lean` | Node-level grammar composition | 1,315 |

Further coupling material is spread across `Proofs/Coupling/`
(`ScannerCoupling.lean`, `SurfaceCoupling.lean`, `CouplingBridge.lean`)
and `Proofs/Scanner/`.

### Surface grammar: 77 inductive rules (counts verified 2026-08-01)

| File | Rules | Content |
|------|-------|---------|
| `Combinators.lean` | 10 | Generic: `GChar`, `GLit`, `GSeq`, `GSeq3`, `GAlt`, `GStar`, `GPlus`, `GOpt`, `GEps`, `GConsumeAll` |
| `Basic.lean` | 16 | Line breaks, whitespace, indentation, comments, directives |
| `Scalars.lean` | 23 | Double/single-quoted, plain, literal, folded scalars |
| `Node.lean` | 18 | Mutual block/flow collection types (one mutual block) |
| `Document.lean` | 10 | Document markers, types, stream-level rules |

---

## Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Context parameter lifting is harder than expected | Medium | HIGH | The grammar rules are structurally insensitive to `n`/`ctx`; mutual induction over the flow types should work |
| Orphaned directives reachable in the scanner | **Confirmed** (mid-stream leniency) | Medium | Option (c) strengthens the scanner; runtime change on spec-invalid inputs only |
| Removing constructors breaks downstream files | None (verified) | — | No case analysis on `SLYamlStream` exists anywhere; only the 8 construction sites break |
| Converse proof (Step 5) is very large | High | Medium | Grammar inversion touches ~77 rules; many lemmas are mechanical |

---

## Success Criteria

- `directiveDrop` and `scannerDrop` removed from `SLYamlStream`
- `scan_strict_proof` and `parse_strict_proof` still compile with 0 sorry (stronger)
- `grammar_completeness` and `parse_iff_grammar` compile with 0 sorry
- All existing v0.4.6/v0.4.7 proof files maintain 0 sorry
- `parse_iff_grammar` (and `grammar_completeness`, if it stays a
  top-level declaration) added to the `theorem` whitelist in
  `scripts/capstones.txt` (a commented slot for capstone 7.7 is already
  reserved there) and `@[capstone]`-tagged with its axiom profile pinned
  in `L4YAML/Capstones.lean` — every non-whitelisted declaration must use
  `lemma` (`Blueprint/06-discipline.md` Rule 7; enforced by
  `scripts/check-theorem-keyword.sh`)

---

## Estimated Scope

### Phase 1: eliminate over-approximation constructors (Steps 1–4)

| Component | LOC estimate |
|-----------|-------------|
| Remove constructors from `Document.lean` | ~10 |
| Fix A: context lifting + `pendingFlow` `h_closable` | 300–500 |
| Fix B: orphaned directive resolution | 100–500 |
| **Phase 1 subtotal** | **400–1,000** |

### Phase 2: prove the converse (Steps 5–6)

| Component | LOC estimate |
|-----------|-------------|
| Grammar inversion lemmas (77 rules) | 2,000–3,500 |
| `parseStream` acceptance from extracted tokens | 500–1,000 |
| Biconditional assembly | ~100 |
| **Phase 2 subtotal** | **2,500–4,500** |

### Total: **3,000–5,500 lines**
