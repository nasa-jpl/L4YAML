# Version 0.4.8 — Grammar Completeness (Converse Acceptance Strictness)

**Goal:** Prove the grammar completeness theorem — that every string in the YAML 1.2.2 formal language parses successfully — and close the biconditional.

```lean
theorem parse_iff_grammar (input : String) :
    (∃ docs, parseYaml input = .ok docs) ↔ InYamlLanguage input
```

Both directions:
- **Forward** (v0.4.6, proven): `parseYaml input = .ok docs → InYamlLanguage input`
- **Converse** (v0.4.8, target): `InYamlLanguage input → ∃ docs, parseYaml input = .ok docs`

**Status:** Open. Depends on v0.4.7 completion and on eliminating the two over-approximation constructors from `SLYamlStream`.

**Codebase baseline (post-v0.4.7):** Assumes v0.4.7's round-trip proof is complete.

---

## Motivation

Version 0.4.6 proved **acceptance strictness** — if the parser accepts an input, the input is in the YAML language:

```lean
theorem parse_strict_proof : parseYaml input = .ok docs → InYamlLanguage input
theorem scan_strict_proof  : scan input = .ok tokens   → InYamlLanguage input
```

The converse — that every YAML-language string is accepted — is missing. Together these would establish a **biconditional**:

```lean
theorem parse_iff_grammar (input : String) :
    (∃ docs, parseYaml input = .ok docs) ↔ InYamlLanguage input
```

This biconditional would prove the parser accepts **exactly** the YAML 1.2.2 language — no more, no less. This is the strongest correctness statement possible for a parser: soundness (forward), completeness (converse), and their conjunction (biconditional).

### Why this matters

1. **Spec-conformance is bidirectional.** Without the converse, the parser could silently reject valid YAML inputs. v0.4.6 proves it doesn't accept *invalid* inputs; v0.4.8 proves it doesn't reject *valid* ones.

2. **Closes the formal verification story.** The biconditional `parse ↔ grammar` is the gold standard for parser correctness in the formal methods literature. Combined with v0.4.7's round-trip theorem, it establishes: the parser accepts exactly the right inputs, and for the emitter's output subset, the parsed result matches the original.

3. **Enables future refactoring confidence.** Any scanner/parser refactor that preserves the biconditional is provably behaviour-preserving. Without completeness, a refactor could accidentally narrow the accepted language.

---

## The Over-Approximation Problem

`InYamlLanguage` is defined via `SLYamlStream`, which has **5 constructors**:

```lean
inductive SLYamlStream : SurfPos → SurfPos → Prop where
  | single           : GStar SLDocumentPrefix → GOpt SLAnyDocument → GStar SLDocumentSuffix → ...
  | suffixContinue   : SLYamlStream s s₁ → GPlus SLDocumentSuffix → ...
  | implicitContinue : SLYamlStream s s₁ → GStar SLDocumentPrefix → GOpt SLAnyDocument → ...
  | directiveDrop    : SLYamlStream s s₁ → GPlus SLDirective s₁ s' → SLYamlStream s s'
  | scannerDrop      : SLYamlStream s s₁ → SSLComments s₂ s' → SLYamlStream s s'
```

The first three constructors correspond directly to the YAML 1.2.2 §9.1 production [211]. The last two — `directiveDrop` and `scannerDrop` — are **over-approximations** added during the v0.4.6 `scan_strict` proof to accommodate scanner behaviour that doesn't map cleanly to spec productions:

- **`directiveDrop`**: Absorbs orphaned directives (e.g., `%YAML 1.2` without a following document). The scanner accepts these silently; the spec is ambiguous about whether they constitute valid YAML.

- **`scannerDrop`**: Opaque gap matcher for characters consumed by the scanner (e.g., incomplete flow indicators, BOM edge cases) that don't fit a clean grammar production. These represent scanner leniency beyond the spec.

### Consequence for the converse

The over-approximation constructors make `InYamlLanguage` **weaker** than "parseable YAML":

```
parseable inputs ⊂ InYamlLanguage inputs
```

A string can satisfy `InYamlLanguage` (via `scannerDrop`) without being parseable — for example, an unclosed flow sequence `[1, 2` may be accepted by `InYamlLanguage` through `scannerDrop` but rejected by `parseYaml` with an unmatched-bracket error.

**This means the converse theorem is false under the current definition.** The fix: remove the over-approximation constructors, making `InYamlLanguage` exactly characterize the parseable YAML language.

---

## Approach: Eliminate Over-Approximation Constructors

Rather than creating a parallel `StrictInYamlLanguage` definition, we **remove `directiveDrop` and `scannerDrop` directly from `SLYamlStream`**, reducing it to its 3 spec-conforming constructors. This is the cleanest approach:

- No duplication of grammar definitions
- The existing `InYamlLanguage` becomes the biconditional target
- Every existing theorem using `InYamlLanguage` is automatically strengthened
- `scan_strict_proof` is *harder* to prove (no escape hatches), but the theorem itself is *stronger*

The work is concentrated in `StreamAccum.lean` (3,332 lines), which is the only file that constructs `SLYamlStream` values using the over-approximation constructors.

### Impact Analysis

**Files that define the constructors (must change):**
- `Lean4Yaml/Surface/Document.lean` — remove `directiveDrop` and `scannerDrop` from the `SLYamlStream` inductive

**Files that USE the constructors (must fix):**
- `Lean4Yaml/Proofs/StreamAccum.lean` — **all 13 usage sites** are here

**Files that ONLY CONSUME `SLYamlStream` values (no change needed):**
- `Lean4Yaml/Proofs/DocumentProduction.lean` — `scan_strict_proof` delegates to `StreamAccum`; no case analysis on constructors
- All other proof files — only thread `SLYamlStream` existentials, never pattern-match on constructors

---

## Precise Dependency Map

### Usage site 1: `PendingNode.close_with_ssl` (line 465)

The `pendingFlow` arm uses `scannerDrop`:

```lean
| pendingFlow =>
    exact SLYamlStream.scannerDrop sp_start sp_block sp_scan sp_mid h_stream h_ssl
```

**Root cause**: `PendingNode.pendingFlow` only stores `h_stream : SLYamlStream sp_start sp_block` — there is an opaque gap `sp_block → sp_scan` where flow indicators (`[`, `{`, `]`, `}`, `,`) were scanned, with no grammar evidence retained.

**Fix required**: `pendingFlow` must carry grammar evidence for the gap. Options:
- (a) Carry a partial `SFlowSequence`/`SFlowMapping` accumulator inside `pendingFlow`, then close it + compose with SSLComments
- (b) Carry an `h_closable` closure (like `pendingContent`) that captures the grammar evidence at dispatch time
- (c) Eliminate `pendingFlow` entirely by constructing the grammar production at dispatch time and transitioning to `pendingContent`

Option (b) is the most consistent with the existing architecture. This is listed as **Sorry Root Cause 1** in `StreamAccum.lean §6`.

### Usage site 2: `PendingNode.close_with_ssl` (line 501)

The `pendingDirective` arm uses `directiveDrop`:

```lean
| @pendingDirective _ h_dir_acc _ _ =>
    exact SLYamlStream.directiveDrop sp_start sp_block sp_mid
      h_stream (h_dir_acc sp_mid h_ssl)
```

**Root cause**: When directives are encountered without a following `---`, the scanner accumulates them but they never form a document. `directiveDrop` absorbs them.

**Fix required**: Show that the scanner DOES form a document from orphaned directives — or show that this code path is unreachable (the scanner always errors or always emits `---` after directives). This requires auditing the scanner's directive handling to determine which case applies.

### Usage sites 3–12: `accum_step_structural/flow/block/content` (lines 1129–2826)

All `pendingDirective` transition cases use `directiveDrop`:

```lean
| @pendingDirective sp_scan h_dir_acc_old h_stream_old h_at_line_end_old =>
    ...
    have h_stream_mid : SLYamlStream sp_start sp_mid :=
      SLYamlStream.directiveDrop sp_start sp_block sp_mid
        h_stream_old (h_dir_acc_old sp_mid h_ssl)
```

This pattern occurs **10 times** across 4 `accum_step_*` theorems (§1b through §1e), always in the `pendingDirective` case (both col=0 and col≠0 sub-cases).

**Root cause**: Same as usage site 2 — closing pending directives without `---`.

**Fix required**: Same resolution as usage site 2. Once `close_with_ssl` is fixed for `pendingDirective`, all 10 downstream sites are automatically fixed (they delegate to `close_with_ssl`).

Wait — actually, only usage sites 3–12 construct `directiveDrop` directly, not through `close_with_ssl`. Let me verify:

Actually, reviewing the code more carefully: the `accum_step_*` theorems construct `directiveDrop` directly (not via `close_with_ssl`). However, the fix is the same — once the directive-without-`---` case is resolved, the same construction replaces `directiveDrop` everywhere.

### Summary: Two independent fixes needed

| Fix | Constructor to eliminate | Usage sites | Root cause |
|-----|------------------------|-------------|------------|
| **Fix A** | `scannerDrop` | 1 site (line 477) | `pendingFlow` lacks grammar evidence for flow indicators |
| **Fix B** | `directiveDrop` | 12 sites (lines 501, 1134, 1158, 1330, 1342, 2806, 2826, + 5 more) | Orphaned directives not mapped to grammar productions |

---

## Fix A: Eliminating `scannerDrop` — Flow Indicator Grammar Evidence

### Current state

`PendingNode.pendingFlow` is used when the scanner processes flow indicators (`]`, `}`, `,`). It carries only the stream at block level, with no grammar evidence for the characters consumed:

```lean
| pendingFlow (sp_start sp_block sp_scan : SurfPos)
    (h_stream : SLYamlStream sp_start sp_block) :
    PendingNode sp_start sp_block sp_scan
```

The gap `sp_block → sp_scan` is opaque. At close time, `scannerDrop` absorbs it.

### Required change

Add an `h_closable` field, matching the pattern of `pendingContent`:

```lean
| pendingFlow (sp_start sp_block sp_scan : SurfPos)
    (h_closable : ∀ sp_mid,
      SSLComments sp_scan sp_mid →
      SLYamlStream sp_start sp_mid) :
    PendingNode sp_start sp_block sp_scan
```

Then at dispatch time (in `accum_step_flow`, §1c), construct the closure by composing:
1. `SFlowSequence` / `SFlowMapping` evidence from `_prod` theorems
2. `SBlockNode.flowInBlock` wrapping
3. Stream extension via `implicitContinue`

### Blocking issue

This is **Sorry Root Cause 1** from `StreamAccum.lean §6`:

> Blocked on 4i: `_prod` theorems give `SFlowNode 0 .blockIn` but `flowInBlock` needs `SFlowNode (n+1) .flowOut`.

The existing `_prod` theorems (Phase B/C coupling proofs) produce grammar evidence with context parameter `n=0, ctx=blockIn`. But the grammar's `SBlockNode.flowInBlock` constructor requires `SFlowNode (n+1) .flowOut`. A **context parameter lifting lemma** is needed:

```lean
theorem SFlowNode_context_lift (n : Nat) (ctx : Context) :
    SFlowNode 0 .blockIn sp sp' → SFlowNode (n+1) .flowOut sp sp'
```

This is provable because flow content parsing doesn't depend on block indent level — the grammar rules for `SFlowSequence`, `SFlowMapping`, and `SFlowNode` are insensitive to `n` and `ctx` at the character level.

### Estimated scope

- Context lifting lemma: ~200 lines (one mutual induction over flow grammar types)
- `h_closable` construction in `accum_step_flow`: ~100 lines (compose `_prod` + lift + `flowInBlock` + stream extension)
- `pendingFlow` definition change: ~10 lines
- `close_with_ssl` pendingFlow arm: ~5 lines (now delegates to `h_closable`)
- **Total: ~300–500 lines**

---

## Fix B: Eliminating `directiveDrop` — Orphaned Directive Resolution

### Current state

When the scanner encounters a `%YAML` or `%TAG` directive, it enters `pendingDirective` mode. If a `---` follows, the directives + `---` compose into an explicit document (`SLExplicitDocument`). But if some OTHER content follows (scalar, flow indicator, EOF), the directives are "orphaned" — they don't form a document.

Currently, `directiveDrop` absorbs orphaned directives. The question is: **does the scanner actually allow orphaned directives?**

### Scanner behaviour audit needed

Check `Scanner.lean` to determine what happens when directives are followed by content other than `---`:

1. Does `dispatchStructural` process `---` after directives specifically?
2. Does `dispatchContent` ever fire when `pendingDirective` is active?
3. Is there a scanner error for "directive without `---`"?

**If the scanner always produces `---` after directives:** Then `pendingDirective` always transitions to `pendingDocStart`, and the `directiveDrop` path is dead code — unreachable by construction. The fix is to show it's unreachable and remove the path.

**If the scanner accepts directives without `---`:** Then we need to either:
- (a) Show the scanner extends the grammar (adds an `implicitContinue` with directives absorbed into document prefix), or
- (b) Prove the parser also accepts such inputs, or
- (c) Strengthen the scanner to reject orphaned directives

### What the YAML spec says

YAML 1.2.2 §9.1.4 (production [205]): A directive document REQUIRES `c-directives-end` (`---`). Orphaned directives are not valid YAML per the spec. If the scanner accepts them, it's scanner leniency beyond the spec.

Given this, the most likely resolution is (a) or showing unreachability — the scanner probably does emit `---` after directives in all valid paths.

### Estimated scope

- Scanner audit: ~2 hours of code reading
- If unreachable: ~100 lines (prove the `pendingDirective → non-directivesDrop` transition is impossible)
- If reachable: ~500 lines (construct proper grammar evidence using `SLDocumentPrefix` with directive absorption)
- **Total: ~100–500 lines**

---

## Implementation Plan

### Step 0: Scanner audit for directive handling

Audit `Scanner.lean` to determine whether orphaned directives can reach `close_with_ssl`. This determines the scope of Fix B.

### Step 1: Remove constructors from `SLYamlStream`

Delete `directiveDrop` and `scannerDrop` from `Surface/Document.lean`. The build will break in `StreamAccum.lean` only — all other files thread `SLYamlStream` existentials without pattern matching.

### Step 2: Fix A — Flow indicator grammar evidence

1. Write the context parameter lifting lemma (`SFlowNode_context_lift`)
2. Change `pendingFlow` to carry `h_closable`
3. Construct `h_closable` at dispatch sites in `accum_step_flow`
4. Update `close_with_ssl` to use `h_closable` instead of `scannerDrop`

### Step 3: Fix B — Orphaned directive resolution

Based on the Step 0 audit:
- If unreachable: prove impossibility and delete the `pendingDirective` arm of `close_with_ssl` dealing with `directiveDrop`
- If reachable: construct proper grammar evidence

### Step 4: Build and verify

Full rebuild. The existing `scan_strict_proof` and `parse_strict_proof` theorems are automatically strengthened — they now produce the stronger `InYamlLanguage` (without over-approximation).

### Step 5: Prove the converse

With `InYamlLanguage` now exactly characterizing parseable inputs, prove:

```lean
theorem grammar_completeness (input : String) (h : InYamlLanguage input) :
    ∃ docs, parseYaml input = .ok docs
```

This requires inverting the 3-constructor `SLYamlStream` into scanner+parser success.

### Step 6: Assemble the biconditional

```lean
theorem parse_iff_grammar (input : String) :
    (∃ docs, parseYaml input = .ok docs) ↔ InYamlLanguage input :=
  ⟨fun ⟨docs, h⟩ => (parse_sound input docs h).elim fun _ => scan_strict_proof ...,
   fun h => grammar_completeness input h⟩
```

---

## Existing Infrastructure

### Forward direction (parse → grammar): v0.4.6

The v0.4.6 proof suite constructs grammar derivation trees from successful parses. Key modules:

| Module | Role | LOC |
|--------|------|-----|
| `StreamAccum.lean` | Threads `SLYamlStream` through the scan loop (26 sub-layers) | 3,332 |
| `DocumentProduction.lean` | Composes stream/document-level productions | ~200 |
| `ScanStrictCoupling.lean` | Bridges scanner state to surface positions | ~1,500 |
| `ScalarCoupling.lean` | Scalar `_prod` theorems (double/single/plain/block) | ~4,000 |
| `StructureCoupling.lean` | Flow/block indicator productions | ~800 |
| `StructureProduction.lean` | Node-level grammar composition | ~1,200 |

### Surface grammar: 77 inductive types

| File | Rules | Content |
|------|-------|---------|
| `Combinators.lean` | 10 | Generic: `GChar`, `GLit`, `GSeq`, `GAlt`, `GStar`, `GPlus`, `GOpt`, `GEps` |
| `Basic.lean` | 16 | Line breaks, whitespace, indentation, comments, directives |
| `Scalars.lean` | 23 | Double/single-quoted, plain, literal, folded scalars |
| `Node.lean` | 18 | Mutual block/flow collection types (11 mutually recursive) |
| `Document.lean` | 10 | Document markers, types, stream-level rules |

### `StreamAccum.lean` sorry inventory (v0.4.6)

The file has 6 sorry declarations across 24 source sites, concentrated in 3 root causes:

| Root cause | Description | Sorry sites | Blocks |
|------------|-------------|-------------|--------|
| **h_closable construction** | `PendingNode` closures for content/flow dispatch need `_prod` → `SFlowNode` → `SBlockNode.flowInBlock` composition | ~16 | `scannerDrop` elimination (Fix A) |
| **BOM col≠0** | SSeparateInLine at col=1 after BOM — genuine grammar edge case | ~6 | Neither constructor (independent) |
| **Context parameter lifting** | `_prod` gives `SFlowNode 0 .blockIn`, need `SFlowNode (n+1) .flowOut` | blocked by | h_closable construction |

---

## Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Context parameter lifting is harder than expected | Medium | HIGH | The grammar rules are structurally insensitive to `n`/`ctx`; mutual induction should work |
| Orphaned directives ARE reachable in the scanner | Medium | Medium | Even if reachable, the fix is to construct proper grammar evidence, not to abandon the approach |
| BOM col≠0 sorry is a genuine grammar limitation | High | Low | This sorry exists independently of the over-approximation constructors; it doesn't block Fix A or Fix B |
| Removing constructors breaks downstream files | Low | Low | Verified: only `StreamAccum.lean` pattern-matches on the removed constructors |
| Converse proof (Step 5) is very large | High | Medium | Grammar inversion requires ~77 lemmas; but many are mechanical |

---

## Dependencies

- **v0.4.7 must be complete first.** The round-trip proof exercises the emit→scan→parse pipeline and may reveal issues relevant to the converse direction.
- **Scanner audit (Step 0) determines Fix B scope.** This should be done early to reduce uncertainty.

---

## Success Criteria

- `directiveDrop` and `scannerDrop` removed from `SLYamlStream`
- `scan_strict_proof` and `parse_strict_proof` still compile with 0 sorry (stronger)
- `grammar_completeness` compiles with 0 sorry
- `parse_iff_grammar` (biconditional) compiles with 0 sorry
- All existing v0.4.6 and v0.4.7 proof files maintain 0 sorry
- BOM col≠0 sorry may remain (independent of this version's goals)

---

## Estimated Scope

### Phase 1: Eliminate over-approximation constructors (Steps 0–4)

| Component | LOC estimate |
|-----------|-------------|
| Scanner directive audit | ~0 (reading, not code) |
| Remove constructors from `Document.lean` | ~10 |
| Fix A: context lifting + `pendingFlow` `h_closable` | 300–500 |
| Fix B: orphaned directive resolution | 100–500 |
| **Phase 1 subtotal** | **400–1,000** |

### Phase 2: Prove the converse (Steps 5–6)

| Component | LOC estimate |
|-----------|-------------|
| Grammar inversion lemmas (77 rules) | 2,000–3,500 |
| `parseStream` acceptance from extracted tokens | 500–1,000 |
| Biconditional assembly | ~100 |
| **Phase 2 subtotal** | **2,500–4,500** |

### Total: **3,000–5,500 lines**
