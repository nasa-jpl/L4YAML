/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Production.ScalarProduction
public import L4YAML.Proofs.Production.StructureProduction

public meta import L4YAML.Spec.YamlSpec
@[expose] public section Blanket

/-! # Node Production Coupling (Layer 2 of v0.4.6)

    Compose Layer 1 scalar `_prod` theorems and Phase C structural `_prod`
    theorems into the `SFlowContent` / `SFlowNode` / `SBlockNode` hierarchy.

    ## Architecture

    - §1: Pure composition — scalar → `SFlowContent` (parametric in n/c)
    - §2: Pure composition — `SFlowContent` → `SFlowNode`
    - §3: Pure composition — `SFlowNode` / scalars → `SBlockNode`
    - §4: Scanner-to-`SFlowContent` production coupling (n=0, c=.blockIn)
    - §5: Scanner-to-`SFlowNode` production coupling (n=0, c=.blockIn)

    The composition from `SFlowNode` to `SBlockNode.flowInBlock` requires
    `SSeparate` (from scan preprocessing) and `SSLComments` (from post-content
    whitespace handling). These are contextual — they come from the scan loop,
    not from individual scanner functions. The parametric §3 lemmas provide
    the building blocks; Layer 3 supplies the context.

    Similarly, collections (`SBlockNode.blockSeq`/`blockMap`) span multiple
    `scanNextToken` calls and require loop-level accumulation (Layer 3).
-/

set_option autoImplicit false

namespace L4YAML.Proofs.NodeProduction

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScalarProduction
open L4YAML.Proofs.StructureProduction

/-! ## §1 Pure Composition: Scalar → SFlowContent -/

-- [154] c-flow-json-content: double-quoted scalar.
lemma doubleQuoted_flowContent {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SCDoubleQuoted n c s s') :
    SFlowContent n c s s' :=
  SFlowContent.doubleQ n c s s' h

-- [154] c-flow-json-content: single-quoted scalar.
lemma singleQuoted_flowContent {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SCSingleQuoted n c s s') :
    SFlowContent n c s s' :=
  SFlowContent.singleQ n c s s' h

-- [159] ns-flow-yaml-content: plain scalar.
lemma plain_flowContent {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SNsPlain n c s s') :
    SFlowContent n c s s' :=
  SFlowContent.plain n c s s' h

-- [154] c-flow-json-content: flow sequence.
lemma flowSeq_flowContent {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SFlowSequence n c s s') :
    SFlowContent n c s s' :=
  SFlowContent.flowSeq n c s s' h

-- [154] c-flow-json-content: flow mapping.
lemma flowMap_flowContent {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SFlowMapping n c s s') :
    SFlowContent n c s s' :=
  SFlowContent.flowMap n c s s' h

/-! ## §2 Pure Composition: SFlowContent → SFlowNode -/

-- [161] ns-flow-node: bare content (no properties).
lemma flowContent_flowNode {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SFlowContent n c s s') :
    SFlowNode n c s s' :=
  SFlowNode.content n c s s' h

-- [161] ns-flow-node: alias reference.
lemma alias_flowNode {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SCNsAliasNode s s') :
    SFlowNode n c s s' :=
  SFlowNode.alias n c s s' h

-- [161] ns-flow-node: properties + separator + content.
lemma propsContent_flowNode {n : Nat} {c : YamlContext}
    {s s₁ s₂ s' : SurfPos}
    (h_props : SCNsProperties n c s s₁)
    (h_sep : SSeparate n c s₁ s₂)
    (h_content : SFlowContent n c s₂ s') :
    SFlowNode n c s s' :=
  SFlowNode.propsContent n c s s₁ s₂ s' h_props h_sep h_content

-- [161] ns-flow-node: properties only (empty content).
lemma propsEmpty_flowNode {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h_props : SCNsProperties n c s s') :
    SFlowNode n c s s' :=
  SFlowNode.propsEmpty n c s s' h_props

/-! ## §3 Pure Composition: SFlowNode / Scalars → SBlockNode -/

-- [195] s-l+flow-in-block(n,c): separator + flow node + comments.
lemma flowInBlock_blockNode {n : Nat} {c : YamlContext}
    {s s₁ s₂ s' : SurfPos}
    (h_sep : SSeparate n .flowOut s s₁)
    (h_flow : SFlowNode n .flowOut s₁ s₂)
    (h_comments : SSLComments s₂ s') :
    SBlockNode n c s s' :=
  SBlockNode.flowInBlock n c s s₁ s₂ s' h_sep h_flow h_comments

-- [198] s-l+block-scalar: separator + optional properties + literal scalar.
lemma literal_blockNode {n : Nat} {c : YamlContext}
    {s s₁ s₂ s' : SurfPos}
    (h_sep : SSeparate n c s s₁)
    (h_props : GOpt (GSeq (SCNsProperties n c) (SSeparate n c)) s₁ s₂)
    (h_lit : SCLLiteral n s₂ s') :
    SBlockNode n c s s' :=
  SBlockNode.blockLiteral n c s s₁ s₂ s' h_sep h_props h_lit

-- [198] s-l+block-scalar: separator + optional properties + folded scalar.
lemma folded_blockNode {n : Nat} {c : YamlContext}
    {s s₁ s₂ s' : SurfPos}
    (h_sep : SSeparate n c s s₁)
    (h_props : GOpt (GSeq (SCNsProperties n c) (SSeparate n c)) s₁ s₂)
    (h_fold : SCLFolded n s₂ s') :
    SBlockNode n c s s' :=
  SBlockNode.blockFolded n c s s₁ s₂ s' h_sep h_props h_fold

-- [72] e-node + s-l-comments: empty node.
lemma emptyNode_blockNode {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SSLComments s s') :
    SBlockNode n c s s' :=
  SBlockNode.emptyNode n c s s' h

/-! ## §4 Scanner-to-SFlowContent Production (n=0, c=.blockIn) -/

-- `scanDoubleQuoted` success → `SFlowContent 0 .blockIn`.
lemma scanDoubleQuoted_flowContent_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_dq : sc.peek? = some '"')
    (hok : scanDoubleQuoted sc = .ok s') :
    ∃ sp', SFlowContent 0 .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨sp', h_dq, -, hcorr'⟩ := scanDoubleQuoted_prod sc sp hcorr hpeek_dq hok
  exact ⟨sp', doubleQuoted_flowContent h_dq, hcorr'⟩

-- `scanSingleQuoted` success → `SFlowContent 0 .blockIn`.
lemma scanSingleQuoted_flowContent_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_sq : sc.peek? = some '\'')
    (hok : scanSingleQuoted sc = .ok s') :
    ∃ sp', SFlowContent 0 .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨sp', h_sq, -, hcorr'⟩ := scanSingleQuoted_prod sc sp hcorr hpeek_sq hok
  exact ⟨sp', singleQuoted_flowContent h_sq, hcorr'⟩

/-! ## §5 Scanner-to-SFlowNode Production (n=0, c=.blockIn) -/

-- `scanDoubleQuoted` success → `SFlowNode 0 .blockIn`.
lemma scanDoubleQuoted_flowNode_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_dq : sc.peek? = some '"')
    (hok : scanDoubleQuoted sc = .ok s') :
    ∃ sp', SFlowNode 0 .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨sp', h_fc, hcorr'⟩ := scanDoubleQuoted_flowContent_prod sc sp hcorr hpeek_dq hok
  exact ⟨sp', flowContent_flowNode h_fc, hcorr'⟩

-- `scanSingleQuoted` success → `SFlowNode 0 .blockIn`.
lemma scanSingleQuoted_flowNode_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_sq : sc.peek? = some '\'')
    (hok : scanSingleQuoted sc = .ok s') :
    ∃ sp', SFlowNode 0 .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨sp', h_fc, hcorr'⟩ := scanSingleQuoted_flowContent_prod sc sp hcorr hpeek_sq hok
  exact ⟨sp', flowContent_flowNode h_fc, hcorr'⟩

/-! ## §5a Context Compatibility: Lifting across YamlContext (Layer 4i building blocks)

    For double-quoted and single-quoted scalars, the body text productions
    ([110] `nb-double-text(n,c)` / [119] `nb-single-text(n,c)`) dispatch on
    context `c` into two equivalence classes:
      - key contexts (`.blockKey`, `.flowKey`) → one-line body
      - non-key contexts (`.flowOut`, `.flowIn`, `.blockOut`, `.blockIn`)
        → multi-line body, parameterized only by `n`
    Within the non-key class all four contexts reduce to the SAME multi-line
    body, so a `SCDoubleQuoted n c₁` / `SCSingleQuoted n c₁` witness can be
    relabelled to any other non-key context (same `n`).

    This is a building block for Layer 4i (context parameter lifting).
    Once `_prod` theorems are strengthened to produce at the scanner's
    actual indent `n`, these lifts bridge `.blockIn → .flowOut` for free.

    Note: `SSeparate n c` for non-key contexts (blockOut/blockIn/flowOut/flowIn)
    all reduce to `SSeparateLines n` definitionally. No explicit lemma needed.

    Note: Plain scalar (`SNsPlain n c`) context lift DOES hold for
    `.blockIn → .flowOut` because `isNsPlainSafe .blockIn` and
    `isNsPlainSafe .flowOut` are both `isNsChar ch` (same match arm).
    It does NOT hold for `.blockIn → .flowIn` (flow indicators forbidden).
    The general multi-line lift requires `SLEmpty` conversion
    (`.block` → `.flow` constructor change), but for the minimal witness
    (first char only, `GStar.nil` continuations) it's trivial.
    `SNsPlain_blockIn_to_flowOut_minimal` handles the minimal-witness case. -/

-- Plain scalar first-char context lift: `.blockIn → .flowOut`.
-- Works because `isNsPlainSafe .blockIn ch = isNsPlainSafe .flowOut ch` definitionally.
lemma SNsPlainFirst_blockIn_to_flowOut {s s' : SurfPos}
    (h : SNsPlainFirst .blockIn s s') : SNsPlainFirst .flowOut s s' := by
  cases h with
  | nonIndicator ch rest col hSafe hNotInd =>
    exact SNsPlainFirst.nonIndicator .flowOut ch rest col hSafe hNotInd
  | dashSafe next rest col hSafe =>
    exact SNsPlainFirst.dashSafe .flowOut next rest col hSafe
  | colonSafe next rest col hSafe =>
    exact SNsPlainFirst.colonSafe .flowOut next rest col hSafe
  | questionSafe next rest col hSafe =>
    exact SNsPlainFirst.questionSafe .flowOut next rest col hSafe

-- Plain scalar minimal witness context lift: `.blockIn → .flowOut`.
-- Works for the minimal witness from `scanPlainScalar_prod` which has
-- `GStar.nil` for both inline entries and continuation lines.
-- Converts: SNsPlainMultiLine.mk 0 .blockIn s s₁ s₁
--             (SNsPlainOneLine.mk .blockIn s s₁ s₁ h_first (GStar.nil _))
--             (GStar.nil _)
-- to the .flowOut version.
lemma SNsPlain_blockIn_to_flowOut_minimal {s s₁ : SurfPos}
    (h_first : SNsPlainFirst .blockIn s s₁) :
    SNsPlain 0 .flowOut s s₁ :=
  SNsPlainMultiLine.mk 0 .flowOut s s₁ s₁
    (SNsPlainOneLine.mk .flowOut s s₁ s₁
      (SNsPlainFirst_blockIn_to_flowOut h_first) (GStar.nil _))
    (GStar.nil _)

-- Plain scalar → SFlowNode context lift for minimal witness.
-- Composes: SNsPlainFirst .blockIn → SNsPlain 0 .flowOut → SFlowContent → SFlowNode.
lemma SFlowNode_plain_blockIn_to_flowOut_minimal {s s₁ : SurfPos}
    (h_first : SNsPlainFirst .blockIn s s₁) :
    SFlowNode 0 .flowOut s s₁ :=
  flowContent_flowNode (plain_flowContent (SNsPlain_blockIn_to_flowOut_minimal h_first))

-- [109] c-double-quoted context lift between non-key contexts (same n).
-- The body production [110] `nb-double-text(n,c)` reduces to
-- `SNbDoubleMultiLine n` for every non-key context (c ∉ {.blockKey, .flowKey}),
-- so the `SCDoubleQuoted` middle witness is identical across the four non-key
-- contexts. The lift relabels c₁ → c₂ at the same indent `n`; the precondition
-- on both endpoints is required because the key contexts use a different body
-- (`SNbDoubleOneLine`) and the lift across that boundary does not hold.
@[yaml_spec "7.3.1" 109 "c-double-quoted(n,c) context lift between non-key contexts (same n)"]
lemma SCDoubleQuoted_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
    (h : SCDoubleQuoted n c₁ s s')
    (hc₁ : c₁ ≠ .blockKey ∧ c₁ ≠ .flowKey)
    (hc₂ : c₂ ≠ .blockKey ∧ c₂ ≠ .flowKey) :
    SCDoubleQuoted n c₂ s s' := by
  obtain ⟨_, _, _, h_open, h_text, h_close⟩ := h
  refine SCDoubleQuoted.mk n c₂ _ _ _ _ h_open ?_ h_close
  obtain ⟨hc₁_bk, hc₁_fk⟩ := hc₁
  obtain ⟨hc₂_bk, hc₂_fk⟩ := hc₂
  cases c₁ <;> cases c₂ <;> simp_all [SNbDoubleText]

-- [120] c-single-quoted context lift between non-key contexts (same n).
-- The body production [119] `nb-single-text(n,c)` reduces to
-- `SNbSingleMultiLine n` for every non-key context (c ∉ {.blockKey, .flowKey}),
-- so the `SCSingleQuoted` middle witness is identical across the four non-key
-- contexts. The lift relabels c₁ → c₂ at the same indent `n`; the precondition
-- on both endpoints is required because the key contexts use a different body
-- (`SNbSingleOneLine`) and the lift across that boundary does not hold.
@[yaml_spec "7.3.1" 120 "c-single-quoted(n,c) context lift between non-key contexts (same n)"]
lemma SCSingleQuoted_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
    (h : SCSingleQuoted n c₁ s s')
    (hc₁ : c₁ ≠ .blockKey ∧ c₁ ≠ .flowKey)
    (hc₂ : c₂ ≠ .blockKey ∧ c₂ ≠ .flowKey) :
    SCSingleQuoted n c₂ s s' := by
  obtain ⟨_, _, _, h_open, h_text, h_close⟩ := h
  refine SCSingleQuoted.mk n c₂ _ _ _ _ h_open ?_ h_close
  obtain ⟨hc₁_bk, hc₁_fk⟩ := hc₁
  obtain ⟨hc₂_bk, hc₂_fk⟩ := hc₂
  cases c₁ <;> cases c₂ <;> simp_all [SNbSingleText]

-- SFlowContent context lift for quoted scalars.
-- Works for double-quoted, single-quoted, and alias (which has no context).
-- Does NOT work for plain scalars or flow collections in general.
lemma SFlowContent_doubleQ_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
    (h : SCDoubleQuoted n c₁ s s')
    (hc₁ : c₁ ≠ .blockKey ∧ c₁ ≠ .flowKey)
    (hc₂ : c₂ ≠ .blockKey ∧ c₂ ≠ .flowKey) :
    SFlowContent n c₂ s s' :=
  doubleQuoted_flowContent (SCDoubleQuoted_ctx_lift h hc₁ hc₂)

lemma SFlowContent_singleQ_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
    (h : SCSingleQuoted n c₁ s s')
    (hc₁ : c₁ ≠ .blockKey ∧ c₁ ≠ .flowKey)
    (hc₂ : c₂ ≠ .blockKey ∧ c₂ ≠ .flowKey) :
    SFlowContent n c₂ s s' :=
  singleQuoted_flowContent (SCSingleQuoted_ctx_lift h hc₁ hc₂)

-- SFlowNode context lift for quoted scalars (bare content, no properties).
lemma SFlowNode_doubleQ_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
    (h : SCDoubleQuoted n c₁ s s')
    (hc₁ : c₁ ≠ .blockKey ∧ c₁ ≠ .flowKey)
    (hc₂ : c₂ ≠ .blockKey ∧ c₂ ≠ .flowKey) :
    SFlowNode n c₂ s s' :=
  flowContent_flowNode (SFlowContent_doubleQ_ctx_lift h hc₁ hc₂)

lemma SFlowNode_singleQ_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
    (h : SCSingleQuoted n c₁ s s')
    (hc₁ : c₁ ≠ .blockKey ∧ c₁ ≠ .flowKey)
    (hc₂ : c₂ ≠ .blockKey ∧ c₂ ≠ .flowKey) :
    SFlowNode n c₂ s s' :=
  flowContent_flowNode (SFlowContent_singleQ_ctx_lift h hc₁ hc₂)

/-! ### §3b A break-free reading mentions no indent (item 23)

`[196] s-l+block-node(n,c)`'s flow arm reads its value at the ENTRY's index —
`SBlockNode.flowInBlock n` takes `SSeparate n .flowOut` and `SFlowNode n
.flowOut` — while every content reading the accumulation produces is stated
at 0.  Widening one to the other is NOT a monotonicity fact and is false in
general: the index occurs in `[71] s-flow-line-prefix(n)` and in `[134]
s-ns-plain-next-line(n,c)`, both of which sit AFTER a line break, and a
reading at 0 admits continuation lines that a reading at `n` forbids.

It holds for one structural reason: **a derivation that crosses no break
contains no occurrence of the index at all.**  The spec says so in its own
vocabulary — `[111] nb-double-one-line` and `[122] nb-single-one-line` are
`GStar` of a character class, `[133] ns-plain-one-line(c)` takes only the
context, and `[104] c-ns-alias-node` takes neither.  So the one-line readings
items 15–17 already extract for the implicit KEY re-read at every index too,
and these lifts are constructor rebuilds with no induction on the span.

The `.blockKey → .flowOut` half is free alongside it: `isNsPlainSafe` selects
the same `isNsChar` arm at both, and the quoted bodies differ only in that the
key context fixes the one-line body the lift is starting from.

What this does NOT reach, and why, is recorded at the deferral sites:
`[170]`/`[174]`'s block scalars auto-detect their own content indent (the
reading at 0 pins the same existential item 22 had to bind on `[183]`/`[187]`),
and the flow collections carry the index inside `SSeparate n c` slots that a
rebuild cannot reach without descending the whole mutual family. -/

-- [126] ns-plain-first(c) relabelled `.blockKey → .flowOut`: `isNsPlainSafe`
-- selects `isNsChar` at both, so every field transports verbatim.
lemma SNsPlainFirst_blockKey_to_flowOut {s s' : SurfPos}
    (h : SNsPlainFirst .blockKey s s') : SNsPlainFirst .flowOut s s' := by
  cases h with
  | nonIndicator ch rest col hSafe hNotInd =>
    exact SNsPlainFirst.nonIndicator .flowOut ch rest col hSafe hNotInd
  | dashSafe next rest col hSafe =>
    exact SNsPlainFirst.dashSafe .flowOut next rest col hSafe
  | colonSafe next rest col hSafe =>
    exact SNsPlainFirst.colonSafe .flowOut next rest col hSafe
  | questionSafe next rest col hSafe =>
    exact SNsPlainFirst.questionSafe .flowOut next rest col hSafe

-- [130] ns-plain-char(c), the same relabelling.
lemma SNsPlainChar_blockKey_to_flowOut {s s' : SurfPos}
    (h : SNsPlainChar .blockKey s s') : SNsPlainChar .flowOut s s' := by
  cases h with
  | safe ch rest col hSafe hNotColon hNotHash =>
    exact SNsPlainChar.safe .flowOut ch rest col hSafe hNotColon hNotHash
  | colonSafe prev next rest col hSafe =>
    exact SNsPlainChar.colonSafe .flowOut prev next rest col hSafe

-- [132] nb-ns-plain-in-line(c), one repetition unit.
lemma SNbNsPlainInLineEntry_blockKey_to_flowOut {s s' : SurfPos}
    (h : SNbNsPlainInLineEntry .blockKey s s') :
    SNbNsPlainInLineEntry .flowOut s s' :=
  match h with
  | .mk _ _ s₁ _ h_ws h_ch =>
    .mk .flowOut s s₁ s' h_ws (SNsPlainChar_blockKey_to_flowOut h_ch)
  | .hash _ _ _ h_lit => .hash .flowOut s s' h_lit

-- The intra-line repetition itself: the only induction the plain lift needs,
-- and it is over the star, not over the grammar.
lemma gstar_plainInLine_blockKey_to_flowOut {s s' : SurfPos}
    (h : GStar (SNbNsPlainInLineEntry .blockKey) s s') :
    GStar (SNbNsPlainInLineEntry .flowOut) s s' := by
  induction h with
  | nil s => exact GStar.nil s
  | cons s₁ s₂ s₃ h_first _ ih =>
    exact GStar.cons s₁ s₂ s₃ (SNbNsPlainInLineEntry_blockKey_to_flowOut h_first) ih

-- [133] ns-plain-one-line(c) relabelled `.blockKey → .flowOut`.
@[yaml_spec "7.3.3" 133 "ns-plain-one-line(c) context lift (blockKey → flowOut)"]
lemma SNsPlainOneLine_blockKey_to_flowOut {s s' : SurfPos}
    (h : SNsPlainOneLine .blockKey s s') : SNsPlainOneLine .flowOut s s' :=
  match h with
  | .mk _ _ s₁ _ h_first h_rest =>
    .mk .flowOut s s₁ s'
      (SNsPlainFirst_blockKey_to_flowOut h_first)
      (gstar_plainInLine_blockKey_to_flowOut h_rest)

-- [131] ns-plain(n,flow-out) from a one-line body, at EVERY index: `[135]
-- ns-plain-multi-line(n,c)`'s continuation star is the only place `n` occurs,
-- and a one-line reading leaves it empty.
lemma SNsPlain_of_oneLine_flowOut (n : Nat) {s s' : SurfPos}
    (h : SNsPlainOneLine .flowOut s s') : SNsPlain n .flowOut s s' :=
  SNsPlainMultiLine.mk n .flowOut s s' s' h (GStar.nil _)

-- [156] ns-flow-content(n,flow-out) from item 15's `.blockKey` one-line plain
-- witness, at every index.  Item 24 wants the CONTENT rather than the node:
-- `[161]`'s `propsContent` arm slots `ns-flow-content` under a property run,
-- so a decorated value needs the reading one production lower down.
lemma SFlowContent_plain_of_keyOneLine (n : Nat) {s s' : SurfPos}
    (h : SNsPlainOneLine .blockKey s s') : SFlowContent n .flowOut s s' :=
  plain_flowContent (SNsPlain_of_oneLine_flowOut n (SNsPlainOneLine_blockKey_to_flowOut h))

-- [161] ns-flow-node(n,flow-out): the bare node is that content unwrapped.
lemma SFlowNode_plain_of_keyOneLine (n : Nat) {s s' : SurfPos}
    (h : SNsPlainOneLine .blockKey s s') : SFlowNode n .flowOut s s' :=
  flowContent_flowNode (SFlowContent_plain_of_keyOneLine n h)

-- [109] c-double-quoted(n,c) re-read at `.flowOut` and EVERY index from a KEY
-- reading.  `[110] nb-double-text(n₀,block-key)` IS `[111] nb-double-one-line`,
-- which `[116] nb-double-multi-line(n)`'s `single` arm admits at any `n`, so
-- the body transports and only the quotes are rebuilt.
@[yaml_spec "7.3.1" 109 "c-double-quoted(n,c) key one-line lift (flow-out, any n)"]
lemma SCDoubleQuoted_key_to_flowOut (n : Nat) {n₀ : Nat} {c₀ : YamlContext}
    {s s' : SurfPos}
    (h : SCDoubleQuoted n₀ c₀ s s')
    (hc : c₀ = .blockKey ∨ c₀ = .flowKey) :
    SCDoubleQuoted n .flowOut s s' :=
  match h with
  | .mk _ _ _ s₁ s₂ _ h_open h_text h_close =>
    .mk n .flowOut s s₁ s₂ s' h_open
      (SNbDoubleMultiLine.single n s₁ s₂
        (by rcases hc with hk | hk <;> subst hk <;> exact h_text))
      h_close

-- [120] c-single-quoted(n,c), the same rebuild over `[122] nb-single-one-line`.
@[yaml_spec "7.3.2" 120 "c-single-quoted(n,c) key one-line lift (flow-out, any n)"]
lemma SCSingleQuoted_key_to_flowOut (n : Nat) {n₀ : Nat} {c₀ : YamlContext}
    {s s' : SurfPos}
    (h : SCSingleQuoted n₀ c₀ s s')
    (hc : c₀ = .blockKey ∨ c₀ = .flowKey) :
    SCSingleQuoted n .flowOut s s' :=
  match h with
  | .mk _ _ _ s₁ s₂ _ h_open h_text h_close =>
    .mk n .flowOut s s₁ s₂ s' h_open
      (SNbSingleMultiLine.single n s₁ s₂
        (by rcases hc with hk | hk <;> subst hk <;> exact h_text))
      h_close

lemma SFlowContent_doubleQ_of_key (n : Nat) {n₀ : Nat} {s s' : SurfPos}
    (h : SCDoubleQuoted n₀ .blockKey s s') : SFlowContent n .flowOut s s' :=
  doubleQuoted_flowContent (SCDoubleQuoted_key_to_flowOut n h (Or.inl rfl))

lemma SFlowContent_singleQ_of_key (n : Nat) {n₀ : Nat} {s s' : SurfPos}
    (h : SCSingleQuoted n₀ .blockKey s s') : SFlowContent n .flowOut s s' :=
  singleQuoted_flowContent (SCSingleQuoted_key_to_flowOut n h (Or.inl rfl))

lemma SFlowNode_doubleQ_of_key (n : Nat) {n₀ : Nat} {s s' : SurfPos}
    (h : SCDoubleQuoted n₀ .blockKey s s') : SFlowNode n .flowOut s s' :=
  flowContent_flowNode (SFlowContent_doubleQ_of_key n h)

lemma SFlowNode_singleQ_of_key (n : Nat) {n₀ : Nat} {s s' : SurfPos}
    (h : SCSingleQuoted n₀ .blockKey s s') : SFlowNode n .flowOut s s' :=
  flowContent_flowNode (SFlowContent_singleQ_of_key n h)

-- [96] c-ns-properties context re-labelling between the two block contexts.
-- The embedded separator is `SSeparate n c`, which reduces to
-- `SSeparateLines n` at BOTH block contexts, so each constructor rebuilds
-- with its fields transported by definitional equality.
@[yaml_spec "6.9" 96 "c-ns-properties(n,c) blockIn → blockOut (same n)"]
lemma SCNsProperties_blockIn_to_blockOut {n : Nat} {s s' : SurfPos}
    (h : SCNsProperties n .blockIn s s') : SCNsProperties n .blockOut s s' :=
  match h with
  | .tagFirst _ _ _ s₁ _ h_tag h_opt =>
    .tagFirst n .blockOut s s₁ s' h_tag h_opt
  | .anchorFirst _ _ _ s₁ _ h_anchor h_opt =>
    .anchorFirst n .blockOut s s₁ s' h_anchor h_opt

private lemma props_sep_opt_blockIn_to_blockOut {n : Nat} {s s' : SurfPos}
    (h : GOpt (GSeq (SCNsProperties n .blockIn) (SSeparate n .blockIn)) s s') :
    GOpt (GSeq (SCNsProperties n .blockOut) (SSeparate n .blockOut)) s s' :=
  match h with
  | .none _ => .none _
  | .some _ _ (.mk _ s₁ _ hp hs) =>
    .some _ _ (.mk _ s₁ _ (SCNsProperties_blockIn_to_blockOut hp) hs)

private lemma sep_props_opt_blockIn_to_blockOut {n : Nat} {s s' : SurfPos}
    (h : GOpt (GSeq (SSeparate n .blockIn) (SCNsProperties n .blockIn)) s s') :
    GOpt (GSeq (SSeparate n .blockOut) (SCNsProperties n .blockOut)) s s' :=
  match h with
  | .none _ => .none _
  | .some _ _ (.mk _ s₁ _ hs hp) =>
    .some _ _ (.mk _ s₁ _ hs (SCNsProperties_blockIn_to_blockOut hp))

-- The BLOCK-OUT sequence index is the BLOCK-IN one, re-detected.
-- `seq-spaces(n,block-out)` is `n-1` where `seq-spaces(n,block-in)` is `n`,
-- so the two contexts disagree about a sequence's entry indent by exactly
-- one — which is precisely the offset `[183]`'s auto-detected `m` absorbs:
-- take `m+1` where BLOCK-IN took `m`, and both name the same index.  (Item 22.
-- Pinning `m` at its minimum is what forced this lemma to `n = 0`, where the
-- truncating subtraction happens to hide the disagreement.)
private lemma seqEntries_blockOut_shift {n m : Nat} {s s' : SurfPos}
    (h : SBlockSeqEntries (seqSpaces n .blockIn + m) s s') :
    SBlockSeqEntries (seqSpaces n .blockOut + (if n = 0 then m else m + 1)) s s' := by
  have heq : seqSpaces n .blockOut + (if n = 0 then m else m + 1)
      = seqSpaces n .blockIn + m := by
    cases n <;> simp [seqSpaces] <;> omega
  rw [heq]; exact h

-- [196] s-l+block-node re-labelling blockIn → blockOut, at any indent.
-- The context surfaces in three places: the separators (`SSeparate n c`
-- reduces to `SSeparateLines n` for both block contexts), the properties
-- (re-labelled above), and `seqSpaces n c` (re-detected as above).  This is
-- what lets a mapping VALUE slot ([189] wants `.blockOut`) consume a node
-- composed by the `.blockIn` machinery the accumulation already has (DOCS
-- item 13; generalized off `n = 0` by item 22's widening).
@[yaml_spec "8.2.3" 196 "s-l+block-node(n,c) blockIn → blockOut"]
lemma SBlockNode_blockIn_to_blockOut {n : Nat} {s s' : SurfPos}
    (h : SBlockNode n .blockIn s s') : SBlockNode n .blockOut s s' :=
  match h with
  | .blockLiteral _ _ _ s₁ s₂ _ h_sep h_props h_lit =>
    .blockLiteral n .blockOut s s₁ s₂ s' h_sep
      (props_sep_opt_blockIn_to_blockOut h_props) h_lit
  | .blockFolded _ _ _ s₁ s₂ _ h_sep h_props h_fld =>
    .blockFolded n .blockOut s s₁ s₂ s' h_sep
      (props_sep_opt_blockIn_to_blockOut h_props) h_fld
  | .blockSeq _ _ m _ s₁ s₂ _ h_props h_ssl h_entries =>
    .blockSeq n .blockOut (if n = 0 then m else m + 1) s s₁ s₂ s'
      (sep_props_opt_blockIn_to_blockOut h_props) h_ssl
      (seqEntries_blockOut_shift h_entries)
  | .blockMap _ _ m _ s₁ s₂ _ h_props h_ssl h_entries =>
    .blockMap n .blockOut m s s₁ s₂ s'
      (sep_props_opt_blockIn_to_blockOut h_props) h_ssl h_entries
  | .flowInBlock _ _ _ s₁ s₂ _ h_sep h_flow h_ssl =>
    .flowInBlock n .blockOut s s₁ s₂ s' h_sep h_flow h_ssl
  | .emptyNode _ _ _ _ h_ssl =>
    .emptyNode n .blockOut s s' h_ssl

-- [185] s-l+block-indented re-labelling blockIn → blockOut, at any indent.
-- The context reaches only the block-node alternative (the compact collections
-- and the empty node are context-inert by construction), so this is one layer
-- over the `[196]` lemma above.  It is what lets an OPEN `[185]` slot — a
-- `?`'s key or an explicit `:`'s value, whose closure is stated at the slot's
-- own `.blockOut` — consume the compact collection the `.blockIn` route
-- machinery composes (DOCS item 89).
@[yaml_spec "8.2.1" 185 "s-l+block-indented(n,c) blockIn → blockOut"]
lemma SBlockIndented_blockIn_to_blockOut {n : Nat} {s s' : SurfPos}
    (h : SBlockIndented n .blockIn s s') : SBlockIndented n .blockOut s s' :=
  match h with
  | .compactSeq _ _ m _ s₁ _ h_ind h_seq =>
    .compactSeq n .blockOut m s s₁ s' h_ind h_seq
  | .compactMap _ _ m _ s₁ _ h_ind h_map =>
    .compactMap n .blockOut m s s₁ s' h_ind h_map
  | .node _ _ _ _ h_node =>
    .node n .blockOut s s' (SBlockNode_blockIn_to_blockOut h_node)
  | .empty _ _ _ _ h_ssl =>
    .empty n .blockOut s s' h_ssl

/-! ## §6 GStar/GPlus Lifting and Alias/Anchor Conversion (Layer 4a) -/

-- Alias node: GLit '*' + GPlus anchor chars → SCNsAliasNode.
-- Takes destructured GLit output + GPlus name.
lemma aliasNode_of_glit_gplus {rest : List Char} {col : Nat} {sp' : SurfPos}
    (h_gplus : GPlus (GChar isNsAnchorChar) ⟨rest, col + 1⟩ sp')
    (h_not : GNot (GChar isNsAnchorChar) sp') :
    SCNsAliasNode ⟨'*' :: rest, col⟩ sp' :=
  SCNsAliasNode.mk rest col sp' h_gplus h_not

-- Anchor property: GLit '&' + GPlus anchor chars → SCNsAnchorProperty.
lemma anchorProp_of_glit_gplus {rest : List Char} {col : Nat} {sp' : SurfPos}
    (h_gplus : GPlus (GChar isNsAnchorChar) ⟨rest, col + 1⟩ sp')
    (h_not : GNot (GChar isNsAnchorChar) sp') :
    SCNsAnchorProperty ⟨'&' :: rest, col⟩ sp' :=
  SCNsAnchorProperty.mk rest col sp' h_gplus h_not

-- scanAnchorOrAlias → SCNsAliasNode (unconditional).
-- Since A10 Except conversion, `.ok` guarantees non-empty name, so sp_mid ≠ sp'.
lemma scanAnchorOrAlias_aliasNode_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '*')
    (s' : ScannerState) (hok : scanAnchorOrAlias sc false = .ok s') :
    ∃ sp', SCNsAliasNode sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨sp_mid, sp', h_glit, h_gstar, h_ne, h_not, hcorr'⟩ :=
    scanAnchorOrAlias_prod sc sp hcorr false '*' hpeek (by decide) (by decide) s' hok
  cases h_glit with
  | mk rest col =>
    exact ⟨sp', aliasNode_of_glit_gplus (GStar_to_GPlus h_gstar h_ne) h_not, hcorr'⟩

-- scanAnchorOrAlias → SCNsAnchorProperty (unconditional).
-- Since A10 Except conversion, `.ok` guarantees non-empty name, so sp_mid ≠ sp'.
lemma scanAnchorOrAlias_anchorProp_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '&')
    (s' : ScannerState) (hok : scanAnchorOrAlias sc true = .ok s') :
    ∃ sp', SCNsAnchorProperty sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨sp_mid, sp', h_glit, h_gstar, h_ne, h_not, hcorr'⟩ :=
    scanAnchorOrAlias_prod sc sp hcorr true '&' hpeek (by decide) (by decide) s' hok
  cases h_glit with
  | mk rest col =>
    exact ⟨sp', anchorProp_of_glit_gplus (GStar_to_GPlus h_gstar h_ne) h_not, hcorr'⟩

-- scanAnchorOrAlias → SFlowNode (alias, unconditional).
lemma scanAnchorOrAlias_flowNode_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '*')
    (s' : ScannerState) (hok : scanAnchorOrAlias sc false = .ok s') :
    ∃ sp', SFlowNode 0 .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨sp', h_alias, hcorr'⟩ :=
    scanAnchorOrAlias_aliasNode_prod sc sp hcorr hpeek s' hok
  exact ⟨sp', alias_flowNode h_alias, hcorr'⟩

/-! ## §6 Block Collection Lemmas -/

/-- Append one entry to the end of a block sequence.

    This is an example of a non-trivial grammar operation whose proof is
    made short (10 lines) by the foundational design choices upstream.
    The hard work was in the definitions, not the proof.

    **Key foundations this depends on:**

    1. **List-like structure of `SBlockSeqEntries`** (`Node.lean`):
       The type has exactly two constructors — `single` (base) and `cons`
       (recursive) — mirroring a cons-list. This is a design choice: the
       YAML spec phrase "one or more entries" could also be encoded as
       `GPlus (SIndent × GLit × GNot × SBlockIndented)`, but the explicit
       `single`/`cons` split makes snoc a direct structural recursion.

    2. **Self-contained entry evidence**: Each entry in `single`/`cons`
       carries all four components (`SIndent n`, `GLit '-'`, `GNot SNsChar`,
       `SBlockIndented n .blockIn`) independently. No shared state or
       context threading between entries — the new entry just needs its own
       four witnesses to slot in.

    3. **`SurfPos`-indexed types**: Position tracking via indices means
       composition is type-checked: the new entry's `SIndent n s_mid s₁`
       must start exactly where the old sequence ended (`s_mid`). No
       runtime position arithmetic — the type system enforces adjacency.

    **Why term-mode `match` instead of `induction`:**
    `SBlockSeqEntries` is part of an 11-type mutual inductive block (with
    `SBlockNode`, `SBlockIndented`, `SBlockMapEntries`, etc.). Lean's
    `induction` tactic does not support mutual inductives — it fails with
    "does not support the type ... because it is mutually inductive".
    Even `cases` + recursive call fails: Lean tries well-founded recursion
    on `SurfPos` and asks to prove `sizeOf s₃' < sizeOf s`, which doesn't
    hold in general for surface positions.

    Term-mode `match` works because Lean's equation compiler recognizes
    that the recursive call passes `h_tail : SBlockSeqEntries n s₃' s_mid`,
    which is a strict subterm of the `cons` pattern's original
    `h_entries : SBlockSeqEntries n s s_mid`. This is **structural recursion
    on the proof term itself** — no termination annotation needed. The
    compiler generates the recursion principle automatically from the
    subterm relationship, bypassing the mutual-inductive restriction that
    blocks the `induction` tactic.

    **Proof idea:** The `single` case converts to `cons` (original entry
    stays as head, new entry becomes a `single` tail). The `cons` case
    keeps the head entry and recurses on the tail. -/
lemma SBlockSeqEntries_snoc {n : Nat} {s s_mid s₁ s₂ s' : SurfPos}
    (h_entries : SBlockSeqEntries n s s_mid)
    (h_indent : SIndent n s_mid s₁)
    (h_dash : GLit '-' s₁ s₂)
    (h_gnot : GNot SNsChar s₂)
    (h_indented : SBlockIndented n .blockIn s₂ s') :
    SBlockSeqEntries n s s' :=
  match h_entries with
  | .single _ _ s₁' s₂' _ _ h_indent' h_dash' h_gnot' h_body =>
    .cons _ _ s₁' s₂' s_mid s'
      h_indent' h_dash' h_gnot' h_body
      (.single _ s_mid s₁ s₂ s₂ s'
        h_indent h_dash h_gnot h_indented)
  | .cons _ _ s₁' s₂' s₃' _ h_indent' h_dash' h_gnot' h_body h_tail =>
    .cons _ _ s₁' s₂' s₃' s'
      h_indent' h_dash' h_gnot' h_body
      (SBlockSeqEntries_snoc h_tail h_indent h_dash h_gnot h_indented)

/-- **One entry plus `[186]`'s tail is `[183]`'s collection** (item 33).

    `ns-l-compact-sequence(n)` is `c-l-block-seq-entry(n)` followed by
    `( s-indent(n) c-l-block-seq-entry(n) )*`, and `l+block-sequence(n)` is
    `( s-indent(n) c-l-block-seq-entry(n) )+` — so the tail of the first is
    literally the whole of the second, and the two productions differ ONLY in
    whether the opening entry carries its own indentation.  That is why the
    accumulation can hand every block-dispatch pending the same continuation
    shape (`∀ sp_end, SCompactSeqTail n sp_mid sp_end → …`): a COMPACT opener
    spends the tail as `SCompactSeq.mk`'s last argument, and an INDENTED one
    spends it here, re-attaching its own `s-indent(n) '-'` in front.

    Term-mode `match` for `SBlockSeqEntries_snoc`'s reason: the surface types
    are one 11-way mutual inductive, so `induction` is unavailable and the
    recursion is structural on the tail proof itself. -/
lemma SBlockSeqEntries_of_compactTail {n : Nat} {s s₁ s₂ s₃ s' : SurfPos}
    (h_indent : SIndent n s s₁)
    (h_dash : GLit '-' s₁ s₂)
    (h_gnot : GNot SNsChar s₂)
    (h_body : SBlockIndented n .blockIn s₂ s₃)
    (h_tail : SCompactSeqTail n s₃ s') :
    SBlockSeqEntries n s s' :=
  match h_tail with
  | .nil _ _ => .single n s s₁ s₂ s₂ s₃ h_indent h_dash h_gnot h_body
  | .cons _ _ _ _ _ _ h_i h_d h_g h_b h_t =>
    .cons n s s₁ s₂ s₃ s' h_indent h_dash h_gnot h_body
      (SBlockSeqEntries_of_compactTail h_i h_d h_g h_b h_t)

/-- The mapping twin: one `[188]` entry plus `[195] ns-l-compact-mapping`'s
    tail is `[187] l+block-mapping`'s collection, for the same reason. -/
lemma SBlockMapEntries_of_compactTail {n : Nat} {s s₁ s₂ s' : SurfPos}
    (h_indent : SIndent n s s₁)
    (h_entry : SBlockMapEntry n s₁ s₂)
    (h_tail : SCompactMapTail n s₂ s') :
    SBlockMapEntries n s s' :=
  match h_tail with
  | .nil _ _ => .single n s s₁ s₂ h_indent h_entry
  | .cons _ _ _ _ _ h_i h_e h_t =>
    .cons n s s₁ s₂ s' h_indent h_entry
      (SBlockMapEntries_of_compactTail h_i h_e h_t)

/-! ## §4b Flow entry snoc (`SFlowSeqEntries` / `SFlowMapEntries`)

    Flow analogues of `SBlockSeqEntries_snoc` (Fix A, Piece 2). Unlike block
    sequences — whose entries are self-delimiting `- content` units — flow
    entries are comma-separated (`ns-s-flow-seq-entries` [138]): the list is
    right-nested with a `consMore` cons (`entry sep , sep <tail>`) and TWO
    terminal forms, `single` (`entry sep`) and `consEnd` (`entry sep , sep`,
    the trailing-comma case `[a,]`).

    Snoc appends one more comma-separated entry at the end (recursing to the
    innermost entry, exactly like the block version). The trailing-comma
    `consEnd` form cannot validly receive another `, entry` (that would be a
    double comma `a,,b`, which is ungrammatical), so snoc is stated for
    *closeable* entries only — a total, structurally-preserved predicate that
    a flow accumulator maintains: a fresh `single` is closeable, and snoc
    yields a closeable result, so the trailing comma is only ever formed at
    the final close (never fed back into snoc). -/

/-- A flow-seq-entries list is *closeable* iff its innermost terminal is a
    `single` (an entry) rather than a `consEnd` (a trailing comma). Encoded as
    an inductive over exactly the `single`/`consMore` spine — so it has no
    `consEnd` constructor, and matching on the evidence is exhaustive without
    touching the excluded trailing-comma case. Preserved by
    `SFlowSeqEntries_snoc`; discharged for freshly-opened accumulators. -/
inductive FlowSeqEntriesCloseable :
    {n : Nat} → {c : YamlContext} → {s s' : SurfPos} → SFlowSeqEntries n c s s' → Prop where
  | single {n : Nat} {c : YamlContext} {s s₁ s' : SurfPos}
      (he : SFlowSeqEntry n c s s₁) (hsep : GOpt (SSeparate n c) s₁ s') :
      FlowSeqEntriesCloseable (SFlowSeqEntries.single n c s s₁ s' he hsep)
  | consMore {n : Nat} {c : YamlContext} {s s₁ s₂ s₃ s₄ s' : SurfPos}
      (he : SFlowSeqEntry n c s s₁) (hsep : GOpt (SSeparate n c) s₁ s₂)
      (hcomma : GLit ',' s₂ s₃) (hsep' : GOpt (SSeparate n c) s₃ s₄)
      (tail : SFlowSeqEntries n c s₄ s') :
      FlowSeqEntriesCloseable tail →
      FlowSeqEntriesCloseable
        (SFlowSeqEntries.consMore n c s s₁ s₂ s₃ s₄ s' he hsep hcomma hsep' tail)

/-- A flow-map-entries list is *closeable* (see `FlowSeqEntriesCloseable`). -/
inductive FlowMapEntriesCloseable :
    {n : Nat} → {c : YamlContext} → {s s' : SurfPos} → SFlowMapEntries n c s s' → Prop where
  | single {n : Nat} {c : YamlContext} {s s₁ s' : SurfPos}
      (he : SFlowMapEntry n c s s₁) (hsep : GOpt (SSeparate n c) s₁ s') :
      FlowMapEntriesCloseable (SFlowMapEntries.single n c s s₁ s' he hsep)
  | consMore {n : Nat} {c : YamlContext} {s s₁ s₂ s₃ s₄ s' : SurfPos}
      (he : SFlowMapEntry n c s s₁) (hsep : GOpt (SSeparate n c) s₁ s₂)
      (hcomma : GLit ',' s₂ s₃) (hsep' : GOpt (SSeparate n c) s₃ s₄)
      (tail : SFlowMapEntries n c s₄ s') :
      FlowMapEntriesCloseable tail →
      FlowMapEntriesCloseable
        (SFlowMapEntries.consMore n c s s₁ s₂ s₃ s₄ s' he hsep hcomma hsep' tail)

set_option linter.defProp false in
/-- Append one comma-separated entry to a closeable `SFlowSeqEntries`.
    Mirrors `SBlockSeqEntries_snoc`, recursing on the closeable spine: the
    `single` terminal becomes a `consMore` (its trailing separator becomes the
    pre-comma separator), `consMore` keeps its head and recurses on the tail.
    The trailing-comma `consEnd` is unreachable — it is not part of the
    `FlowSeqEntriesCloseable` spine. -/
def SFlowSeqEntries_snoc {n : Nat} {c : YamlContext} {s s_mid s_c s_d s_e s' : SurfPos}
    {h_entries : SFlowSeqEntries n c s s_mid}
    (h_cl : FlowSeqEntriesCloseable h_entries)
    (h_comma : GLit ',' s_mid s_c)
    (h_sep : GOpt (SSeparate n c) s_c s_d)
    (h_entry : SFlowSeqEntry n c s_d s_e)
    (h_sep2 : GOpt (SSeparate n c) s_e s') :
    SFlowSeqEntries n c s s' :=
  match h_cl with
  | .single (s₁ := s₁) he hsep =>
    .consMore _ _ _ s₁ s_mid s_c s_d s' he hsep h_comma h_sep
      (.single _ _ s_d s_e s' h_entry h_sep2)
  | .consMore (s₁ := s₁) (s₂ := s₂) (s₃ := s₃) (s₄ := s₄) he hsep hcomma hsep' _ h_tail_cl =>
    .consMore _ _ _ s₁ s₂ s₃ s₄ s' he hsep hcomma hsep'
      (SFlowSeqEntries_snoc h_tail_cl h_comma h_sep h_entry h_sep2)

/-- `SFlowSeqEntries_snoc` yields a closeable result (its innermost terminal is
    the freshly-appended `single`). Lets an accumulator snoc repeatedly. -/
lemma SFlowSeqEntries_snoc_closeable {n : Nat} {c : YamlContext}
    {s s_mid s_c s_d s_e s' : SurfPos}
    {h_entries : SFlowSeqEntries n c s s_mid}
    (h_cl : FlowSeqEntriesCloseable h_entries)
    (h_comma : GLit ',' s_mid s_c)
    (h_sep : GOpt (SSeparate n c) s_c s_d)
    (h_entry : SFlowSeqEntry n c s_d s_e)
    (h_sep2 : GOpt (SSeparate n c) s_e s') :
    FlowSeqEntriesCloseable
      (SFlowSeqEntries_snoc h_cl h_comma h_sep h_entry h_sep2) :=
  match h_cl with
  | .single he hsep =>
    .consMore he hsep h_comma h_sep _ (.single h_entry h_sep2)
  | .consMore he hsep hcomma hsep' _ h_tail_cl =>
    .consMore he hsep hcomma hsep' _
      (SFlowSeqEntries_snoc_closeable h_tail_cl h_comma h_sep h_entry h_sep2)

set_option linter.defProp false in
/-- Append one comma-separated entry to a closeable `SFlowMapEntries`.
    Structurally identical to `SFlowSeqEntries_snoc`. -/
def SFlowMapEntries_snoc {n : Nat} {c : YamlContext} {s s_mid s_c s_d s_e s' : SurfPos}
    {h_entries : SFlowMapEntries n c s s_mid}
    (h_cl : FlowMapEntriesCloseable h_entries)
    (h_comma : GLit ',' s_mid s_c)
    (h_sep : GOpt (SSeparate n c) s_c s_d)
    (h_entry : SFlowMapEntry n c s_d s_e)
    (h_sep2 : GOpt (SSeparate n c) s_e s') :
    SFlowMapEntries n c s s' :=
  match h_cl with
  | .single (s₁ := s₁) he hsep =>
    .consMore _ _ _ s₁ s_mid s_c s_d s' he hsep h_comma h_sep
      (.single _ _ s_d s_e s' h_entry h_sep2)
  | .consMore (s₁ := s₁) (s₂ := s₂) (s₃ := s₃) (s₄ := s₄) he hsep hcomma hsep' _ h_tail_cl =>
    .consMore _ _ _ s₁ s₂ s₃ s₄ s' he hsep hcomma hsep'
      (SFlowMapEntries_snoc h_tail_cl h_comma h_sep h_entry h_sep2)

/-- `SFlowMapEntries_snoc` yields a closeable result. -/
lemma SFlowMapEntries_snoc_closeable {n : Nat} {c : YamlContext}
    {s s_mid s_c s_d s_e s' : SurfPos}
    {h_entries : SFlowMapEntries n c s s_mid}
    (h_cl : FlowMapEntriesCloseable h_entries)
    (h_comma : GLit ',' s_mid s_c)
    (h_sep : GOpt (SSeparate n c) s_c s_d)
    (h_entry : SFlowMapEntry n c s_d s_e)
    (h_sep2 : GOpt (SSeparate n c) s_e s') :
    FlowMapEntriesCloseable
      (SFlowMapEntries_snoc h_cl h_comma h_sep h_entry h_sep2) :=
  match h_cl with
  | .single he hsep =>
    .consMore he hsep h_comma h_sep _ (.single h_entry h_sep2)
  | .consMore he hsep hcomma hsep' _ h_tail_cl =>
    .consMore he hsep hcomma hsep' _
      (SFlowMapEntries_snoc_closeable h_tail_cl h_comma h_sep h_entry h_sep2)

set_option linter.defProp false in
/-- Convert a closeable `SFlowSeqEntries` to trailing-comma form (`[a, b,]`):
    the innermost `single` terminal becomes a `consEnd`. Recurses through
    `consMore` like `SFlowSeqEntries_snoc`; the result is NOT closeable
    (a trailing comma is terminal — it may only precede the closing bracket). -/
def SFlowSeqEntries_addTrailingComma {n : Nat} {c : YamlContext}
    {s s_mid s_c s' : SurfPos} {h_entries : SFlowSeqEntries n c s s_mid}
    (h_cl : FlowSeqEntriesCloseable h_entries)
    (h_comma : GLit ',' s_mid s_c) (h_sep : GOpt (SSeparate n c) s_c s') :
    SFlowSeqEntries n c s s' :=
  match h_cl with
  | .single (s₁ := s₁) he hsep =>
    .consEnd _ _ _ s₁ s_mid s_c s' he hsep h_comma h_sep
  | .consMore (s₁ := s₁) (s₂ := s₂) (s₃ := s₃) (s₄ := s₄) he hsep hcomma hsep' _ h_tail_cl =>
    .consMore _ _ _ s₁ s₂ s₃ s₄ _ he hsep hcomma hsep'
      (SFlowSeqEntries_addTrailingComma h_tail_cl h_comma h_sep)

set_option linter.defProp false in
/-- Convert a closeable `SFlowMapEntries` to trailing-comma form. -/
def SFlowMapEntries_addTrailingComma {n : Nat} {c : YamlContext}
    {s s_mid s_c s' : SurfPos} {h_entries : SFlowMapEntries n c s s_mid}
    (h_cl : FlowMapEntriesCloseable h_entries)
    (h_comma : GLit ',' s_mid s_c) (h_sep : GOpt (SSeparate n c) s_c s') :
    SFlowMapEntries n c s s' :=
  match h_cl with
  | .single (s₁ := s₁) he hsep =>
    .consEnd _ _ _ s₁ s_mid s_c s' he hsep h_comma h_sep
  | .consMore (s₁ := s₁) (s₂ := s₂) (s₃ := s₃) (s₄ := s₄) he hsep hcomma hsep' _ h_tail_cl =>
    .consMore _ _ _ s₁ s₂ s₃ s₄ _ he hsep hcomma hsep'
      (SFlowMapEntries_addTrailingComma h_tail_cl h_comma h_sep)

/-! ## §4c Flow separation primitives (Fix A, Piece 2)

    In flow contexts (`.flowOut`/`.flowIn`) `s-separate(n,c)` [69] unfolds to
    `s-separate-lines(n)` [70], whose `inline` case wraps `s-separate-in-line`
    [66]: a run of whitespace is a flow separation, and the zero-width one
    exists only at column 0.  These are the separators threaded between
    flow-collection tokens (`[`, entries, `,`, `]`). -/

/-- A run of whitespace is a flow separation. -/
lemma SSeparate_flow_of_whites (n : Nat) {c : YamlContext} {sp sp' : SurfPos}
    (hc : c = .flowOut ∨ c = .flowIn) (h : GPlus SSWhite sp sp') : SSeparate n c sp sp' := by
  rcases hc with rfl | rfl <;>
    exact SSeparateLines.inline n sp sp' (SSeparateInLine.whites sp sp' h)

/-- The optional separator `GOpt (SSeparate n c)` is always dischargeable
    zero-width (`e` / `s-separate?` absent). -/
lemma GOpt_SSeparate_none {n : Nat} {c : YamlContext} (sp : SurfPos) :
    GOpt (SSeparate n c) sp sp := GOpt.none sp

/-- A run of trailing whitespace (`GStar SSWhite`, as emitted by content
    producers like `scanPlainScalar_to_flowNode_flowIn`) is an optional flow
    separator: empty run → `GOpt.none`, non-empty → `GOpt.some` via `whites`. -/
lemma GOpt_SSeparate_of_GStar_SSWhite {n : Nat} {c : YamlContext} {sp sp' : SurfPos}
    (hc : c = .flowOut ∨ c = .flowIn) (h : GStar SSWhite sp sp') :
    GOpt (SSeparate n c) sp sp' := by
  cases h with
  | nil => exact GOpt.none _
  | cons _ s₂ _ hd tl =>
    exact GOpt.some sp sp' (SSeparate_flow_of_whites n hc (GPlus.mk sp s₂ sp' hd tl))

/-! ## §4d Flow collection assembly (Fix A, Piece 2)

    Assemble a completed `SFlowSequence`/`SFlowMapping` [137]/[140] from the
    bracket literals, the optional post-`[` separation, and the accumulated
    entries (at `in-flow(c)` context), then lift to `SFlowContent`/`SFlowNode`.
    These are the "close a flow level" operations for the accumulator. -/

/-- Assemble a non-empty flow sequence: `[` sep entries `]`. -/
lemma flowSeq_nonempty {n : Nat} {c : YamlContext} {s s₁ s₂ s₃ s' : SurfPos}
    (hopen : GLit '[' s s₁) (hsep : GOpt (SSeparate n c) s₁ s₂)
    (hentries : SFlowSeqEntries n (inFlowCtx c) s₂ s₃) (hclose : GLit ']' s₃ s') :
    SFlowSequence n c s s' :=
  SFlowSequence.nonempty n c s s₁ s₂ s₃ s' hopen hsep hentries hclose

/-- Assemble an empty flow sequence: `[` sep `]`. -/
lemma flowSeq_empty {n : Nat} {c : YamlContext} {s s₁ s₂ s' : SurfPos}
    (hopen : GLit '[' s s₁) (hsep : GOpt (SSeparate n c) s₁ s₂) (hclose : GLit ']' s₂ s') :
    SFlowSequence n c s s' :=
  SFlowSequence.empty n c s s₁ s₂ s' hopen hsep hclose

/-- Assemble a non-empty flow mapping: `{` sep entries `}`. -/
lemma flowMap_nonempty {n : Nat} {c : YamlContext} {s s₁ s₂ s₃ s' : SurfPos}
    (hopen : GLit '{' s s₁) (hsep : GOpt (SSeparate n c) s₁ s₂)
    (hentries : SFlowMapEntries n (inFlowCtx c) s₂ s₃) (hclose : GLit '}' s₃ s') :
    SFlowMapping n c s s' :=
  SFlowMapping.nonempty n c s s₁ s₂ s₃ s' hopen hsep hentries hclose

/-- Assemble an empty flow mapping: `{` sep `}`. -/
lemma flowMap_empty {n : Nat} {c : YamlContext} {s s₁ s₂ s' : SurfPos}
    (hopen : GLit '{' s s₁) (hsep : GOpt (SSeparate n c) s₁ s₂) (hclose : GLit '}' s₂ s') :
    SFlowMapping n c s s' :=
  SFlowMapping.empty n c s s₁ s₂ s' hopen hsep hclose

/-- A completed flow sequence is a flow node. -/
lemma flowSeq_flowNode {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SFlowSequence n c s s') : SFlowNode n c s s' :=
  flowContent_flowNode (flowSeq_flowContent h)

/-- A completed flow mapping is a flow node. -/
lemma flowMap_flowNode {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SFlowMapping n c s s') : SFlowNode n c s s' :=
  flowContent_flowNode (flowMap_flowContent h)

/-- A single-entry flow sequence from one entry (+ trailing separator). -/
lemma SFlowSeqEntries_single {n : Nat} {c : YamlContext} {s s₁ s' : SurfPos}
    (h_entry : SFlowSeqEntry n c s s₁) (h_sep : GOpt (SSeparate n c) s₁ s') :
    SFlowSeqEntries n c s s' :=
  SFlowSeqEntries.single n c s s₁ s' h_entry h_sep

/-- The single-entry flow sequence is closeable (seeds a snoc accumulator). -/
lemma SFlowSeqEntries_single_closeable {n : Nat} {c : YamlContext} {s s₁ s' : SurfPos}
    (h_entry : SFlowSeqEntry n c s s₁) (h_sep : GOpt (SSeparate n c) s₁ s') :
    FlowSeqEntriesCloseable (SFlowSeqEntries_single h_entry h_sep) :=
  .single h_entry h_sep

/-- A single-entry flow mapping from one entry (+ trailing separator). -/
lemma SFlowMapEntries_single {n : Nat} {c : YamlContext} {s s₁ s' : SurfPos}
    (h_entry : SFlowMapEntry n c s s₁) (h_sep : GOpt (SSeparate n c) s₁ s') :
    SFlowMapEntries n c s s' :=
  SFlowMapEntries.single n c s s₁ s' h_entry h_sep

/-- The single-entry flow mapping is closeable (seeds a snoc accumulator). -/
lemma SFlowMapEntries_single_closeable {n : Nat} {c : YamlContext} {s s₁ s' : SurfPos}
    (h_entry : SFlowMapEntry n c s s₁) (h_sep : GOpt (SSeparate n c) s₁ s') :
    FlowMapEntriesCloseable (SFlowMapEntries_single h_entry h_sep) :=
  .single h_entry h_sep

/-- A flow node is a flow-sequence entry. -/
lemma flowNode_seqEntry {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SFlowNode n c s s') : SFlowSeqEntry n c s s' :=
  SFlowSeqEntry.node n c s s' h

/-! ## §4e Flow accumulator state machine (Fix A, Piece 2 / Stage B)

    A `PartialFlowSeq`/`PartialFlowMap` is the entries of a flow collection
    being built across `scanNextToken` calls. Three states mirror the scanner's
    per-token progress inside `[…]`/`{…}`:
    - `empty`: just opened (`[`), no entries yet;
    - `entries`: ≥1 entry accumulated, closeable (last token was an entry) — a
      `,` may follow (→ `held`) or the bracket may close (→ non-empty collection);
    - `held`: a `,` was just scanned after an entry — the next token must be an
      entry (→ back to `entries` via snoc) or the bracket closes (→ trailing-comma
      collection).
    The entries live at the entry context `c = inFlowCtx c_out`. `closeSeq`/
    `closeMap` finalize any state into a complete `SFlowSequence`/`SFlowMapping`
    at the outer context `c_out`, given the bracket literals and post-`[`
    separation. The invalid transitions (leading/consecutive comma, adjacent
    entries) are exactly the scanner errors (`invalidFlowEntry`, the Piece-1
    flow-adjacency check), so they never arise. -/

/-- Entries of a flow sequence under construction (see §4e). -/
inductive PartialFlowSeq (n : Nat) (c : YamlContext) : SurfPos → SurfPos → Prop where
  | empty (sp : SurfPos) : PartialFlowSeq n c sp sp
  | entries (sp sp' : SurfPos) (h : SFlowSeqEntries n c sp sp')
      (hcl : FlowSeqEntriesCloseable h) : PartialFlowSeq n c sp sp'
  | held (sp sp_e sp_c sp' : SurfPos) (h : SFlowSeqEntries n c sp sp_e)
      (hcl : FlowSeqEntriesCloseable h) (hcomma : GLit ',' sp_e sp_c)
      (hsep : GOpt (SSeparate n c) sp_c sp') : PartialFlowSeq n c sp sp'

/-- Entries of a flow mapping under construction (see §4e). -/
inductive PartialFlowMap (n : Nat) (c : YamlContext) : SurfPos → SurfPos → Prop where
  | empty (sp : SurfPos) : PartialFlowMap n c sp sp
  | entries (sp sp' : SurfPos) (h : SFlowMapEntries n c sp sp')
      (hcl : FlowMapEntriesCloseable h) : PartialFlowMap n c sp sp'
  | held (sp sp_e sp_c sp' : SurfPos) (h : SFlowMapEntries n c sp sp_e)
      (hcl : FlowMapEntriesCloseable h) (hcomma : GLit ',' sp_e sp_c)
      (hsep : GOpt (SSeparate n c) sp_c sp') : PartialFlowMap n c sp sp'

/-- Snoc an entry onto a `held` partial (the `,` then entry transition):
    `held … → entries`. -/
lemma PartialFlowSeq_snocFromHeld {n : Nat} {c : YamlContext}
    {sp sp_e sp_c sp_d sp_f sp' : SurfPos}
    (h : SFlowSeqEntries n c sp sp_e) (hcl : FlowSeqEntriesCloseable h)
    (hcomma : GLit ',' sp_e sp_c) (hsep : GOpt (SSeparate n c) sp_c sp_d)
    (h_entry : SFlowSeqEntry n c sp_d sp_f) (h_sep2 : GOpt (SSeparate n c) sp_f sp') :
    PartialFlowSeq n c sp sp' :=
  .entries sp sp' (SFlowSeqEntries_snoc hcl hcomma hsep h_entry h_sep2)
    (SFlowSeqEntries_snoc_closeable hcl hcomma hsep h_entry h_sep2)

/-- Snoc an entry onto a `held` partial map: `held … → entries`. -/
lemma PartialFlowMap_snocFromHeld {n : Nat} {c : YamlContext}
    {sp sp_e sp_c sp_d sp_f sp' : SurfPos}
    (h : SFlowMapEntries n c sp sp_e) (hcl : FlowMapEntriesCloseable h)
    (hcomma : GLit ',' sp_e sp_c) (hsep : GOpt (SSeparate n c) sp_c sp_d)
    (h_entry : SFlowMapEntry n c sp_d sp_f) (h_sep2 : GOpt (SSeparate n c) sp_f sp') :
    PartialFlowMap n c sp sp' :=
  .entries sp sp' (SFlowMapEntries_snoc hcl hcomma hsep h_entry h_sep2)
    (SFlowMapEntries_snoc_closeable hcl hcomma hsep h_entry h_sep2)

/-- Finalize a partial flow sequence into a complete `SFlowSequence` at the
    outer context, given the bracket literals and post-`[` separation. -/
lemma PartialFlowSeq.closeSeq {n : Nat} {c_out : YamlContext}
    {sp_before sp_open sp_es sp_cur sp' : SurfPos}
    (h_open : GLit '[' sp_before sp_open)
    (h_sep : GOpt (SSeparate n c_out) sp_open sp_es)
    (p : PartialFlowSeq n (inFlowCtx c_out) sp_es sp_cur)
    (h_close : GLit ']' sp_cur sp') :
    SFlowSequence n c_out sp_before sp' := by
  cases p with
  | empty => exact flowSeq_empty h_open h_sep h_close
  | entries _ h _ => exact flowSeq_nonempty h_open h_sep h h_close
  | held _ _ _ h hcl hcomma hsep =>
    exact flowSeq_nonempty h_open h_sep
      (SFlowSeqEntries_addTrailingComma hcl hcomma hsep) h_close

/-- Finalize a partial flow mapping into a complete `SFlowMapping`. -/
lemma PartialFlowMap.closeMap {n : Nat} {c_out : YamlContext}
    {sp_before sp_open sp_es sp_cur sp' : SurfPos}
    (h_open : GLit '{' sp_before sp_open)
    (h_sep : GOpt (SSeparate n c_out) sp_open sp_es)
    (p : PartialFlowMap n (inFlowCtx c_out) sp_es sp_cur)
    (h_close : GLit '}' sp_cur sp') :
    SFlowMapping n c_out sp_before sp' := by
  cases p with
  | empty => exact flowMap_empty h_open h_sep h_close
  | entries _ h _ => exact flowMap_nonempty h_open h_sep h h_close
  | held _ _ _ h hcl hcomma hsep =>
    exact flowMap_nonempty h_open h_sep
      (SFlowMapEntries_addTrailingComma hcl hcomma hsep) h_close

/-! ## §4f Flow-entry completion + mid-entry states (Fix A, Stage B.3)

    A flow-collection entry can span several `scanNextToken` steps: `{a: b}` is
    scanned as key `a`, then `:`, then value `b`. The `empty`/`entries`/`held`
    `PartialFlow*` states capture only the *between-entries* positions; the
    *mid-entry* positions (key seen, `:` not yet; or `:` seen, value not yet) get
    their own evidence here, carried by `PendingFlowMapEntry`/`PendingFlowSeqEntry`.

    Because plain scalars are right-trimmed, every separator (key→`:`, `:`→value,
    and the trailing one before `,`/`]`/`}`) is consumed by the *following* scan
    step's preprocessing. So a mid-entry state ends exactly at its last token
    (key-end or colon-end) and each transition supplies its own leading separator.
    Completing a mid-entry snocs a finished entry onto the entries so far — first
    (`FlowMapPrefix.init`, accumulator was `empty`) or subsequent
    (`FlowMapPrefix.cons`, accumulator was `held`) — via `appendEntry`, landing
    back in the closeable `entries` state. `closeMap`/`closeSeq` are therefore
    unchanged: B.4 completes any mid-entry state before closing. This section is
    additive; wiring `PendingFlow*Entry` into the accumulation invariant is B.4.

    Scope: the *implicit* forms (`{a}` bareKey/G1, `{a: b}` implicitValue,
    `{a:}` implicitEmpty; `[a]` node, `[a: b]` pairValue, `[a:]` pairEmpty). The
    explicit-`?` and empty-key mid-entry states are a follow-on. -/

/-- The committed map entries a fresh entry extends: none yet (`init`; the
    accumulator was `empty`) or a closeable run then `,` + separator (`cons`; the
    accumulator was `held`). Unifies the first-vs-subsequent entry snoc. -/
inductive FlowMapPrefix (n : Nat) (c : YamlContext) : SurfPos → SurfPos → Prop where
  | init (sp : SurfPos) : FlowMapPrefix n c sp sp
  | cons (sp sp_e sp_c sp' : SurfPos) (h : SFlowMapEntries n c sp sp_e)
      (hcl : FlowMapEntriesCloseable h) (hcomma : GLit ',' sp_e sp_c)
      (hsep : GOpt (SSeparate n c) sp_c sp') : FlowMapPrefix n c sp sp'

/-- The committed seq entries a fresh entry extends (see `FlowMapPrefix`). -/
inductive FlowSeqPrefix (n : Nat) (c : YamlContext) : SurfPos → SurfPos → Prop where
  | init (sp : SurfPos) : FlowSeqPrefix n c sp sp
  | cons (sp sp_e sp_c sp' : SurfPos) (h : SFlowSeqEntries n c sp sp_e)
      (hcl : FlowSeqEntriesCloseable h) (hcomma : GLit ',' sp_e sp_c)
      (hsep : GOpt (SSeparate n c) sp_c sp') : FlowSeqPrefix n c sp sp'

/-- Snoc a completed map entry (+ trailing separator) onto a prefix, landing in
    the closeable `entries` state. `init` → single; `cons` → snoc-from-held. -/
lemma FlowMapPrefix.appendEntry {n : Nat} {c : YamlContext} {sp sp_d sp_e sp' : SurfPos}
    (pre : FlowMapPrefix n c sp sp_d)
    (h_entry : SFlowMapEntry n c sp_d sp_e) (h_sep : GOpt (SSeparate n c) sp_e sp') :
    PartialFlowMap n c sp sp' := by
  cases pre with
  | init =>
      exact .entries _ _ (SFlowMapEntries_single h_entry h_sep)
        (SFlowMapEntries_single_closeable h_entry h_sep)
  | cons _ _ _ h hcl hcomma hsep =>
      exact PartialFlowMap_snocFromHeld h hcl hcomma hsep h_entry h_sep

/-- Snoc a completed seq entry (+ trailing separator) onto a prefix. -/
lemma FlowSeqPrefix.appendEntry {n : Nat} {c : YamlContext} {sp sp_d sp_e sp' : SurfPos}
    (pre : FlowSeqPrefix n c sp sp_d)
    (h_entry : SFlowSeqEntry n c sp_d sp_e) (h_sep : GOpt (SSeparate n c) sp_e sp') :
    PartialFlowSeq n c sp sp' := by
  cases pre with
  | init =>
      exact .entries _ _ (SFlowSeqEntries_single h_entry h_sep)
        (SFlowSeqEntries_single_closeable h_entry h_sep)
  | cons _ _ _ h hcl hcomma hsep =>
      exact PartialFlowSeq_snocFromHeld h hcl hcomma hsep h_entry h_sep

/-- A flow-map entry under construction (see §4f). `keyPending`: a YAML key node
    has been scanned, awaiting `:` or a bare close (`{a}`, G1). `colonPending`:
    the mapping `:` has been scanned, awaiting a value (`{a: b}`) or empty close
    (`{a:}`). -/
inductive PendingFlowMapEntry (n : Nat) (c : YamlContext) : SurfPos → SurfPos → Prop where
  | keyPending (sp sp_d sp' : SurfPos) (pre : FlowMapPrefix n c sp sp_d)
      (hkey : SFlowNode n c sp_d sp') : PendingFlowMapEntry n c sp sp'
  | colonPending (sp sp_d sp_k sp_s sp' : SurfPos) (pre : FlowMapPrefix n c sp sp_d)
      (hkey : SFlowNode n c sp_d sp_k) (hsep : GOpt (SSeparate n c) sp_k sp_s)
      (hcolon : GLit ':' sp_s sp') : PendingFlowMapEntry n c sp sp'
  | explicitKeyPending (sp sp_q sp_qe sp_k0 sp' : SurfPos) (pre : FlowMapPrefix n c sp sp_q)
      (hq : GLit '?' sp_q sp_qe) (hqsep : SSeparate n c sp_qe sp_k0)
      (hkey : SFlowNode n c sp_k0 sp') : PendingFlowMapEntry n c sp sp'
  | explicitColonPending (sp sp_q sp_qe sp_k0 sp_k sp_s sp' : SurfPos)
      (pre : FlowMapPrefix n c sp sp_q) (hq : GLit '?' sp_q sp_qe)
      (hqsep : SSeparate n c sp_qe sp_k0) (hkey : SFlowNode n c sp_k0 sp_k)
      (hsep : GOpt (SSeparate n c) sp_k sp_s) (hcolon : GLit ':' sp_s sp') :
      PendingFlowMapEntry n c sp sp'
  | emptyColonPending (sp sp_s sp' : SurfPos) (pre : FlowMapPrefix n c sp sp_s)
      (hcolon : GLit ':' sp_s sp') : PendingFlowMapEntry n c sp sp'

/-- `keyPending` + (key→`:` separator) + `:` → `colonPending`. -/
lemma PendingFlowMapEntry.toColon {n : Nat} {c : YamlContext} {sp sp_d sp_k sp_s sp' : SurfPos}
    (pre : FlowMapPrefix n c sp sp_d) (hkey : SFlowNode n c sp_d sp_k)
    (hsep : GOpt (SSeparate n c) sp_k sp_s) (hcolon : GLit ':' sp_s sp') :
    PendingFlowMapEntry n c sp sp' :=
  .colonPending sp sp_d sp_k sp_s sp' pre hkey hsep hcolon

/-- Close a `keyPending` as a bare-key entry (G1): `{a}`. The trailing separator
    is the closing step's preprocessing whitespace. -/
lemma PendingFlowMapEntry.finishBareKey {n : Nat} {c : YamlContext} {sp sp_d sp_k sp' : SurfPos}
    (pre : FlowMapPrefix n c sp sp_d) (hkey : SFlowNode n c sp_d sp_k)
    (h_sep_tr : GOpt (SSeparate n c) sp_k sp') :
    PartialFlowMap n c sp sp' :=
  pre.appendEntry (SFlowMapEntry.bareKey n c sp_d sp_k hkey) h_sep_tr

/-- Close a `colonPending` with an empty value (`implicitEmpty`): `{a:}`. -/
lemma PendingFlowMapEntry.finishEmpty {n : Nat} {c : YamlContext} {sp sp_d sp_k sp_s sp_c sp' : SurfPos}
    (pre : FlowMapPrefix n c sp sp_d) (hkey : SFlowNode n c sp_d sp_k)
    (hsep : GOpt (SSeparate n c) sp_k sp_s) (hcolon : GLit ':' sp_s sp_c)
    (h_sep_tr : GOpt (SSeparate n c) sp_c sp') :
    PartialFlowMap n c sp sp' :=
  pre.appendEntry (SFlowMapEntry.implicitEmpty n c sp_d sp_k sp_s sp_c hkey hsep hcolon) h_sep_tr

/-- A flow-seq entry under construction. `nodePending`: a flow node has been
    scanned; it closes as a plain entry (`[a]`) or, if `:` follows, is a pair key.
    `colonPending`: the pair `:` has been scanned (`[a: b]`, `[a:]`). -/
inductive PendingFlowSeqEntry (n : Nat) (c : YamlContext) : SurfPos → SurfPos → Prop where
  | nodePending (sp sp_d sp' : SurfPos) (pre : FlowSeqPrefix n c sp sp_d)
      (hnode : SFlowNode n c sp_d sp') : PendingFlowSeqEntry n c sp sp'
  | colonPending (sp sp_d sp_k sp_s sp' : SurfPos) (pre : FlowSeqPrefix n c sp sp_d)
      (hkey : SFlowNode n c sp_d sp_k) (hsep : GOpt (SSeparate n c) sp_k sp_s)
      (hcolon : GLit ':' sp_s sp') : PendingFlowSeqEntry n c sp sp'
  | explicitPending (sp sp_q sp_qe sp_k0 sp' : SurfPos) (pre : FlowSeqPrefix n c sp sp_q)
      (hq : GLit '?' sp_q sp_qe) (hqsep : SSeparate n c sp_qe sp_k0)
      (hkey : SFlowNode n c sp_k0 sp') : PendingFlowSeqEntry n c sp sp'
  | explicitColonPending (sp sp_q sp_qe sp_k0 sp_k sp_s sp' : SurfPos)
      (pre : FlowSeqPrefix n c sp sp_q) (hq : GLit '?' sp_q sp_qe)
      (hqsep : SSeparate n c sp_qe sp_k0) (hkey : SFlowNode n c sp_k0 sp_k)
      (hsep : GOpt (SSeparate n c) sp_k sp_s) (hcolon : GLit ':' sp_s sp') :
      PendingFlowSeqEntry n c sp sp'

/-- `nodePending` + (node→`:` separator) + `:` → `colonPending` (the node was a
    pair key after all). -/
lemma PendingFlowSeqEntry.toColon {n : Nat} {c : YamlContext} {sp sp_d sp_k sp_s sp' : SurfPos}
    (pre : FlowSeqPrefix n c sp sp_d) (hkey : SFlowNode n c sp_d sp_k)
    (hsep : GOpt (SSeparate n c) sp_k sp_s) (hcolon : GLit ':' sp_s sp') :
    PendingFlowSeqEntry n c sp sp' :=
  .colonPending sp sp_d sp_k sp_s sp' pre hkey hsep hcolon

/-- Close a `nodePending` as a plain node entry: `[a]`, `[[x], y]`. -/
lemma PendingFlowSeqEntry.finishNode {n : Nat} {c : YamlContext} {sp sp_d sp_n sp' : SurfPos}
    (pre : FlowSeqPrefix n c sp sp_d) (hnode : SFlowNode n c sp_d sp_n)
    (h_sep_tr : GOpt (SSeparate n c) sp_n sp') :
    PartialFlowSeq n c sp sp' :=
  pre.appendEntry (SFlowSeqEntry.node n c sp_d sp_n hnode) h_sep_tr

/-- Close a `colonPending` seq pair with an empty value (`pairEmpty`): `[a:]`. -/
lemma PendingFlowSeqEntry.finishPairEmpty {n : Nat} {c : YamlContext}
    {sp sp_d sp_k sp_s sp_c sp' : SurfPos}
    (pre : FlowSeqPrefix n c sp sp_d) (hkey : SFlowNode n c sp_d sp_k)
    (hsep : GOpt (SSeparate n c) sp_k sp_s) (hcolon : GLit ':' sp_s sp_c)
    (h_sep_tr : GOpt (SSeparate n c) sp_c sp') :
    PartialFlowSeq n c sp sp' :=
  pre.appendEntry (SFlowSeqEntry.pairEmpty n c sp_d sp_k sp_s sp_c hkey hsep hcolon) h_sep_tr

/-! ## §4g Explicit-`?` and empty-key flow-entry completions (Fix A, Stage B.3b)

    The remaining flow-entry forms behind `scannerDrop`: explicit `?`-marked
    entries (`{? a}`, `{? a : b}`, `{? a :}` and their `[ ]` pair analogs) and
    empty-key map entries (`{: b}`, `{:}`). Same completion discipline as §4f: a
    mid-entry state (extended `PendingFlow*Entry`) ends at its last token; each
    completion snocs the finished entry via `appendEntry` with the closing/comma
    step's trailing separator. The `?` and the leading `:` are literal surface
    characters, so each carries a `GLit '?'`/`GLit ':'` derivation. -/

/-- Close an `explicitKeyPending` as `explicitKeyOnly` (G2): `{? a}`. -/
lemma PendingFlowMapEntry.finishExplicitKeyOnly {n : Nat} {c : YamlContext}
    {sp sp_q sp_qe sp_k0 sp_k sp' : SurfPos}
    (pre : FlowMapPrefix n c sp sp_q) (hq : GLit '?' sp_q sp_qe)
    (hqsep : SSeparate n c sp_qe sp_k0) (hkey : SFlowNode n c sp_k0 sp_k)
    (h_sep_tr : GOpt (SSeparate n c) sp_k sp') :
    PartialFlowMap n c sp sp' :=
  pre.appendEntry (SFlowMapEntry.explicitKeyOnly n c sp_q sp_qe sp_k0 sp_k hq hqsep hkey) h_sep_tr

/-- Close an `explicitColonPending` with an empty value (`explicitEmpty`): `{? a :}`. -/
lemma PendingFlowMapEntry.finishExplicitEmpty {n : Nat} {c : YamlContext}
    {sp sp_q sp_qe sp_k0 sp_k sp_s sp_col sp' : SurfPos}
    (pre : FlowMapPrefix n c sp sp_q) (hq : GLit '?' sp_q sp_qe)
    (hqsep : SSeparate n c sp_qe sp_k0) (hkey : SFlowNode n c sp_k0 sp_k)
    (hsep : GOpt (SSeparate n c) sp_k sp_s) (hcolon : GLit ':' sp_s sp_col)
    (h_sep_tr : GOpt (SSeparate n c) sp_col sp') :
    PartialFlowMap n c sp sp' :=
  pre.appendEntry
    (SFlowMapEntry.explicitEmpty n c sp_q sp_qe sp_k0 sp_k sp_s sp_col hq hqsep hkey hsep hcolon)
    h_sep_tr

/-- Close an `emptyColonPending` with an empty value (`emptyKeyEmpty`): `{:}`. -/
lemma PendingFlowMapEntry.finishEmptyKeyEmpty {n : Nat} {c : YamlContext}
    {sp sp_s sp_col sp' : SurfPos}
    (pre : FlowMapPrefix n c sp sp_s) (hcolon : GLit ':' sp_s sp_col)
    (h_sep_tr : GOpt (SSeparate n c) sp_col sp') :
    PartialFlowMap n c sp sp' :=
  pre.appendEntry (SFlowMapEntry.emptyKeyEmpty n c sp_s sp_col hcolon) h_sep_tr

/-- Close an `explicitPending` seq entry as `explicitPairKeyOnly`: `[? a]`. -/
lemma PendingFlowSeqEntry.finishExplicitKeyOnly {n : Nat} {c : YamlContext}
    {sp sp_q sp_qe sp_k0 sp_k sp' : SurfPos}
    (pre : FlowSeqPrefix n c sp sp_q) (hq : GLit '?' sp_q sp_qe)
    (hqsep : SSeparate n c sp_qe sp_k0) (hkey : SFlowNode n c sp_k0 sp_k)
    (h_sep_tr : GOpt (SSeparate n c) sp_k sp') :
    PartialFlowSeq n c sp sp' :=
  pre.appendEntry (SFlowSeqEntry.explicitPairKeyOnly n c sp_q sp_qe sp_k0 sp_k hq hqsep hkey) h_sep_tr

/-- Close an `explicitColonPending` seq pair with an empty value (`explicitPairEmpty`): `[? a :]`. -/
lemma PendingFlowSeqEntry.finishExplicitPairEmpty {n : Nat} {c : YamlContext}
    {sp sp_q sp_qe sp_k0 sp_k sp_s sp_col sp' : SurfPos}
    (pre : FlowSeqPrefix n c sp sp_q) (hq : GLit '?' sp_q sp_qe)
    (hqsep : SSeparate n c sp_qe sp_k0) (hkey : SFlowNode n c sp_k0 sp_k)
    (hsep : GOpt (SSeparate n c) sp_k sp_s) (hcolon : GLit ':' sp_s sp_col)
    (h_sep_tr : GOpt (SSeparate n c) sp_col sp') :
    PartialFlowSeq n c sp sp' :=
  pre.appendEntry
    (SFlowSeqEntry.explicitPairEmpty n c sp_q sp_qe sp_k0 sp_k sp_s sp_col hq hqsep hkey hsep hcolon)
    h_sep_tr

end L4YAML.Proofs.NodeProduction

end Blanket
