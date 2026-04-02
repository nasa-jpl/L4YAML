import Lean4Yaml.Proofs.ScalarProduction
import Lean4Yaml.Proofs.StructureProduction

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

namespace Lean4Yaml.Proofs.NodeProduction

open Lean4Yaml.Surface
open Lean4Yaml.Scanner
open Lean4Yaml.Proofs.CouplingBridge
open Lean4Yaml.Proofs.ScalarProduction
open Lean4Yaml.Proofs.StructureProduction

/-! ## §1 Pure Composition: Scalar → SFlowContent -/

-- [154] c-flow-json-content: double-quoted scalar.
theorem doubleQuoted_flowContent {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SCDoubleQuoted n c s s') :
    SFlowContent n c s s' :=
  SFlowContent.doubleQ n c s s' h

-- [154] c-flow-json-content: single-quoted scalar.
theorem singleQuoted_flowContent {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SCSingleQuoted n c s s') :
    SFlowContent n c s s' :=
  SFlowContent.singleQ n c s s' h

-- [159] ns-flow-yaml-content: plain scalar.
theorem plain_flowContent {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SNsPlain n c s s') :
    SFlowContent n c s s' :=
  SFlowContent.plain n c s s' h

-- [154] c-flow-json-content: flow sequence.
theorem flowSeq_flowContent {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SFlowSequence n c s s') :
    SFlowContent n c s s' :=
  SFlowContent.flowSeq n c s s' h

-- [154] c-flow-json-content: flow mapping.
theorem flowMap_flowContent {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SFlowMapping n c s s') :
    SFlowContent n c s s' :=
  SFlowContent.flowMap n c s s' h

/-! ## §2 Pure Composition: SFlowContent → SFlowNode -/

-- [161] ns-flow-node: bare content (no properties).
theorem flowContent_flowNode {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SFlowContent n c s s') :
    SFlowNode n c s s' :=
  SFlowNode.content n c s s' h

-- [161] ns-flow-node: alias reference.
theorem alias_flowNode {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SCNsAliasNode s s') :
    SFlowNode n c s s' :=
  SFlowNode.alias n c s s' h

-- [161] ns-flow-node: properties + separator + content.
theorem propsContent_flowNode {n : Nat} {c : YamlContext}
    {s s₁ s₂ s' : SurfPos}
    (h_props : SCNsProperties n c s s₁)
    (h_sep : SSeparate n c s₁ s₂)
    (h_content : SFlowContent n c s₂ s') :
    SFlowNode n c s s' :=
  SFlowNode.propsContent n c s s₁ s₂ s' h_props h_sep h_content

-- [161] ns-flow-node: properties only (empty content).
theorem propsEmpty_flowNode {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h_props : SCNsProperties n c s s') :
    SFlowNode n c s s' :=
  SFlowNode.propsEmpty n c s s' h_props

/-! ## §3 Pure Composition: SFlowNode / Scalars → SBlockNode -/

-- [195] s-l+flow-in-block(n,c): separator + flow node + comments.
theorem flowInBlock_blockNode {n : Nat} {c : YamlContext}
    {s s₁ s₂ s' : SurfPos}
    (h_sep : SSeparate (n + 1) .flowOut s s₁)
    (h_flow : SFlowNode (n + 1) .flowOut s₁ s₂)
    (h_comments : SSLComments s₂ s') :
    SBlockNode n c s s' :=
  SBlockNode.flowInBlock n c s s₁ s₂ s' h_sep h_flow h_comments

-- [198] s-l+block-scalar: separator + optional properties + literal scalar.
theorem literal_blockNode {n : Nat} {c : YamlContext}
    {s s₁ s₂ s' : SurfPos}
    (h_sep : SSeparate (n + 1) c s s₁)
    (h_props : GOpt (GSeq (SCNsProperties (n + 1) c) (SSeparate (n + 1) c)) s₁ s₂)
    (h_lit : SCLLiteral n s₂ s') :
    SBlockNode n c s s' :=
  SBlockNode.blockLiteral n c s s₁ s₂ s' h_sep h_props h_lit

-- [198] s-l+block-scalar: separator + optional properties + folded scalar.
theorem folded_blockNode {n : Nat} {c : YamlContext}
    {s s₁ s₂ s' : SurfPos}
    (h_sep : SSeparate (n + 1) c s s₁)
    (h_props : GOpt (GSeq (SCNsProperties (n + 1) c) (SSeparate (n + 1) c)) s₁ s₂)
    (h_fold : SCLFolded n s₂ s') :
    SBlockNode n c s s' :=
  SBlockNode.blockFolded n c s s₁ s₂ s' h_sep h_props h_fold

-- [72] e-node + s-l-comments: empty node.
theorem emptyNode_blockNode {n : Nat} {c : YamlContext} {s s' : SurfPos}
    (h : SSLComments s s') :
    SBlockNode n c s s' :=
  SBlockNode.emptyNode n c s s' h

/-! ## §4 Scanner-to-SFlowContent Production (n=0, c=.blockIn) -/

-- `scanDoubleQuoted` success → `SFlowContent 0 .blockIn`.
theorem scanDoubleQuoted_flowContent_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_dq : sc.peek? = some '"')
    (hok : scanDoubleQuoted sc = .ok s') :
    ∃ sp', SFlowContent 0 .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨sp', h_dq, hcorr'⟩ := scanDoubleQuoted_prod sc sp hcorr hpeek_dq hok
  exact ⟨sp', doubleQuoted_flowContent h_dq, hcorr'⟩

-- `scanSingleQuoted` success → `SFlowContent 0 .blockIn`.
theorem scanSingleQuoted_flowContent_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_sq : sc.peek? = some '\'')
    (hok : scanSingleQuoted sc = .ok s') :
    ∃ sp', SFlowContent 0 .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨sp', h_sq, hcorr'⟩ := scanSingleQuoted_prod sc sp hcorr hpeek_sq hok
  exact ⟨sp', singleQuoted_flowContent h_sq, hcorr'⟩

/-! ## §5 Scanner-to-SFlowNode Production (n=0, c=.blockIn) -/

-- `scanDoubleQuoted` success → `SFlowNode 0 .blockIn`.
theorem scanDoubleQuoted_flowNode_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_dq : sc.peek? = some '"')
    (hok : scanDoubleQuoted sc = .ok s') :
    ∃ sp', SFlowNode 0 .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨sp', h_fc, hcorr'⟩ := scanDoubleQuoted_flowContent_prod sc sp hcorr hpeek_dq hok
  exact ⟨sp', flowContent_flowNode h_fc, hcorr'⟩

-- `scanSingleQuoted` success → `SFlowNode 0 .blockIn`.
theorem scanSingleQuoted_flowNode_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_sq : sc.peek? = some '\'')
    (hok : scanSingleQuoted sc = .ok s') :
    ∃ sp', SFlowNode 0 .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨sp', h_fc, hcorr'⟩ := scanSingleQuoted_flowContent_prod sc sp hcorr hpeek_sq hok
  exact ⟨sp', flowContent_flowNode h_fc, hcorr'⟩

/-! ## §5a Context Compatibility: Lifting across YamlContext (Layer 4i building blocks)

    For double-quoted and single-quoted scalars, the body text production
    (`SNbDoubleText`/`SNbSingleText`) dispatches on context `c`:
      - `.flowKey` → one-line body
      - `_`        → multi-line body (parameterized only by `n`)
    Since all non-flowKey contexts reduce to the SAME multi-line body,
    these scalar types can be freely lifted across non-flowKey contexts.

    This is a building block for Layer 4i (context parameter lifting).
    Once `_prod` theorems are strengthened to produce at the scanner's
    actual indent `n`, these lifts bridge `.blockIn → .flowOut` for free.

    Note: `SSeparate n c` for non-key contexts (blockOut/blockIn/flowOut/flowIn)
    all reduce to `SSeparateLines n` definitionally. No explicit lemma needed.

    Note: Plain scalar (`SNsPlain n c`) context lift does NOT hold in the
    `.blockIn → .flowOut` direction because `isNsPlainSafe .blockIn` allows
    flow indicator characters that `isNsPlainSafe .flowOut` forbids.
    The reverse direction (`.flowOut → .blockIn`) holds but is not needed. -/

-- [107] c-double-quoted context lift: any non-flowKey → any non-flowKey (same n).
-- SNbDoubleText n c reduces to SNbDoubleMultiLine n for all c ≠ .flowKey.
theorem SCDoubleQuoted_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
    (h : SCDoubleQuoted n c₁ s s') (hc₁ : c₁ ≠ .flowKey) (hc₂ : c₂ ≠ .flowKey) :
    SCDoubleQuoted n c₂ s s' := by
  obtain ⟨_, _, _, h_open, h_text, h_close⟩ := h
  refine SCDoubleQuoted.mk n c₂ _ _ _ _ h_open ?_ h_close
  cases c₁ <;> cases c₂ <;> simp_all [SNbDoubleText]

-- [118] c-single-quoted context lift: any non-flowKey → any non-flowKey (same n).
-- SNbSingleText n c reduces to SNbSingleMultiLine n for all c ≠ .flowKey.
theorem SCSingleQuoted_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
    (h : SCSingleQuoted n c₁ s s') (hc₁ : c₁ ≠ .flowKey) (hc₂ : c₂ ≠ .flowKey) :
    SCSingleQuoted n c₂ s s' := by
  obtain ⟨_, _, _, h_open, h_text, h_close⟩ := h
  refine SCSingleQuoted.mk n c₂ _ _ _ _ h_open ?_ h_close
  cases c₁ <;> cases c₂ <;> simp_all [SNbSingleText]

-- SFlowContent context lift for quoted scalars.
-- Works for double-quoted, single-quoted, and alias (which has no context).
-- Does NOT work for plain scalars or flow collections in general.
theorem SFlowContent_doubleQ_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
    (h : SCDoubleQuoted n c₁ s s') (hc₁ : c₁ ≠ .flowKey) (hc₂ : c₂ ≠ .flowKey) :
    SFlowContent n c₂ s s' :=
  doubleQuoted_flowContent (SCDoubleQuoted_ctx_lift h hc₁ hc₂)

theorem SFlowContent_singleQ_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
    (h : SCSingleQuoted n c₁ s s') (hc₁ : c₁ ≠ .flowKey) (hc₂ : c₂ ≠ .flowKey) :
    SFlowContent n c₂ s s' :=
  singleQuoted_flowContent (SCSingleQuoted_ctx_lift h hc₁ hc₂)

-- SFlowNode context lift for quoted scalars (bare content, no properties).
theorem SFlowNode_doubleQ_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
    (h : SCDoubleQuoted n c₁ s s') (hc₁ : c₁ ≠ .flowKey) (hc₂ : c₂ ≠ .flowKey) :
    SFlowNode n c₂ s s' :=
  flowContent_flowNode (SFlowContent_doubleQ_ctx_lift h hc₁ hc₂)

theorem SFlowNode_singleQ_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
    (h : SCSingleQuoted n c₁ s s') (hc₁ : c₁ ≠ .flowKey) (hc₂ : c₂ ≠ .flowKey) :
    SFlowNode n c₂ s s' :=
  flowContent_flowNode (SFlowContent_singleQ_ctx_lift h hc₁ hc₂)

/-! ## §6 GStar/GPlus Lifting and Alias/Anchor Conversion (Layer 4a) -/

-- General combinator: convert GStar to GPlus given proof of non-emptiness.
-- The non-emptiness evidence is `s ≠ s'` (the start ≠ end position).
theorem GStar_to_GPlus {P : SurfPos → SurfPos → Prop} {s s' : SurfPos}
    (h : GStar P s s') (hne : s ≠ s') : GPlus P s s' := by
  match h with
  | .nil _ => exact absurd rfl hne
  | .cons _ sp_mid _ h_head h_tail => exact GPlus.mk _ sp_mid _ h_head h_tail

-- Alias node: GLit '*' + GPlus anchor chars → SCNsAliasNode.
-- Takes destructured GLit output + GPlus name.
theorem aliasNode_of_glit_gplus {rest : List Char} {col : Nat} {sp' : SurfPos}
    (h_gplus : GPlus (GChar isNsAnchorChar) ⟨rest, col + 1⟩ sp') :
    SCNsAliasNode ⟨'*' :: rest, col⟩ sp' :=
  SCNsAliasNode.mk rest col sp' h_gplus

-- Anchor property: GLit '&' + GPlus anchor chars → SCNsAnchorProperty.
theorem anchorProp_of_glit_gplus {rest : List Char} {col : Nat} {sp' : SurfPos}
    (h_gplus : GPlus (GChar isNsAnchorChar) ⟨rest, col + 1⟩ sp') :
    SCNsAnchorProperty ⟨'&' :: rest, col⟩ sp' :=
  SCNsAnchorProperty.mk rest col sp' h_gplus

-- scanAnchorOrAlias with non-empty name → SCNsAliasNode.
-- Hypothesis: sp_mid ≠ sp' (scanner collected ≥1 anchor char after '*').
theorem scanAnchorOrAlias_aliasNode_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '*') :
    ∃ sp_mid sp', GLit '*' sp sp_mid ∧
                  GStar (GChar isNsAnchorChar) sp_mid sp' ∧
                  (sp_mid ≠ sp' → SCNsAliasNode sp sp') ∧
                  ScannerSurfCorr (scanAnchorOrAlias sc false) sp' := by
  obtain ⟨sp_mid, sp', h_glit, h_gstar, hcorr'⟩ :=
    scanAnchorOrAlias_prod sc sp hcorr false '*' hpeek (by decide) (by decide)
  refine ⟨sp_mid, sp', h_glit, h_gstar, ?_, hcorr'⟩
  intro hne
  cases h_glit with
  | mk rest col =>
    exact aliasNode_of_glit_gplus (GStar_to_GPlus h_gstar hne)

-- scanAnchorOrAlias with non-empty name → SCNsAnchorProperty.
-- Hypothesis: sp_mid ≠ sp' (scanner collected ≥1 anchor char after '&').
theorem scanAnchorOrAlias_anchorProp_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '&') :
    ∃ sp_mid sp', GLit '&' sp sp_mid ∧
                  GStar (GChar isNsAnchorChar) sp_mid sp' ∧
                  (sp_mid ≠ sp' → SCNsAnchorProperty sp sp') ∧
                  ScannerSurfCorr (scanAnchorOrAlias sc true) sp' := by
  obtain ⟨sp_mid, sp', h_glit, h_gstar, hcorr'⟩ :=
    scanAnchorOrAlias_prod sc sp hcorr true '&' hpeek (by decide) (by decide)
  refine ⟨sp_mid, sp', h_glit, h_gstar, ?_, hcorr'⟩
  intro hne
  cases h_glit with
  | mk rest col =>
    exact anchorProp_of_glit_gplus (GStar_to_GPlus h_gstar hne)

-- scanAnchorOrAlias with non-empty name → SFlowNode (alias).
theorem scanAnchorOrAlias_flowNode_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '*') :
    ∃ sp_mid sp', GLit '*' sp sp_mid ∧
                  GStar (GChar isNsAnchorChar) sp_mid sp' ∧
                  (sp_mid ≠ sp' → SFlowNode 0 .blockIn sp sp') ∧
                  ScannerSurfCorr (scanAnchorOrAlias sc false) sp' := by
  obtain ⟨sp_mid, sp', h_glit, h_gstar, h_alias, hcorr'⟩ :=
    scanAnchorOrAlias_aliasNode_prod sc sp hcorr hpeek
  exact ⟨sp_mid, sp', h_glit, h_gstar,
         fun hne => alias_flowNode (h_alias hne), hcorr'⟩

end Lean4Yaml.Proofs.NodeProduction
