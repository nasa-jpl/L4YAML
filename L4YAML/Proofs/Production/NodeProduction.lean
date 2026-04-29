import L4YAML.Proofs.Production.ScalarProduction
import L4YAML.Proofs.Production.StructureProduction

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
    (h_sep : SSeparate n .flowOut s s₁)
    (h_flow : SFlowNode n .flowOut s₁ s₂)
    (h_comments : SSLComments s₂ s') :
    SBlockNode n c s s' :=
  SBlockNode.flowInBlock n c s s₁ s₂ s' h_sep h_flow h_comments

-- [198] s-l+block-scalar: separator + optional properties + literal scalar.
theorem literal_blockNode {n : Nat} {c : YamlContext}
    {s s₁ s₂ s' : SurfPos}
    (h_sep : SSeparate n c s s₁)
    (h_props : GOpt (GSeq (SCNsProperties n c) (SSeparate n c)) s₁ s₂)
    (h_lit : SCLLiteral n s₂ s') :
    SBlockNode n c s s' :=
  SBlockNode.blockLiteral n c s s₁ s₂ s' h_sep h_props h_lit

-- [198] s-l+block-scalar: separator + optional properties + folded scalar.
theorem folded_blockNode {n : Nat} {c : YamlContext}
    {s s₁ s₂ s' : SurfPos}
    (h_sep : SSeparate n c s s₁)
    (h_props : GOpt (GSeq (SCNsProperties n c) (SSeparate n c)) s₁ s₂)
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
theorem SNsPlainFirst_blockIn_to_flowOut {s s' : SurfPos}
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
theorem SNsPlain_blockIn_to_flowOut_minimal {s s₁ : SurfPos}
    (h_first : SNsPlainFirst .blockIn s s₁) :
    SNsPlain 0 .flowOut s s₁ :=
  SNsPlainMultiLine.mk 0 .flowOut s s₁ s₁
    (SNsPlainOneLine.mk .flowOut s s₁ s₁
      (SNsPlainFirst_blockIn_to_flowOut h_first) (GStar.nil _))
    (GStar.nil _)

-- Plain scalar → SFlowNode context lift for minimal witness.
-- Composes: SNsPlainFirst .blockIn → SNsPlain 0 .flowOut → SFlowContent → SFlowNode.
theorem SFlowNode_plain_blockIn_to_flowOut_minimal {s s₁ : SurfPos}
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
theorem SCDoubleQuoted_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
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
theorem SCSingleQuoted_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
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
theorem SFlowContent_doubleQ_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
    (h : SCDoubleQuoted n c₁ s s')
    (hc₁ : c₁ ≠ .blockKey ∧ c₁ ≠ .flowKey)
    (hc₂ : c₂ ≠ .blockKey ∧ c₂ ≠ .flowKey) :
    SFlowContent n c₂ s s' :=
  doubleQuoted_flowContent (SCDoubleQuoted_ctx_lift h hc₁ hc₂)

theorem SFlowContent_singleQ_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
    (h : SCSingleQuoted n c₁ s s')
    (hc₁ : c₁ ≠ .blockKey ∧ c₁ ≠ .flowKey)
    (hc₂ : c₂ ≠ .blockKey ∧ c₂ ≠ .flowKey) :
    SFlowContent n c₂ s s' :=
  singleQuoted_flowContent (SCSingleQuoted_ctx_lift h hc₁ hc₂)

-- SFlowNode context lift for quoted scalars (bare content, no properties).
theorem SFlowNode_doubleQ_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
    (h : SCDoubleQuoted n c₁ s s')
    (hc₁ : c₁ ≠ .blockKey ∧ c₁ ≠ .flowKey)
    (hc₂ : c₂ ≠ .blockKey ∧ c₂ ≠ .flowKey) :
    SFlowNode n c₂ s s' :=
  flowContent_flowNode (SFlowContent_doubleQ_ctx_lift h hc₁ hc₂)

theorem SFlowNode_singleQ_ctx_lift {n : Nat} {c₁ c₂ : YamlContext} {s s' : SurfPos}
    (h : SCSingleQuoted n c₁ s s')
    (hc₁ : c₁ ≠ .blockKey ∧ c₁ ≠ .flowKey)
    (hc₂ : c₂ ≠ .blockKey ∧ c₂ ≠ .flowKey) :
    SFlowNode n c₂ s s' :=
  flowContent_flowNode (SFlowContent_singleQ_ctx_lift h hc₁ hc₂)

/-! ## §6 GStar/GPlus Lifting and Alias/Anchor Conversion (Layer 4a) -/

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

-- scanAnchorOrAlias → SCNsAliasNode (unconditional).
-- Since A10 Except conversion, `.ok` guarantees non-empty name, so sp_mid ≠ sp'.
theorem scanAnchorOrAlias_aliasNode_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '*')
    (s' : ScannerState) (hok : scanAnchorOrAlias sc false = .ok s') :
    ∃ sp', SCNsAliasNode sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨sp_mid, sp', h_glit, h_gstar, h_ne, hcorr'⟩ :=
    scanAnchorOrAlias_prod sc sp hcorr false '*' hpeek (by decide) (by decide) s' hok
  cases h_glit with
  | mk rest col =>
    exact ⟨sp', aliasNode_of_glit_gplus (GStar_to_GPlus h_gstar h_ne), hcorr'⟩

-- scanAnchorOrAlias → SCNsAnchorProperty (unconditional).
-- Since A10 Except conversion, `.ok` guarantees non-empty name, so sp_mid ≠ sp'.
theorem scanAnchorOrAlias_anchorProp_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '&')
    (s' : ScannerState) (hok : scanAnchorOrAlias sc true = .ok s') :
    ∃ sp', SCNsAnchorProperty sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨sp_mid, sp', h_glit, h_gstar, h_ne, hcorr'⟩ :=
    scanAnchorOrAlias_prod sc sp hcorr true '&' hpeek (by decide) (by decide) s' hok
  cases h_glit with
  | mk rest col =>
    exact ⟨sp', anchorProp_of_glit_gplus (GStar_to_GPlus h_gstar h_ne), hcorr'⟩

-- scanAnchorOrAlias → SFlowNode (alias, unconditional).
theorem scanAnchorOrAlias_flowNode_prod (sc : ScannerState) (sp : SurfPos)
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
theorem SBlockSeqEntries_snoc {n : Nat} {s s_mid s₁ s₂ s' : SurfPos}
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

end L4YAML.Proofs.NodeProduction
