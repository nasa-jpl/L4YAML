/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Proofs.Serialization.TraceOf.DocBridge
public import L4YAML.Proofs.Serialization.TraceOf.ContentBridge
public import L4YAML.Proofs.Foundation.SurfaceSpan

/-!
# The depth-0 pending node, T side (item 527, β PR 1)

`PendingNode` (`StreamAccum`) is what the accumulation invariant holds open at depth 0 beside
the closed stream; its stream-level constructors — `noPending`, `pendingDocEnd`,
`pendingDirective`, `pendingDocStart` — carry ROUTES into `SLYamlStream`.  `TPendingNode` is
their twin on the trace side: what the park holds open of the trace (`ev_o`, the open document's
events) and of `goOut`'s state (`p`, the pending `%TAG` handles), and the route that closes them
into `TLYamlStream` — `TSLYamlStream` (DocBridge §α) carries the closed stream and the coupling.
Priority 136: every depth-0 corpus prefix, by park class, against the `goOut` split.

The content parks (`pendingContent`, `pendingProps`, `pendingBlock`, `pendingMapValue`,
`pendingBlockContent`) are the next PR's; `pendingFlow` stays STARVED until Row 12 retires
`SLYamlStream.scannerDrop`.
-/

namespace L4YAML.Proofs.Serialization.TraceOf.StreamBridge

public section

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.Serialization.EventsOf (declaredHandle)
open L4YAML.Proofs.StreamAccum (scannedDirective_toSL white_prepend_SSLComments)
open L4YAML.Proofs.PreprocessProduction (SSLComments_to_GStar)
open L4YAML.Proofs.SurfaceSpan (sslComments_suffix)
open L4YAML.Proofs.StructureProduction L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.StreamAccum (ContentArm dispatchContent_blockScalar_prod)
open L4YAML.Proofs.NodeProduction (SCDoubleQuoted_ctx_lift SCSingleQuoted_ctx_lift)
open L4YAML.Proofs.Serialization.TraceOf.ContentBridge (accum_step_content_trace_out)

/-- `[79]` at a line start extends the closed stream without an event (the twin of
`ssl_comments_extend_stream`): the comments are `[202]` prefixes. -/
lemma TLYamlStream.extendComments {s s₁ s' : SurfPos} {e : List Event}
    (h : TLYamlStream s s₁ e) (hcol : s₁.col = 0) (hc : SSLComments s₁ s') :
    TLYamlStream s s' e := by
  simpa using TLYamlStream.implicitContinue s s₁ s' s' s' e [] [] h
    (GStar.cons s₁ s' s' (SLDocumentPrefix.comments s₁ s' (SSLComments_to_GStar s₁ s' hc hcol))
      (GStar.nil _))
    (TOpt.none _) (TStar.nil _)

/-- `[96]` read at `.flowOut` re-reads at `.blockIn` (the twin of `props_linesLift`): the embedded
`s-separate` is `s-separate-lines` in both. -/
lemma TCNsProperties.blockIn_of_flowOut {n : Nat} {s s' : SurfPos} {ev : List Event}
    (h : TCNsProperties n .flowOut s s' ev) : TCNsProperties n .blockIn s s' ev := by
  cases h with
  | tagFirst _ s₁ _ e₁ e₂ ht ho =>
    refine .tagFirst _ s₁ _ e₁ e₂ ht ?_
    cases ho with
    | none => exact .none _
    | some _ _ _ hs =>
      obtain ⟨_, sm, _, ea, eb, hsep, ha⟩ := hs
      exact .some _ _ _ (.mk _ sm _ ea eb hsep ha)
  | anchorFirst _ s₁ _ e₁ e₂ ha ho =>
    refine .anchorFirst _ s₁ _ e₁ e₂ ha ?_
    cases ho with
    | none => exact .none _
    | some _ _ _ hs =>
      obtain ⟨_, sm, _, ea, eb, hsep, ht⟩ := hs
      exact .some _ _ _ (.mk _ sm _ ea eb hsep ht)

/-- The suffix route (the twin of `suffixNodeRoute`): after `...` and its `[79]`, a completed node
is the bare document in `suffixContinue`'s own slot. -/
lemma TLYamlStream.suffixRoute {s s₁ s₂ s₃ : SurfPos} {e : List Event}
    (h : TLYamlStream s s₁ e) (hm : SCDocumentEnd s₁ s₂) (hc : SSLComments s₂ s₃) :
    ∀ sp_m ev_n, TBlockNode 0 .blockIn s₃ sp_m ev_n →
      TLYamlStream s sp_m (e ++ .endDocument :: ev_n) :=
  fun sp_m ev_n hb => by
    simpa using TLYamlStream.suffixContinue s s₁ s₃ s₃ sp_m sp_m e [.endDocument] ev_n [] h
      (TPlus.mk _ _ _ _ [] (TLDocumentSuffix.mk s₁ s₂ s₃ hm hc) (TStar.nil _))
      (GStar.nil _)
      (TOpt.some _ _ _ (TLAnyDocument.bare _ _ _ (TLBareDocument.mk _ _ _ hb))) (TStar.nil _)

/-- `[96]` read at `.blockIn` re-reads at `.blockOut` (the twin of `SCNsProperties_blockIn_to_blockOut`). -/
lemma TCNsProperties.blockOut_of_blockIn {n : Nat} {s s' : SurfPos} {ev : List Event}
    (h : TCNsProperties n .blockIn s s' ev) : TCNsProperties n .blockOut s s' ev := by
  cases h with
  | tagFirst _ s₁ _ e₁ e₂ ht ho =>
    refine .tagFirst _ s₁ _ e₁ e₂ ht ?_
    cases ho with
    | none => exact .none _
    | some _ _ _ hs =>
      obtain ⟨_, sm, _, ea, eb, hsep, ha⟩ := hs
      exact .some _ _ _ (.mk _ sm _ ea eb hsep ha)
  | anchorFirst _ s₁ _ e₁ e₂ ha ho =>
    refine .anchorFirst _ s₁ _ e₁ e₂ ha ?_
    cases ho with
    | none => exact .none _
    | some _ _ _ hs =>
      obtain ⟨_, sm, _, ea, eb, hsep, ht⟩ := hs
      exact .some _ _ _ (.mk _ sm _ ea eb hsep ht)

/-- `[196]` read at `.blockIn` re-reads at `.blockOut` (the twin of `SBlockNode_blockIn_to_blockOut`): a
`:`'s value slot takes the node the `.blockIn` routes build; `[183]`'s `m` absorbs `seq-spaces`' offset. -/
lemma TBlockNode.blockOut_of_blockIn {n : Nat} {s s' : SurfPos} {ev : List Event}
    (h : TBlockNode n .blockIn s s' ev) : TBlockNode n .blockOut s s' ev := by
  have h_ps : ∀ {a b : SurfPos} {e : List Event},
      TOpt (TSeq (TCNsProperties n .blockIn) (Lift (SSeparate n .blockIn))) a b e →
      TOpt (TSeq (TCNsProperties n .blockOut) (Lift (SSeparate n .blockOut))) a b e := fun ho => by
    cases ho with
    | none => exact .none _
    | some _ _ _ hs =>
      obtain ⟨_, sm, _, ea, eb, hp, hsep⟩ := hs
      exact .some _ _ _ (.mk _ sm _ ea eb (TCNsProperties.blockOut_of_blockIn hp) hsep)
  have h_sp : ∀ {a b : SurfPos} {e : List Event},
      TOpt (TSeq (Lift (SSeparate n .blockIn)) (TCNsProperties n .blockIn)) a b e →
      TOpt (TSeq (Lift (SSeparate n .blockOut)) (TCNsProperties n .blockOut)) a b e := fun ho => by
    cases ho with
    | none => exact .none _
    | some _ _ _ hs =>
      obtain ⟨_, sm, _, ea, eb, hsep, hp⟩ := hs
      exact .some _ _ _ (.mk _ sm _ ea eb hsep (TCNsProperties.blockOut_of_blockIn hp))
  cases h with
  | blockLiteral _ _ _ s₁ s₂ _ _ h_sep h_props h_lit =>
    exact .blockLiteral n .blockOut s s₁ s₂ s' ev h_sep (h_ps h_props) h_lit
  | blockFolded _ _ _ s₁ s₂ _ _ h_sep h_props h_fld =>
    exact .blockFolded n .blockOut s s₁ s₂ s' ev h_sep (h_ps h_props) h_fld
  | blockSeq _ _ m _ s₁ s₂ _ ev1 ev2 h_props h_ssl h_entries =>
    refine .blockSeq n .blockOut (if n = 0 then m else m + 1) s s₁ s₂ s' ev1 ev2 (h_sp h_props) h_ssl ?_
    have heq : seqSpaces n .blockOut + (if n = 0 then m else m + 1) = seqSpaces n .blockIn + m := by
      cases n <;> simp [seqSpaces] <;> omega
    rw [heq]; exact h_entries
  | blockMap _ _ m _ s₁ s₂ _ ev1 ev2 h_props h_ssl h_entries =>
    exact .blockMap n .blockOut m s s₁ s₂ s' ev1 ev2 (h_sp h_props) h_ssl h_entries
  | flowInBlock _ _ _ s₁ s₂ _ _ h_sep h_flow h_ssl =>
    exact .flowInBlock n .blockOut s s₁ s₂ s' ev h_sep h_flow h_ssl
  | emptyNode _ _ _ _ h_ssl => exact .emptyNode n .blockOut s s' h_ssl

/-- The twin of `PendingNode` at the four stream-level parks.  Indices: the directive flag (S's
`b`), the closed stream's end `sp_block`, the scanner's `sp_scan`, the closed trace `ev_c`, the
open events `ev_o`, the pending handles `p` (newest first). -/
inductive TPendingNode (sp_start : SurfPos) :
    Bool → SurfPos → SurfPos → List Event → List Event → List String → Prop where
  /-- Nothing open, at a block-context line start: no event, no handle. -/
  | noPending (sp : SurfPos) (ev_c : List Event) (h_col : sp.col = 0) :
      TPendingNode sp_start false sp sp ev_c [] []
  /-- `...` scanned: `endDocument` is open, awaiting `[79]`. -/
  | pendingDocEnd (sp_block sp_scan : SurfPos) (ev_c : List Event) (p : List String)
      (h_marker : SCDocumentEnd sp_block sp_scan) :
      TPendingNode sp_start false sp_block sp_scan ev_c [.endDocument] p
  /-- A directive run since `sp_block`: no event yet; closed by `[79]` it is `[82]+` with the
  pending handles' declarations in textual order (`p` is newest first). -/
  | pendingDirective (sp_block sp_scan : SurfPos) (ev_c : List Event) (p : List String)
      (h_dir_acc : ∀ sp_mid, SSLComments sp_scan sp_mid →
        TPlus TLDirective sp_block sp_mid (p.reverse.map .declareTag)) :
      TPendingNode sp_start true sp_block sp_scan ev_c [] p
  /-- `---` scanned: `beginDocument` and the declarations are open; the body closes the
  document into the stream (the twin of `h_doc_route`, a route not a document). -/
  | pendingDocStart (sp_block sp_scan : SurfPos) (ev_c ed : List Event)
      (h_doc_route : ∀ sp_end eb, TLExplicitBody sp_scan sp_end eb →
        TLYamlStream sp_start sp_end (ev_c ++ .beginDocument :: ed ++ eb)) :
      TPendingNode sp_start false sp_block sp_scan ev_c (.beginDocument :: ed) []
  /-- A content node parked (the twin of `pendingContent.h_closable`, item 528): `ev_o` is the open
  document's events so far, the node's own included; `[79]` from `sp_gram` closes it into the stream. -/
  | pendingContent (sp_block sp_scan sp_gram : SurfPos) (ev_c ev_o : List Event)
      (h_closable : ∀ sp_mid, SSLComments sp_gram sp_mid →
        TLYamlStream sp_start sp_mid (ev_c ++ ev_o))
      (h_run : GStar SSWhite sp_gram sp_scan) :
      TPendingNode sp_start false sp_block sp_scan ev_c ev_o []
  /-- A property run parked before its node (the twin of `pendingProps.h_route`): the run's events
  `ev_p` are already in the open trace; the node they decorate carries them. -/
  | pendingProps (sp_block sp_scan sp_node sp_p : SurfPos) (n : Nat) (ev_c ev_o ev_p : List Event)
      (h_sep : SSeparate n .flowOut sp_node sp_p)
      (h_props : TCNsProperties n .flowOut sp_p sp_scan ev_p)
      (h_route : ∀ sp_m ev_n, TBlockNode n .blockIn sp_node sp_m ev_n →
        TLYamlStream sp_start sp_m (ev_c ++ ev_o ++ ev_n)) :
      TPendingNode sp_start false sp_block sp_scan ev_c (ev_o ++ ev_p) []
  /-- A `-` parked (the twin of `pendingBlock.h_close`): the entry's node, indented, closes it. -/
  | pendingBlock (sp_block sp_scan : SurfPos) (n : Nat) (ev_c ev_o : List Event)
      (h_close : ∀ sp_mid ev_n, TBlockIndented n .blockIn sp_scan sp_mid ev_n →
        TLYamlStream sp_start sp_mid (ev_c ++ ev_o ++ ev_n)) :
      TPendingNode sp_start false sp_block sp_scan ev_c ev_o []
  /-- A `:` parked (the twin of `pendingMapValue.h_close`): the value node closes it. -/
  | pendingMapValue (sp_block sp_scan : SurfPos) (n : Nat) (ev_c ev_o : List Event)
      (h_close : ∀ sp_mid ev_n, TBlockNode (n + 1) .blockOut sp_scan sp_mid ev_n →
        TLYamlStream sp_start sp_mid (ev_c ++ ev_o ++ ev_n)) :
      TPendingNode sp_start false sp_block sp_scan ev_c ev_o []
  /-- Content inside a compact entry (the twin of `pendingBlockContent.h_closable`). -/
  | pendingBlockContent (sp_block sp_scan sp_gram : SurfPos) (n : Nat) (ev_c ev_o : List Event)
      (h_closable : ∀ sp_mid, SSLComments sp_gram sp_mid →
        TLYamlStream sp_start sp_mid (ev_c ++ ev_o))
      (h_closable_entry : ∀ sp_mid, SSLComments sp_gram sp_mid →
        ∀ sp_end ev_n, TCompactSeqTail n sp_mid sp_end ev_n →
          TLYamlStream sp_start sp_end (ev_c ++ ev_o ++ ev_n))
      (h_run : GStar SSWhite sp_gram sp_scan) :
      TPendingNode sp_start false sp_block sp_scan ev_c ev_o []

namespace TPendingNode

/-- The close (the twin of `PendingNode.close_with_ssl` at these parks): `[79]` from the park
closes the open events into the stream.  A directive run (`true`) does not close this way. -/
lemma close_with_ssl {sp_start sp_block sp_scan sp_mid : SurfPos} {sc : ScannerState}
    {ev_c ev_o : List Event} {p : List String}
    (hS : TSLYamlStream sp_start sc sp_block ev_c ev_o p)
    (hP : TPendingNode sp_start false sp_block sp_scan ev_c ev_o p)
    (h_ssl : SSLComments sp_scan sp_mid) :
    TLYamlStream sp_start sp_mid (ev_c ++ ev_o) := by
  cases hP with
  | noPending _ _ h_col => simpa using TLYamlStream.extendComments hS.stream h_col h_ssl
  | pendingDocEnd _ _ _ _ h_marker => exact TLYamlStream.closeSuffix hS.stream h_marker h_ssl
  | pendingDocStart _ _ _ ed h_route =>
    simpa using h_route sp_mid [] (TAlt.right _ _ _ (TSeq.mk _ _ _ [] [] ⟨GEps.mk _, rfl⟩ ⟨h_ssl, rfl⟩))
  | pendingContent _ _ _ _ _ h_closable h_run =>
    exact h_closable sp_mid (white_prepend_SSLComments h_run h_ssl)
  | pendingProps _ _ _ _ n _ _ ev_p h_sep h_props h_route =>
    simpa using h_route sp_mid ev_p
      (TBlockNode.flowInBlock n .blockIn _ _ _ _ ev_p h_sep (TFlowNode.propsEmpty n .flowOut _ _ ev_p h_props) h_ssl)
  | pendingBlock _ _ n _ _ h_close =>
    simpa using h_close sp_mid [] (TBlockIndented.empty n .blockIn _ _ h_ssl)
  | pendingMapValue _ _ n _ _ h_close =>
    simpa using h_close sp_mid [] (TBlockNode.emptyNode (n + 1) .blockOut _ _ h_ssl)
  | pendingBlockContent _ _ _ _ _ _ h_closable _ h_run =>
    exact h_closable sp_mid (white_prepend_SSLComments h_run h_ssl)

/-- At the stream's end with nothing pending: the tokens' events ARE the stream's trace. -/
lemma total {sp_start sp_block sp_scan sp_mid : SurfPos} {sc : ScannerState}
    {ev_c ev_o : List Event}
    (hS : TSLYamlStream sp_start sc sp_block ev_c ev_o [])
    (hP : TPendingNode sp_start false sp_block sp_scan ev_c ev_o [])
    (h_ssl : SSLComments sp_scan sp_mid) :
    TLYamlStream sp_start sp_mid (tokenEvents sc.tokens) := by
  rw [hS.total]; exact close_with_ssl hS hP h_ssl

/-- `Option.toList` is its own reverse. -/
lemma option_toList_reverse {α : Type} (o : Option α) : o.toList.reverse = o.toList := by
  cases o <;> rfl

/-- **`%`** at a line-start park (the twin of `accum_structural_pending`'s directive arm from
`noPending`): the run opens at the landing `sp_prep`, the stream is extended over the landing, the
handle (if named) is pending, no event.  Stated at the preprocessed state `s_prep`. -/
lemma directive_step_noPending {sp_start sp sp_prep : SurfPos} {s_prep s' : ScannerState}
    {ev_c : List Event}
    (hS : TSLYamlStream sp_start s_prep sp ev_c [] []) (h_col : sp.col = 0)
    (h_pre : SSLComments sp sp_prep)
    (hcorr : ScannerSurfCorr s_prep sp_prep) (hpeek : s_prep.peek? = some '%')
    (hok : scanDirective s_prep = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' ∧
      TSLYamlStream sp_start s' sp_prep ev_c [] (declaredHandle (span sp_prep sp')).toList ∧
      TPendingNode sp_start true sp_prep sp' ev_c [] (declaredHandle (span sp_prep sp')).toList := by
  obtain ⟨sp', hsd, hcorr', hbrk, new, htoks, hgo, hstable⟩ :=
    scanDirective_trace s_prep sp_prep hcorr hpeek s' hok
  have hS' : TSLYamlStream sp_start s' sp ev_c [] (declaredHandle (span sp_prep sp')).toList := by
    simpa using hS.push htoks (hgo [])
  refine ⟨sp', hcorr', ⟨TLYamlStream.extendComments hS'.stream h_col h_pre, hS'.events⟩, ?_⟩
  refine TPendingNode.pendingDirective _ _ _ _ fun sp_mid hssl => ?_
  have := hstable sp_mid (List.IsSuffix.length_le (sslComments_suffix hssl))
  simpa [option_toList_reverse] using TPlus.mk _ _ _ _ [] (⟨scannedDirective_toSL hsd hbrk hssl, by rw [this]⟩ :
    TLDirective sp_prep sp_mid ((declaredHandle (span sp_prep sp')).toList.map .declareTag)) (TStar.nil _)

/-- **`%`** inside a run: the run grows at its end, the handle (if named) joins the pending list. -/
lemma directive_step_run {sp_start sp_block sp_scan sp_prep : SurfPos} {s_prep s' : ScannerState}
    {ev_c : List Event} {p : List String}
    (hS : TSLYamlStream sp_start s_prep sp_block ev_c [] p)
    (h_acc : ∀ sp_mid, SSLComments sp_scan sp_mid →
      TPlus TLDirective sp_block sp_mid (p.reverse.map .declareTag))
    (h_pre : SSLComments sp_scan sp_prep)
    (hcorr : ScannerSurfCorr s_prep sp_prep) (hpeek : s_prep.peek? = some '%')
    (hok : scanDirective s_prep = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' ∧
      TSLYamlStream sp_start s' sp_block ev_c [] ((declaredHandle (span sp_prep sp')).toList ++ p) ∧
      TPendingNode sp_start true sp_block sp' ev_c [] ((declaredHandle (span sp_prep sp')).toList ++ p) := by
  obtain ⟨sp', hsd, hcorr', hbrk, new, htoks, hgo, hstable⟩ :=
    scanDirective_trace s_prep sp_prep hcorr hpeek s' hok
  refine ⟨sp', hcorr', by simpa using hS.push htoks (hgo p), ?_⟩
  refine TPendingNode.pendingDirective _ _ _ _ fun sp_mid hssl => ?_
  have := hstable sp_mid (List.IsSuffix.length_le (sslComments_suffix hssl))
  simpa [option_toList_reverse, List.reverse_append] using
    TPlus_TLDirective_snoc (h_acc sp_prep h_pre) (⟨scannedDirective_toSL hsd hbrk hssl, by rw [this]⟩ :
      TLDirective sp_prep sp_mid ((declaredHandle (span sp_prep sp')).toList.map .declareTag))

/-- The park's `[79]` landing as `[202]` prefixes. -/
lemma SSLComments_to_GStar_prefix {sp sp' : SurfPos} (h_col : sp.col = 0) (h : SSLComments sp sp') :
    GStar SLDocumentPrefix sp sp' :=
  GStar.cons sp sp' sp' (SLDocumentPrefix.comments sp sp' (SSLComments_to_GStar sp sp' h h_col))
    (GStar.nil _)

/-- **`---`** at a line-start park: `[beginDocument]` opens, the route is `explicitRoute`. -/
lemma docStart_step_noPending {sp_start sp sp_prep : SurfPos} {s_prep : ScannerState} {ev_c : List Event}
    (hS : TSLYamlStream sp_start s_prep sp ev_c [] []) (h_col : sp.col = 0)
    (h_pre : SSLComments sp sp_prep)
    (hcorr : ScannerSurfCorr s_prep sp_prep)
    (rest : List Char) (hchars : sp_prep.chars = '-' :: '-' :: '-' :: rest) (hcol : sp_prep.col = 0) :
    ∃ sp', ScannerSurfCorr (scanDocumentStart s_prep) sp' ∧
      TSLYamlStream sp_start (scanDocumentStart s_prep) sp ev_c [.beginDocument] [] ∧
      TPendingNode sp_start false sp sp' ev_c [.beginDocument] [] := by
  obtain ⟨sp', hde, hcorr', hS'⟩ := hS.docStart sp_prep hcorr rest hchars hcol
  refine ⟨sp', hcorr', by simpa using hS', ?_⟩
  exact TPendingNode.pendingDocStart _ _ _ [] fun sp_end eb hb => by
    simpa using TLYamlStream.explicitRoute hS.stream (SSLComments_to_GStar_prefix h_col h_pre) hde hb

/-- **`---`** after a run: the handles flush after `beginDocument` in directive order, the route is
`directiveRoute` on the run. -/
lemma docStart_step_run {sp_start sp_block sp_scan sp_prep : SurfPos} {s_prep : ScannerState}
    {ev_c : List Event} {p : List String}
    (hS : TSLYamlStream sp_start s_prep sp_block ev_c [] p)
    (h_acc : ∀ sp_mid, SSLComments sp_scan sp_mid →
      TPlus TLDirective sp_block sp_mid (p.reverse.map .declareTag))
    (h_pre : SSLComments sp_scan sp_prep)
    (hcorr : ScannerSurfCorr s_prep sp_prep)
    (rest : List Char) (hchars : sp_prep.chars = '-' :: '-' :: '-' :: rest) (hcol : sp_prep.col = 0) :
    ∃ sp', ScannerSurfCorr (scanDocumentStart s_prep) sp' ∧
      TSLYamlStream sp_start (scanDocumentStart s_prep) sp_block ev_c
        (.beginDocument :: p.reverse.map .declareTag) [] ∧
      TPendingNode sp_start false sp_block sp' ev_c (.beginDocument :: p.reverse.map .declareTag) [] := by
  obtain ⟨sp', hde, hcorr', hS'⟩ := hS.docStart sp_prep hcorr rest hchars hcol
  refine ⟨sp', hcorr', by simpa using hS', ?_⟩
  exact TPendingNode.pendingDocStart _ _ _ _ fun sp_end eb hb => by
    simpa using TLYamlStream.directiveRoute hS.stream (GStar.nil _) (h_acc sp_prep h_pre) hde hb

/-- **`...`** at a line-start park: `endDocument` opens, awaiting `[79]`; the closed stream is
extended over the park's landing first. -/
lemma docEnd_step {sp_start sp sp_prep : SurfPos} {s_prep s' : ScannerState} {ev_c : List Event}
    (hS : TSLYamlStream sp_start s_prep sp ev_c [] []) (h_col : sp.col = 0)
    (h_pre : SSLComments sp sp_prep)
    (hcorr : ScannerSurfCorr s_prep sp_prep)
    (rest : List Char) (hchars : sp_prep.chars = '.' :: '.' :: '.' :: rest) (hcol : sp_prep.col = 0)
    (hok : scanDocumentEnd s_prep = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' ∧
      TSLYamlStream sp_start s' sp_prep ev_c [.endDocument] [] ∧
      TPendingNode sp_start false sp_prep sp' ev_c [.endDocument] [] := by
  obtain ⟨sp', hm, hcorr', hS'⟩ := hS.docEnd sp_prep hcorr rest hchars hcol s' hok
  exact ⟨sp', hcorr', ⟨TLYamlStream.extendComments hS'.stream h_col h_pre, by simpa using hS'.events⟩,
    TPendingNode.pendingDocEnd _ _ _ _ hm⟩

/-- A quoted scalar's content at `.flowOut`, read off the arm (the leaf's `.blockIn` reading does not
lift wholesale). -/
lemma quoted_flowOut {s_prep s' : ScannerState} {c : Char} {sp_prep sp_a : SurfPos}
    (arm : ContentArm s_prep s' c sp_prep sp_a) (hc : c = '"' ∨ c = '\'')
    (h_depth : s_prep.flowLevel = 0) : TFlowContent 0 .flowOut sp_prep sp_a [] := by
  cases arm with
  | doubleQuoted _ _ hq _ _ =>
    exact .doubleQ _ _ _ _ (SCDoubleQuoted_ctx_lift hq (by decide) (by decide))
  | singleQuoted _ _ hq _ _ =>
    exact .singleQ _ _ _ _ (SCSingleQuoted_ctx_lift hq (by decide) (by decide))
  | plainIn _ _ hd _ _ => omega
  | plain _ _ h_c _ _ _ _ _ => rcases hc with h | h <;> simp_all
  | blockScalar _ h_c _ _ => rcases hc with h | h <;> rcases h_c with h' | h' <;> simp_all
  | anchor _ h_c _ _ _ => rcases hc with h | h <;> simp_all
  | tag _ h_c _ _ _ => rcases hc with h | h <;> simp_all
  | alias _ h_c _ _ => rcases hc with h | h <;> simp_all

/-- **The content step, routed** (items 529 / 531, the twin of `content_dispatch_routed`): the node
anchors at `sp_node` beside the open events `ev_o`, and parks as `pendingContent` (a scalar, an alias)
or `pendingProps` (`&` / `!`); `h_route` is how a completed node at the anchor re-enters the stream. -/
lemma content_step_routed {sp_start sp_block sp_node sp_prep sp_a : SurfPos} {s_prep s' : ScannerState}
    {c : Char} {ev_c ev_o : List Event}
    (hS : TSLYamlStream sp_start s_prep sp_block ev_c ev_o [])
    (h_sep : SSeparateLines 0 sp_node sp_prep)
    (arm : ContentArm s_prep s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_prep sp_prep) (hcorr' : ScannerSurfCorr s' sp_a)
    (hpeek : s_prep.peek? = some c)
    (h_depth : s_prep.flowLevel = 0)
    (h_dispatch : scanNextToken_dispatchContent s_prep c = .ok s')
    (h_route : ∀ sp_m ev_n, TBlockNode 0 .blockIn sp_node sp_m ev_n →
      TLYamlStream sp_start sp_m (ev_c ++ ev_o ++ ev_n)) :
    ∃ ev_n, TSLYamlStream sp_start s' sp_block ev_c (ev_o ++ ev_n) [] ∧
      TPendingNode sp_start false sp_block sp_a ev_c (ev_o ++ ev_n) [] := by
  obtain ⟨ev_n, hpt, hdisj⟩ := accum_step_content_trace_out arm hcorr hpeek h_depth h_dispatch
  refine ⟨ev_n, ⟨hS.stream, by rw [hpt.goOut_at [], hS.events]; simp⟩, ?_⟩
  rcases hdisj with ⟨hev, sp_gram, hT, hws, -, -⟩ | ⟨hev, hc, -⟩ | ⟨hev, hc, -⟩ | ⟨-, ha, -⟩ | ⟨-, ht, -⟩ | ⟨-, hal⟩
  · subst hev
    exact .pendingContent sp_block sp_a sp_gram ev_c (ev_o ++ [])
      (fun sp_mid h_ssl => by
        simpa using h_route sp_mid []
          (.flowInBlock 0 .blockIn sp_node sp_prep sp_gram sp_mid [] h_sep (.content _ _ _ _ _ hT) h_ssl))
      hws
  · subst hev
    exact .pendingContent sp_block sp_a sp_a ev_c (ev_o ++ [])
      (fun sp_mid h_ssl => by
        simpa using h_route sp_mid []
          (.flowInBlock 0 .blockIn sp_node sp_prep sp_a sp_mid [] h_sep
            (.content _ _ _ _ _ (quoted_flowOut arm hc h_depth)) h_ssl))
      (GStar.nil _)
  · subst hev
    obtain ⟨sp_bs, -, hcorr_bs, h_absorb⟩ := dispatchContent_blockScalar_prod s_prep sp_prep hcorr hpeek hc h_dispatch
    have heq := ScannerSurfCorr_unique hcorr_bs hcorr'
    rw [heq] at h_absorb
    exact .pendingContent sp_block sp_a sp_a ev_c (ev_o ++ [])
      (fun sp_mid h_ssl => by
        simpa using h_route sp_mid [] ((h_absorb sp_mid h_ssl).elim
          (fun hl => .blockLiteral 0 .blockIn sp_node sp_prep sp_prep sp_mid [] h_sep (TOpt.none _) hl)
          (fun hf => .blockFolded 0 .blockIn sp_node sp_prep sp_prep sp_mid [] h_sep (TOpt.none _) hf)))
      (GStar.nil _)
  · exact .pendingProps sp_block sp_a sp_node sp_prep 0 ev_c ev_o ev_n h_sep
      (by simpa using TCNsProperties.anchorFirst sp_prep sp_a sp_a ev_n [] ha (TOpt.none _))
      h_route
  · exact .pendingProps sp_block sp_a sp_node sp_prep 0 ev_c ev_o ev_n h_sep
      (by simpa using TCNsProperties.tagFirst sp_prep sp_a sp_a ev_n [] ht (TOpt.none _))
      h_route
  · exact .pendingContent sp_block sp_a sp_a ev_c (ev_o ++ ev_n)
      (fun sp_mid h_ssl => by
        simpa [List.append_assoc] using h_route sp_mid ev_n
          (.flowInBlock 0 .blockIn sp_node sp_prep sp_a sp_mid ev_n h_sep (.alias 0 .flowOut sp_prep sp_a ev_n hal) h_ssl))
      (GStar.nil _)

/-- **The content step at a line-start park** (item 529, the twin of `content_dispatch_routed`'s two
sites): `content_step_routed` from `noPending` at `sp` — nothing open, the node anchors at the park;
`h_route` is `TLYamlStream.bareRoute` at the first document. -/
lemma content_step_noPending {sp_start sp sp_prep sp_a : SurfPos} {s_prep s' : ScannerState} {c : Char}
    {ev_c : List Event}
    (hS : TSLYamlStream sp_start s_prep sp ev_c [] [])
    (h_sep : SSeparateLines 0 sp sp_prep)
    (arm : ContentArm s_prep s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_prep sp_prep) (hcorr' : ScannerSurfCorr s' sp_a)
    (hpeek : s_prep.peek? = some c)
    (h_depth : s_prep.flowLevel = 0)
    (h_dispatch : scanNextToken_dispatchContent s_prep c = .ok s')
    (h_route : ∀ sp_m ev_n, TBlockNode 0 .blockIn sp sp_m ev_n →
      TLYamlStream sp_start sp_m (ev_c ++ ev_n)) :
    ∃ ev_n, TSLYamlStream sp_start s' sp ev_c ev_n [] ∧
      TPendingNode sp_start false sp sp_a ev_c ev_n [] := by
  simpa using content_step_routed hS h_sep arm hcorr hcorr' hpeek h_depth h_dispatch
    (fun sp_m ev h => by simpa using h_route sp_m ev h)

/-- **The content step behind `---`** (item 531, the twin of `accum_content_pending`'s `pendingDocStart`
arm): the node anchors just after the marker — on its line or across `h_sep`'s comment lines — and
re-enters through `h_doc_route`'s bare-document branch, inside the one explicit document. -/
lemma content_step_docStart {sp_start sp_block sp_scan sp_prep sp_a : SurfPos} {s_prep s' : ScannerState}
    {c : Char} {ev_c ed : List Event}
    (hS : TSLYamlStream sp_start s_prep sp_block ev_c (.beginDocument :: ed) [])
    (h_doc_route : ∀ sp_end eb, TLExplicitBody sp_scan sp_end eb →
      TLYamlStream sp_start sp_end (ev_c ++ .beginDocument :: ed ++ eb))
    (h_sep : SSeparateLines 0 sp_scan sp_prep)
    (arm : ContentArm s_prep s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_prep sp_prep) (hcorr' : ScannerSurfCorr s' sp_a)
    (hpeek : s_prep.peek? = some c)
    (h_depth : s_prep.flowLevel = 0)
    (h_dispatch : scanNextToken_dispatchContent s_prep c = .ok s') :
    ∃ ev_n, TSLYamlStream sp_start s' sp_block ev_c (.beginDocument :: ed ++ ev_n) [] ∧
      TPendingNode sp_start false sp_block sp_a ev_c (.beginDocument :: ed ++ ev_n) [] := by
  simpa using content_step_routed hS h_sep arm hcorr hcorr' hpeek h_depth h_dispatch
    (fun sp_m ev h => by
      simpa using h_doc_route sp_m ev (TAlt.left _ _ _ (TLBareDocument.mk _ _ _ h)))

/-- **The content step behind `...`** (item 531, the twin of `accum_content_pending`'s `pendingDocEnd`
arm): the marker's line ends in `[79]`, so the node anchors at the landing `sp_mid` and re-enters
through `TLYamlStream.suffixRoute` — `suffixContinue`'s own document slot. -/
lemma content_step_docEnd {sp_start sp_block sp_scan sp_mid sp_prep sp_a : SurfPos}
    {s_prep s' : ScannerState} {c : Char} {ev_c : List Event}
    (hS : TSLYamlStream sp_start s_prep sp_block ev_c [.endDocument] [])
    (h_marker : SCDocumentEnd sp_block sp_scan) (h_ssl : SSLComments sp_scan sp_mid)
    (h_sep : SSeparateLines 0 sp_mid sp_prep)
    (arm : ContentArm s_prep s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_prep sp_prep) (hcorr' : ScannerSurfCorr s' sp_a)
    (hpeek : s_prep.peek? = some c)
    (h_depth : s_prep.flowLevel = 0)
    (h_dispatch : scanNextToken_dispatchContent s_prep c = .ok s') :
    ∃ ev_n, TSLYamlStream sp_start s' sp_block ev_c (.endDocument :: ev_n) [] ∧
      TPendingNode sp_start false sp_block sp_a ev_c (.endDocument :: ev_n) [] := by
  simpa using content_step_routed hS h_sep arm hcorr hcorr' hpeek h_depth h_dispatch
    (fun sp_m ev h => by simpa using TLYamlStream.suffixRoute hS.stream h_marker h_ssl sp_m ev h)

/-- **The value behind a property run** (items 531 / 532, the twin of `accum_content_pending`'s five
content sites in its `pendingProps` arm): a scalar is silent and the run DECORATES it at the run's own
indentation `n` — `[161]`'s `propsContent` over `content_leaf_at`, or `[198]`'s props slot for a block
scalar — so the open events are unchanged and the park's own route takes the decorated node.
`h_floor` is the park's `IndentFloor`, read at the preprocessed state. -/
lemma content_step_props {n : Nat} {sp_start sp_block sp_scan sp_node sp_p sp_prep sp_a : SurfPos}
    {s_prep s' : ScannerState} {c : Char} {ev_c ev_o ev_p : List Event}
    (hS : TSLYamlStream sp_start s_prep sp_block ev_c (ev_o ++ ev_p) [])
    (h_sepP : SSeparate n .flowOut sp_node sp_p)
    (h_props : TCNsProperties n .flowOut sp_p sp_scan ev_p)
    (h_route : ∀ sp_m ev_n, TBlockNode n .blockIn sp_node sp_m ev_n →
      TLYamlStream sp_start sp_m (ev_c ++ ev_o ++ ev_n))
    (h_sep : SSeparate n .flowOut sp_scan sp_prep)
    (arm : ContentArm s_prep s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_prep sp_prep) (hcorr' : ScannerSurfCorr s' sp_a)
    (hpeek : s_prep.peek? = some c)
    (h_depth : s_prep.flowLevel = 0)
    (h_dispatch : scanNextToken_dispatchContent s_prep c = .ok s')
    (h_not_doc : s_prep.col = 0 → atDocumentBoundary s_prep = false)
    (h_floor : n ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf s_prep)
    (h_value : c ≠ '&' ∧ c ≠ '!' ∧ c ≠ '*') :
    TSLYamlStream sp_start s' sp_block ev_c (ev_o ++ ev_p) [] ∧
      TPendingNode sp_start false sp_block sp_a ev_c (ev_o ++ ev_p) [] := by
  obtain ⟨ev_n, hpt, hdisj⟩ := accum_step_content_trace_out arm hcorr hpeek h_depth h_dispatch
  have hev : ev_n = [] := by
    rcases hdisj with ⟨hev, -⟩ | ⟨hev, -⟩ | ⟨hev, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
    · exact hev
    · exact hev
    · exact hev
    · exact absurd hc h_value.1
    · exact absurd hc h_value.2.1
    · exact absurd hc h_value.2.2
  subst hev
  refine ⟨⟨hS.stream, by rw [hpt.goOut_at [], hS.events]; simp⟩, ?_⟩
  by_cases hbs : c = '|' ∨ c = '>'
  · obtain ⟨sp_bs, d, h_fl, -, hcorr_bs, h_absorb⟩ :=
      L4YAML.Proofs.StreamAccum.dispatchContent_blockScalar_prod_at s_prep sp_prep hcorr hpeek hbs h_dispatch
    have heq := ScannerSurfCorr_unique hcorr_bs hcorr'
    rw [heq] at h_absorb
    have hn : n ≤ d := by
      unfold L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf at h_floor
      exact Nat.le_trans h_floor h_fl
    have h_slot : TOpt (TSeq (TCNsProperties n .blockIn) (Lift (SSeparate n .blockIn))) sp_p sp_prep (ev_p ++ []) :=
      TOpt.some _ _ _ (TSeq.mk sp_p sp_scan sp_prep ev_p [] (TCNsProperties.blockIn_of_flowOut h_props) ⟨h_sep, rfl⟩)
    exact .pendingContent sp_block sp_a sp_a ev_c (ev_o ++ ev_p)
      (fun sp_mid h_ssl => by
        simpa [List.append_assoc] using h_route sp_mid (ev_p ++ []) ((h_absorb sp_mid h_ssl).elim
          (fun hl => .blockLiteral n .blockIn sp_node sp_p sp_prep sp_mid (ev_p ++ []) h_sepP h_slot (hl n hn))
          (fun hf => .blockFolded n .blockIn sp_node sp_p sp_prep sp_mid (ev_p ++ []) h_sepP h_slot (hf n hn))))
      (GStar.nil _)
  · obtain ⟨sp_gram, sp_res, hT, hws, hcorr_res⟩ :=
      L4YAML.Proofs.Serialization.TraceOf.ContentBridge.content_leaf_at n hcorr hpeek
        (by unfold ScannerState.inFlow; rw [h_depth]; rfl) h_not_doc
        h_value.1 h_value.2.2 h_value.2.1 (fun h => hbs (Or.inl h)) (fun h => hbs (Or.inr h))
        h_dispatch h_floor
    obtain rfl : sp_res = sp_a := ScannerSurfCorr_unique hcorr_res hcorr'
    exact .pendingContent sp_block sp_res sp_gram ev_c (ev_o ++ ev_p)
      (fun sp_mid h_ssl => by
        simpa [List.append_assoc] using h_route sp_mid (ev_p ++ [])
          (.flowInBlock n .blockIn sp_node sp_p sp_gram sp_mid (ev_p ++ []) h_sepP
            (.propsContent n .flowOut sp_p sp_scan sp_prep sp_gram ev_p [] h_props h_sep hT) h_ssl))
      hws

/-- **The content step at indentation `n`, routed** (item 534, the twin of
`indentedValue_reads_at_any_indent`'s readings): `content_step_routed` off a park whose node reads at
`n`, under the scanner's content floor.  A scalar or an alias parks as `pendingContent`, the leaf
re-read at `n` (`content_leaf_at`); `&` / `!` park as `pendingProps` at `n`. -/
lemma content_step_at {n : Nat} {sp_start sp_block sp_node sp_prep sp_a : SurfPos} {s_prep s' : ScannerState}
    {c : Char} {ev_c ev_o : List Event}
    (hS : TSLYamlStream sp_start s_prep sp_block ev_c ev_o [])
    (h_sep : SSeparate n .flowOut sp_node sp_prep)
    (h_route : ∀ sp_m ev_n, TBlockNode n .blockIn sp_node sp_m ev_n →
      TLYamlStream sp_start sp_m (ev_c ++ ev_o ++ ev_n))
    (arm : ContentArm s_prep s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_prep sp_prep) (hcorr' : ScannerSurfCorr s' sp_a)
    (hpeek : s_prep.peek? = some c)
    (h_depth : s_prep.flowLevel = 0)
    (h_dispatch : scanNextToken_dispatchContent s_prep c = .ok s')
    (h_not_doc : s_prep.col = 0 → atDocumentBoundary s_prep = false)
    (h_floor : n ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf s_prep) :
    ∃ ev_n, TSLYamlStream sp_start s' sp_block ev_c (ev_o ++ ev_n) [] ∧
      TPendingNode sp_start false sp_block sp_a ev_c (ev_o ++ ev_n) [] := by
  obtain ⟨ev_n, hpt, hdisj⟩ := accum_step_content_trace_out arm hcorr hpeek h_depth h_dispatch
  refine ⟨ev_n, ⟨hS.stream, by rw [hpt.goOut_at [], hS.events]; simp⟩, ?_⟩
  have h_scalar : ev_n = [] → (c ≠ '&' ∧ c ≠ '!' ∧ c ≠ '*') →
      TPendingNode sp_start false sp_block sp_a ev_c (ev_o ++ ev_n) [] := fun hev h_value => by
    subst hev
    by_cases hbs : c = '|' ∨ c = '>'
    · obtain ⟨sp_bs, d, h_fl, -, hcorr_bs, h_absorb⟩ :=
        L4YAML.Proofs.StreamAccum.dispatchContent_blockScalar_prod_at s_prep sp_prep hcorr hpeek hbs h_dispatch
      have heq := ScannerSurfCorr_unique hcorr_bs hcorr'
      rw [heq] at h_absorb
      have hn : n ≤ d := by
        unfold L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf at h_floor
        exact Nat.le_trans h_floor h_fl
      exact .pendingContent sp_block sp_a sp_a ev_c (ev_o ++ [])
        (fun sp_mid h_ssl => by
          simpa using h_route sp_mid [] ((h_absorb sp_mid h_ssl).elim
            (fun hl => .blockLiteral n .blockIn sp_node sp_prep sp_prep sp_mid [] h_sep (TOpt.none _) (hl n hn))
            (fun hf => .blockFolded n .blockIn sp_node sp_prep sp_prep sp_mid [] h_sep (TOpt.none _) (hf n hn))))
        (GStar.nil _)
    · obtain ⟨sp_gram, sp_res, hT, hws, hcorr_res⟩ :=
        L4YAML.Proofs.Serialization.TraceOf.ContentBridge.content_leaf_at n hcorr hpeek
          (by unfold ScannerState.inFlow; rw [h_depth]; rfl) h_not_doc
          h_value.1 h_value.2.2 h_value.2.1 (fun h => hbs (Or.inl h)) (fun h => hbs (Or.inr h))
          h_dispatch h_floor
      obtain rfl : sp_res = sp_a := ScannerSurfCorr_unique hcorr_res hcorr'
      exact .pendingContent sp_block sp_res sp_gram ev_c (ev_o ++ [])
        (fun sp_mid h_ssl => by
          simpa using h_route sp_mid []
            (.flowInBlock n .blockIn sp_node sp_prep sp_gram sp_mid [] h_sep (.content _ _ _ _ _ hT) h_ssl))
        hws
  rcases hdisj with ⟨hev, -, -, -, -, hv⟩ | ⟨hev, hc, -⟩ | ⟨hev, hc, -⟩ | ⟨-, ha, -⟩ | ⟨-, ht, -⟩ | ⟨-, hal⟩
  · exact h_scalar hev hv
  · exact h_scalar hev (by rcases hc with h | h <;> subst h <;> decide)
  · exact h_scalar hev (by rcases hc with h | h <;> subst h <;> decide)
  · exact .pendingProps sp_block sp_a sp_node sp_prep n ev_c ev_o ev_n h_sep
      (by simpa using TCNsProperties.anchorFirst sp_prep sp_a sp_a ev_n [] ha (TOpt.none _))
      h_route
  · exact .pendingProps sp_block sp_a sp_node sp_prep n ev_c ev_o ev_n h_sep
      (by simpa using TCNsProperties.tagFirst sp_prep sp_a sp_a ev_n [] ht (TOpt.none _))
      h_route
  · exact .pendingContent sp_block sp_a sp_a ev_c (ev_o ++ ev_n)
      (fun sp_mid h_ssl => by
        simpa [List.append_assoc] using h_route sp_mid ev_n
          (.flowInBlock n .blockIn sp_node sp_prep sp_a sp_mid ev_n h_sep (.alias n .flowOut sp_prep sp_a ev_n hal) h_ssl))
      (GStar.nil _)

/-- **The content step behind `-`** (item 534, the twin of `accum_content_on_pendingBlock_indented`'s
content sites): the entry's node reads at `n + 1` and closes the park through `[185]`'s node branch. -/
lemma content_step_block {n : Nat} {sp_start sp_block sp_scan sp_prep sp_a : SurfPos} {s_prep s' : ScannerState}
    {c : Char} {ev_c ev_o : List Event}
    (hS : TSLYamlStream sp_start s_prep sp_block ev_c ev_o [])
    (h_close : ∀ sp_mid ev_n, TBlockIndented n .blockIn sp_scan sp_mid ev_n →
      TLYamlStream sp_start sp_mid (ev_c ++ ev_o ++ ev_n))
    (h_sep : SSeparate (n + 1) .flowOut sp_scan sp_prep)
    (arm : ContentArm s_prep s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_prep sp_prep) (hcorr' : ScannerSurfCorr s' sp_a)
    (hpeek : s_prep.peek? = some c)
    (h_depth : s_prep.flowLevel = 0)
    (h_dispatch : scanNextToken_dispatchContent s_prep c = .ok s')
    (h_not_doc : s_prep.col = 0 → atDocumentBoundary s_prep = false)
    (h_floor : n + 1 ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf s_prep) :
    ∃ ev_n, TSLYamlStream sp_start s' sp_block ev_c (ev_o ++ ev_n) [] ∧
      TPendingNode sp_start false sp_block sp_a ev_c (ev_o ++ ev_n) [] :=
  content_step_at hS h_sep (fun sp_m ev h => h_close sp_m ev (.node n .blockIn _ _ _ h))
    arm hcorr hcorr' hpeek h_depth h_dispatch h_not_doc h_floor

/-- **The content step behind `:`** (item 534, the twin of `accum_content_on_pendingMapValue_indented`'s
content sites): the value reads at `n + 1` and fills `[189]`'s `.blockOut` slot re-labelled. -/
lemma content_step_mapValue {n : Nat} {sp_start sp_block sp_scan sp_prep sp_a : SurfPos}
    {s_prep s' : ScannerState} {c : Char} {ev_c ev_o : List Event}
    (hS : TSLYamlStream sp_start s_prep sp_block ev_c ev_o [])
    (h_close : ∀ sp_mid ev_n, TBlockNode (n + 1) .blockOut sp_scan sp_mid ev_n →
      TLYamlStream sp_start sp_mid (ev_c ++ ev_o ++ ev_n))
    (h_sep : SSeparate (n + 1) .flowOut sp_scan sp_prep)
    (arm : ContentArm s_prep s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_prep sp_prep) (hcorr' : ScannerSurfCorr s' sp_a)
    (hpeek : s_prep.peek? = some c)
    (h_depth : s_prep.flowLevel = 0)
    (h_dispatch : scanNextToken_dispatchContent s_prep c = .ok s')
    (h_not_doc : s_prep.col = 0 → atDocumentBoundary s_prep = false)
    (h_floor : n + 1 ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf s_prep) :
    ∃ ev_n, TSLYamlStream sp_start s' sp_block ev_c (ev_o ++ ev_n) [] ∧
      TPendingNode sp_start false sp_block sp_a ev_c (ev_o ++ ev_n) [] :=
  content_step_at hS h_sep (fun sp_m ev h => h_close sp_m ev (TBlockNode.blockOut_of_blockIn h))
    arm hcorr hcorr' hpeek h_depth h_dispatch h_not_doc h_floor


/-- **The separation a content step lands with, off preprocessing** (item 534, the fold's half of the
indicator parks): `indentedValue_reads_at_any_indent`'s five readings, folded to the two the trace side
spends — `s-separate(m)` from the park to the landing with the content floor at the dispatch state
(`preprocess_some_floor_at_landing`), or the DEDENT, where the value is not this park's. -/
lemma content_sep_of_preprocess {m : Nat} {sc s_prep s_ad s' : ScannerState} {c : Char}
    {sp_scan sp_prep sp_a : SurfPos}
    (h_ad : s_ad = if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true } else s_prep)
    (h_floor : L4YAML.Proofs.PreprocessIndentStable.IndentFloor sc m)
    (h_col : m ≤ sp_scan.col) (h_col0 : 0 < sp_scan.col)
    (h_next : L4YAML.Proofs.StreamAccum.NextIsSep sc)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep) (hcorr' : ScannerSurfCorr s' sp_a)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_not_doc : s_ad.col = 0 → atDocumentBoundary s_ad = false)
    (h_flow : s_ad.inFlow = false)
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s')
    (h_src : L4YAML.Proofs.StreamAccum.SlotGateAt s_prep) :
    (SSeparate m .flowOut sp_scan sp_prep ∧
        m ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf s_ad) ∨
      L4YAML.Proofs.FlowIndexLift.DedentLanding m sp_scan sp_prep := by
  subst h_ad
  have h_fl : ∀ {cc : YamlContext}, SSeparate m cc sp_scan sp_prep →
      m ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true } else s_prep) := by
    intro cc h
    have h1 := L4YAML.Proofs.StreamAccum.preprocess_some_floor_at_landing h_preprocess h_floor.2
      (by rw [← hcorr_prep.col_eq]; exact L4YAML.Proofs.StreamAccum.separate_col_ge h h_col)
    rw [L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf_congr
      (t := s_prep) (by split <;> rfl)]
    exact h1
  rcases L4YAML.Proofs.StreamAccum.indentedValue_reads_at_any_indent (h_src := h_src) sc sp_scan m
      s_prep s' c sp_prep sp_a h_floor h_col0 h_next hcorr_prep hcorr' h_corr h_preprocess h_not_doc
      h_flow h_dispatch with
    ⟨_, h_sep, -⟩ | ⟨_, _, h_sep, -⟩ | ⟨-, -, h_sep, -⟩ | ⟨_, -, -, -, h_sep, -⟩ | h_ded
  · exact Or.inl ⟨h_sep, h_fl h_sep⟩
  · have h : SSeparate m .flowOut sp_scan sp_prep := by unfold SSeparate; exact h_sep
    exact Or.inl ⟨h, h_fl h⟩
  · have h : SSeparate m .flowOut sp_scan sp_prep := by unfold SSeparate at h_sep ⊢; exact h_sep
    exact Or.inl ⟨h, h_fl h⟩
  · exact Or.inl ⟨h_sep, h_fl h_sep⟩
  · exact Or.inr (h_ded h_floor)

/-- **The content step off an indicator park, one fold step** (item 534, the twin of
`accum_content_pending`'s `pendingBlock` / `pendingMapValue` arms): from the park's own state `sc` —
its floor at `n + 1`, its column, the separator behind it — preprocessing lands the content at
`s-separate(n + 1)` and the park's route takes the node (`content_step_block` behind `-`,
`content_step_mapValue` behind `:`); or the landing is the DEDENT and the park is not this step's. -/
lemma content_step_indicator {n : Nat} {sp_start sp_block sp_scan sp_prep sp_a : SurfPos}
    {sc s_prep s_ad s' : ScannerState} {c : Char} {ev_c ev_o : List Event}
    (hS : TSLYamlStream sp_start s_ad sp_block ev_c ev_o [])
    (h_close :
      (∀ sp_mid ev_n, TBlockIndented n .blockIn sp_scan sp_mid ev_n →
        TLYamlStream sp_start sp_mid (ev_c ++ ev_o ++ ev_n)) ∨
      (∀ sp_mid ev_n, TBlockNode (n + 1) .blockOut sp_scan sp_mid ev_n →
        TLYamlStream sp_start sp_mid (ev_c ++ ev_o ++ ev_n)))
    (h_ad : s_ad = if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true } else s_prep)
    (h_floor : L4YAML.Proofs.PreprocessIndentStable.IndentFloor sc (n + 1))
    (h_col : n + 1 ≤ sp_scan.col)
    (h_next : L4YAML.Proofs.StreamAccum.NextIsSep sc)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep) (hcorr' : ScannerSurfCorr s' sp_a)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (arm : ContentArm s_ad s' c sp_prep sp_a)
    (h_depth : s_ad.flowLevel = 0)
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s')
    (h_not_doc : s_ad.col = 0 → atDocumentBoundary s_ad = false)
    (h_src : L4YAML.Proofs.StreamAccum.SlotGateAt s_prep) :
    (∃ ev_n, TSLYamlStream sp_start s' sp_block ev_c (ev_o ++ ev_n) [] ∧
        TPendingNode sp_start false sp_block sp_a ev_c (ev_o ++ ev_n) []) ∨
      L4YAML.Proofs.FlowIndexLift.DedentLanding (n + 1) sp_scan sp_prep := by
  have hcorr_ad : ScannerSurfCorr s_ad sp_prep := by
    rw [h_ad]; exact L4YAML.Proofs.StreamAccum.corr_of_allowDirectives_update hcorr_prep
  have hpeek : s_ad.peek? = some c := by
    rw [h_ad]
    have := L4YAML.Proofs.StreamAccum.preprocess_some_peek h_preprocess
    split <;> exact this
  rcases content_sep_of_preprocess h_ad h_floor h_col (by omega) h_next h_corr hcorr_prep hcorr'
      h_preprocess h_not_doc (by unfold ScannerState.inFlow; rw [h_depth]; rfl) h_dispatch h_src with
    ⟨h_sep, h_fl⟩ | h_ded
  · refine Or.inl ?_
    rcases h_close with h_close | h_close
    · exact content_step_block hS h_close h_sep arm hcorr_ad hcorr' hpeek h_depth h_dispatch
        h_not_doc h_fl
    · exact content_step_mapValue hS h_close h_sep arm hcorr_ad hcorr' hpeek h_depth h_dispatch
        h_not_doc h_fl
  · exact Or.inr h_ded
end TPendingNode

/-- The bare-document route at the first document's line start: a completed `TBlockNode` at the park is
the stream's `[210]` body (the twin of `nodocNodeRoute`). -/
lemma TLYamlStream.bareRoute {sp_start sp : SurfPos}
    (h_nodoc : GStar SLDocumentPrefix sp_start sp) :
    ∀ sp_m ev_n, TBlockNode 0 .blockIn sp sp_m ev_n → TLYamlStream sp_start sp_m ev_n :=
  fun sp_m ev_n h_bn => by
    simpa using TLYamlStream.single sp_start sp sp_m sp_m ev_n [] h_nodoc
      (TOpt.some _ _ _ (TLAnyDocument.bare _ _ _ (TLBareDocument.mk _ _ _ h_bn))) (TStar.nil _)

end

end L4YAML.Proofs.Serialization.TraceOf.StreamBridge
