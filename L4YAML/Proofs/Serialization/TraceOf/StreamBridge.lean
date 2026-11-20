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

/-- **The content step at a line-start park** (item 529, the twin of `content_dispatch_routed`'s two
sites): from `noPending` at `sp`, the depth-0 content dispatch parks as `pendingContent` (a scalar, an
alias) or `pendingProps` (`&` / `!`), the step's events read off `accum_step_content_trace_out`;
`h_route` is how a completed node at the park re-enters the stream (`TLYamlStream.bareRoute` at the
first document, `h_route`'s own shape at the parks below). -/
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
  obtain ⟨ev_n, hpt, hdisj⟩ := accum_step_content_trace_out arm hcorr hpeek h_depth h_dispatch
  refine ⟨ev_n, ⟨hS.stream, by rw [hpt.goOut_at [], hS.events]; simp⟩, ?_⟩
  rcases hdisj with ⟨hev, sp_gram, hT, hws, -⟩ | ⟨hev, hc, -⟩ | ⟨hev, hc, -⟩ | ⟨-, ha, -⟩ | ⟨-, ht, -⟩ | ⟨-, hal⟩
  · subst hev
    exact .pendingContent sp sp_a sp_gram ev_c []
      (fun sp_mid h_ssl => h_route sp_mid [] (.flowInBlock 0 .blockIn sp sp_prep sp_gram sp_mid [] h_sep hT h_ssl))
      hws
  · subst hev
    refine .pendingContent sp sp_a sp_a ev_c []
      (fun sp_mid h_ssl => h_route sp_mid [] (.flowInBlock 0 .blockIn sp sp_prep sp_a sp_mid [] h_sep ?_ h_ssl))
      (GStar.nil _)
    cases arm with
    | doubleQuoted _ _ hq _ _ =>
      exact .content _ _ _ _ _ (.doubleQ _ _ _ _ (SCDoubleQuoted_ctx_lift hq (by decide) (by decide)))
    | singleQuoted _ _ hq _ _ =>
      exact .content _ _ _ _ _ (.singleQ _ _ _ _ (SCSingleQuoted_ctx_lift hq (by decide) (by decide)))
    | plainIn _ _ hd _ _ => omega
    | plain _ _ h_c _ _ _ _ _ => rcases hc with h | h <;> simp_all
    | blockScalar _ h_c _ _ => rcases hc with h | h <;> rcases h_c with h' | h' <;> simp_all
    | anchor _ h_c _ _ _ => rcases hc with h | h <;> simp_all
    | tag _ h_c _ _ _ => rcases hc with h | h <;> simp_all
    | alias _ h_c _ _ => rcases hc with h | h <;> simp_all
  · subst hev
    obtain ⟨sp_bs, -, hcorr_bs, h_absorb⟩ := dispatchContent_blockScalar_prod s_prep sp_prep hcorr hpeek hc h_dispatch
    have heq := ScannerSurfCorr_unique hcorr_bs hcorr'
    rw [heq] at h_absorb
    exact .pendingContent sp sp_a sp_a ev_c []
      (fun sp_mid h_ssl => h_route sp_mid [] ((h_absorb sp_mid h_ssl).elim
        (fun hl => .blockLiteral 0 .blockIn sp sp_prep sp_prep sp_mid [] h_sep (TOpt.none _) hl)
        (fun hf => .blockFolded 0 .blockIn sp sp_prep sp_prep sp_mid [] h_sep (TOpt.none _) hf)))
      (GStar.nil _)
  · exact .pendingProps sp sp_a sp sp_prep 0 ev_c [] ev_n h_sep
      (by simpa using TCNsProperties.anchorFirst sp_prep sp_a sp_a ev_n [] ha (TOpt.none _))
      (fun sp_m ev h => by simpa using h_route sp_m ev h)
  · exact .pendingProps sp sp_a sp sp_prep 0 ev_c [] ev_n h_sep
      (by simpa using TCNsProperties.tagFirst sp_prep sp_a sp_a ev_n [] ht (TOpt.none _))
      (fun sp_m ev h => by simpa using h_route sp_m ev h)
  · exact .pendingContent sp sp_a sp_a ev_c ev_n
      (fun sp_mid h_ssl => h_route sp_mid ev_n
        (.flowInBlock 0 .blockIn sp sp_prep sp_a sp_mid ev_n h_sep (.alias 0 .flowOut sp_prep sp_a ev_n hal) h_ssl))
      (GStar.nil _)

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
