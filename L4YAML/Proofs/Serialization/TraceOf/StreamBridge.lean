/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Proofs.Serialization.TraceOf.DocBridge
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
open L4YAML.Proofs.StreamAccum (scannedDirective_toSL)
open L4YAML.Proofs.PreprocessProduction (SSLComments_to_GStar)
open L4YAML.Proofs.SurfaceSpan (sslComments_suffix)
open L4YAML.Proofs.StructureProduction L4YAML.Proofs.CouplingBridge

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

/-- **`%`** at a line-start park or inside a run (the twin of `accum_structural_pending`'s
directive arm): the handles grow by the directive's, the run grows at its end, no event.  Stated
at the preprocessed state `s_prep` (its `[79]` landing `h_pre` from the park). -/
lemma directive_step {sp_start sp_block sp_scan sp_prep : SurfPos} {s_prep s' : ScannerState}
    {b : Bool} {ev_c : List Event} {p : List String}
    (hS : TSLYamlStream sp_start s_prep sp_block ev_c [] p)
    (hP : TPendingNode sp_start b sp_block sp_scan ev_c [] p)
    (h_pre : SSLComments sp_scan sp_prep)
    (hcorr : ScannerSurfCorr s_prep sp_prep) (hpeek : s_prep.peek? = some '%')
    (hok : scanDirective s_prep = .ok s') :
    ∃ sp_block' sp' p', ScannerSurfCorr s' sp' ∧
      TSLYamlStream sp_start s' sp_block' ev_c [] p' ∧
      TPendingNode sp_start true sp_block' sp' ev_c [] p' := by
  obtain ⟨sp', hsd, hcorr', hbrk, new, htoks, hgo, hstable⟩ :=
    scanDirective_trace s_prep sp_prep hcorr hpeek s' hok
  have hS' : TSLYamlStream sp_start s' sp_block ev_c []
      ((declaredHandle (span sp_prep sp')).toList ++ p) := by simpa using hS.push htoks (hgo p)
  have leaf : ∀ sp_mid, SSLComments sp' sp_mid →
      TLDirective sp_prep sp_mid ((declaredHandle (span sp_prep sp')).toList.map .declareTag) := by
    intro sp_mid hssl
    have := hstable sp_mid (List.IsSuffix.length_le (sslComments_suffix hssl))
    exact ⟨scannedDirective_toSL hsd hbrk hssl, by rw [this]⟩
  cases hP with
  | noPending _ _ h_col =>
    refine ⟨sp_prep, sp', _, hcorr', ⟨TLYamlStream.extendComments hS'.stream h_col h_pre, hS'.events⟩, ?_⟩
    refine TPendingNode.pendingDirective _ _ _ _ fun sp_mid hssl => ?_
    simpa [option_toList_reverse] using TPlus.mk _ _ _ _ [] (leaf sp_mid hssl) (TStar.nil _)
  | pendingDirective _ _ _ _ h_acc =>
    refine ⟨sp_block, sp', _, hcorr', hS', ?_⟩
    refine TPendingNode.pendingDirective _ _ _ _ fun sp_mid hssl => ?_
    simpa [option_toList_reverse, List.reverse_append] using
      TPlus_TLDirective_snoc (h_acc sp_prep h_pre) (leaf sp_mid hssl)

/-- **`---`** at a line-start park or after a run (the twin of the document-start arm): the
handles flush after `beginDocument`, the route into the stream is `explicitRoute` /
`directiveRoute` on the closed stream. -/
lemma docStart_step {sp_start sp_block sp_scan sp_prep : SurfPos} {s_prep : ScannerState}
    {b : Bool} {ev_c : List Event} {p : List String}
    (hS : TSLYamlStream sp_start s_prep sp_block ev_c [] p)
    (hP : TPendingNode sp_start b sp_block sp_scan ev_c [] p)
    (h_pre : SSLComments sp_scan sp_prep)
    (hcorr : ScannerSurfCorr s_prep sp_prep)
    (rest : List Char) (hchars : sp_prep.chars = '-' :: '-' :: '-' :: rest) (hcol : sp_prep.col = 0) :
    ∃ sp', ScannerSurfCorr (scanDocumentStart s_prep) sp' ∧
      TSLYamlStream sp_start (scanDocumentStart s_prep) sp_block ev_c
        (.beginDocument :: p.reverse.map .declareTag) [] ∧
      TPendingNode sp_start false sp_block sp' ev_c (.beginDocument :: p.reverse.map .declareTag) [] := by
  obtain ⟨sp', hde, hcorr', hS'⟩ := hS.docStart sp_prep hcorr rest hchars hcol
  refine ⟨sp', hcorr', by simpa using hS', ?_⟩
  cases hP with
  | noPending _ _ h_col =>
    exact TPendingNode.pendingDocStart _ _ _ _ fun sp_end eb hb => by
      simpa using TLYamlStream.explicitRoute hS.stream (SSLComments_to_GStar_prefix h_col h_pre) hde hb
  | pendingDirective _ _ _ _ h_acc =>
    exact TPendingNode.pendingDocStart _ _ _ _ fun sp_end eb hb => by
      simpa using TLYamlStream.directiveRoute hS.stream (GStar.nil _) (h_acc sp_prep h_pre) hde hb
where
  /-- the park's `[79]` landing as `[202]` prefixes -/
  SSLComments_to_GStar_prefix {sp sp' : SurfPos} (h_col : sp.col = 0) (h : SSLComments sp sp') :
      GStar SLDocumentPrefix sp sp' :=
    GStar.cons sp sp' sp' (SLDocumentPrefix.comments sp sp' (SSLComments_to_GStar sp sp' h h_col))
      (GStar.nil _)

/-- **`...`** at a line-start park (the twin of the document-end arm): `endDocument` opens,
awaiting `[79]`; the closed stream is extended over the park's landing first. -/
lemma docEnd_step {sp_start sp sp_prep : SurfPos} {s_prep s' : ScannerState} {ev_c : List Event}
    (hS : TSLYamlStream sp_start s_prep sp ev_c [] [])
    (hP : TPendingNode sp_start false sp sp ev_c [] [])
    (h_pre : SSLComments sp sp_prep)
    (hcorr : ScannerSurfCorr s_prep sp_prep)
    (rest : List Char) (hchars : sp_prep.chars = '.' :: '.' :: '.' :: rest) (hcol : sp_prep.col = 0)
    (hok : scanDocumentEnd s_prep = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' ∧
      TSLYamlStream sp_start s' sp_prep ev_c [.endDocument] [] ∧
      TPendingNode sp_start false sp_prep sp' ev_c [.endDocument] [] := by
  obtain ⟨sp', hm, hcorr', hS'⟩ := hS.docEnd sp_prep hcorr rest hchars hcol s' hok
  cases hP with
  | noPending _ _ h_col =>
    exact ⟨sp', hcorr', ⟨TLYamlStream.extendComments hS'.stream h_col h_pre, by simpa using hS'.events⟩,
      TPendingNode.pendingDocEnd _ _ _ _ hm⟩

end TPendingNode

end

end L4YAML.Proofs.Serialization.TraceOf.StreamBridge
