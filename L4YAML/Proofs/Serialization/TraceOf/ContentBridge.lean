/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import L4YAML.Proofs.Serialization.ScannerShape
public import L4YAML.Proofs.Serialization.TraceOf.UniqueFlow
import all L4YAML.Proofs.Serialization.TokenEvents
/-!
# S3 slice (4), PR 1 — the content step's T twin
(EVENTSOF §10, capstone 7.7 `parse_iff_grammar`; item 486)

`accum_step_content` (`StreamAccum`) concludes its arm, `ContentArm` (item 484).  This module
reads the arm into the `TraceOf` twins, the way `accum_step_flow_trace` reads `FlowArm`:

* `goOut_push` — the trace of one pushed token, in `goOut` form (the `tokenEvents`
  equation item 485 wrote is only true once no `%TAG` handle is pending; the twins
  couple through `goOut`, as 2c states it);
* `SFlowNode_head_lift` — the first-char lift: an `SFlowNode` whose first character is
  none of `& * ! [ {` is its content, `SNsPlain` / `SCDoubleQuoted` / `SCSingleQuoted`;
* `accum_step_content_trace_in` — depth ≥ 1: the value arms land on the T flow stack
  through `TFlowOpenStack.receiveNode`, the property arms leave it (the tail is kept), the
  block scalars are refused;
* `accum_step_content_trace_out` — depth 0: every arm's T leaf.

The depth-≥1 receive's premises (`h_tail`, `h_lead`) are the ones `accum_step_content_core`
derives from `h_interior` for its own `FlowOpenStack.receiveNode`; the twin takes them as
stated and the derivation stays the core's (no `StreamAccum` edit; item 486 prices the
replay).  (b) — the parser's refusal of a held run followed by an alias at depth 0 — does not
enter here: the twin concludes the alias LEAF; (b) is spent where the depth-0 node is
assembled.
-/

namespace L4YAML.Proofs.Serialization.TraceOf.ContentBridge

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.FlowWalk
open L4YAML.Proofs.StructureProduction L4YAML.Proofs.ScalarProduction L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.NodeProduction L4YAML.Proofs.Acceptance

public section
open L4YAML.Proofs.Serialization.ScannerShape
open L4YAML.Proofs.Serialization.TokenEvents (tokenEvent goOut goOut_append)
open L4YAML.Proofs.StreamAccum (ContentArm FrameTail tailOf tailOf_push_prop NextIsSep
  tailOf_dispatchContent_value dispatchContent_tokens_push dispatchContent_tokens_push_prop
  dispatchContent_evidence_flowIn_at)

/-! ## §1 The trace of one pushed token -/

/-- `ts'` extends `ts` by tokens whose trace is `ev`, from every pending-handle state: the
    `goOut` form of "the events grew by `ev`" (2c's coupling). -/
def PushesTrace (ts ts' : Array (Positioned YamlToken)) (ev : List Event) : Prop :=
  ∀ p, goOut ts'.toList p = ((goOut ts.toList p).1 ++ ev, (goOut ts.toList p).2)

/-- `PushesTrace` read at one pending-handle state (the def's body is not exposed to importers). -/
lemma PushesTrace.goOut_at {ts ts' : Array (Positioned YamlToken)} {ev : List Event}
    (h : PushesTrace ts ts' ev) (p : List String) :
    goOut ts'.toList p = ((goOut ts.toList p).1 ++ ev, (goOut ts.toList p).2) := h p

lemma goOut_single (t : Positioned YamlToken) (p : List String)
    (hds : t.val ≠ .documentStart) (htd : ∀ h pfx, t.val ≠ .tagDirective h pfx) :
    goOut [t] p = ((tokenEvent t.val).toList, p) := by
  obtain ⟨_, v, _⟩ := t
  cases v <;> simp_all [goOut, tokenEvent]
  all_goals (try split <;> simp_all)

lemma pushesTrace_push (ts : Array (Positioned YamlToken)) (t : Positioned YamlToken)
    (hds : t.val ≠ .documentStart) (htd : ∀ h pfx, t.val ≠ .tagDirective h pfx) :
    PushesTrace ts (ts.push t) (tokenEvent t.val).toList := by
  intro p
  rw [Array.toList_push, goOut_append, goOut_single t _ hds htd]

/-- A scalar of any style is silent. -/
lemma pushesTrace_push_scalar (ts : Array (Positioned YamlToken)) (t : Positioned YamlToken)
    {str : String} {sty : ScalarStyle} (hv : t.val = .scalar str sty) :
    PushesTrace ts (ts.push t) [] := by
  have h := pushesTrace_push ts t (by rw [hv]; simp) (by intro h pfx; rw [hv]; simp)
  rw [hv] at h
  simpa [tokenEvent] using h

/-! ## §2 The first-char lift -/

/-- An `SFlowNode` whose first character is none of `& * ! [ {` is its content: a plain
    scalar unless the character is a quote. -/
lemma SFlowNode_head_lift {n : Nat} {c : YamlContext} {ch : Char} {rest : List Char}
    {col : Nat} {m : SurfPos}
    (h : SFlowNode n c ⟨ch :: rest, col⟩ m)
    (hc : ch ≠ '&' ∧ ch ≠ '*' ∧ ch ≠ '!' ∧ ch ≠ '[' ∧ ch ≠ '{') :
    (ch ≠ '"' ∧ ch ≠ '\'' ∧ SNsPlain n c ⟨ch :: rest, col⟩ m) ∨
    (ch = '"' ∧ SCDoubleQuoted n c ⟨ch :: rest, col⟩ m) ∨
    (ch = '\'' ∧ SCSingleQuoted n c ⟨ch :: rest, col⟩ m) := by
  obtain ⟨h_amp, h_star, h_bang, h_lb, h_lc⟩ := hc
  cases h with
  | alias _ _ _ _ ha =>
    obtain ⟨r, k, hk⟩ := alias_head ha
    simp only [SurfPos.mk.injEq, List.cons.injEq] at hk; exact absurd hk.1.1 h_star
  | content _ _ _ _ hcont =>
    cases hcont with
    | plain _ _ _ _ hp =>
      refine Or.inl ⟨?_, ?_, hp⟩
      · obtain ⟨ch', r, k, hk, hind⟩ := plain_head hp
        cases hk
        rintro rfl
        rcases hind with hi | hi | hi | hi <;> simp [isIndicatorProp] at hi
      · obtain ⟨ch', r, k, hk, hind⟩ := plain_head hp
        cases hk
        rintro rfl
        rcases hind with hi | hi | hi | hi <;> simp [isIndicatorProp] at hi
    | flowSeq _ _ _ _ hs =>
      exfalso
      cases hs <;> (rename_i hl; try (rename_i _ _ _ _ _); cases ‹GLit '[' _ _›; exact h_lb rfl)
    | flowMap _ _ _ _ hm =>
      exfalso
      cases hm <;> (cases ‹GLit '{' _ _›; exact h_lc rfl)
    | singleQ _ _ _ _ hq =>
      refine Or.inr (Or.inr ⟨?_, hq⟩)
      cases hq
      rename_i hl _ _
      cases hl; rfl
    | doubleQ _ _ _ _ hq =>
      refine Or.inr (Or.inl ⟨?_, hq⟩)
      cases hq
      rename_i hl _ _
      cases hl; rfl
  | propsContent _ _ _ _ _ _ hp _ _ =>
    exfalso
    cases hp with
    | tagFirst =>
      rename_i ht _
      obtain ⟨r, k, hk⟩ := tag_head ht
      simp only [SurfPos.mk.injEq, List.cons.injEq] at hk; exact h_bang hk.1.1
    | anchorFirst =>
      rename_i ha _
      obtain ⟨r, k, hk⟩ := anchor_head ha
      simp only [SurfPos.mk.injEq, List.cons.injEq] at hk; exact h_amp hk.1.1
  | propsEmpty _ _ _ _ hp =>
    exfalso
    cases hp with
    | tagFirst =>
      rename_i ht _
      obtain ⟨r, k, hk⟩ := tag_head ht
      simp only [SurfPos.mk.injEq, List.cons.injEq] at hk; exact h_bang hk.1.1
    | anchorFirst =>
      rename_i ha _
      obtain ⟨r, k, hk⟩ := anchor_head ha
      simp only [SurfPos.mk.injEq, List.cons.injEq] at hk; exact h_amp hk.1.1

/-- An `SFlowContent` whose first character opens no flow collection is a scalar, and a scalar's
    trace is empty: the T reading at the SAME indentation and context. -/
lemma TFlowContent.of_scalar {n : Nat} {c : YamlContext} {ch : Char} {rest : List Char}
    {col : Nat} {m : SurfPos}
    (h : SFlowContent n c ⟨ch :: rest, col⟩ m) (h_lb : ch ≠ '[') (h_lc : ch ≠ '{') :
    TFlowContent n c ⟨ch :: rest, col⟩ m [] := by
  cases h with
  | plain _ _ _ _ hp => exact .plain _ _ _ _ hp
  | flowSeq _ _ _ _ hs =>
    exfalso
    cases hs <;> (rename_i hl; try (rename_i _ _ _ _ _); cases ‹GLit '[' _ _›; exact h_lb rfl)
  | flowMap _ _ _ _ hm =>
    exfalso
    cases hm <;> (cases ‹GLit '{' _ _›; exact h_lc rfl)
  | singleQ _ _ _ _ hq => exact .singleQ _ _ _ _ hq
  | doubleQ _ _ _ _ hq => exact .doubleQ _ _ _ _ hq

/-- The plain arm of the content dispatcher pushes one plain scalar
    (`scanPlainScalar_tokens` through the dispatcher's seven refusals). -/
lemma dispatchContent_plain_tokens {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchContent s c = .ok s')
    (hamp : c ≠ '&') (hstar : c ≠ '*') (hbang : c ≠ '!') (hpipe : c ≠ '|') (hgt : c ≠ '>')
    (hdq : c ≠ '"') (hsq : c ≠ '\'') :
    ∃ str, s'.tokens = s.tokens.push ⟨s.currentPos, .scalar str .plain, s.currentPos⟩ := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hamp
  · split at hok
    · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hstar
    · split at hok
      · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hbang
      · split at hok
        · rename_i h_eq
          cases Bool.or_eq_true_iff.mp h_eq with
          | inl h => exact absurd (beq_iff_eq.mp h) hpipe
          | inr h => exact absurd (beq_iff_eq.mp h) hgt
        · split at hok
          · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hdq
          · split at hok
            · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hsq
            · split at hok
              · exact L4YAML.Proofs.StreamAccum.scanPlainScalar_tokens hok
              · simp at hok

/-! ## §3 The twin at depth ≥ 1 -/

/-- The value arms of a content step inside a flow collection land on the T flow stack: the
    S node the step produces (`dispatchContent_evidence_flowIn_at`) is lifted to its
    `TFlowNode` (first-char lift; `TCNsAliasNode` for `*`) and received at the tail the
    scanner computes (`tailOf_dispatchContent_value`); the property arms push a silent-or-not
    property and keep the tail; block scalars are refused in flow.  `h_tail` / `h_lead` are
    the receive's premises as `accum_step_content_core` derives them from `h_interior`. -/
lemma accum_step_content_trace_in {n D : Nat} {ks km : Array Bool}
    {s_ad s' : ScannerState} {c : Char} {sp_block sp_flow sp_prep sp_a : SurfPos}
    {ev : List Event}
    (arm : ContentArm s_ad s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_ad sp_prep) (hpeek : s_ad.peek? = some c)
    (h_inflow : s_ad.inFlow = true)
    (h_not_doc : s_ad.col = 0 → atDocumentBoundary s_ad = false)
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s')
    (hcol : s_ad.currentIndent < (s_ad.col : Int))
    (hn : (n : Int) ≤ max 0 (s_ad.currentIndent + 1))
    (hT : TFlowOpenStack n D ks km (tailOf s_ad.tokens) sp_block sp_flow ev)
    (h_tail : ∀ kj, tailOf s_ad.tokens ≠ .value kj)
    (h_lead : SSeparateLines n sp_flow sp_prep ∨
      (sp_prep = sp_flow ∧ (tailOf s_ad.tokens).leadFree)) :
    ∃ ev_n, PushesTrace s_ad.tokens s'.tokens ev_n ∧
      ((∃ kj sp_ne, tailOf s'.tokens = .value kj ∧ GStar SSWhite sp_ne sp_a ∧
          SFlowNode n .flowIn sp_prep sp_ne ∧
          TFlowOpenStack n D ks km (.value kj) sp_block sp_ne (ev ++ ev_n) ∧
          -- Item 509: the key-then-colon closure (`receiveNodeColon`), where the pre-tail
          -- admits a key — `TFlowStackK`'s T closure is produced here.
          ((tailOf s_ad.tokens = .sep ∨ tailOf s_ad.tokens = .question) →
            ∀ sp_prep₂ sp_tok, (SSeparateLines n sp_ne sp_prep₂ ∨ sp_prep₂ = sp_ne) →
              GLit ':' sp_prep₂ sp_tok →
              TFlowOpenStack n D ks km (.colon kj) sp_block sp_tok (ev ++ ev_n))) ∨
       (tailOf s'.tokens = tailOf s_ad.tokens ∧
         ((c = '&' ∧ TCNsAnchorProperty sp_prep sp_a ev_n) ∨
          (c = '!' ∧ TCNsTagProperty sp_prep sp_a ev_n)))) := by
  obtain ⟨rest, hsp_prep⟩ := peek_some_sp hcorr hpeek
  by_cases hamp : c = '&'
  · subst hamp
    obtain ⟨sp', name, htok, hcorr', hT_anchor⟩ :=
      dispatchContent_anchor_trace s_ad sp_prep hcorr hpeek s' h_dispatch
    have hsp : sp' = sp_a := by
      cases arm with
      | anchor _ h_c _ _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
      | plain _ _ h_c => exact absurd rfl h_c.1
      | plainIn _ h_c => exact absurd rfl h_c.1
      | doubleQuoted _ h_c => exact absurd h_c (by decide)
      | singleQuoted _ h_c => exact absurd h_c (by decide)
      | blockScalar _ h_c => rcases h_c with h | h <;> exact absurd h (by decide)
      | tag _ h_c => exact absurd h_c (by decide)
      | alias _ h_c => exact absurd h_c (by decide)
    subst hsp
    refine ⟨[.defineAnchor name], ?_, Or.inr ⟨?_, Or.inl ⟨rfl, hT_anchor⟩⟩⟩
    · rw [htok]
      simpa [tokenEvent] using pushesTrace_push s_ad.tokens ⟨s_ad.currentPos, .anchor name, s_ad.currentPos⟩ (by simp) (by simp)
    · rw [htok]; exact (tailOf_push_prop (by simp) (by simp [YamlToken.isNodeProperty])).1
  by_cases hbang : c = '!'
  · subst hbang
    obtain ⟨sp', handle, suffix, htok, hcorr', hT_tag⟩ :=
      dispatchContent_tag_trace s_ad sp_prep hcorr hpeek s' h_dispatch
    have hsp : sp' = sp_a := by
      cases arm with
      | tag _ h_c _ _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
      | plain _ _ h_c => exact absurd rfl h_c.2.2.1
      | plainIn _ h_c => exact absurd rfl h_c.2.2.1
      | doubleQuoted _ h_c => exact absurd h_c (by decide)
      | singleQuoted _ h_c => exact absurd h_c (by decide)
      | blockScalar _ h_c => rcases h_c with h | h <;> exact absurd h (by decide)
      | anchor _ h_c => exact absurd h_c (by decide)
      | alias _ h_c => exact absurd h_c (by decide)
    subst hsp
    refine ⟨_, ?_, Or.inr ⟨?_, Or.inr ⟨rfl, hT_tag⟩⟩⟩
    · rw [htok]
      exact pushesTrace_push s_ad.tokens ⟨s_ad.currentPos, .tag handle suffix, s_ad.currentPos⟩ (by simp) (by simp)
    · rw [htok]; exact (tailOf_push_prop (by simp) (by simp [YamlToken.isNodeProperty])).1
  obtain ⟨hpipe, hgt⟩ :=
    Proofs.BlockScalarFlowGuard.dispatchContent_not_blockScalar_of_inFlow h_inflow h_dispatch
  obtain ⟨⟨kj, h_tl', hkj⟩, -, -⟩ :=
    tailOf_dispatchContent_value h_dispatch hamp hbang hpipe hgt
  by_cases hstar : c = '*'
  · subst hstar
    obtain ⟨sp', name, htok, hcorr', hT_alias⟩ :=
      dispatchContent_alias_trace s_ad sp_prep hcorr hpeek s' h_dispatch
    have hsp : sp' = sp_a := by
      cases arm with
      | alias _ h_c _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
      | plain _ _ h_c => exact absurd rfl h_c.2.1
      | plainIn _ h_c => exact absurd rfl h_c.2.1
      | doubleQuoted _ h_c => exact absurd h_c (by decide)
      | singleQuoted _ h_c => exact absurd h_c (by decide)
      | blockScalar _ h_c => rcases h_c with h | h <;> exact absurd h (by decide)
      | anchor _ h_c => exact absurd h_c (by decide)
      | tag _ h_c => exact absurd h_c (by decide)
    subst hsp
    have hkj0 : kj = false := by
      cases kj with
      | false => rfl
      | true => rcases hkj rfl with h | h <;> exact absurd h (by decide)
    subst hkj0
    refine ⟨[.useAlias name], ?_, Or.inl ⟨false, sp', h_tl', .nil _, .alias _ _ _ _ hT_alias.1, ?_, ?_⟩⟩
    · rw [htok]
      simpa [tokenEvent] using pushesTrace_push s_ad.tokens ⟨s_ad.currentPos, .alias name, s_ad.currentPos⟩ (by simp) (by simp)
    · exact hT.receiveNode h_tail h_lead (.alias _ _ _ _ _ hT_alias) (fun h => nomatch h)
    · intro h_sq sp_p₂ sp_t h_l h_col
      exact hT.receiveNodeColon h_sq h_lead (.alias _ _ _ _ _ hT_alias) (fun h => nomatch h) h_l h_col
  -- The scalar arms: plain, double-quoted, single-quoted.
  obtain ⟨sp_gram, sp', h_node, h_ws, hcorr', -, h_json⟩ :=
    dispatchContent_evidence_flowIn_at n s_ad sp_prep c hcorr hpeek h_inflow h_not_doc h_dispatch hcol hn
  have hsp : sp' = sp_a := by
    cases arm with
    | plain _ _ _ _ _ _ _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
    | plainIn _ _ _ hcorr_a _ => exact ScannerSurfCorr_unique hcorr' hcorr_a
    | doubleQuoted _ _ _ _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
    | singleQuoted _ _ _ _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
    | blockScalar _ h_c =>
      rcases h_c with h | h
      · exact absurd h hpipe
      · exact absurd h hgt
    | anchor _ h_c => exact absurd h_c hamp
    | tag _ h_c => exact absurd h_c hbang
    | alias _ h_c => exact absurd h_c hstar
  subst hsp
  have hglue := L4YAML.Proofs.StreamAccum.content_not_glue h_dispatch
  simp only [isFlowIndicatorBool, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    List.mem_cons, List.mem_nil_iff, or_false, not_or] at hglue
  have hlb : c ≠ '[' := hglue.2.2.1
  have hlc : c ≠ '{' := hglue.2.2.2.2.1
  have hsilent : PushesTrace s_ad.tokens s'.tokens [] := by
    by_cases hdq : c = '"'
    · subst hdq
      obtain ⟨_, v, htok, -, -⟩ :=
        dispatchContent_doubleQuoted_trace s_ad sp_prep hcorr hpeek s' h_dispatch
      rw [htok]; exact pushesTrace_push_scalar _ _ rfl
    by_cases hsq : c = '\''
    · subst hsq
      obtain ⟨_, v, htok, -, -⟩ :=
        dispatchContent_singleQuoted_trace s_ad sp_prep hcorr hpeek s' h_dispatch
      rw [htok]; exact pushesTrace_push_scalar _ _ rfl
    obtain ⟨str, htok⟩ := dispatchContent_plain_tokens h_dispatch hamp hstar hbang hpipe hgt hdq hsq
    rw [htok]; exact pushesTrace_push_scalar _ _ rfl
  -- The T node and its JSON-ness, once; `receiveNode` lands it, `receiveNodeColon` is the closure.
  have h_tn : TFlowNode n .flowIn sp_prep sp_gram [] ∧
      (kj = true → TCFlowJsonNode n .flowIn sp_prep sp_gram []) := by
    subst hsp_prep
    rcases SFlowNode_head_lift h_node ⟨hamp, hstar, hbang, hlb, hlc⟩ with
      ⟨hdq, hsq, hplain⟩ | ⟨hdq, hq⟩ | ⟨hsq, hq⟩
    · refine ⟨.content _ _ _ _ _ (.plain _ _ _ _ hplain), ?_⟩
      intro hk
      rcases hkj hk with h | h
      · exact absurd h hdq
      · exact absurd h hsq
    · exact ⟨.content _ _ _ _ _ (.doubleQ _ _ _ _ hq), fun _ => .content _ _ _ _ _ (.doubleQ _ _ _ _ hq)⟩
    · exact ⟨.content _ _ _ _ _ (.singleQ _ _ _ _ hq), fun _ => .content _ _ _ _ _ (.singleQ _ _ _ _ hq)⟩
  subst hsp_prep
  exact ⟨[], hsilent, Or.inl ⟨kj, sp_gram, h_tl', h_ws, h_node,
    hT.receiveNode h_tail h_lead h_tn.1 h_tn.2,
    fun h_sq sp_p₂ sp_t h_l h_col => hT.receiveNodeColon h_sq h_lead h_tn.1 h_tn.2 h_l h_col⟩⟩

/-- The `.props` interior: a property run is held (`TCNsProperties`, item 472's lift of
    `PropsRun`), the content follows a separator, and the scalar arms land on the T flow stack
    through `receivePropsContent` with the run's events before the scalar's.  The alias arm is
    excluded by hypothesis: the dispatcher refuses `*` after a property inside a flow
    (`lastTokenIsNodeProperty`'s in-flow half; P113's two refused rows), and the property arms
    extend the run (the `_in` twin's second disjunct, run-free). -/
lemma accum_step_content_trace_in_props {n D : Nat} {ks km : Array Bool}
    {s_ad s' : ScannerState} {c : Char} {sp_block sp_flow sp_p sp_e sp_prep sp_a : SurfPos}
    {ev ev_p : List Event}
    (arm : ContentArm s_ad s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_ad sp_prep) (hpeek : s_ad.peek? = some c)
    (h_inflow : s_ad.inFlow = true)
    (h_not_doc : s_ad.col = 0 → atDocumentBoundary s_ad = false)
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s')
    (hcol : s_ad.currentIndent < (s_ad.col : Int))
    (hn : (n : Int) ≤ max 0 (s_ad.currentIndent + 1))
    (hT : TFlowOpenStack n D ks km (tailOf s_ad.tokens) sp_block sp_flow ev)
    (h_tail : ∀ kj, tailOf s_ad.tokens ≠ .value kj)
    (h_lead : SSeparateLines n sp_flow sp_p ∨
      (sp_p = sp_flow ∧ (tailOf s_ad.tokens).leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_e ev_p)
    (h_sep : SSeparate n .flowIn sp_e sp_prep)
    (h_val : c ≠ '&' ∧ c ≠ '!' ∧ c ≠ '*') :
    ∃ kj sp_ne, PushesTrace s_ad.tokens s'.tokens [] ∧
      tailOf s'.tokens = .value kj ∧ GStar SSWhite sp_ne sp_a ∧ SFlowNode n .flowIn sp_prep sp_ne ∧
      TFlowOpenStack n D ks km (.value kj) sp_block sp_ne (ev ++ (ev_p ++ [])) ∧
      -- Item 509: the decorated key's closure (`receivePropsNodeColon`).
      ((tailOf s_ad.tokens = .sep ∨ tailOf s_ad.tokens = .question) →
        ∀ sp_prep₂ sp_tok, (SSeparateLines n sp_ne sp_prep₂ ∨ sp_prep₂ = sp_ne) →
          GLit ':' sp_prep₂ sp_tok →
          TFlowOpenStack n D ks km (.colon kj) sp_block sp_tok (ev ++ (ev_p ++ []))) := by
  obtain ⟨hamp, hbang, hstar⟩ := h_val
  obtain ⟨rest, hsp_prep⟩ := peek_some_sp hcorr hpeek
  obtain ⟨hpipe, hgt⟩ :=
    Proofs.BlockScalarFlowGuard.dispatchContent_not_blockScalar_of_inFlow h_inflow h_dispatch
  obtain ⟨⟨kj, h_tl', hkj⟩, -, -⟩ :=
    tailOf_dispatchContent_value h_dispatch hamp hbang hpipe hgt
  obtain ⟨sp_gram, sp', h_node, h_ws, hcorr', -, -⟩ :=
    dispatchContent_evidence_flowIn_at n s_ad sp_prep c hcorr hpeek h_inflow h_not_doc h_dispatch hcol hn
  have hsp : sp' = sp_a := by
    cases arm with
    | plain _ _ _ _ _ _ _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
    | plainIn _ _ _ hcorr_a _ => exact ScannerSurfCorr_unique hcorr' hcorr_a
    | doubleQuoted _ _ _ _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
    | singleQuoted _ _ _ _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
    | blockScalar _ h_c =>
      rcases h_c with h | h
      · exact absurd h hpipe
      · exact absurd h hgt
    | anchor _ h_c => exact absurd h_c hamp
    | tag _ h_c => exact absurd h_c hbang
    | alias _ h_c => exact absurd h_c hstar
  subst hsp
  have hglue := L4YAML.Proofs.StreamAccum.content_not_glue h_dispatch
  simp only [isFlowIndicatorBool, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    List.mem_cons, List.mem_nil_iff, or_false, not_or] at hglue
  have hlb : c ≠ '[' := hglue.2.2.1
  have hlc : c ≠ '{' := hglue.2.2.2.2.1
  have hsilent : PushesTrace s_ad.tokens s'.tokens [] := by
    by_cases hdq : c = '"'
    · subst hdq
      obtain ⟨_, v, htok, -, -⟩ :=
        dispatchContent_doubleQuoted_trace s_ad sp_prep hcorr hpeek s' h_dispatch
      rw [htok]; exact pushesTrace_push_scalar _ _ rfl
    by_cases hsq : c = '\''
    · subst hsq
      obtain ⟨_, v, htok, -, -⟩ :=
        dispatchContent_singleQuoted_trace s_ad sp_prep hcorr hpeek s' h_dispatch
      rw [htok]; exact pushesTrace_push_scalar _ _ rfl
    obtain ⟨str, htok⟩ := dispatchContent_plain_tokens h_dispatch hamp hstar hbang hpipe hgt hdq hsq
    rw [htok]; exact pushesTrace_push_scalar _ _ rfl
  have h_tc : TFlowContent n .flowIn sp_prep sp_gram [] ∧
      (kj = true → TCFlowJsonContent n .flowIn sp_prep sp_gram []) := by
    subst hsp_prep
    rcases SFlowNode_head_lift h_node ⟨hamp, hstar, hbang, hlb, hlc⟩ with
      ⟨hdq, hsq, hplain⟩ | ⟨hdq, hq⟩ | ⟨hsq, hq⟩
    · refine ⟨.plain _ _ _ _ hplain, ?_⟩
      intro hk
      rcases hkj hk with h | h
      · exact absurd h hdq
      · exact absurd h hsq
    · exact ⟨.doubleQ _ _ _ _ hq, fun _ => .doubleQ _ _ _ _ hq⟩
    · exact ⟨.singleQ _ _ _ _ hq, fun _ => .singleQ _ _ _ _ hq⟩
  subst hsp_prep
  exact ⟨kj, sp_gram, hsilent, h_tl', h_ws, h_node,
    hT.receivePropsContent h_tail h_lead h_props h_sep h_tc.1 h_tc.2,
    fun h_sq sp_p₂ sp_t h_l h_col => hT.receivePropsNodeColon h_sq h_lead h_props h_sep h_tc.1
      (fun hk => .propsContent _ _ _ _ _ _ _ _ h_props h_sep (h_tc.2 hk)) h_l h_col⟩

/-! ## §4 The twin at depth 0 -/

/-- The block-scalar arm of the content dispatcher pushes one scalar. -/
lemma dispatchContent_blockScalar_tokens {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchContent s c = .ok s')
    (hamp : c ≠ '&') (hstar : c ≠ '*') (hbang : c ≠ '!') (hbs : c = '|' ∨ c = '>') :
    ∃ str sty, s'.tokens = s.tokens.push ⟨s.currentPos, .scalar str sty, s.currentPos⟩ := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hamp
  · split at hok
    · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hstar
    · split at hok
      · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) hbang
      · split at hok
        · split at hok
          · cases hok
          · exact L4YAML.Proofs.StreamAccum.scanBlockScalar_tokens_push hok
        · rename_i h_eq
          rcases hbs with h | h <;> simp [h] at h_eq

/-- Every arm's T leaf at depth 0: the plain arm's `TFlowNode 0 .flowOut` (first-char lift) with
    its trailing white and the `#` guard, the quoted arms' `TFlowContent 0 .blockIn`, the block
    scalar's surface relation (its T twin is the block re-walk's, which opens with `SSeparate`
    before the header), the property leaves with `NextIsSep`, the alias leaf.  Scalars are silent;
    the property and alias leaves carry their event. -/
lemma accum_step_content_trace_out {s_ad s' : ScannerState} {c : Char} {sp_prep sp_a : SurfPos}
    (arm : ContentArm s_ad s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_ad sp_prep) (hpeek : s_ad.peek? = some c)
    (h_depth : s_ad.flowLevel = 0)
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s') :
    ∃ ev_n, PushesTrace s_ad.tokens s'.tokens ev_n ∧
      ((ev_n = [] ∧ ∃ sp_gram, TFlowContent 0 .flowOut sp_prep sp_gram [] ∧
          GStar SSWhite sp_gram sp_a ∧ (sp_gram = sp_a → s'.peek? ≠ some '#') ∧
          (c ≠ '&' ∧ c ≠ '!' ∧ c ≠ '*')) ∨
       (ev_n = [] ∧ (c = '"' ∨ c = '\'') ∧ TFlowContent 0 .blockIn sp_prep sp_a []) ∨
       (ev_n = [] ∧ (c = '|' ∨ c = '>') ∧ (SCLLiteral 0 sp_prep sp_a ∨ SCLFolded 0 sp_prep sp_a)) ∨
       (c = '&' ∧ TCNsAnchorProperty sp_prep sp_a ev_n ∧ NextIsSep s') ∨
       (c = '!' ∧ TCNsTagProperty sp_prep sp_a ev_n ∧ NextIsSep s') ∨
       (c = '*' ∧ TCNsAliasNode sp_prep sp_a ev_n)) := by
  obtain ⟨rest, hsp_prep⟩ := peek_some_sp hcorr hpeek
  have hglue := L4YAML.Proofs.StreamAccum.content_not_glue h_dispatch
  simp only [isFlowIndicatorBool, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    List.mem_cons, List.mem_nil_iff, or_false, not_or] at hglue
  have hlb : c ≠ '[' := hglue.2.2.1
  have hlc : c ≠ '{' := hglue.2.2.2.2.1
  cases arm with
  | plain sp_gram _ h_c _ h_node h_ws h_hash hcorr_a =>
    obtain ⟨h_amp, h_star, h_bang, h_pipe, h_gt, h_dq, h_sq⟩ := h_c
    obtain ⟨str, htok⟩ :=
      dispatchContent_plain_tokens h_dispatch h_amp h_star h_bang h_pipe h_gt h_dq h_sq
    refine ⟨[], by rw [htok]; exact pushesTrace_push_scalar _ _ rfl,
      Or.inl ⟨rfl, sp_gram, ?_, h_ws, h_hash, h_amp, h_bang, h_star⟩⟩
    subst hsp_prep
    rcases SFlowNode_head_lift h_node ⟨h_amp, h_star, h_bang, hlb, hlc⟩ with
      ⟨-, -, hplain⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact .plain _ _ _ _ hplain
    · exact absurd h h_dq
    · exact absurd h h_sq
  | plainIn _ _ h_depth' => omega
  | doubleQuoted _ h_c _ _ hcorr_a =>
    subst h_c
    obtain ⟨sp', v, htok, hcorr', hT_q⟩ :=
      dispatchContent_doubleQuoted_trace s_ad sp_prep hcorr hpeek s' h_dispatch
    obtain rfl : sp' = sp_a := ScannerSurfCorr_unique hcorr' hcorr_a
    exact ⟨[], by rw [htok]; exact pushesTrace_push_scalar _ _ rfl,
      Or.inr (Or.inl ⟨rfl, Or.inl rfl, hT_q⟩)⟩
  | singleQuoted _ h_c _ _ hcorr_a =>
    subst h_c
    obtain ⟨sp', v, htok, hcorr', hT_q⟩ :=
      dispatchContent_singleQuoted_trace s_ad sp_prep hcorr hpeek s' h_dispatch
    obtain rfl : sp' = sp_a := ScannerSurfCorr_unique hcorr' hcorr_a
    exact ⟨[], by rw [htok]; exact pushesTrace_push_scalar _ _ rfl,
      Or.inr (Or.inl ⟨rfl, Or.inr rfl, hT_q⟩)⟩
  | blockScalar _ h_c h_bs _ =>
    have h_amp : c ≠ '&' := by rcases h_c with h | h <;> subst h <;> decide
    have h_star : c ≠ '*' := by rcases h_c with h | h <;> subst h <;> decide
    have h_bang : c ≠ '!' := by rcases h_c with h | h <;> subst h <;> decide
    obtain ⟨str, sty, htok⟩ :=
      dispatchContent_blockScalar_tokens h_dispatch h_amp h_star h_bang h_c
    exact ⟨[], by rw [htok]; exact pushesTrace_push_scalar _ _ rfl,
      Or.inr (Or.inr (Or.inl ⟨rfl, h_c, h_bs⟩))⟩
  | anchor _ h_c _ h_next hcorr_a =>
    subst h_c
    obtain ⟨sp', name, htok, hcorr', hT_a⟩ :=
      dispatchContent_anchor_trace s_ad sp_prep hcorr hpeek s' h_dispatch
    obtain rfl : sp' = sp_a := ScannerSurfCorr_unique hcorr' hcorr_a
    refine ⟨[.defineAnchor name], ?_, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hT_a, h_next⟩)))⟩
    rw [htok]
    simpa [tokenEvent] using
      pushesTrace_push s_ad.tokens ⟨s_ad.currentPos, .anchor name, s_ad.currentPos⟩ (by simp) (by simp)
  | tag _ h_c _ h_next hcorr_a =>
    subst h_c
    obtain ⟨sp', handle, suffix, htok, hcorr', hT_t⟩ :=
      dispatchContent_tag_trace s_ad sp_prep hcorr hpeek s' h_dispatch
    obtain rfl : sp' = sp_a := ScannerSurfCorr_unique hcorr' hcorr_a
    refine ⟨_, ?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hT_t, h_next⟩))))⟩
    rw [htok]
    exact pushesTrace_push s_ad.tokens ⟨s_ad.currentPos, .tag handle suffix, s_ad.currentPos⟩
      (by simp) (by simp)
  | alias _ h_c _ hcorr_a =>
    subst h_c
    obtain ⟨sp', name, htok, hcorr', hT_al⟩ :=
      dispatchContent_alias_trace s_ad sp_prep hcorr hpeek s' h_dispatch
    obtain rfl : sp' = sp_a := ScannerSurfCorr_unique hcorr' hcorr_a
    refine ⟨[.useAlias name], ?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hT_al⟩))))⟩
    rw [htok]
    simpa [tokenEvent] using
      pushesTrace_push s_ad.tokens ⟨s_ad.currentPos, .alias name, s_ad.currentPos⟩ (by simp) (by simp)

/-- **The value's leaf at the park's indentation** (item 532): a depth-0 flow scalar reads as
    `TFlowContent n .flowOut` at every `n` under the scanner's content floor — the S arm's three
    `…_prod_at` readings (double-quoted, single-quoted, plain) through `TFlowContent.of_scalar`. -/
lemma content_leaf_at (n : Nat) {s_ad s' : ScannerState} {c : Char} {sp_prep : SurfPos}
    (hcorr : ScannerSurfCorr s_ad sp_prep) (hpeek : s_ad.peek? = some c)
    (h_flow : s_ad.inFlow = false)
    (h_not_doc : s_ad.col = 0 → atDocumentBoundary s_ad = false)
    (h_amp : c ≠ '&') (h_star : c ≠ '*') (h_bang : c ≠ '!') (h_pipe : c ≠ '|') (h_gt : c ≠ '>')
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s')
    (hn : n ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf s_ad) :
    ∃ sp_gram sp', TFlowContent n .flowOut sp_prep sp_gram [] ∧ GStar SSWhite sp_gram sp' ∧
      ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_prep⟩ := peek_some_sp hcorr hpeek
  have hglue := L4YAML.Proofs.StreamAccum.content_not_glue h_dispatch
  simp only [isFlowIndicatorBool, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    List.mem_cons, List.mem_nil_iff, or_false, not_or] at hglue
  have hlb : c ≠ '[' := hglue.2.2.1
  have hlc : c ≠ '{' := hglue.2.2.2.2.1
  have hn_max : (n : Int) ≤ max 0 (s_ad.currentIndent + 1) := by
    unfold L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf at hn
    omega
  by_cases hdq : c = '"'
  · subst hdq
    obtain ⟨sp', hg, -, hcorr'⟩ :=
      L4YAML.Proofs.StreamAccum.dispatchContent_doubleQuoted_prod_at n s_ad sp_prep hcorr hpeek
        h_dispatch hn_max
    exact ⟨sp', sp', .doubleQ _ _ _ _
      (L4YAML.Proofs.ScalarFoldAt.SCDoubleQuoted_multiCtx .flowOut (Or.inl rfl) hg), GStar.nil _, hcorr'⟩
  · by_cases hsq : c = '\''
    · subst hsq
      obtain ⟨sp', hg, -, hcorr'⟩ :=
        L4YAML.Proofs.StreamAccum.dispatchContent_singleQuoted_prod_at n s_ad sp_prep hcorr hpeek
          h_dispatch hn_max
      exact ⟨sp', sp', .singleQ _ _ _ _
        (L4YAML.Proofs.ScalarFoldAt.SCSingleQuoted_multiCtx .flowOut (Or.inl rfl) hg), GStar.nil _, hcorr'⟩
    · obtain ⟨sp_g, sp', hcont, hws, -, hcorr'⟩ :=
        L4YAML.Proofs.StreamAccum.dispatchContent_plainScalar_content_prod_at n s_ad sp_prep hcorr hpeek
          h_amp h_star h_bang h_pipe h_gt hdq hsq h_not_doc h_dispatch h_flow hn
      subst hsp_prep
      exact ⟨sp_g, sp', TFlowContent.of_scalar hcont hlb hlc, hws, hcorr'⟩

/-! ## §5 The receive's premises, replayed from the core's inputs (item 487)

`accum_step_content_core` derives `h_tail` / `h_lead` (and, under a held run, the run and its
separator) inside its proof from `h_interior` at `(sc, sp_scan)`, the preprocess and the structural
`none`; the twins above take them at `(s_ad, sp_prep)`.  This lemma is that derivation, stated once,
from the wrapper's hypotheses (the public lemmas the core uses; no `StreamAccum` edit). -/

/-- The flow receive's premises at the dispatch state, from the interior at the pre-state. -/
inductive ContentLead (sc : ScannerState) (tl : FrameTail) (sp_flow sp_prep : SurfPos) : Prop where
  | white
      (h_tail : ∀ kj, tl ≠ .value kj)
      (h_lead : ∀ m, m ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf sc →
        SSeparateLines m sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.leadFree)) :
      ContentLead sc tl sp_flow sp_prep
  | props (ha ht : Bool) (sp_p sp_e : SurfPos)
      (h_tail : ∀ kj, tl ≠ .value kj)
      (h_lead : ∀ m, m ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf sc →
        SSeparateLines m sp_flow sp_p ∨ (sp_p = sp_flow ∧ tl.leadFree))
      (h_run : ∀ m, m ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf sc →
        L4YAML.Proofs.StreamAccum.PropsRun m (inFlowCtx .flowOut) ha ht sp_p sp_e)
      (h_sep : ∀ m, m ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf sc →
        SSeparate m (inFlowCtx .flowOut) sp_e sp_prep)
      (h_last : ∃ t, L4YAML.Scanner.lastRealTokenVal? sc.tokens = some t ∧
        t.isNodeProperty = true) :
      ContentLead sc tl sp_flow sp_prep

/-- The frame tail rides the preprocess inside a flow: `tailOf` reads `frameTokenVal?` and
    `jsonKeyBefore`, both preserved (and the `allowDirectives` update keeps the tokens). -/
lemma tailOf_preprocess_eq {sc s_prep s_ad : ScannerState} {c : Char}
    (h_flow : 0 < sc.flowLevel)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_ad_tokens : s_ad.tokens = s_prep.tokens) :
    tailOf s_ad.tokens = tailOf sc.tokens := by
  unfold L4YAML.Proofs.StreamAccum.tailOf
  rw [h_ad_tokens,
    L4YAML.Proofs.StreamAccum.preprocess_preserves_frameTokenVal_inFlow sc s_prep c h_flow h_preprocess,
    L4YAML.Proofs.StreamAccum.preprocess_preserves_jsonKeyBefore_inFlow sc s_prep c h_flow h_preprocess]

/-- The replay: `accum_step_content_core`'s derivation of the receive's premises, from the
    wrapper's hypotheses.  `s_ad` is the dispatch state (`s_prep` with `allowDirectives` cleared);
    the two `h_ad_*` equalities are `split <;> rfl` at the caller. -/
lemma contentLead_of_interior {sc s_prep s_ad s' : ScannerState} {c : Char} {d : Nat}
    {sp_flow sp_scan sp_prep : SurfPos}
    (hd : sc.flowLevel = d + 1)
    (h_corr : ScannerSurfCorr sc sp_scan) (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_str_none : scanNextToken_dispatchStructural s_prep c = .ok none)
    (h_ad_tokens : s_ad.tokens = s_prep.tokens)
    (h_ad_fl : s_ad.flowLevel = s_prep.flowLevel)
    (h_flow_none : scanNextToken_dispatchFlowIndicators s_ad c = .ok none)
    (h_blk_none : scanNextToken_dispatchBlockIndicators s_ad c = .ok none)
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s')
    (h_gap : L4YAML.Proofs.StreamAccum.InteriorGap sc (tailOf sc.tokens) sp_flow sp_scan)
    (h_real : L4YAML.Proofs.FlowAdjacency.LastTokenReal sc.tokens) :
    ContentLead sc (tailOf sc.tokens) sp_flow sp_prep := by
  open L4YAML.Proofs.StreamAccum in
  have h_sc_inflow : sc.inFlow = true := inFlow_of_flowLevel_eq hd
  have h_prep_fl : s_prep.flowLevel = sc.flowLevel :=
    L4YAML.Proofs.FlowSync.preprocess_preserves_flowLevel sc s_prep c h_preprocess
  have h_ad_inflow : s_ad.inFlow = true := by
    unfold ScannerState.inFlow; rw [h_ad_fl, h_prep_fl, hd]; simp
  have hpeek_prep : s_prep.peek? = some c := L4YAML.Proofs.StreamAccum.preprocess_some_peek h_preprocess
  have h_lead_from : ∀ {sp_g : SurfPos}, GStar SSWhite sp_g sp_scan →
      (sp_g = sp_scan → sc.col ≠ 0 → ¬ (L4YAML.Proofs.ScannerCoupling.CommentOk sc ∧ sc.peek? = some '#')) →
      ∀ m : Nat, (SSeparateLines m sp_g sp_prep ∨ (sp_prep = sp_scan ∧ sp_g = sp_scan)) ∨
        ¬ (m ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf sc) :=
    fun h_trail h_gate m =>
      L4YAML.Proofs.StreamAccum.SSeparateLines_at_interior m h_sc_inflow
        (L4YAML.Proofs.StreamAccum.InteriorGap.col_pos h_gap)
        (L4YAML.Proofs.StreamAccum.content_ne_comment h_dispatch) h_corr h_trail h_gate hcorr_prep
        h_preprocess h_str_none
  have h_peek : sp_prep = sp_scan → sc.peek? = some c := fun heq =>
    L4YAML.Proofs.StreamAccum.peek_of_corr_pair h_corr hcorr_prep heq hpeek_prep
  have h_glue := L4YAML.Proofs.StreamAccum.content_not_glue h_dispatch
  cases h_gap with
  | white h_ws h_sync h_colon h_col0 h_gate h_free h_q =>
    have h_tail : ∀ kj, tailOf sc.tokens ≠ .value kj := by
      have h_tl_eq := tailOf_preprocess_eq (by omega) h_preprocess h_ad_tokens
      rw [← h_tl_eq]
      have h_ad_sync : L4YAML.Proofs.StreamAccum.frameTokenVal? s_ad.tokens =
          L4YAML.Scanner.lastRealTokenVal? s_ad.tokens := by
        rw [h_ad_tokens]
        exact L4YAML.Proofs.StreamAccum.preprocess_preserves_sync_inFlow (by omega) h_real h_preprocess h_sync
      obtain ⟨-, hne_rb, -, hne_rc, hne_comma⟩ :=
        L4YAML.Proofs.StreamAccum.not_flow_indicator_of_dispatch_none h_flow_none
      have h_adj : scanNextToken_checkFlowAdjacency s_ad c = .ok () := by
        have h' := h_flow_none
        unfold scanNextToken_dispatchFlowIndicators at h'
        exact L4YAML.Proofs.FlowAdjacency.flowAdj_ok_of_dispatch_ok h'
      exact L4YAML.Proofs.StreamAccum.tailOf_ne_value h_ad_sync
        (L4YAML.Proofs.FlowAdjacency.notCompletes_of_checkFlowAdjacency_ok_nodeStart h_adj h_ad_inflow
          ⟨hne_comma, hne_rb, hne_rc⟩
          (L4YAML.Proofs.StreamAccum.not_valueCandidate_of_dispatch_none h_blk_none))
    refine .white h_tail (fun m hm => ?_)
    have h_at := (h_lead_from h_ws h_gate m).resolve_right (fun h => h hm)
    exact L4YAML.Proofs.StreamAccum.lead_of_white_gap h_free h_peek
      (L4YAML.Proofs.StreamAccum.not_glue_weaken h_glue) h_at
  | props ha ht sp_p h_tail h_lead h_run h_anchor h_tag h_colon h_gate h_next h_q h_some =>
    have h_lead_at := h_lead_from (GStar.nil _) (fun _ => h_gate)
    refine .props ha ht sp_p sp_scan h_tail (fun m hm => (h_lead m).resolve_right (fun h => h hm))
      (fun m hm => (h_run m).resolve_right (fun h => h hm)) (fun m hm => ?_)
      (by rcases ((h_run 0).resolve_right (fun h => h (Nat.zero_le _))).some_half with h | h
          · exact L4YAML.Proofs.StreamAccum.lastReal_isProperty_of_run (h_anchor h)
          · exact L4YAML.Proofs.StreamAccum.lastReal_isProperty_of_run (h_tag h))
    rcases (h_lead_at m).resolve_right (fun h => h hm) with h | ⟨h1, -⟩
    · exact h
    · exact absurd (L4YAML.Proofs.StreamAccum.NextIsSep.not_content h_next (h_peek h1) h_glue) id


/-! ## §6 The K caller — the content step on the T flow stack (item 487)

At depth ≥ 1, from `accum_step_content`'s inputs and the T stack at the pre-state: the value arms
land the T stack at `s'` through `_in` / `_in_props`, the property arms keep it (tail and trace
unchanged), the lead replayed by `contentLead_of_interior`.  Depth 0 is `_out`'s business. -/

/-- A property arm (`&` / `!`) keeps the frame tail: the pushed token is a node property. -/
lemma content_prop_tail_kept {s_ad s' : ScannerState} {c : Char} {sp_prep : SurfPos}
    (hcorr : ScannerSurfCorr s_ad sp_prep) (hpeek : s_ad.peek? = some c)
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s')
    (hc : c = '&' ∨ c = '!') :
    tailOf s'.tokens = tailOf s_ad.tokens := by
  rcases hc with hc | hc <;> subst hc
  · obtain ⟨-, name, htok, -, -⟩ := dispatchContent_anchor_trace s_ad sp_prep hcorr hpeek s' h_dispatch
    rw [htok]; exact (tailOf_push_prop (by simp) (by simp [YamlToken.isNodeProperty])).1
  · obtain ⟨-, handle, suffix, htok, -, -⟩ := dispatchContent_tag_trace s_ad sp_prep hcorr hpeek s' h_dispatch
    rw [htok]; exact (tailOf_push_prop (by simp) (by simp [YamlToken.isNodeProperty])).1

/-- The content step's T twin at the stack level: the S inputs of `accum_step_content` (restricted
    to what the receive reads) and the T stack at `sc` give the T stack at `s'`. -/
lemma accum_step_content_traceK {n d : Nat} {km : Array Bool} {sc s_prep s' : ScannerState} {c : Char}
    {sp_block sp_flow sp_scan : SurfPos} {ev : List Event}
    (hd : sc.flowLevel = d + 1)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_str_none : scanNextToken_dispatchStructural s_prep c = .ok none)
    (h_flow_none : scanNextToken_dispatchFlowIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok none)
    (h_blk_none : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok none)
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s')
    (h_not_doc : (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep).col = 0 →
      atDocumentBoundary (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) = false)
    (h_gap : L4YAML.Proofs.StreamAccum.InteriorGap sc (tailOf sc.tokens) sp_flow sp_scan)
    (h_real : L4YAML.Proofs.FlowAdjacency.LastTokenReal sc.tokens)
    (hT : TFlowStackB n sc.flowLevel sc.flowStack km (tailOf sc.tokens) sp_block sp_flow ev)
    (hn : n ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf sc) :
    ∃ ev_n sp_prep sp_a,
      ScannerSurfCorr (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) sp_prep ∧
      ContentArm (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) s' c sp_prep sp_a ∧
      ((∃ kj sp_ne, tailOf s'.tokens = .value kj ∧ (c ≠ '&' ∧ c ≠ '!') ∧ GStar SSWhite sp_ne sp_a ∧
          SFlowNode n .flowIn sp_prep sp_ne ∧
          TFlowStackB n s'.flowLevel s'.flowStack km (tailOf s'.tokens) sp_block sp_ne (ev ++ ev_n)) ∨
       (tailOf s'.tokens = tailOf sc.tokens ∧ (c = '&' ∨ c = '!') ∧
          TFlowStackB n s'.flowLevel s'.flowStack km (tailOf s'.tokens) sp_block sp_flow ev)) := by
  -- The dispatch state and its projections.
  generalize h_ad_def : (if s_prep.allowDirectives then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep) = s_ad at h_flow_none h_blk_none h_dispatch h_not_doc ⊢
  have h_ad_tokens : s_ad.tokens = s_prep.tokens := by rw [← h_ad_def]; split <;> rfl
  have h_ad_peek : s_ad.peek? = s_prep.peek? := by rw [← h_ad_def]; split <;> rfl
  have h_ad_fl : s_ad.flowLevel = s_prep.flowLevel := by rw [← h_ad_def]; split <;> rfl
  have h_ad_fs : s_ad.flowStack = s_prep.flowStack := by rw [← h_ad_def]; split <;> rfl
  have h_ad_ind : s_ad.indents = s_prep.indents := by rw [← h_ad_def]; split <;> rfl
  have h_ad_col : s_ad.col = s_prep.col := by rw [← h_ad_def]; split <;> rfl
  have h_sc_inflow : sc.inFlow = true := L4YAML.Proofs.StreamAccum.inFlow_of_flowLevel_eq hd
  have h_prep_fl : s_prep.flowLevel = sc.flowLevel :=
    L4YAML.Proofs.FlowSync.preprocess_preserves_flowLevel sc s_prep c h_preprocess
  have h_prep_fs : s_prep.flowStack = sc.flowStack :=
    L4YAML.Proofs.ScannerFlowStack.preprocess_preserves_flowStack sc s_prep c h_preprocess
  have h_prep_ind : s_prep.indents = sc.indents :=
    L4YAML.Proofs.FlowIndentStable.preprocess_indents_of_inFlow h_sc_inflow h_preprocess
  have h_prep_inflow : s_prep.inFlow = true := by
    unfold ScannerState.inFlow; rw [h_prep_fl, hd]; simp
  have h_ad_inflow : s_ad.inFlow = true := by
    unfold ScannerState.inFlow; rw [h_ad_fl, h_prep_fl, hd]; simp
  have hpeek : s_ad.peek? = some c :=
    h_ad_peek.trans (L4YAML.Proofs.StreamAccum.preprocess_some_peek h_preprocess)
  obtain ⟨sp_prep, hcorr_prep⟩ :=
    L4YAML.Proofs.ScanStrictCoupling.scanNextToken_preprocess_corr sc sp_scan h_corr s_prep c h_preprocess
  have hcorr_ad : ScannerSurfCorr s_ad sp_prep := by
    rw [← h_ad_def]; exact L4YAML.Proofs.StreamAccum.corr_of_allowDirectives_update hcorr_prep
  have hcol : s_ad.currentIndent < (s_ad.col : Int) := by
    rw [h_ad_col, L4YAML.Proofs.PreprocessIndentStable.currentIndent_of_indents_eq h_ad_ind]
    exact L4YAML.Proofs.FlowIndentStable.structural_none_col_gt_of_inFlow h_prep_inflow h_str_none
  have hn' : (n : Int) ≤ max 0 (s_ad.currentIndent + 1) := by
    rw [L4YAML.Proofs.PreprocessIndentStable.currentIndent_of_indents_eq (h_ad_ind.trans h_prep_ind)]
    unfold L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf at hn
    omega
  have h_tl_eq : tailOf s_ad.tokens = tailOf sc.tokens :=
    tailOf_preprocess_eq (by omega) h_preprocess h_ad_tokens
  -- The post-state's flow indices are the pre-state's.
  have h_fl' : s'.flowLevel = sc.flowLevel :=
    (L4YAML.Proofs.ScannerCorrectness.dispatchContent_preserves_flowLevel s_ad c s' h_dispatch).trans
      (h_ad_fl.trans h_prep_fl)
  have h_fs' : s'.flowStack = sc.flowStack :=
    (L4YAML.Proofs.ScannerFlowStack.dispatchContent_preserves_flowStack s_ad c s' h_dispatch).trans
      (h_ad_fs.trans h_prep_fs)
  obtain ⟨sp_a, arm⟩ :=
    L4YAML.Proofs.StreamAccum.contentArm_of_dispatch s_ad sp_prep c hcorr_ad hpeek h_not_doc (fun _ => hcol) h_dispatch
  have h_lead := contentLead_of_interior hd h_corr hcorr_prep h_preprocess h_str_none h_ad_tokens
    h_ad_fl h_flow_none h_blk_none h_dispatch h_gap h_real
  -- The T stack at depth ≥ 1 is open.
  rw [hd] at hT
  rcases hT with _ | ⟨_, _, _, _, _, _, _, h_fos⟩
  rw [h_fl', h_fs', hd]
  have h_fos' := h_fos
  rw [← h_tl_eq] at h_fos'
  by_cases hprop : c = '&' ∨ c = '!'
  · -- Property arms keep the tail and the trace.
    have h_kept := content_prop_tail_kept hcorr_ad hpeek h_dispatch hprop
    refine ⟨[], sp_prep, sp_a, hcorr_ad, arm, Or.inr ⟨h_kept.trans h_tl_eq, hprop, ?_⟩⟩
    rw [h_kept]; exact .«open» _ _ _ _ _ _ _ h_fos'
  · have hamp : c ≠ '&' := fun h => hprop (Or.inl h)
    have hbang : c ≠ '!' := fun h => hprop (Or.inr h)
    cases h_lead with
    | white h_tail h_lead =>
      obtain ⟨ev_n, -, h | ⟨-, h⟩⟩ := accum_step_content_trace_in arm hcorr_ad hpeek h_ad_inflow h_not_doc
        h_dispatch hcol hn' h_fos' (by rw [h_tl_eq]; exact h_tail)
        (by rw [h_tl_eq]; exact h_lead n hn)
      · obtain ⟨kj, sp_ne, h_tl', h_ws, h_nd, h_open, -⟩ := h
        exact ⟨ev_n, sp_prep, sp_a, hcorr_ad, arm, Or.inl ⟨kj, sp_ne, h_tl', ⟨hamp, hbang⟩, h_ws, h_nd, by
          rw [h_tl']; exact .«open» _ _ _ _ _ _ _ h_open⟩⟩
      · rcases h with ⟨hc, -⟩ | ⟨hc, -⟩
        · exact absurd hc hamp
        · exact absurd hc hbang
    | props ha ht sp_p sp_e h_tail h_lead_p h_run h_sep h_last_sc =>
      have hstar : c ≠ '*' := by
        intro hc; subst hc
        have h_false := L4YAML.Proofs.StreamAccum.lastTokenIsNodeProperty_false_of_dispatch h_dispatch
        obtain ⟨t, h_last, h_prop⟩ := h_last_sc
        have h_ad_last : L4YAML.Scanner.lastRealTokenVal? s_ad.tokens =
            L4YAML.Scanner.lastRealTokenVal? sc.tokens := by
          rw [h_ad_tokens]
          exact L4YAML.Proofs.StreamAccum.preprocess_preserves_lastRealTokenVal_inFlow sc s_prep _
            (by omega) h_real h_preprocess
        unfold lastTokenIsNodeProperty at h_false
        rw [h_ad_inflow, h_ad_last, h_last] at h_false
        simp [h_prop] at h_false
      obtain ⟨ev_p, h_props⟩ := L4YAML.Proofs.Serialization.TraceOf.FlowWalk.PropsRun.toT (h_run n hn)
      obtain ⟨kj, sp_ne, -, h_tl', h_ws, h_nd, h_open, -⟩ := accum_step_content_trace_in_props arm hcorr_ad hpeek
        h_ad_inflow h_not_doc h_dispatch hcol hn' h_fos' (by rw [h_tl_eq]; exact h_tail)
        (by rw [h_tl_eq]; exact h_lead_p n hn) h_props (h_sep n hn) ⟨hamp, hbang, hstar⟩
      exact ⟨ev_p ++ [], sp_prep, sp_a, hcorr_ad, arm, Or.inl ⟨kj, sp_ne, h_tl', ⟨hamp, hbang⟩, h_ws, h_nd, by
        rw [h_tl']; exact .«open» _ _ _ _ _ _ _ h_open⟩⟩

end

end L4YAML.Proofs.Serialization.TraceOf.ContentBridge

/-! ## §7 The plain landing is floor-independent (item 488, review round 2)

`ContentArm.plainIn`'s landing is per floor (`∀ n, … → ∃ sp_gram`); `TFlowStackK`'s `∀`-floor T half
needs one.  Two plain ends from one start with white runs to one `sp'` coincide: a plain's last
character is not white, so neither end can sit inside the other's trailing run.  P116 is the shadow. -/

namespace L4YAML.Proofs.Serialization.TraceOf.ContentBridge

open L4YAML L4YAML.Surface L4YAML.CharPredicates

public section

/-- "The last character consumed between `s` and `e` is not white." -/
def LastNonWhite (s e : SurfPos) : Prop :=
  ∃ pre ch, s.chars = pre ++ ch :: e.chars ∧ isWhiteSpaceBool ch = false

lemma SSWhite_chars {s e : SurfPos} (h : SSWhite s e) :
    ∃ ch, s.chars = ch :: e.chars ∧ isWhiteSpaceBool ch = true ∧ e.col = s.col + 1 := by
  cases h with
  | space => exact ⟨' ', rfl, by decide, rfl⟩
  | tab => exact ⟨'\t', rfl, by decide, rfl⟩

lemma GStar_SSWhite_chars' {s e : SurfPos} (h : GStar SSWhite s e) :
    ∃ ws : List Char, s.chars = ws ++ e.chars ∧ (∀ c ∈ ws, isWhiteSpaceBool c = true) ∧
      e.col = s.col + ws.length := by
  induction h with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons s₁ s₂ s₃ h₁ _ ih =>
    obtain ⟨ch, hch, hw, hcol⟩ := SSWhite_chars h₁
    obtain ⟨ws, hws, hall, hcol'⟩ := ih
    refine ⟨ch :: ws, by rw [hch, hws]; rfl, ?_, by simp [hcol', hcol]; omega⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hw
    · exact hall c hc

lemma lastNonWhite_pre {s s₁ e : SurfPos} (hpre : s₁.chars <:+ s.chars)
    (h : LastNonWhite s₁ e) : LastNonWhite s e := by
  obtain ⟨p, hp⟩ := hpre
  obtain ⟨pre, ch, hpre, hnw⟩ := h
  exact ⟨p ++ pre, ch, by rw [← hp, hpre, List.append_assoc], hnw⟩

lemma GStar_SSWhite_suffix {s e : SurfPos} (h : GStar SSWhite s e) : e.chars <:+ s.chars := by
  obtain ⟨ws, hws, _, _⟩ := GStar_SSWhite_chars' h
  exact ⟨ws, hws.symm⟩

lemma lastNonWhite_white_pre {s s₁ e : SurfPos} (hw : GStar SSWhite s s₁) (h : LastNonWhite s₁ e) :
    LastNonWhite s e :=
  lastNonWhite_pre (GStar_SSWhite_suffix hw) h

lemma lastNonWhite_suffix {s e : SurfPos} (h : LastNonWhite s e) : e.chars <:+ s.chars := by
  obtain ⟨pre, ch, hpre, _⟩ := h
  exact ⟨pre ++ [ch], by rw [hpre, List.append_assoc]; rfl⟩

lemma isNsPlainSafe_not_white {c : YamlContext} {ch : Char} (h : isNsPlainSafe c ch) :
    isWhiteSpaceBool ch = false := by
  have hns : isNsChar ch := by
    cases c <;> simp only [isNsPlainSafe] at h <;> first | exact h | exact h.1
  cases hw : isWhiteSpaceBool ch
  · rfl
  · exact absurd hns (L4YAML.Proofs.Serialization.TraceOf.DocBridge.not_isNsChar_of_white ch hw)

lemma SNsPlainChar_last {c : YamlContext} {s e : SurfPos} (h : SNsPlainChar c s e) :
    LastNonWhite s e := by
  cases h with
  | safe => rename_i ch rest col hSafe _ _; exact ⟨[], ch, rfl, isNsPlainSafe_not_white hSafe⟩
  | colonSafe => exact ⟨[], ':', rfl, by decide⟩

lemma SNsPlainFirst_last {c : YamlContext} {s e : SurfPos} (h : SNsPlainFirst c s e) :
    LastNonWhite s e := by
  cases h with
  | nonIndicator => rename_i ch rest col hSafe _; exact ⟨[], ch, rfl, isNsPlainSafe_not_white hSafe⟩
  | dashSafe => exact ⟨[], '-', rfl, by decide⟩
  | colonSafe => exact ⟨[], ':', rfl, by decide⟩
  | questionSafe => exact ⟨[], '?', rfl, by decide⟩

lemma SNbNsPlainInLineEntry_last {c : YamlContext} {s e : SurfPos}
    (h : SNbNsPlainInLineEntry c s e) : LastNonWhite s e := by
  cases h with
  | mk => rename_i s₁ hw hch; exact lastNonWhite_white_pre hw (SNsPlainChar_last hch)
  | hash => rename_i hl; cases hl; exact ⟨[], '#', rfl, by decide⟩

/-- A run of entries: empty, or its last entry's last character is not white. -/
lemma GStar_entries_last {c : YamlContext} {s e : SurfPos}
    (h : GStar (SNbNsPlainInLineEntry c) s e) : s = e ∨ LastNonWhite s e := by
  induction h with
  | nil => exact Or.inl rfl
  | cons s₁ s₂ s₃ h₁ _ ih =>
    right
    rcases ih with rfl | hl
    · exact SNbNsPlainInLineEntry_last h₁
    · exact lastNonWhite_pre (lastNonWhite_suffix (SNbNsPlainInLineEntry_last h₁)) hl

lemma SNsPlainOneLine_last {c : YamlContext} {s e : SurfPos} (h : SNsPlainOneLine c s e) :
    LastNonWhite s e := by
  cases h
  rename_i s₁ hf hes
  rcases GStar_entries_last hes with rfl | hl
  · exact SNsPlainFirst_last hf
  · exact lastNonWhite_pre (lastNonWhite_suffix (SNsPlainFirst_last hf)) hl

/-! The line-folding prefix of a continuation line only consumes characters. -/

lemma SIndent_suffix {n : Nat} {s e : SurfPos} (h : SIndent n s e) : e.chars <:+ s.chars := by
  induction h with
  | zero => exact List.suffix_refl _
  | succ n rest col s' _ ih => exact ih.trans (List.suffix_cons ' ' rest)

lemma SSeparateInLine_suffix {s e : SurfPos} (h : SSeparateInLine s e) : e.chars <:+ s.chars := by
  cases h with
  | whites =>
    rename_i hp
    cases hp
    rename_i mid h₁ hs
    exact (GStar_SSWhite_suffix hs).trans (GStar_SSWhite_suffix (GStar.cons _ _ _ h₁ (GStar.nil _)))
  | startOfLine => exact List.suffix_refl _

lemma GOpt_suffix {P : SurfPos → SurfPos → Prop} (hP : ∀ {a b}, P a b → b.chars <:+ a.chars)
    {s e : SurfPos} (h : GOpt P s e) : e.chars <:+ s.chars := by
  cases h with
  | none => exact List.suffix_refl _
  | some => rename_i hp; exact hP hp

lemma SFlowLinePrefix_suffix {n : Nat} {s e : SurfPos} (h : SFlowLinePrefix n s e) :
    e.chars <:+ s.chars := by
  cases h
  rename_i s₁ hi ho
  exact (GOpt_suffix SSeparateInLine_suffix ho).trans (SIndent_suffix hi)

lemma SLEmpty_flowIn_suffix {n : Nat} {s e : SurfPos} (h : SLEmpty n .flowIn s e) :
    e.chars <:+ s.chars := by
  cases h with
  | block => rename_i hc _ _; rcases hc with hc | hc <;> cases hc
  | flow =>
    rename_i s₁ _ ho hb
    exact (L4YAML.Proofs.SurfaceSpan.sbBreak_suffix hb).trans (GOpt_suffix SFlowLinePrefix_suffix ho)
  | flowLt =>
    rename_i s₁ _ hlt hb
    obtain ⟨m, _, hi⟩ := hlt
    exact (L4YAML.Proofs.SurfaceSpan.sbBreak_suffix hb).trans (SIndent_suffix hi)

lemma GStar_SLEmpty_flowIn_suffix {n : Nat} {s e : SurfPos} (h : GStar (SLEmpty n .flowIn) s e) :
    e.chars <:+ s.chars := by
  induction h with
  | nil => exact List.suffix_refl _
  | cons s₁ s₂ s₃ h₁ _ ih => exact ih.trans (SLEmpty_flowIn_suffix h₁)

lemma SSNsPlainNextLine_last {n : Nat} {c : YamlContext} {s e : SurfPos}
    (h : SSNsPlainNextLine n c s e) : LastNonWhite s e := by
  cases h
  rename_i s_ws s₁ s₂ s₃ s₄ hws hbr hemp hpref hch hes
  have hpre : s₃.chars <:+ s.chars :=
    (((SFlowLinePrefix_suffix hpref).trans (GStar_SLEmpty_flowIn_suffix hemp)).trans
      (L4YAML.Proofs.SurfaceSpan.sbBreak_suffix hbr)).trans (GStar_SSWhite_suffix hws)
  rcases GStar_entries_last hes with rfl | hl
  · exact lastNonWhite_pre hpre (SNsPlainChar_last hch)
  · exact lastNonWhite_pre hpre (lastNonWhite_pre (lastNonWhite_suffix (SNsPlainChar_last hch)) hl)

lemma SNsPlainMultiLine_last {n : Nat} {c : YamlContext} {s e : SurfPos}
    (h : SNsPlainMultiLine n c s e) : LastNonWhite s e := by
  cases h
  rename_i s₁ hone hnext
  suffices H : ∀ {a b : SurfPos}, GStar (SSNsPlainNextLine n c) a b → LastNonWhite s a →
      LastNonWhite s b from H hnext (SNsPlainOneLine_last hone)
  intro a b hab hsa
  induction hab with
  | nil => exact hsa
  | cons a₁ a₂ a₃ h₁ _ ih =>
    exact ih (lastNonWhite_pre (lastNonWhite_suffix hsa) (SSNsPlainNextLine_last h₁))

/-- A plain scalar's last character is not white (flow contexts). -/
lemma SNsPlain_last_not_white {n : Nat} {c : YamlContext} {s e : SurfPos}
    (hc : c = .flowIn ∨ c = .flowOut) (h : SNsPlain n c s e) : LastNonWhite s e := by
  rcases hc with rfl | rfl <;> exact SNsPlainMultiLine_last h


/-- The maximal white suffix, read off the reversed list: a white run followed by a non-white
    character is exactly what `takeWhile` keeps. -/
lemma takeWhile_white_run (ws : List Char) (hw : ∀ c ∈ ws, isWhiteSpaceBool c = true)
    (ch : Char) (hc : isWhiteSpaceBool ch = false) (rest : List Char) :
    (ws ++ ch :: rest).takeWhile isWhiteSpaceBool = ws := by
  induction ws with
  | nil => simp [hc]
  | cons x t ih =>
    have hx := hw x (by simp)
    simp [hx, ih (fun c hc => hw c (by simp [hc]))]

/-- Two plain ends from one start with white runs to one `sp'` coincide: neither can sit inside the
    other's trailing white, because a plain's last character is not white. -/
lemma lastNonWhite_white_eq {s a b sp' : SurfPos}
    (ha : LastNonWhite s a) (hb : LastNonWhite s b)
    (wa : GStar SSWhite a sp') (wb : GStar SSWhite b sp') : a = b := by
  obtain ⟨pa, cha, hpa, hna⟩ := ha
  obtain ⟨pb, chb, hpb, hnb⟩ := hb
  obtain ⟨wsa, hwsa, halla, hcola⟩ := GStar_SSWhite_chars' wa
  obtain ⟨wsb, hwsb, hallb, hcolb⟩ := GStar_SSWhite_chars' wb
  have key : pa ++ cha :: wsa = pb ++ chb :: wsb := by
    have h1 : s.chars = (pa ++ cha :: wsa) ++ sp'.chars := by rw [hpa, hwsa]; simp
    have h2 : s.chars = (pb ++ chb :: wsb) ++ sp'.chars := by rw [hpb, hwsb]; simp
    exact List.append_cancel_right (h1.symm.trans h2)
  have hrev := congrArg (fun l : List Char => l.reverse.takeWhile isWhiteSpaceBool) key
  simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append] at hrev
  rw [takeWhile_white_run wsa.reverse (fun c hc => halla c (List.mem_reverse.mp hc)) cha hna,
    takeWhile_white_run wsb.reverse (fun c hc => hallb c (List.mem_reverse.mp hc)) chb hnb] at hrev
  have hws : wsa = wsb := List.reverse_inj.mp hrev
  subst hws
  have hchars : a.chars = b.chars := hwsa.trans hwsb.symm
  have hcol : a.col = b.col := by omega
  cases a; cases b
  simp only at hchars hcol
  rw [hchars, hcol]

/-- `ContentArm.plainIn`'s per-floor landings are one landing: from the arm's `h_node` at every
    floor, one `sp_gram` serving every floor (the witness at floor 0, transported by
    `lastNonWhite_white_eq`).  The uniformity `TFlowStackK`'s `∀`-floor T half needs (item 488). -/
lemma plainIn_landing_uniform {sc s' : L4YAML.Scanner.ScannerState} {ch : Char} {rest : List Char}
    {col : Nat} {sp' : SurfPos}
    (hc : ch ≠ '&' ∧ ch ≠ '*' ∧ ch ≠ '!' ∧ ch ≠ '[' ∧ ch ≠ '{' ∧ ch ≠ '"' ∧ ch ≠ '\'')
    (h_node : ∀ n : Nat, (n : Int) ≤ max 0 (sc.currentIndent + 1) →
      ∃ sp_gram, SFlowNode n .flowIn ⟨ch :: rest, col⟩ sp_gram ∧ GStar SSWhite sp_gram sp' ∧
        (sp_gram = sp' → s'.col ≠ 0 → ¬ (L4YAML.Proofs.ScannerCoupling.CommentOk s' ∧ s'.peek? = some '#'))) :
    ∃ sp_gram, ∀ n : Nat, (n : Int) ≤ max 0 (sc.currentIndent + 1) →
      SFlowNode n .flowIn ⟨ch :: rest, col⟩ sp_gram ∧ GStar SSWhite sp_gram sp' ∧
        (sp_gram = sp' → s'.col ≠ 0 → ¬ (L4YAML.Proofs.ScannerCoupling.CommentOk s' ∧ s'.peek? = some '#')) := by
  obtain ⟨g0, hn0, hw0, hg0⟩ := h_node 0 (by omega)
  refine ⟨g0, fun n hn => ?_⟩
  obtain ⟨gn, hnn, hwn, hgn⟩ := h_node n hn
  have hplain : ∀ {m : Nat} {g : SurfPos}, SFlowNode m .flowIn ⟨ch :: rest, col⟩ g → LastNonWhite ⟨ch :: rest, col⟩ g := by
    intro m g hg
    rcases SFlowNode_head_lift hg ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1⟩ with
      ⟨_, _, hp⟩ | ⟨hq, _⟩ | ⟨hq, _⟩
    · exact SNsPlain_last_not_white (Or.inl rfl) hp
    · exact absurd hq hc.2.2.2.2.2.1
    · exact absurd hq hc.2.2.2.2.2.2
  have heq : gn = g0 := lastNonWhite_white_eq (hplain hnn) (hplain hn0) hwn hw0
  subst heq
  exact ⟨hnn, hwn, hgn⟩

/-! ## §8 The landing agreement (item 489)

After a value arm the wrapper's S landing (the core's `sp_ne`) and the T landing (the arm's
`sp_gram`) are both flow-node ends from `sp_prep` with white runs to the one scan position.  Every
value node — plain, quoted, alias — ends in a non-white character (the quote, the last anchor
character, the plain's last `ns-char`), so `lastNonWhite_white_eq` identifies them.  P117 is the
shadow. -/

lemma GLit_last {ch : Char} {s e : SurfPos} (h : GLit ch s e) (hw : isWhiteSpaceBool ch = false) :
    LastNonWhite s e := by
  cases h; exact ⟨[], ch, rfl, hw⟩

lemma GChar_last {p : Char → Prop} (hp : ∀ ch, p ch → isWhiteSpaceBool ch = false)
    {s e : SurfPos} (h : GChar p s e) : LastNonWhite s e := by
  cases h; rename_i ch rest col hch; exact ⟨[], ch, rfl, hp ch hch⟩

lemma GPlus_GChar_last {p : Char → Prop} (hp : ∀ ch, p ch → isWhiteSpaceBool ch = false)
    {s e : SurfPos} (h : GPlus (GChar p) s e) : LastNonWhite s e := by
  match h with
  | .mk _ _ _ h₁ hs =>
    suffices H : ∀ {a b : SurfPos}, GStar (GChar p) a b → LastNonWhite s a → LastNonWhite s b from
      H hs (GChar_last hp h₁)
    intro a b hab hsa
    induction hab with
    | nil => exact hsa
    | cons a₁ a₂ a₃ h₁ _ ih =>
      exact ih (lastNonWhite_pre (lastNonWhite_suffix hsa) (GChar_last hp h₁))

lemma isNsAnchorChar_not_white {ch : Char} (h : isNsAnchorChar ch) : isWhiteSpaceBool ch = false := by
  cases hw : isWhiteSpaceBool ch
  · rfl
  · exact absurd h.1 (L4YAML.Proofs.Serialization.TraceOf.DocBridge.not_isNsChar_of_white ch hw)

lemma SCNsAliasNode_last {s e : SurfPos} (h : SCNsAliasNode s e) : LastNonWhite s e := by
  match h with
  | .mk rest _ _ hp _ =>
    exact lastNonWhite_pre (List.suffix_cons '*' rest)
      (GPlus_GChar_last (fun _ h => isNsAnchorChar_not_white h) hp)

lemma SCDoubleQuoted_last {n : Nat} {c : YamlContext} {s e : SurfPos} (h : SCDoubleQuoted n c s e) :
    LastNonWhite s e := by
  match h with
  | .mk _ _ _ _ _ _ hq1 ht hq2 =>
    exact lastNonWhite_pre
      ((L4YAML.Proofs.SurfaceSpan.snbDoubleText_suffix ht).trans (L4YAML.Proofs.SurfaceSpan.glit_suffix hq1))
      (GLit_last hq2 (by decide))

lemma SCSingleQuoted_last {n : Nat} {c : YamlContext} {s e : SurfPos} (h : SCSingleQuoted n c s e) :
    LastNonWhite s e := by
  match h with
  | .mk _ _ _ _ _ _ hq1 ht hq2 =>
    exact lastNonWhite_pre
      ((L4YAML.Proofs.SurfaceSpan.snbSingleText_suffix ht).trans (L4YAML.Proofs.SurfaceSpan.glit_suffix hq1))
      (GLit_last hq2 (by decide))

/-- A value node (not a property run, not a bracketed collection) ends in a non-white character. -/
lemma SFlowNode_value_last {n : Nat} {ch : Char} {rest : List Char} {col : Nat} {m : SurfPos}
    (h : SFlowNode n .flowIn ⟨ch :: rest, col⟩ m)
    (hc : ch ≠ '&' ∧ ch ≠ '!' ∧ ch ≠ '[' ∧ ch ≠ '{') : LastNonWhite ⟨ch :: rest, col⟩ m := by
  obtain ⟨h_amp, h_bang, h_lb, h_lc⟩ := hc
  by_cases hstar : ch = '*'
  · subst hstar
    cases h with
    | alias _ _ _ _ ha => exact SCNsAliasNode_last ha
    | content _ _ _ _ hcont =>
      cases hcont with
      | plain _ _ _ _ hp => exact SNsPlain_last_not_white (Or.inl rfl) hp
      | flowSeq _ _ _ _ hs =>
        exfalso
        cases hs <;> (rename_i hl; try (rename_i _ _ _ _ _); cases ‹GLit '[' _ _›)
      | flowMap _ _ _ _ hm =>
        exfalso
        cases hm <;> (cases ‹GLit '{' _ _›)
      | singleQ _ _ _ _ hq => exact SCSingleQuoted_last hq
      | doubleQ _ _ _ _ hq => exact SCDoubleQuoted_last hq
    | propsContent _ _ _ _ _ _ hp _ _ =>
      exfalso
      cases hp with
      | tagFirst =>
        rename_i ht _
        obtain ⟨r, k, hk⟩ := tag_head ht
        simp at hk
      | anchorFirst =>
        rename_i ha _
        obtain ⟨r, k, hk⟩ := anchor_head ha
        simp at hk
    | propsEmpty _ _ _ _ hp =>
      exfalso
      cases hp with
      | tagFirst =>
        rename_i ht _
        obtain ⟨r, k, hk⟩ := tag_head ht
        simp at hk
      | anchorFirst =>
        rename_i ha _
        obtain ⟨r, k, hk⟩ := anchor_head ha
        simp at hk
  · rcases SFlowNode_head_lift h ⟨h_amp, hstar, h_bang, h_lb, h_lc⟩ with
      ⟨_, _, hp⟩ | ⟨_, hq⟩ | ⟨_, hq⟩
    · exact SNsPlain_last_not_white (Or.inl rfl) hp
    · exact SCDoubleQuoted_last hq
    · exact SCSingleQuoted_last hq

/-- Item 517: `content_km_transport` with the per-arm `h_kf` replaced by the dispatcher's own
    two-way reading of the pending key (`dispatchContent_pending_cases`): a content scan keeps the
    reservation or clears it, so the T mask rides any content step with no arm split.  The body
    is the S lemma's (the token prefix, the key stack, the stamps ride by the same facts). -/
lemma content_km_transport_any {sc s_prep s_ad s' : L4YAML.Scanner.ScannerState} {c : Char}
    {km : Array Bool} {kc : Nat}
    (h_flow : 0 < sc.flowLevel)
    (h_km : L4YAML.Proofs.StreamAccum.KmSound sc km kc)
    (h_pre : L4YAML.Scanner.scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_ad_def : (if s_prep.allowDirectives = true then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep) = s_ad)
    (hok : L4YAML.Scanner.scanNextToken_dispatchContent s_ad c = .ok s')
    (h_off' : s_ad.offset ≤ s'.offset) :
    L4YAML.Proofs.StreamAccum.KmSound s' km kc := by
  obtain ⟨h_ppref, h_poff, h_psks⟩ := L4YAML.Proofs.StreamAccum.preprocess_inFlow_facts h_flow h_pre
  have h_ad_tk : s_ad.tokens = s_prep.tokens := by rw [← h_ad_def]; split <;> rfl
  have h_ad_off : s_ad.offset = s_prep.offset := by rw [← h_ad_def]; split <;> rfl
  have h_ad_sks : s_ad.simpleKeyStack = s_prep.simpleKeyStack := by
    rw [← h_ad_def]; split <;> rfl
  have h_ad_sk : s_ad.simpleKey = s_prep.simpleKey := by rw [← h_ad_def]; split <;> rfl
  have h_pref : ∀ i, i < sc.tokens.size → s'.tokens[i]? = sc.tokens[i]? := by
    intro i hi
    have h1 := h_ppref i hi
    have h_sz : i < s_ad.tokens.size := by
      cases hgt : decide (i < s_ad.tokens.size) with
      | true => exact of_decide_eq_true hgt
      | false =>
        have hge := of_decide_eq_false hgt
        rw [show s_prep.tokens = s_ad.tokens from h_ad_tk.symm,
            Array.getElem?_eq_none (by omega), Array.getElem?_eq_getElem hi] at h1
        exact absurd h1.symm (by simp)
    have hp : s'.tokens[i]? = s_ad.tokens[i]? := by
      rw [Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le h_sz
          (L4YAML.Proofs.ScannerCorrectness.ScanHelpers.dispatchContent_tokens_mono s_ad c s' hok)),
          Array.getElem?_eq_getElem h_sz]
      exact congrArg some
        (L4YAML.Proofs.ScannerCorrectness.ScanHelpers.dispatchContent_preserves_prefix s_ad c s' hok i h_sz)
    rw [hp, h_ad_tk]
    exact h1
  have h_mono : sc.tokens.size ≤ s_ad.tokens.size := by
    rw [h_ad_tk]
    cases hz : sc.tokens.size with
    | zero => exact Nat.zero_le _
    | succ k =>
      have hk : k < sc.tokens.size := by omega
      have h1 := h_ppref k hk
      rw [Array.getElem?_eq_getElem hk] at h1
      obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp h1
      omega
  refine h_km.transport
    ?_ h_pref (by omega)
    (Nat.le_trans h_mono
      (L4YAML.Proofs.ScannerCorrectness.ScanHelpers.dispatchContent_tokens_mono s_ad c s' hok)) ?_
  · rw [L4YAML.Proofs.ScannerCorrectness.dispatchContent_preserves_simpleKeyStack s_ad c s' hok,
        h_ad_sks, h_psks]
  · rcases L4YAML.Proofs.StreamAccum.dispatchContent_pending_cases hok with h_kf | h_false
    · rcases L4YAML.Proofs.StreamAccum.preprocess_pending_cases h_flow h_pre with h_eq | ⟨h_p, h_ti⟩
      · exact Or.inl ⟨by rw [h_kf.1, h_ad_sk, h_eq], by rw [h_kf.2, h_ad_sk, h_eq]⟩
      · exact Or.inr (Or.inr ⟨by rw [h_kf.1, h_ad_sk]; exact h_p,
          by rw [h_kf.2, h_ad_sk, h_ti]; exact Nat.le_refl _⟩)
    · exact Or.inr (Or.inl h_false)

/-- The landing agreement: two value-node ends from one start (at any two floors) with white runs
    to one scan position coincide. -/
lemma flowNode_landing_eq {n m : Nat} {ch : Char} {rest : List Char} {col : Nat} {a b sp' : SurfPos}
    (hc : ch ≠ '&' ∧ ch ≠ '!' ∧ ch ≠ '[' ∧ ch ≠ '{')
    (ha : SFlowNode n .flowIn ⟨ch :: rest, col⟩ a) (hb : SFlowNode m .flowIn ⟨ch :: rest, col⟩ b)
    (wa : GStar SSWhite a sp') (wb : GStar SSWhite b sp') : a = b :=
  lastNonWhite_white_eq (SFlowNode_value_last ha hc) (SFlowNode_value_last hb hc) wa wb

/-! ## §9 The content step on the pair, one floor (item 489)

`accum_step_content` at depth ≥ 1 with the T stack at floor `n ≤ minContentIndentOf sc`: the T stack
lands at the WRAPPER's `sp_flow'` and `sp_block'` — the landing agreement (§8) identifies the T
landing (`accum_step_content_traceK`'s `sp_ne`) with the S landing the core now concludes.  The
`∀`-floor fold into `TFlowStackK` (one `ev_n` at every floor) is the next item. -/

open L4YAML.Scanner
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.FlowWalk
open L4YAML.Proofs.ScalarProduction L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.FlowAdjacency L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.ScannerCoupling L4YAML.Proofs.Serialization.SerializationWellFormed

lemma ContentArm_corr {sc s' : ScannerState} {c : Char} {sp sp' : SurfPos}
    (h : ContentArm sc s' c sp sp') : ScannerSurfCorr s' sp' := by
  cases h <;> assumption

lemma accum_step_content_pairB {n d : Nat} {km : Array Bool} {ev : List Event} (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flowK : FlowStackK sp_start sc sc.flowLevel sc.flowStack (tailOf sc.tokens) sp_block sp_flow)
    (h_pending : sc.flowLevel = 0 → PendingNode sc false sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_interior : sc.flowLevel ≥ 1 →
      InteriorGap sc (tailOf sc.tokens) sp_flow sp_scan ∧
        LastTokenReal sc.tokens ∧ sc.allowDirectives = false)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_sound : PendingKeySound.Sound sc)
    -- **Item 157: §9.2's DANGLING refusal, threaded from `scanNextToken`.**  It
    -- runs BEFORE every dispatch, so its success reaches all four of them
    -- unchanged; what the landing turns it into is the park's own face.
    (h_dn : scanNextToken_checkDanglingNode sc s_prep = .ok ())
    -- Item 275: §8.1's check, carried beside §9.2's.
    (h_fv : scanNextToken_checkFlowValueIndent sc s_prep = .ok ())
    -- Content dispatch is `scanNextToken`'s LAST arm: it runs only after both
    -- indicator dispatches fell through.  Those two fall-throughs are what pin
    -- `c` off `,`/`]`/`}` and off the value-indicator `:`, which is what item
    -- 9d's adjacency inversion needs at a content character (§1c''b'').
    (h_flow_none : scanNextToken_dispatchFlowIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok none)
    (h_blk_none : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok none)
    -- Item 47: the adjacent-value check sits between the block and content
    -- dispatches, so a content step carries its success — which is what the
    -- two content parks' `:`-residue arms refute.
    (h_adj : scanNextToken_checkAdjacentValue
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok ())
    -- **Item 139: and §9.2's landing refusal, beside it.**  It runs one check
    -- earlier — before the `allowDirectives` update — so it reads `s_prep`
    -- itself, and it is what the two content parks' FALLBACK route refutes.
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    -- Item 146: the stack's BASE, carried by the accumulation from `mk'`
    -- down.  §9.2's landing refusal spends it to read the dedent exemption
    -- off the landing's column instead of splitting on it.
    (h_base : IndentStackBase.SentinelBase sc)
    -- **Item 149: and its SHAPE**, carried the same way and from the same
    -- seed.  A dedent landing's pack reads the scanner stack it pops to,
    -- and reading a bound on the TOP as a bound on every entry is what
    -- monotonicity buys (`IndentStackCover.Covered.pop_to`).
    (h_mono : IndentStackMono.Mono sc)
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s')
    -- Item 67: the structural dispatch's FALL-THROUGH, which inside a flow is
    -- the statement that the token cleared the enclosing block's indent — the
    -- other half of what a multi-line reading at the stack's index needs.
    (h_str_none : scanNextToken_dispatchStructural s_prep c = .ok none)
    (h_not_doc : (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep).col = 0 →
      atDocumentBoundary (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) = false)
    (hd : sc.flowLevel = d + 1)
    (hT : TFlowStackB n sc.flowLevel sc.flowStack km (tailOf sc.tokens) sp_block sp_flow ev)
    (hn : n ≤ minContentIndentOf sc) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackK sp_start s' s'.flowLevel s'.flowStack (tailOf s'.tokens) sp_block' sp_flow' ∧
      (s'.flowLevel = 0 → PendingNode s' false sp_start sp_flow' sp_scan') ∧
      ScannerSurfCorr s' sp_scan' ∧
      (s'.flowLevel ≥ 1 →
        InteriorGap s' (tailOf s'.tokens) sp_flow' sp_scan' ∧
          LastTokenReal s'.tokens ∧ s'.allowDirectives = false) ∧
      sp_block' = sp_block ∧
      ∃ ev_n, TFlowStackB n s'.flowLevel s'.flowStack km (tailOf s'.tokens) sp_block sp_flow' (ev ++ ev_n) := by
  obtain ⟨g, b, f, sn, q1, q2, q3, q4, q5, q6, sp_prepW, sp_aW, hcW, armW, q7⟩ :=
    accum_step_content (h_sound := h_sound) sc sp_start sp_gram sp_block sp_flow sp_scan s_prep s' c
      h_stream h_stack h_flowK h_pending h_corr h_interior h_preprocess h_dn h_fv h_flow_none
      h_blk_none h_adj h_bare h_base h_mono h_dispatch h_str_none h_not_doc
  obtain ⟨hblk, hprop, hval⟩ := q7 (by omega)
  obtain ⟨h_gap, h_real, -⟩ := h_interior (by omega)
  obtain ⟨ev_n, sp_prep, sp_a, hc, arm, hdisj⟩ :=
    accum_step_content_traceK hd h_corr h_preprocess h_str_none h_flow_none h_blk_none h_dispatch
      h_not_doc h_gap h_real hT hn
  have hsp : sp_prepW = sp_prep := ScannerSurfCorr_unique hcW hc
  subst hsp
  have ha : sp_a = sn := ScannerSurfCorr_unique (ContentArm_corr arm) q5
  subst ha
  refine ⟨g, b, f, sp_a, q1, q2, q3, q4, q5, q6, hblk, ?_⟩
  rcases hdisj with ⟨kj, sp_ne, htl, ⟨hamp, hbang⟩, hws, hnd, hTB⟩ | ⟨-, hc', hTB⟩
  · obtain ⟨m, -, hnS, hwS⟩ := hval kj htl
    have hpeek : (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep).peek? = some c :=
      (by split <;> rfl : (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep).peek? = s_prep.peek?).trans (preprocess_some_peek h_preprocess)
    obtain ⟨rest, hsp⟩ := peek_some_sp hc hpeek
    subst hsp
    have hglue := content_not_glue h_dispatch
    simp only [isFlowIndicatorBool, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      List.mem_cons, List.mem_nil_iff, or_false, not_or] at hglue
    have heq := flowNode_landing_eq ⟨hamp, hbang, hglue.2.2.1, hglue.2.2.2.2.1⟩ hnd hnS hws hwS
    subst heq
    exact ⟨ev_n, hTB⟩
  · rw [hprop hc']
    exact ⟨[], by simpa using hTB⟩


/-! ## §10 The `∀`-floor fold's two uniformities (item 490)

`TFlowStackK` holds ONE event list at every floor the S half admits; after a
content step the per-floor traces must agree. White lead: the pushed tokens'
`goOut` trace is unique (`PushesTrace` read at `p := []`). Held run: the
`TCNsProperties` witness at the top floor transfers DOWN to every floor with its
events — a flow-line prefix at `n` is one at `m ≤ n` (the surplus indent spaces
are separate-in-line white). -/

lemma PushesTrace_unique {ts ts' : Array (Positioned YamlToken)} {e e' : List Event}
    (h : PushesTrace ts ts' e) (h' : PushesTrace ts ts' e') : e = e' := by
  have h1 := h []
  have h2 := h' []
  rw [h1] at h2
  exact List.append_cancel_left (congrArg Prod.fst h2)

lemma SIndent_split {n : Nat} {s t : SurfPos} (h : SIndent n s t) :
    ∀ m, m ≤ n → ∃ u, SIndent m s u ∧ SIndent (n - m) u t := by
  induction h with
  | zero s =>
    intro m hmn
    have : m = 0 := by omega
    subst this
    exact ⟨s, .zero s, .zero s⟩
  | succ k rest col s' h ih =>
    intro m hmn
    cases m with
    | zero => exact ⟨_, .zero _, by simpa using SIndent.succ k rest col s' h⟩
    | succ m =>
      obtain ⟨u, h₁, h₂⟩ := ih m (by omega)
      exact ⟨u, .succ m rest col u h₁, by simpa [Nat.succ_sub_succ] using h₂⟩

lemma SIndent_to_GStar_SSWhite' {k : Nat} {u t : SurfPos} (h : SIndent k u t) :
    GStar SSWhite u t := by
  induction h with
  | zero s => exact .nil s
  | succ k rest col s' _ ih => exact .cons _ _ _ (.space rest col) ih

lemma SIndent_succ_GPlus_white {k : Nat} {u t : SurfPos} (h : SIndent (k + 1) u t) :
    GPlus SSWhite u t := by
  cases h with
  | succ _ rest col s' h' => exact .mk _ _ _ (.space rest col) (SIndent_to_GStar_SSWhite' h')

lemma GStar_SSWhite_append {a b c : SurfPos} (h₁ : GStar SSWhite a b) (h₂ : GStar SSWhite b c) :
    GStar SSWhite a c := by
  induction h₁ with
  | nil _ => exact h₂
  | cons _ _ _ h _ ih => exact .cons _ _ _ h (ih h₂)

lemma SFlowLinePrefix_mono {m n : Nat} {s s' : SurfPos} (hmn : m ≤ n)
    (h : SFlowLinePrefix n s s') : SFlowLinePrefix m s s' := by
  cases h
  rename_i t hind hopt
  obtain ⟨u, hu, hrest⟩ := SIndent_split hind m hmn
  rcases Nat.eq_zero_or_pos (n - m) with hz | hpos
  · rw [hz] at hrest
    cases hrest
    exact .mk m s _ s' hu hopt
  · obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
    rw [hk] at hrest
    have hplus := SIndent_succ_GPlus_white hrest
    cases hplus
    rename_i v hw hws
    refine .mk m s u s' hu (.some u s' (.whites u s' (.mk _ v _ hw ?_)))
    cases hopt with
    | none => exact hws
    | some =>
      rename_i hil
      exact GStar_SSWhite_append hws
        (L4YAML.Proofs.PreprocessProduction.SSeparateInLine_to_GStar_SSWhite hil)

lemma SSeparateLines_mono {m n : Nat} {s s' : SurfPos} (hmn : m ≤ n)
    (h : SSeparateLines n s s') : SSeparateLines m s s' := by
  cases h with
  | commented =>
    rename_i s₁ hc hp
    exact .commented m s s₁ s' hc (SFlowLinePrefix_mono hmn hp)
  | inline =>
    rename_i hil
    exact .inline m s s' hil

lemma SSeparate_flowIn_mono {m n : Nat} {s s' : SurfPos} (hmn : m ≤ n)
    (h : SSeparate n .flowIn s s') : SSeparate m .flowIn s s' :=
  SSeparateLines_mono hmn h

lemma TCNsProperties_floor_mono {m n : Nat} {s s' : SurfPos} {ev : List Event} (hmn : m ≤ n)
    (h : TCNsProperties n .flowIn s s' ev) : TCNsProperties m .flowIn s s' ev := by
  cases h with
  | tagFirst =>
    rename_i s₁ e₁ e₂ h₁ h₂
    refine .tagFirst s s₁ s' e₁ e₂ h₁ ?_
    cases h₂ with
    | none => exact .none _
    | some =>
      rename_i hseq
      cases hseq
      rename_i t e₁' e₂' hl hp
      obtain ⟨hsep, he⟩ := hl
      exact .some _ _ _ (.mk _ t _ _ _ ⟨SSeparate_flowIn_mono hmn hsep, he⟩ hp)
  | anchorFirst =>
    rename_i s₁ e₁ e₂ h₁ h₂
    refine .anchorFirst s s₁ s' e₁ e₂ h₁ ?_
    cases h₂ with
    | none => exact .none _
    | some =>
      rename_i hseq
      cases hseq
      rename_i t e₁' e₂' hl hp
      obtain ⟨hsep, he⟩ := hl
      exact .some _ _ _ (.mk _ t _ _ _ ⟨SSeparate_flowIn_mono hmn hsep, he⟩ hp)


/-! ## §11 The `∀`-floor fold: the content step on `TFlowStackK` (item 490)

`accum_step_content_pairB` closes the pair-level content step at ONE floor; `TFlowStackK` holds its
T half at EVERY floor the S half admits, with one `sp_flow` and one event list.  The fold runs the
wrapper once, picks the event suffix once — at a `.white` lead the pushed tokens' `goOut` trace
(`PushesTrace_unique`), at a `.props` lead the held run's events read at the top floor and carried
down (`TCNsProperties_floor_mono`) — and lands every floor at the wrapper's `sp_flow'` through
`flowNode_landing_eq`.  The floor ceiling rides the step: a content step inside a flow leaves the
indent stack alone, so `minContentIndentOf s' = minContentIndentOf sc`. -/

lemma accum_step_content_pairK {d : Nat} {ev : List Event} (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flowK : TFlowStackK sp_start sc sc.flowLevel sc.flowStack (tailOf sc.tokens) sp_block sp_flow ev)
    (h_pending : sc.flowLevel = 0 → PendingNode sc false sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_interior : sc.flowLevel ≥ 1 →
      InteriorGap sc (tailOf sc.tokens) sp_flow sp_scan ∧
        LastTokenReal sc.tokens ∧ sc.allowDirectives = false)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_sound : PendingKeySound.Sound sc)
    (h_dn : scanNextToken_checkDanglingNode sc s_prep = .ok ())
    (h_fv : scanNextToken_checkFlowValueIndent sc s_prep = .ok ())
    (h_flow_none : scanNextToken_dispatchFlowIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok none)
    (h_blk_none : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok none)
    (h_adj : scanNextToken_checkAdjacentValue
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok ())
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    (h_base : IndentStackBase.SentinelBase sc)
    (h_mono : IndentStackMono.Mono sc)
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s')
    (h_str_none : scanNextToken_dispatchStructural s_prep c = .ok none)
    (h_not_doc : (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep).col = 0 →
      atDocumentBoundary (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) = false)
    (hd : sc.flowLevel = d + 1) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan' ev_n,
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      (s'.flowLevel = 0 → PendingNode s' false sp_start sp_flow' sp_scan') ∧
      ScannerSurfCorr s' sp_scan' ∧
      (s'.flowLevel ≥ 1 →
        InteriorGap s' (tailOf s'.tokens) sp_flow' sp_scan' ∧
          LastTokenReal s'.tokens ∧ s'.allowDirectives = false) ∧
      sp_block' = sp_block ∧
      TFlowStackK sp_start s' s'.flowLevel s'.flowStack (tailOf s'.tokens) sp_block sp_flow' (ev ++ ev_n) := by
  obtain ⟨h_flowS, km, kc, hKm, hTall⟩ := h_flowK
  obtain ⟨g, b, f, sn, q1, q2, q3, q4, q5, q6, sp_prep, sp_a, hcorr_ad, arm, q7⟩ :=
    accum_step_content (h_sound := h_sound) sc sp_start sp_gram sp_block sp_flow sp_scan s_prep s' c
      h_stream h_stack h_flowS h_pending h_corr h_interior h_preprocess h_dn h_fv h_flow_none
      h_blk_none h_adj h_bare h_base h_mono h_dispatch h_str_none h_not_doc
  obtain ⟨hblk, hkeep, hval⟩ := q7 (by omega)
  obtain ⟨h_gap, h_real, -⟩ := h_interior (by omega)
  obtain ⟨sp_prep0, hcorr_prep⟩ :=
    L4YAML.Proofs.ScanStrictCoupling.scanNextToken_preprocess_corr sc sp_scan h_corr s_prep c h_preprocess
  have h_lead := contentLead_of_interior hd h_corr hcorr_prep
    h_preprocess h_str_none (by split <;> rfl) (by split <;> rfl) h_flow_none h_blk_none h_dispatch h_gap h_real
  have hcorr_ad0 : ScannerSurfCorr (if s_prep.allowDirectives then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep) sp_prep0 := L4YAML.Proofs.StreamAccum.corr_of_allowDirectives_update hcorr_prep
  generalize h_ad_def : (if s_prep.allowDirectives then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep) = s_ad at h_flow_none h_blk_none h_dispatch h_not_doc hcorr_ad hcorr_ad0 arm q3 q4 q5 q6 ⊢
  have hsp0 : sp_prep = sp_prep0 := ScannerSurfCorr_unique hcorr_ad hcorr_ad0
  subst hsp0
  have h_ad_tokens : s_ad.tokens = s_prep.tokens := by rw [← h_ad_def]; split <;> rfl
  have h_ad_peek : s_ad.peek? = s_prep.peek? := by rw [← h_ad_def]; split <;> rfl
  have h_ad_fl : s_ad.flowLevel = s_prep.flowLevel := by rw [← h_ad_def]; split <;> rfl
  have h_ad_ind : s_ad.indents = s_prep.indents := by rw [← h_ad_def]; split <;> rfl
  have h_ad_col : s_ad.col = s_prep.col := by rw [← h_ad_def]; split <;> rfl
  have h_sc_inflow : sc.inFlow = true := L4YAML.Proofs.StreamAccum.inFlow_of_flowLevel_eq hd
  have h_prep_fl : s_prep.flowLevel = sc.flowLevel :=
    L4YAML.Proofs.FlowSync.preprocess_preserves_flowLevel sc s_prep c h_preprocess
  have h_prep_fs : s_prep.flowStack = sc.flowStack :=
    L4YAML.Proofs.ScannerFlowStack.preprocess_preserves_flowStack sc s_prep c h_preprocess
  have h_prep_ind : s_prep.indents = sc.indents :=
    L4YAML.Proofs.FlowIndentStable.preprocess_indents_of_inFlow h_sc_inflow h_preprocess
  have h_prep_inflow : s_prep.inFlow = true := by
    unfold ScannerState.inFlow; rw [h_prep_fl, hd]; simp
  have h_ad_inflow : s_ad.inFlow = true := by
    unfold ScannerState.inFlow; rw [h_ad_fl, h_prep_fl, hd]; simp
  have hpeek : s_ad.peek? = some c :=
    h_ad_peek.trans (L4YAML.Proofs.StreamAccum.preprocess_some_peek h_preprocess)
  have hcol : s_ad.currentIndent < (s_ad.col : Int) := by
    rw [h_ad_col, L4YAML.Proofs.PreprocessIndentStable.currentIndent_of_indents_eq h_ad_ind]
    exact L4YAML.Proofs.FlowIndentStable.structural_none_col_gt_of_inFlow h_prep_inflow h_str_none
  have hn' : ∀ m, m ≤ minContentIndentOf sc → (m : Int) ≤ max 0 (s_ad.currentIndent + 1) := by
    intro m hm
    rw [L4YAML.Proofs.PreprocessIndentStable.currentIndent_of_indents_eq (h_ad_ind.trans h_prep_ind)]
    unfold L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf at hm
    omega
  have h_tl_eq : tailOf s_ad.tokens = tailOf sc.tokens :=
    tailOf_preprocess_eq (by omega) h_preprocess h_ad_tokens
  have h_fl' : s'.flowLevel = sc.flowLevel :=
    (L4YAML.Proofs.ScannerCorrectness.dispatchContent_preserves_flowLevel s_ad c s' h_dispatch).trans
      (h_ad_fl.trans h_prep_fl)
  have h_fs' : s'.flowStack = sc.flowStack :=
    (L4YAML.Proofs.ScannerFlowStack.dispatchContent_preserves_flowStack s_ad c s' h_dispatch).trans
      ((by rw [← h_ad_def]; split <;> rfl : s_ad.flowStack = s_prep.flowStack).trans h_prep_fs)
  -- The floor ceiling rides the step.
  have hmin : minContentIndentOf s' = minContentIndentOf sc :=
    L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf_congr
      ((L4YAML.Proofs.FlowIndentStable.dispatchContent_preserves_indents h_ad_inflow h_dispatch).trans
        (h_ad_ind.trans h_prep_ind))
  -- The T open stack at every floor.
  have h_fos : ∀ m, m ≤ minContentIndentOf sc →
      TFlowOpenStack m (d + 1) sc.flowStack km (tailOf s_ad.tokens) sp_block sp_flow ev := by
    intro m hm
    have hTm := (hTall m hm).1
    rw [hd] at hTm
    rcases hTm with _ | ⟨_, _, _, _, _, _, _, h⟩
    rw [h_tl_eq]; exact h
  have hglue := content_not_glue h_dispatch
  simp only [isFlowIndicatorBool, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    List.mem_cons, List.mem_nil_iff, or_false, not_or] at hglue
  -- Item 509: the pre-tail is never `.value` (the adjacency guard, as the lead reads it).
  have h_tail0 : ∀ kj, tailOf sc.tokens ≠ .value kj := by
    cases h_lead with
    | white h_tail _ => exact h_tail
    | props _ _ _ _ h_tail _ _ _ _ => exact h_tail
  -- Item 509: a `.colon` pre-tail means the node COMPLETES a pair — the scanner's layout
  -- afterwards is `KeyAfterValueLayout s'` (the S `.value` site's reading, `content_value_layout`).
  have h_colon_sc : ∀ kj, tailOf sc.tokens = .colon kj →
      (sc.simpleKeyAllowed = true ∧ sc.explicitKeyLine = none ∧
        ∃ tok, sc.tokens[sc.tokens.size - 1]? = some tok ∧ tok.val = .value) ∨
      L4YAML.Proofs.EntryBoundaryLayout.KeyAfterValueLayout sc := by
    intro kj htl
    cases h_gap with
    | white _ _ h_colon _ _ _ _ => exact Or.inl (h_colon kj htl)
    | props _ _ _ _ _ _ _ _ h_colon _ _ _ _ => exact Or.inr (h_colon kj htl)
  have h_off_gt : s_ad.offset < s'.offset :=
    L4YAML.Proofs.ScannerCorrectness.dispatchContent_offset_gt s_ad s' c
      (by
        have hpk := hpeek
        unfold ScannerState.peek? at hpk
        split at hpk
        · assumption
        · exact absurd hpk (by simp))
      hpeek
      (by cases hcol0 : s_ad.col == 0 with
          | false => simp
          | true =>
            simp only [Bool.true_and]
            simp only [beq_iff_eq] at hcol0
            exact h_not_doc hcol0)
      h_dispatch
  have h_kavl_of_colon : c ≠ '&' → c ≠ '!' → ∀ kj, tailOf sc.tokens = .colon kj →
      L4YAML.Proofs.EntryBoundaryLayout.KeyAfterValueLayout s' := by
    intro hamp hbang kj htl
    obtain ⟨hpipe, hgt⟩ :=
      L4YAML.Proofs.BlockScalarFlowGuard.dispatchContent_not_blockScalar_of_inFlow h_ad_inflow h_dispatch
    exact L4YAML.Proofs.StreamAccum.content_value_layout (by omega) (h_colon_sc kj htl) h_preprocess
      h_ad_def h_dispatch hamp hbang hpipe hgt h_off_gt
  -- One landing at every floor, from one T open stack at `sp_ne` landing at the wrapper's `f`;
  -- the T closure rides it (item 509): a `.colon` pre-tail stores the layout, `.sep` /
  -- `.question` the `receiveNodeColon` closure the twin handed over.
  have land : ∀ m kj sp_ne ev_n, tailOf s'.tokens = .value kj → (c ≠ '&' ∧ c ≠ '!') →
      GStar SSWhite sp_ne sp_a → SFlowNode m .flowIn sp_prep sp_ne →
      TFlowOpenStack m (d + 1) sc.flowStack km (.value kj) sp_block sp_ne (ev ++ ev_n) →
      ((tailOf s_ad.tokens = .sep ∨ tailOf s_ad.tokens = .question) →
        ∀ sp_p₂ sp_t, (SSeparateLines m sp_ne sp_p₂ ∨ sp_p₂ = sp_ne) → GLit ':' sp_p₂ sp_t →
          TFlowOpenStack m (d + 1) sc.flowStack km (.colon kj) sp_block sp_t (ev ++ ev_n)) →
      TFlowStackB m s'.flowLevel s'.flowStack km (tailOf s'.tokens) sp_block f (ev ++ ev_n) ∧
      (0 < s'.flowLevel → ∀ kj', tailOf s'.tokens = .value kj' →
        L4YAML.Proofs.EntryBoundaryLayout.KeyAfterValueLayout s' ∨
        ∀ sp_prep sp_tok, (SSeparateLines m f sp_prep ∨ sp_prep = f) → GLit ':' sp_prep sp_tok →
          TFlowStackB m s'.flowLevel s'.flowStack km (.colon kj') sp_block sp_tok (ev ++ ev_n)) := by
    intro m kj sp_ne ev_n htl ⟨hamp, hbang⟩ hws hnd h_open h_clos
    obtain ⟨m', -, hnS, hwS⟩ := hval kj htl
    -- The landing's start is the content character.
    obtain ⟨rest, hsp⟩ := peek_some_sp hcorr_ad hpeek
    subst hsp
    have ha : sp_a = sn := ScannerSurfCorr_unique (ContentArm_corr arm) q5
    subst ha
    have heq := flowNode_landing_eq ⟨hamp, hbang, hglue.2.2.1, hglue.2.2.2.2.1⟩ hnd hnS hws hwS
    subst heq
    rw [h_fl', h_fs', hd, htl]
    refine ⟨.«open» _ _ _ _ _ _ _ h_open, ?_⟩
    intro _ kj' htl'
    injection htl' with hkj
    subst hkj
    cases h_tl_case : tailOf sc.tokens with
    | value kj₀ => exact absurd h_tl_case (h_tail0 kj₀)
    | colon kj₀ => exact Or.inl (h_kavl_of_colon hamp hbang kj₀ h_tl_case)
    | sep =>
      exact Or.inr (fun sp_p sp_t h_l h_col => .«open» _ _ _ _ _ _ _
        (h_clos (by rw [h_tl_eq, h_tl_case]; exact Or.inl rfl) sp_p sp_t h_l h_col))
    | question =>
      exact Or.inr (fun sp_p sp_t h_l h_col => .«open» _ _ _ _ _ _ _
        (h_clos (by rw [h_tl_eq, h_tl_case]; exact Or.inr rfl) sp_p sp_t h_l h_col))
  have key : ∃ ev_n, ∀ m, m ≤ minContentIndentOf sc →
      TFlowStackB m s'.flowLevel s'.flowStack km (tailOf s'.tokens) sp_block f (ev ++ ev_n) ∧
      (0 < s'.flowLevel → ∀ kj, tailOf s'.tokens = .value kj →
        L4YAML.Proofs.EntryBoundaryLayout.KeyAfterValueLayout s' ∨
        ∀ sp_prep sp_tok, (SSeparateLines m f sp_prep ∨ sp_prep = f) → GLit ':' sp_prep sp_tok →
          TFlowStackB m s'.flowLevel s'.flowStack km (.colon kj) sp_block sp_tok (ev ++ ev_n)) := by
    by_cases hprop : c = '&' ∨ c = '!'
    · -- Property arms: tail, trace and `sp_flow` kept at every floor; the kept tail is not
      -- `.value`, so the closure is vacuous.
      refine ⟨[], ?_⟩
      intro m hm
      have h_kept := content_prop_tail_kept hcorr_ad hpeek h_dispatch hprop
      rw [hkeep hprop, h_fl', h_fs', hd, h_kept, List.append_nil]
      refine ⟨.«open» _ _ _ _ _ _ _ (h_fos m hm), ?_⟩
      intro _ kj htl
      rw [h_tl_eq] at htl
      exact absurd htl (h_tail0 kj)
    · have hamp : c ≠ '&' := fun h => hprop (Or.inl h)
      have hbang : c ≠ '!' := fun h => hprop (Or.inr h)
      cases h_lead with
      | white h_tail h_lead =>
        -- The event suffix read at the top floor; every floor's suffix is the same `goOut` trace.
        obtain ⟨ev_N, hpushN, -⟩ := accum_step_content_trace_in arm hcorr_ad hpeek h_ad_inflow h_not_doc
          h_dispatch hcol (hn' _ (Nat.le_refl _)) (h_fos _ (Nat.le_refl _)) (by rw [h_tl_eq]; exact h_tail)
          (by rw [h_tl_eq]; exact h_lead _ (Nat.le_refl _))
        refine ⟨ev_N, ?_⟩
        intro m hm
        obtain ⟨ev_m, hpush_m, h | ⟨-, h⟩⟩ := accum_step_content_trace_in arm hcorr_ad hpeek h_ad_inflow
          h_not_doc h_dispatch hcol (hn' m hm) (h_fos m hm) (by rw [h_tl_eq]; exact h_tail)
          (by rw [h_tl_eq]; exact h_lead m hm)
        · obtain ⟨kj, sp_ne, h_tl', h_ws, h_nd, h_open, h_clos⟩ := h
          rw [PushesTrace_unique hpush_m hpushN] at h_open h_clos
          exact land m kj sp_ne ev_N h_tl' ⟨hamp, hbang⟩ h_ws h_nd h_open h_clos
        · rcases h with ⟨hc, -⟩ | ⟨hc, -⟩
          · exact absurd hc hamp
          · exact absurd hc hbang
      | props ha ht sp_p sp_e h_tail h_lead_p h_run h_sep h_last_sc =>
        have hstar : c ≠ '*' := by
          intro hc; subst hc
          have h_false := L4YAML.Proofs.StreamAccum.lastTokenIsNodeProperty_false_of_dispatch h_dispatch
          obtain ⟨t, h_last, h_prop⟩ := h_last_sc
          have h_ad_last : L4YAML.Scanner.lastRealTokenVal? s_ad.tokens =
              L4YAML.Scanner.lastRealTokenVal? sc.tokens := by
            rw [h_ad_tokens]
            exact L4YAML.Proofs.StreamAccum.preprocess_preserves_lastRealTokenVal_inFlow sc s_prep _
              (by omega) h_real h_preprocess
          unfold lastTokenIsNodeProperty at h_false
          rw [h_ad_inflow, h_ad_last, h_last] at h_false
          simp [h_prop] at h_false
        -- The held run's events, read at the top floor and carried down.
        obtain ⟨ev_p, h_props⟩ :=
          L4YAML.Proofs.Serialization.TraceOf.FlowWalk.PropsRun.toT (h_run _ (Nat.le_refl _))
        refine ⟨ev_p ++ [], ?_⟩
        intro m hm
        obtain ⟨kj, sp_ne, -, h_tl', h_ws, h_nd, h_open, h_clos⟩ := accum_step_content_trace_in_props arm hcorr_ad hpeek
          h_ad_inflow h_not_doc h_dispatch hcol (hn' m hm) (h_fos m hm) (by rw [h_tl_eq]; exact h_tail)
          (by rw [h_tl_eq]; exact h_lead_p m hm) (TCNsProperties_floor_mono hm h_props) (h_sep m hm)
          ⟨hamp, hbang, hstar⟩
        exact land m kj sp_ne (ev_p ++ []) h_tl' ⟨hamp, hbang⟩ h_ws h_nd h_open h_clos
  obtain ⟨ev_n, hk⟩ := key
  rw [hblk] at q3
  exact ⟨g, b, f, sn, ev_n, q1, q2, q4, q5, q6, hblk, q3, km, kc,
    content_km_transport_any (by omega) hKm h_preprocess h_ad_def h_dispatch (Nat.le_of_lt h_off_gt),
    fun m hm => hk m (by rwa [hmin] at hm)⟩

/-! ## §10 The flow step on the T stack (item 520) -/

/-- Item 520: the gap's events at every floor at once — the white gap pushes none and the held
    run's `TCNsProperties` events are floor-independent (`TCNsProperties_floor_mono`), read at the
    ceiling `minContentIndentOf sc` and carried down to every floor the S half admits. -/
lemma gapRead_onT_uniform {sc : L4YAML.Scanner.ScannerState} {sp_flow sp_scan sp_flow₂ : SurfPos}
    (gap : L4YAML.Proofs.StreamAccum.GapRead sc sp_flow sp_scan sp_flow₂) :
    ∃ ev_g, ∀ {n d : Nat} {ks km : Array Bool} {sp_block : SurfPos} {ev : List Event},
      n ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf sc →
      TFlowOpenStack n d ks km (tailOf sc.tokens) sp_block sp_flow ev →
      TFlowOpenStack n d ks km (L4YAML.Proofs.StreamAccum.gapTail sc) sp_block sp_flow₂ (ev ++ ev_g) := by
  cases gap with
  | white _ h_nil =>
    rw [L4YAML.Proofs.StreamAccum.gapTail_of_nil h_nil]
    exact ⟨[], fun _ hT => by simpa using hT⟩
  | props ha ht sp_p h_tail h_lead h_run _ h_held =>
    rw [L4YAML.Proofs.StreamAccum.gapTail_of_held h_held]
    obtain ⟨ev_p, hp⟩ := PropsRun.toT ((h_run _).resolve_right (fun h => h (Nat.le_refl _)))
    exact ⟨ev_p, fun hn hT =>
      hT.receivePropsEmpty h_tail ((h_lead _).resolve_right (fun h => h hn))
        (TCNsProperties_floor_mono hn hp)⟩

/-- Item 520: the `.colon`-tail layout case `dispatch_key_after_value` reads — the S side's
    `h_klay`, carried by `FlowArm.openNest`. -/
abbrev ColonKeyCase (sc : ScannerState) : Prop :=
  ∀ kj, tailOf sc.tokens = .colon kj →
    (sc.simpleKeyAllowed = true ∧ sc.explicitKeyLine = none ∧
      ∃ tok, sc.tokens[sc.tokens.size - 1]? = some tok ∧ tok.val = .value) ∨
    L4YAML.Proofs.EntryBoundaryLayout.KeyAfterValueLayout sc

/-- Item 520: the flow indicator's effect on the key-map mask, read off the dispatcher once for
    every arm — the open pushes `kmBit` of the pre-tail (`km_push_at_open`, the `.colon` face fed by
    `dispatch_key_after_value` off the carried layout fact), the close pops the top bit
    (`close_km_pop`) and a `true` top bit refutes the next `:` (`close_layout_of_bit`), the `,`
    keeps the mask (`comma_km_transport`).  `h_kpos` is the T stack's `km.size = depth` at a
    nested step. -/
lemma dispatchFlow_km_faces {sc s_prep s' : ScannerState} {c : Char} {km : Array Bool} {kc : Nat}
    (h_flow : 0 < sc.flowLevel) (h_kpos : 0 < km.size)
    (h_km : KmSound sc km kc)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchFlowIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ((c = '[' ∨ c = '{') ∧ (ColonKeyCase sc → KmSound s' (km.push (kmBit (tailOf sc.tokens))) kc)) ∨
    ((c = ']' ∨ c = '}') ∧ ∀ km₀ b₀, km = km₀.push b₀ →
      KmSound s' km₀ kc ∧
        (b₀ = true → L4YAML.Proofs.EntryBoundaryLayout.KeyAfterValueLayout s')) ∨
    (c = ',' ∧ KmSound s' km kc) := by
  unfold scanNextToken_dispatchFlowIndicators at h_dispatch
  replace h_dispatch := peel_flowAdj h_dispatch
  simp only [bind, Except.bind, pure, Except.pure] at h_dispatch
  have hpeek_ad : (if s_prep.allowDirectives = true then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep).peek? = s_prep.peek? := by split <;> rfl
  generalize h_ad_def : (if s_prep.allowDirectives = true then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep) = s_ad at h_dispatch hpeek_ad
  have hpk : s_ad.peek? = some c := hpeek_ad.trans (preprocess_some_peek h_preprocess)
  have h_hm : s_ad.offset < s_ad.inputEnd := by
    unfold ScannerState.peek? at hpk
    split at hpk
    · assumption
    · exact absurd hpk (by simp)
  have h_bkey : ColonKeyCase sc → kmBit (tailOf sc.tokens) = true →
      s_ad.simpleKey.possible = true ∧ 0 < s_ad.simpleKey.tokenIndex ∧
      (∃ tok, s_ad.tokens[s_ad.simpleKey.tokenIndex - 1]? = some tok ∧ tok.val = .value) ∧
      s_ad.simpleKey.pos.offset ≤ s_ad.offset ∧
      s_ad.simpleKey.tokenIndex + 1 < s_ad.tokens.size := fun h_klay hb => by
    obtain ⟨kj, hkj⟩ := (kmBit_iff _).1 hb
    exact dispatch_key_after_value h_flow (h_klay kj hkj) h_preprocess h_ad_def
  split at h_dispatch
  · rename_i heq
    have hc : c = '[' := by simpa using heq
    have hs := Option.some.inj (Except.ok.inj h_dispatch)
    subst hs
    have h_off_lt := ScannerProgress.scanFlowSequenceStart_offset_lt s_ad h_hm
    exact Or.inl ⟨Or.inl hc, fun h_klay => km_push_at_open h_flow h_km h_preprocess h_ad_def
      (ScannerCorrectness.scanFlowSequenceStart_stack_pushed s_ad)
      (ScannerCorrectness.scanFlowSequenceStart_simpleKey_cleared s_ad)
      ⟨_, scanFlowSequenceStart_tokens s_ad⟩ (Nat.le_of_lt h_off_lt)
      (fun hb => by
        obtain ⟨h1, h2, h3, h4, h5⟩ := h_bkey h_klay hb
        exact ⟨h1, h2, h3, by omega, h5⟩)
      (fun h0 => absurd h0 (by omega)) (fun h0 => absurd h0 (by omega))⟩
  · split at h_dispatch
    · rename_i heq
      have hc : c = ']' := by simpa using heq
      split at h_dispatch
      · simp at h_dispatch
      · split at h_dispatch
        · simp at h_dispatch
        · split at h_dispatch
          · simp at h_dispatch
          · have hs := Option.some.inj (Except.ok.inj h_dispatch)
            subst hs
            have h_off_lt := ScannerProgress.scanFlowSequenceEnd_offset_lt s_ad h_hm
            refine Or.inr (Or.inl ⟨Or.inl hc, ?_⟩)
            rintro km₀ b₀ rfl
            refine ⟨close_km_pop h_flow h_km h_preprocess h_ad_def
              (ScannerCorrectness.scanFlowSequenceEnd_stack_popped s_ad)
              (ScannerCorrectness.scanFlowSequenceEnd_simpleKey_restored s_ad)
              ⟨_, scanFlowSequenceEnd_tokens s_ad⟩ (Nat.le_of_lt h_off_lt), fun hb => ?_⟩
            subst hb
            exact close_layout_of_bit h_flow h_km h_preprocess h_ad_def
              (ScannerCorrectness.scanFlowSequenceEnd_simpleKey_restored s_ad) rfl
              ⟨_, scanFlowSequenceEnd_tokens s_ad⟩ (Nat.le_of_lt h_off_lt) rfl
    · split at h_dispatch
      · rename_i heq
        have hc : c = '{' := by simpa using heq
        have hs := Option.some.inj (Except.ok.inj h_dispatch)
        subst hs
        have h_off_lt := ScannerProgress.scanFlowMappingStart_offset_lt s_ad h_hm
        exact Or.inl ⟨Or.inr hc, fun h_klay => km_push_at_open h_flow h_km h_preprocess h_ad_def
          (ScannerCorrectness.scanFlowMappingStart_stack_pushed s_ad)
          (ScannerCorrectness.scanFlowMappingStart_simpleKey_cleared s_ad)
          ⟨_, scanFlowMappingStart_tokens s_ad⟩ (Nat.le_of_lt h_off_lt)
          (fun hb => by
            obtain ⟨h1, h2, h3, h4, h5⟩ := h_bkey h_klay hb
            exact ⟨h1, h2, h3, by omega, h5⟩)
          (fun h0 => absurd h0 (by omega)) (fun h0 => absurd h0 (by omega))⟩
      · split at h_dispatch
        · rename_i heq
          have hc : c = '}' := by simpa using heq
          split at h_dispatch
          · simp at h_dispatch
          · split at h_dispatch
            · simp at h_dispatch
            · split at h_dispatch
              · simp at h_dispatch
              · have hs := Option.some.inj (Except.ok.inj h_dispatch)
                subst hs
                have h_off_lt := ScannerProgress.scanFlowMappingEnd_offset_lt s_ad h_hm
                refine Or.inr (Or.inl ⟨Or.inr hc, ?_⟩)
                rintro km₀ b₀ rfl
                refine ⟨close_km_pop h_flow h_km h_preprocess h_ad_def
                  (ScannerCorrectness.scanFlowMappingEnd_stack_popped s_ad)
                  (ScannerCorrectness.scanFlowMappingEnd_simpleKey_restored s_ad)
                  ⟨_, scanFlowMappingEnd_tokens s_ad⟩ (Nat.le_of_lt h_off_lt), fun hb => ?_⟩
                subst hb
                exact close_layout_of_bit h_flow h_km h_preprocess h_ad_def
                  (ScannerCorrectness.scanFlowMappingEnd_simpleKey_restored s_ad) rfl
                  ⟨_, scanFlowMappingEnd_tokens s_ad⟩ (Nat.le_of_lt h_off_lt) rfl
        · split at h_dispatch
          · rename_i heq
            have hc : c = ',' := by simpa using heq
            split at h_dispatch
            · simp at h_dispatch
            · split at h_dispatch
              · simp at h_dispatch
              · rename_i s_fe hfe
                have hs := Option.some.inj (Except.ok.inj h_dispatch)
                subst hs
                exact Or.inr (Or.inr ⟨hc, comma_km_transport h_flow h_km h_preprocess h_ad_def h_hm hfe⟩)
          · simp at h_dispatch

/-- Item 520: `accum_step_flow_trace` with the floor inside — ONE event suffix `ev_g` and ONE
    mask effect for every floor `n ≤ minContentIndentOf sc` (the gap's events are floor-independent
    by `gapRead_onT_uniform`; the base open pushes none), each effect tagged by the indicator it
    answers to.  Three faces as the per-floor lemma: the T stack steps (kept / pushed `kmBit` /
    popped) and, at a `.value`-tail landing (the nested close), either the popped bit was `true`
    (the S side's `close_layout_of_bit` face) or the next `:` continues on the T stack (item 513's
    `closeNested*Colon`); the base close ends the flow node (`TFlowContent` at every floor, the T
    stack back to `nil`); the base open starts one at `#[false]`, its mask sound by the carried
    `FlowArm.openBase.h_km`. -/
lemma accum_step_flow_trace_uniform {sc s' : L4YAML.Scanner.ScannerState} {c : Char}
    {sp_block sp_flow sp_scan sp_block' sp_flow' : SurfPos} {ev : List Event} (km : Array Bool)
    (arm : L4YAML.Proofs.StreamAccum.FlowArm sc s' c sp_block sp_flow sp_scan sp_block' sp_flow') :
    ∃ ev_g,
      (0 < sc.flowLevel ∧ ∃ km',
        ((c = ',' ∧ km' = km) ∨
          ((c = '[' ∨ c = '{') ∧ ColonKeyCase sc ∧
            ∃ b, km' = km.push b ∧ (b = true ↔ ∃ kj, tailOf sc.tokens = .colon kj)) ∨
          ((c = ']' ∨ c = '}') ∧ km' = km.pop)) ∧
        ∀ {n : Nat}, n ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf sc →
          TFlowStackB n sc.flowLevel sc.flowStack km (tailOf sc.tokens) sp_block sp_flow ev →
          TFlowStackB n s'.flowLevel s'.flowStack km' (tailOf s'.tokens) sp_block' sp_flow' (ev ++ ev_g) ∧
          (∀ kj, tailOf s'.tokens = .value kj → (km' = km.pop ∧ km.back? = some true) ∨
            ∀ sp_prep sp_tok, (SSeparateLines n sp_flow' sp_prep ∨ sp_prep = sp_flow') →
              GLit ':' sp_prep sp_tok →
              TFlowStackB n s'.flowLevel s'.flowStack km' (.colon kj) sp_block' sp_tok (ev ++ ev_g))) ∨
      (s'.flowLevel = 0 ∧ s'.flowStack = #[] ∧ 0 < sc.flowLevel ∧ sp_flow' = sp_block' ∧
        ∀ {n : Nat}, n ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf sc →
          TFlowStackB n sc.flowLevel sc.flowStack km (tailOf sc.tokens) sp_block sp_flow ev →
          ∃ sp_br sp_tok, TFlowContent n .flowOut sp_br sp_tok (ev ++ ev_g) ∧
            TFlowStackB n 0 #[] #[] (tailOf s'.tokens) sp_block' sp_flow' []) ∨
      (sc.flowLevel = 0 ∧ ev_g = [] ∧ (∃ kc, KmSound s' #[false] kc) ∧
        (∀ kj, tailOf s'.tokens ≠ .value kj) ∧
        ∀ n, TFlowStackB n s'.flowLevel s'.flowStack #[false] (tailOf s'.tokens) sp_block' sp_flow' []) := by
  cases arm with
  | openBase b sp_br sp_open sp_block'' sp_flow'' h_depth h_c h_open h_fl h_ks h_tl h_km h_sp =>
    refine ⟨[], Or.inr (Or.inr ⟨h_depth, rfl, h_km, (fun _ h => by rw [h_tl] at h; cases h),
      fun n => ?_⟩)⟩
    rw [h_fl, h_ks, h_tl, h_sp]
    cases b
    · have h_open' : GLit '{' sp_br sp_open := by subst h_c; simpa using h_open
      exact TFlowStackB.openMapBase h_open' (GOpt.none sp_open)
    · have h_open' : GLit '[' sp_br sp_open := by subst h_c; simpa using h_open
      exact TFlowStackB.openSeqBase h_open' (GOpt.none sp_open)
  | openNest b sp_flow₂ sp_br sp_open gap h_depth h_c h_tail h_klay h_lead h_open h_fl h_ks h_tl =>
    obtain ⟨d, hd⟩ : ∃ d, sc.flowLevel = d + 1 := ⟨sc.flowLevel - 1, by omega⟩
    have h_ctag : c = '[' ∨ c = '{' := by subst h_c; cases b <;> simp
    cases gap with
    | props ha ht sp_p h_tail₀ h_lead₀ h_run _ h_held =>
      obtain ⟨ev_p, hp₀⟩ := PropsRun.toT ((h_run _).resolve_right (fun h => h (Nat.le_refl _)))
      refine ⟨ev_p, Or.inl ⟨by omega, _,
        Or.inr (Or.inl ⟨h_ctag, h_klay, kmBit (tailOf sc.tokens), rfl, kmBit_iff _⟩),
        fun {n} hn hT => ?_⟩⟩
      have hp := TCNsProperties_floor_mono hn hp₀
      generalize hks : sc.flowStack = ks at hT
      rw [hd] at hT
      cases hT with
      | «open» _ _ _ _ _ _ _ hTO =>
      have h_lead₀' := (h_lead₀ n).resolve_right (fun h => h hn)
      have h_psep : SSeparate n .flowIn sp_scan sp_br :=
        ((h_lead n).resolve_right (fun h => h hn)).resolve_right (fun h => h_held h.2.2)
      rw [h_fl, h_ks, h_tl, hd, hks]
      refine ⟨?_, fun _ h => nomatch h⟩
      cases b
      · have h_open' : GLit '{' sp_br sp_flow' := by subst h_c; simpa using h_open
        exact .open _ _ _ _ _ _ _ (TFlowOpenStack.retrace (by simp)
          (hTO.openNestMapProps (kmBit_iff _) h_tail₀ h_lead₀' hp h_psep h_open'))
      · have h_open' : GLit '[' sp_br sp_flow' := by subst h_c; simpa using h_open
        exact .open _ _ _ _ _ _ _ (TFlowOpenStack.retrace (by simp)
          (hTO.openNestSeqProps (kmBit_iff _) h_tail₀ h_lead₀' hp h_psep h_open'))
    | white _ h_nil =>
      refine ⟨[], Or.inl ⟨by omega, _,
        Or.inr (Or.inl ⟨h_ctag, h_klay, kmBit (tailOf sc.tokens), rfl, kmBit_iff _⟩),
        fun {n} hn hT => ?_⟩⟩
      generalize hks : sc.flowStack = ks at hT
      rw [hd] at hT
      cases hT with
      | «open» _ _ _ _ _ _ _ hTO =>
      have h_lead' := (h_lead n).resolve_right (fun h => h hn)
      rw [L4YAML.Proofs.StreamAccum.gapTail_of_nil h_nil] at h_lead'
      replace h_lead' := h_lead'.imp id (fun h => And.intro h.1 h.2.1)
      rw [h_fl, h_ks, h_tl, hd, hks]
      refine ⟨?_, fun _ h => nomatch h⟩
      cases b
      · have h_open' : GLit '{' sp_br sp_flow' := by subst h_c; simpa using h_open
        exact .open _ _ _ _ _ _ _ (hTO.openNestMap (kmBit_iff _) h_tail h_lead' h_open')
      · have h_open' : GLit '[' sp_br sp_flow' := by subst h_c; simpa using h_open
        exact .open _ _ _ _ _ _ _ (hTO.openNestSeq (kmBit_iff _) h_tail h_lead' h_open')
  | comma sp_flow₂ sp_prep sp_tok gap h_depth h_c h_tail h_lead h_lit h_fl h_ks h_tl =>
    obtain ⟨d, hd⟩ : ∃ d, sc.flowLevel = d + 1 := ⟨sc.flowLevel - 1, by omega⟩
    obtain ⟨ev_g, hG⟩ := gapRead_onT_uniform gap
    refine ⟨ev_g, Or.inl ⟨by omega, _, Or.inl ⟨h_c, rfl⟩, fun {n} hn hT => ?_⟩⟩
    generalize hks : sc.flowStack = ks at hT
    rw [hd] at hT
    cases hT with
    | «open» _ _ _ _ _ _ _ hTO =>
    have h_lead' := (h_lead n).resolve_right (fun h => h hn)
    have hTO₂ := hG hn hTO
    rw [h_fl, h_ks, h_tl, hd, hks]
    exact ⟨.open _ _ _ _ _ _ _ (hTO₂.comma h_tail h_lead' h_lit), fun _ h => nomatch h⟩
  | closeNested b sp_flow₂ sp_prep sp_tok gap h_depth h_c h_top h_lead h_lit h_fl h_ks h_tl =>
    obtain ⟨d, hd⟩ : ∃ d, sc.flowLevel = d + 1 + 1 := ⟨sc.flowLevel - 2, by omega⟩
    have h_ctag : c = ']' ∨ c = '}' := by subst h_c; cases b <;> simp
    obtain ⟨ev_g, hG⟩ := gapRead_onT_uniform gap
    refine ⟨ev_g, Or.inl ⟨by omega, _, Or.inr (Or.inr ⟨h_ctag, rfl⟩), fun {n} hn hT => ?_⟩⟩
    generalize hks : sc.flowStack = ks at hT
    rw [hd] at hT
    cases hT with
    | «open» _ _ _ _ _ _ _ hTO =>
    have h_lead' := (h_lead n).resolve_right (fun h => h hn)
    have hTO₂ := hG hn hTO
    have h_fl' : s'.flowLevel = d + 1 := by omega
    rw [h_fl', h_ks, h_tl, hks]
    rw [hks] at h_top
    generalize hE : ev ++ ev_g = evT at hTO₂ ⊢
    generalize hgt : L4YAML.Proofs.StreamAccum.gapTail sc = tl₂ at hTO₂ h_lead'
    cases hTO₂ with
    | seqNest _ ks₀ km₀ b₀ tl_par _ _ _ _ _ _ _ _ _ parent h_b₀ h_tail_p h_lead_p h_open h_sep st =>
      rw [Array.back?_push] at h_top
      cases b
      · simp at h_top
      · have h_lit' : GLit ']' sp_prep sp_flow' := by subst h_c; simpa using h_lit
        rw [Array.pop_push, Array.pop_push, Array.back?_push]
        refine ⟨.open _ _ _ _ _ _ _
          (TFlowOpenStack.closeNestedSeq parent h_tail_p h_lead_p h_open h_sep st h_lead' h_lit'),
          fun kj hkj => ?_⟩
        cases FrameTail.value.inj hkj
        cases b₀
        · refine Or.inr (fun sp_p sp_t h_l h_col => .open _ _ _ _ _ _ _
            (TFlowOpenStack.closeNestedSeqColon parent ?_ h_lead_p h_open h_sep st h_lead' h_lit' h_l h_col))
          cases tl_par with
          | sep => exact Or.inl rfl
          | question => exact Or.inr rfl
          | colon kj => exact absurd (h_b₀.2 ⟨kj, rfl⟩) Bool.false_ne_true
          | value kj => exact absurd rfl (h_tail_p kj)
        · exact Or.inl ⟨rfl, rfl⟩
    | mapNest _ ks₀ km₀ b₀ tl_par _ _ _ _ _ _ _ _ _ parent h_b₀ h_tail_p h_lead_p h_open h_sep st =>
      rw [Array.back?_push] at h_top
      cases b
      · have h_lit' : GLit '}' sp_prep sp_flow' := by subst h_c; simpa using h_lit
        rw [Array.pop_push, Array.pop_push, Array.back?_push]
        refine ⟨.open _ _ _ _ _ _ _
          (TFlowOpenStack.closeNestedMap parent h_tail_p h_lead_p h_open h_sep st h_lead' h_lit'),
          fun kj hkj => ?_⟩
        cases FrameTail.value.inj hkj
        cases b₀
        · refine Or.inr (fun sp_p sp_t h_l h_col => .open _ _ _ _ _ _ _
            (TFlowOpenStack.closeNestedMapColon parent ?_ h_lead_p h_open h_sep st h_lead' h_lit' h_l h_col))
          cases tl_par with
          | sep => exact Or.inl rfl
          | question => exact Or.inr rfl
          | colon kj => exact absurd (h_b₀.2 ⟨kj, rfl⟩) Bool.false_ne_true
          | value kj => exact absurd rfl (h_tail_p kj)
        · exact Or.inl ⟨rfl, rfl⟩
      · simp at h_top
    | seqNestProps _ ks₀ km₀ b₀ tl_par _ _ _ _ _ _ _ _ _ _ _ _ parent h_b₀ h_tail_p h_lead_p h_props h_psep h_open h_sep st =>
      rw [Array.back?_push] at h_top
      cases b
      · simp at h_top
      · have h_lit' : GLit ']' sp_prep sp_flow' := by subst h_c; simpa using h_lit
        rw [Array.pop_push, Array.pop_push, Array.back?_push]
        refine ⟨.open _ _ _ _ _ _ _
          (TFlowOpenStack.closeNestedSeqProps parent h_tail_p h_lead_p h_props h_psep h_open h_sep st
            h_lead' h_lit'),
          fun kj hkj => ?_⟩
        cases FrameTail.value.inj hkj
        cases b₀
        · refine Or.inr (fun sp_p sp_t h_l h_col => .open _ _ _ _ _ _ _
            (TFlowOpenStack.closeNestedSeqPropsColon parent ?_ h_lead_p h_props h_psep h_open h_sep st
              h_lead' h_lit' h_l h_col))
          cases tl_par with
          | sep => exact Or.inl rfl
          | question => exact Or.inr rfl
          | colon kj => exact absurd (h_b₀.2 ⟨kj, rfl⟩) Bool.false_ne_true
          | value kj => exact absurd rfl (h_tail_p kj)
        · exact Or.inl ⟨rfl, rfl⟩
    | mapNestProps _ ks₀ km₀ b₀ tl_par _ _ _ _ _ _ _ _ _ _ _ _ parent h_b₀ h_tail_p h_lead_p h_props h_psep h_open h_sep st =>
      rw [Array.back?_push] at h_top
      cases b
      · have h_lit' : GLit '}' sp_prep sp_flow' := by subst h_c; simpa using h_lit
        rw [Array.pop_push, Array.pop_push, Array.back?_push]
        refine ⟨.open _ _ _ _ _ _ _
          (TFlowOpenStack.closeNestedMapProps parent h_tail_p h_lead_p h_props h_psep h_open h_sep st
            h_lead' h_lit'),
          fun kj hkj => ?_⟩
        cases FrameTail.value.inj hkj
        cases b₀
        · refine Or.inr (fun sp_p sp_t h_l h_col => .open _ _ _ _ _ _ _
            (TFlowOpenStack.closeNestedMapPropsColon parent ?_ h_lead_p h_props h_psep h_open h_sep st
              h_lead' h_lit' h_l h_col))
          cases tl_par with
          | sep => exact Or.inl rfl
          | question => exact Or.inr rfl
          | colon kj => exact absurd (h_b₀.2 ⟨kj, rfl⟩) Bool.false_ne_true
          | value kj => exact absurd rfl (h_tail_p kj)
        · exact Or.inl ⟨rfl, rfl⟩
      · simp at h_top
  | closeBase b sp_flow₂ sp_prep sp_tok gap h_depth h_c h_top h_lead h_lit h_fl h_ks h_tl =>
    obtain ⟨ev_g, hG⟩ := gapRead_onT_uniform gap
    refine ⟨ev_g, Or.inr (Or.inl ⟨h_fl, h_ks, by omega, rfl, fun {n} hn hT => ?_⟩)⟩
    generalize hks : sc.flowStack = ks at hT
    rw [h_depth] at hT
    cases hT with
    | «open» _ _ _ _ _ _ _ hTO =>
    have h_lead' := (h_lead n).resolve_right (fun h => h hn)
    have hTO₂ := hG hn hTO
    rw [h_tl]
    rw [hks] at h_top
    generalize hE : ev ++ ev_g = evT at hTO₂ ⊢
    generalize hgt : L4YAML.Proofs.StreamAccum.gapTail sc = tl₂ at hTO₂ h_lead'
    cases hTO₂ with
    | seqBase _ sp_br _ _ _ _ _ h_open h_sep st =>
      cases b
      · exact absurd h_top (by decide)
      · have h_lit' : GLit ']' sp_prep sp_tok := by subst h_c; simpa using h_lit
        exact ⟨sp_br, sp_tok, TSeqFrame.closeBase h_open h_sep st h_lead' h_lit'⟩
    | mapBase _ sp_br _ _ _ _ _ h_open h_sep st =>
      cases b
      · have h_lit' : GLit '}' sp_prep sp_tok := by subst h_c; simpa using h_lit
        exact ⟨sp_br, sp_tok, TMapFrame.closeBase h_open h_sep st h_lead' h_lit'⟩
      · exact absurd h_top (by decide)
    | seqNest _ _ _ _ _ _ _ _ _ _ _ _ _ _ parent _ _ _ _ _ _ => cases parent
    | mapNest _ _ _ _ _ _ _ _ _ _ _ _ _ _ parent _ _ _ _ _ _ => cases parent
    | seqNestProps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ parent _ _ _ _ _ _ _ _ => cases parent
    | mapNestProps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ parent _ _ _ _ _ _ _ _ => cases parent

/-- Item 520 (price (3) PR 2, the fold): the flow-indicator step on `TFlowStackK` — the S step
    `accum_step_flow` whole, its `FlowArm` read into the T twin at every floor at once
    (`accum_step_flow_trace_uniform`), the T mask re-packed by the dispatcher's face
    (`dispatchFlow_km_faces`).  Two outcomes: the T stack steps (open / `,` / nested close, the
    `.value`-tail closure by `close_layout_of_bit` or item 513's `closeNested*Colon`), or the base
    close ends the flow node — `TFlowContent` at every floor the S half admitted, the T stack back
    to `nil` with the empty mask.  No `StreamAccum` arm is re-proved here. -/
lemma accum_step_flow_pairK {ev : List Event} (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flowK : TFlowStackK sp_start sc sc.flowLevel sc.flowStack (tailOf sc.tokens) sp_block sp_flow ev)
    (h_pending : sc.flowLevel = 0 → PendingNode sc false sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_interior : sc.flowLevel ≥ 1 →
      InteriorGap sc (tailOf sc.tokens) sp_flow sp_scan ∧
        LastTokenReal sc.tokens ∧ sc.allowDirectives = false)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_sound : PendingKeySound.Sound sc)
    (h_dn : scanNextToken_checkDanglingNode sc s_prep = .ok ())
    (h_fv : scanNextToken_checkFlowValueIndent sc s_prep = .ok ())
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    (h_base : IndentStackBase.SentinelBase sc)
    (h_mono : IndentStackMono.Mono sc)
    (h_str_none : scanNextToken_dispatchStructural s_prep c = .ok none)
    (h_dispatch : scanNextToken_dispatchFlowIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan' ev_g,
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      L4YAML.Proofs.StreamAccum.FlowArm sc s' c sp_block sp_flow sp_scan sp_block' sp_flow' ∧
      (TFlowStackK sp_start s' s'.flowLevel s'.flowStack (tailOf s'.tokens) sp_block' sp_flow' (ev ++ ev_g) ∨
        (s'.flowLevel = 0 ∧ 0 < sc.flowLevel ∧
          TFlowStackK sp_start s' s'.flowLevel s'.flowStack (tailOf s'.tokens) sp_block' sp_flow' [] ∧
          ∀ n, n ≤ minContentIndentOf sc →
            ∃ sp_br sp_tok, TFlowContent n .flowOut sp_br sp_tok (ev ++ ev_g))) ∧
      (s'.flowLevel = 0 → PendingNode s' false sp_start sp_flow' sp_scan') ∧
      ScannerSurfCorr s' sp_scan' ∧
      (s'.flowLevel ≥ 1 →
        InteriorGap s' (tailOf s'.tokens) sp_flow' sp_scan' ∧
          LastTokenReal s'.tokens ∧ s'.allowDirectives = false) := by
  obtain ⟨hS, km, kc, hKm, hTall⟩ := h_flowK
  obtain ⟨g, b, f, sn, q1, q2, ⟨q3, arm⟩, q4, q5, q6⟩ :=
    accum_step_flow sc sp_start sp_gram sp_block sp_flow sp_scan s_prep s' c
      h_stream h_stack hS h_pending h_corr h_sound h_mono h_interior h_preprocess h_dn h_fv h_str_none
      h_dispatch h_bare h_base
  have h_ksz : km.size = sc.flowLevel := TFlowStackB.km_size (hTall 0 (Nat.zero_le _)).1
  obtain ⟨ev_g, hU⟩ := accum_step_flow_trace_uniform km arm
  refine ⟨g, b, f, sn, ev_g, q1, q2, arm, ?_, q4, q5, q6⟩
  rcases hU with ⟨hflow, km', heff, hstep⟩ | ⟨hfl0, hks0, hflow, _, hclose⟩ |
    ⟨hsc0, hevg, ⟨kc0, hkm0⟩, htl', hopen⟩
  · -- The floor ceiling rides a nested step: the dispatcher keeps the indents, so does the
    -- in-flow preprocess.
    obtain ⟨d, hd⟩ : ∃ d, sc.flowLevel = d + 1 := ⟨sc.flowLevel - 1, by omega⟩
    have hmin : minContentIndentOf s' = minContentIndentOf sc :=
      L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf_congr
        ((L4YAML.Proofs.FlowIndentStable.dispatchFlowIndicators_preserves_indents h_dispatch).trans
          ((by split <;> rfl : (if s_prep.allowDirectives then
              { s_prep with allowDirectives := false, documentEverStarted := true }
            else s_prep).indents = s_prep.indents).trans
            (L4YAML.Proofs.FlowIndentStable.preprocess_indents_of_inFlow
              (inFlow_of_flowLevel_eq hd) h_preprocess)))
    have hkpos : 0 < km.size := by omega
    have hfaces := dispatchFlow_km_faces hflow hkpos hKm h_preprocess h_dispatch
    have hK : KmSound s' km' kc ∧
        (km' = km.pop → km.back? = some true →
          L4YAML.Proofs.EntryBoundaryLayout.KeyAfterValueLayout s') := by
      rcases heff with ⟨hc, rfl⟩ | ⟨hc, hklay, b', rfl, hb⟩ | ⟨hc, rfl⟩
      · rcases hfaces with ⟨hc', _⟩ | ⟨hc', _⟩ | ⟨_, hK⟩
        · rcases hc' with h | h <;> simp [hc] at h
        · rcases hc' with h | h <;> simp [hc] at h
        · refine ⟨hK, fun hpop _ => ?_⟩
          have := congrArg Array.size hpop
          simp at this
          omega
      · rcases hfaces with ⟨_, hK⟩ | ⟨hc', _⟩ | ⟨hc', _⟩
        · have hbit : b' = kmBit (tailOf sc.tokens) := Bool.eq_iff_iff.2 (hb.trans (kmBit_iff _).symm)
          refine ⟨hbit ▸ hK hklay, fun hpop _ => ?_⟩
          have := congrArg Array.size hpop
          simp at this
          omega
        · rcases hc with rfl | rfl <;> rcases hc' with h | h <;> simp at h
        · rcases hc with rfl | rfl <;> simp at hc'
      · rcases hfaces with ⟨hc', _⟩ | ⟨_, hK⟩ | ⟨hc', _⟩
        · rcases hc with rfl | rfl <;> rcases hc' with h | h <;> simp at h
        · have hdec := Array.eq_push_pop_back!_of_size_ne_zero (xs := km) (by omega)
          obtain ⟨hK1, hK2⟩ := hK km.pop km.back! hdec
          refine ⟨hK1, fun _ hback => hK2 ?_⟩
          rw [hdec, Array.back?_push] at hback
          exact Option.some.inj hback
        · rcases hc with rfl | rfl <;> simp at hc'
    refine Or.inl ⟨q3, km', kc, hK.1, fun n hn => ?_⟩
    rw [hmin] at hn
    obtain ⟨hT', hcl⟩ := hstep hn (hTall n hn).1
    refine ⟨hT', fun _ kj htl => ?_⟩
    rcases hcl kj htl with ⟨hpop, hback⟩ | hcont
    · exact Or.inl (hK.2 hpop hback)
    · exact Or.inr hcont
  · -- The base close: the flow node is done, the T stack back to `nil`.
    obtain ⟨d, hd⟩ : ∃ d, sc.flowLevel = d + 1 := ⟨sc.flowLevel - 1, by omega⟩
    have hmin : minContentIndentOf s' = minContentIndentOf sc :=
      L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf_congr
        ((L4YAML.Proofs.FlowIndentStable.dispatchFlowIndicators_preserves_indents h_dispatch).trans
          ((by split <;> rfl : (if s_prep.allowDirectives then
              { s_prep with allowDirectives := false, documentEverStarted := true }
            else s_prep).indents = s_prep.indents).trans
            (L4YAML.Proofs.FlowIndentStable.preprocess_indents_of_inFlow
              (inFlow_of_flowLevel_eq hd) h_preprocess)))
    refine Or.inr ⟨hfl0, hflow, ⟨q3, #[], kc, KmSound.empty s' kc, fun n hn => ?_⟩, fun n hn => ?_⟩
    · rw [hmin] at hn
      obtain ⟨_, _, _, hnil⟩ := hclose hn (hTall n hn).1
      refine ⟨?_, fun h0 => absurd h0 (by omega)⟩
      rw [hfl0, hks0]
      exact hnil
    · obtain ⟨sp_br, sp_tok, hcont, _⟩ := hclose hn (hTall n hn).1
      exact ⟨sp_br, sp_tok, hcont⟩
  · -- The base open: the T stack was `nil` (no events), the new mask `#[false]` sound by the carrier.
    subst hevg
    have hev : ev = [] := by
      have h0 := (hTall 0 (Nat.zero_le _)).1
      generalize hks : sc.flowStack = ks at h0
      rw [hsc0] at h0
      cases h0 with
      | nil => rfl
      | «open» _ _ _ _ _ _ _ h => cases h
    subst hev
    exact Or.inl ⟨q3, #[false], kc0, hkm0, fun n _ => ⟨hopen n, fun _ kj h => absurd h (htl' kj)⟩⟩


/-! ## §12 The key step on the T stack (item 522)

`accum_step_block`'s six in-flow `?` / `:` arms (`KeyArm`, item 499) folded onto `TFlowStackK` at
every floor: the T twins are FlowWalk §6's `receiveQuestion` / `receiveColonSep` /
`receiveColonQuestion` / `receiveColonProps*`; the `.value kj`-tail `:` is the T closure's right
disjunct (item 509), selected by `KeyArm.colonValue.h_layout`.  The mask is unchanged across a
key step (no frame opens or closes); `KmSound` is re-packed by `scanKey_km_transport` /
`scanValue_km_transport` under the block dispatcher's in-flow split. -/

/-- In flow the block dispatcher fires only as `scanKey` (`?`) or `scanValue` (`:`): the `-` arm is
    gated by `!s.inFlow`. -/
lemma dispatchBlock_inFlow_cases {s_ad s' : ScannerState} {c : Char}
    (h_inflow : s_ad.inFlow = true)
    (h : scanNextToken_dispatchBlockIndicators s_ad c = .ok (some s')) :
    (c = '?' ∧ scanKey s_ad = .ok s') ∨ (c = ':' ∧ scanValue s_ad = .ok s') := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [h_inflow, Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i heq
    have hc : c = '?' := by
      simp only [Bool.and_eq_true, beq_iff_eq] at heq
      exact heq.1.1.1
    cases hk : scanKey s_ad with
    | error e => rw [hk] at h; simp at h
    | ok sk =>
      rw [hk] at h
      simp only [Except.ok.injEq, Option.some.injEq] at h
      exact Or.inl ⟨hc, by rw [h]⟩
  · split at h
    · rename_i heq
      have hc : c = ':' := by
        simp only [Bool.and_eq_true, beq_iff_eq] at heq
        exact heq.1
      cases hv : scanValue s_ad with
      | error e => rw [hv] at h; simp at h
      | ok sv =>
        rw [hv] at h
        simp only [Except.ok.injEq, Option.some.injEq] at h
        exact Or.inr ⟨hc, by rw [h]⟩
    · simp at h

/-- The mask across a key step: unchanged, and `KmSound` re-packed through the two feeders. -/
lemma dispatchBlock_km_faces {sc s_prep s' : ScannerState} {c : Char} {km : Array Bool} {kc : Nat}
    (h_flow : 0 < sc.flowLevel)
    (h_km : KmSound sc km kc)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    KmSound s' km kc := by
  have hpeek_ad : (if s_prep.allowDirectives = true then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep).peek? = s_prep.peek? := by split <;> rfl
  have hfl_ad : (if s_prep.allowDirectives = true then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep).flowLevel = sc.flowLevel := by
    rw [← preprocess_preserves_flowLevel sc s_prep c h_preprocess]; split <;> rfl
  generalize h_ad_def : (if s_prep.allowDirectives = true then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep) = s_ad at h_dispatch hpeek_ad hfl_ad
  have hpk : s_ad.peek? = some c := hpeek_ad.trans (preprocess_some_peek h_preprocess)
  have h_hm : s_ad.offset < s_ad.inputEnd := by
    unfold ScannerState.peek? at hpk
    split at hpk
    · assumption
    · exact absurd hpk (by simp)
  have h_inflow : s_ad.inFlow = true :=
    inFlow_of_flowLevel_eq (n := sc.flowLevel - 1) (by rw [hfl_ad]; omega)
  rcases dispatchBlock_inFlow_cases h_inflow h_dispatch with ⟨_, hk⟩ | ⟨_, hv⟩
  · exact scanKey_km_transport h_flow h_inflow h_km h_preprocess h_ad_def h_hm hk
  · exact scanValue_km_transport h_flow h_inflow h_km h_preprocess h_ad_def hv

/-- The indents (the floor ceiling) ride a key step. -/
lemma dispatchBlock_indents_of_inFlow {sc s_prep s' : ScannerState} {c : Char}
    (h_flow : 0 < sc.flowLevel)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    s'.indents = sc.indents := by
  have hfl_ad : (if s_prep.allowDirectives = true then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep).flowLevel = sc.flowLevel := by
    rw [← preprocess_preserves_flowLevel sc s_prep c h_preprocess]; split <;> rfl
  have hind_ad : (if s_prep.allowDirectives = true then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep).indents = sc.indents := by
    rw [← L4YAML.Proofs.FlowIndentStable.preprocess_indents_of_inFlow
      (inFlow_of_flowLevel_eq (n := sc.flowLevel - 1) (by omega)) h_preprocess]
    split <;> rfl
  generalize h_ad_def : (if s_prep.allowDirectives = true then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep) = s_ad at h_dispatch hfl_ad hind_ad
  have h_inflow : s_ad.inFlow = true :=
    inFlow_of_flowLevel_eq (n := sc.flowLevel - 1) (by rw [hfl_ad]; omega)
  rcases dispatchBlock_inFlow_cases h_inflow h_dispatch with ⟨_, hk⟩ | ⟨_, hv⟩
  · exact (L4YAML.Proofs.FlowIndentStable.scanKey_indents_of_inFlow h_inflow hk).trans hind_ad
  · exact (L4YAML.Proofs.FlowIndentStable.scanValue_indents_of_inFlow h_inflow hv).trans hind_ad

/-- Every key arm keeps `flowLevel` and `flowStack`, and lands on `sp_block` / its `:` or `?`. -/
lemma KeyArm.rides {sc s' : ScannerState} {c : Char} {sp_block sp_flow sp_scan sp_block' sp_flow' : SurfPos}
    (arm : L4YAML.Proofs.StreamAccum.KeyArm sc s' c sp_block sp_flow sp_scan sp_block' sp_flow') :
    s'.flowLevel = sc.flowLevel ∧ s'.flowStack = sc.flowStack ∧ sp_block' = sp_block := by
  cases arm <;> exact ⟨‹_›, ‹_›, rfl⟩

/-- No key arm leaves a `.value` tail: the T closure obligation is vacuous after the step. -/
lemma KeyArm.tail_ne_value {sc s' : ScannerState} {c : Char} {sp_block sp_flow sp_scan sp_block' sp_flow' : SurfPos}
    (arm : L4YAML.Proofs.StreamAccum.KeyArm sc s' c sp_block sp_flow sp_scan sp_block' sp_flow')
    (kj : Bool) : tailOf s'.tokens ≠ .value kj := by
  intro h
  cases arm <;> simp_all

/-- The key step's T twin at every floor, one event suffix: `[]` on the white arms (the `?` / `:`
    emit no event), the held run's `ev_p` on the two props arms — taken at the ceiling and lowered
    by `TCNsProperties_floor_mono`, so the suffix is the same at every floor.  The `.value kj`-tail
    `:` is paid by the T closure `TFlowStackK` carries (item 509), whose right disjunct
    `KeyArm.colonValue.h_layout` selects. -/
lemma accum_step_key_trace {d : Nat} {sc s' : ScannerState} {c : Char}
    {sp_block sp_flow sp_scan sp_block' sp_flow' : SurfPos} {ks km : Array Bool} {ev : List Event}
    (arm : L4YAML.Proofs.StreamAccum.KeyArm sc s' c sp_block sp_flow sp_scan sp_block' sp_flow') :
    ∃ ev_g, ∀ n, n ≤ minContentIndentOf sc →
      TFlowStackB n (d + 1) ks km (tailOf sc.tokens) sp_block sp_flow ev →
      (∀ kj, tailOf sc.tokens = .value kj →
        L4YAML.Proofs.EntryBoundaryLayout.KeyAfterValueLayout sc ∨
        ∀ sp_prep sp_tok, (SSeparateLines n sp_flow sp_prep ∨ sp_prep = sp_flow) →
          GLit ':' sp_prep sp_tok → TFlowStackB n (d + 1) ks km (.colon kj) sp_block sp_tok ev) →
      TFlowStackB n (d + 1) ks km (tailOf s'.tokens) sp_block' sp_flow' (ev ++ ev_g) := by
  cases arm with
  | question sp_prep sp_tok h_c h_tail h_run h_lead h_lit h_fl h_ks h_tl =>
    refine ⟨[], fun n hn hT _ => ?_⟩
    rw [List.append_nil, h_tl]
    cases hT with
    | «open» _ _ _ _ _ _ _ hTO =>
      exact .open _ _ _ _ _ _ _ (hTO.receiveQuestion h_tail
        (((h_lead n).resolve_right (fun h => h hn)).imp id (fun h => ⟨h, by rw [h_tail]; rfl⟩)) h_lit)
  | colonValue kj sp_prep sp_tok h_c h_tail h_run h_lead h_lit h_layout h_fl h_ks h_tl =>
    refine ⟨[], fun n hn hT hcl => ?_⟩
    rw [List.append_nil, h_tl]
    exact ((hcl kj h_tail).resolve_left h_layout) _ _
      ((h_lead n).resolve_right (fun h => h hn)) h_lit
  | colonSep sp_prep sp_tok h_c h_tail h_run h_lead h_lit h_fl h_ks h_tl =>
    refine ⟨[], fun n hn hT _ => ?_⟩
    rw [List.append_nil, h_tl]
    cases hT with
    | «open» _ _ _ _ _ _ _ hTO =>
      exact .open _ _ _ _ _ _ _ (hTO.receiveColonSep h_tail
        (((h_lead n).resolve_right (fun h => h hn)).imp id (fun h => ⟨h, by rw [h_tail]; rfl⟩)) h_lit)
  | colonQuestion sp_prep sp_tok h_c h_tail h_run h_lead h_lit h_fl h_ks h_tl =>
    refine ⟨[], fun n hn hT _ => ?_⟩
    rw [List.append_nil, h_tl]
    cases hT with
    | «open» _ _ _ _ _ _ _ hTO =>
      exact .open _ _ _ _ _ _ _ (hTO.receiveColonQuestion h_tail
        (Or.inl ((h_lead n).resolve_right (fun h => h hn))) h_lit)
  | colonPropsSep ha ht sp_p sp_prep sp_tok h_c h_tail h_held h_lead h_run h_sep h_lit h_fl h_ks h_tl =>
    obtain ⟨ev_p, hp₀⟩ :=
      L4YAML.Proofs.Serialization.TraceOf.FlowWalk.PropsRun.toT
        ((h_run _).resolve_right (fun h => h (Nat.le_refl _)))
    refine ⟨ev_p, fun n hn hT _ => ?_⟩
    rw [h_tl]
    cases hT with
    | «open» _ _ _ _ _ _ _ hTO =>
      have hp := TCNsProperties_floor_mono hn hp₀
      have h_gap : GOpt (SSeparate n .flowIn) sp_scan sp_prep := by
        rcases (h_sep n).resolve_right (fun h => h hn) with hs | hs
        · exact GOpt.some _ _ hs
        · cases hs; exact GOpt.none _
      exact .open _ _ _ _ _ _ _ (hTO.receiveColonPropsSep h_tail
        ((h_lead n).resolve_right (fun h => h hn)) hp h_gap h_lit)
  | colonPropsQuestion ha ht sp_p sp_prep sp_tok h_c h_tail h_held h_lead h_run h_sep h_lit h_fl h_ks h_tl =>
    obtain ⟨ev_p, hp₀⟩ :=
      L4YAML.Proofs.Serialization.TraceOf.FlowWalk.PropsRun.toT
        ((h_run _).resolve_right (fun h => h (Nat.le_refl _)))
    refine ⟨ev_p, fun n hn hT _ => ?_⟩
    rw [h_tl]
    cases hT with
    | «open» _ _ _ _ _ _ _ hTO =>
      have hp := TCNsProperties_floor_mono hn hp₀
      have h_gap : GOpt (SSeparate n .flowIn) sp_scan sp_prep := by
        rcases (h_sep n).resolve_right (fun h => h hn) with hs | hs
        · exact GOpt.some _ _ hs
        · cases hs; exact GOpt.none _
      exact .open _ _ _ _ _ _ _ (hTO.receiveColonPropsQuestion h_tail
        ((h_lead n).resolve_right (fun h => h hn)) hp h_gap h_lit)

/-- **The key fold (item 522).**  `accum_step_block`'s in-flow `?` / `:` step carried from
    `TFlowStackK sc` to `TFlowStackK s'` at every floor the post-state admits, with the arm it
    took, one event suffix across floors, the mask unchanged and `KmSound` re-packed. -/
lemma accum_step_key_pairK {ev : List Event} (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_kbc : ScannerCorrectness.KeysBehindCursor sc)
    (h_scf : StaleCursorFloor.StaleKeyCursorFloor sc)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flowK : TFlowStackK sp_start sc sc.flowLevel sc.flowStack (tailOf sc.tokens) sp_block sp_flow ev)
    (h_pending : sc.flowLevel = 0 → PendingNode sc false sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_interior : sc.flowLevel ≥ 1 →
      InteriorGap sc (tailOf sc.tokens) sp_flow sp_scan ∧
        LastTokenReal sc.tokens ∧ sc.allowDirectives = false)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dn : scanNextToken_checkDanglingNode sc s_prep = .ok ())
    (h_fv : scanNextToken_checkFlowValueIndent sc s_prep = .ok ())
    (h_str_none : scanNextToken_dispatchStructural s_prep c = .ok none)
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s'))
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    (h_base : IndentStackBase.SentinelBase sc)
    (h_mono : IndentStackMono.Mono sc)
    (h_sound : PendingKeySound.Sound sc)
    (h_cf : ColFloor.ColFloor sc) (h_lkt : ScalarWalkColFloor.LiveKeyTop sc)
    (h_pos : 0 < sc.flowLevel) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan' ev_g,
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      L4YAML.Proofs.StreamAccum.KeyArm sc s' c sp_block sp_flow sp_scan sp_block' sp_flow' ∧
      TFlowStackK sp_start s' s'.flowLevel s'.flowStack (tailOf s'.tokens) sp_block' sp_flow' (ev ++ ev_g) ∧
      (s'.flowLevel = 0 → PendingNode s' false sp_start sp_flow' sp_scan') ∧
      ScannerSurfCorr s' sp_scan' ∧
      (s'.flowLevel ≥ 1 →
        InteriorGap s' (tailOf s'.tokens) sp_flow' sp_scan' ∧
          LastTokenReal s'.tokens ∧ s'.allowDirectives = false) := by
  obtain ⟨hS, km, kc, hKm, hTall⟩ := h_flowK
  obtain ⟨g, b, f, sn, q1, q2, q3, q4, q5, q6, q7⟩ :=
    accum_step_block sc sp_start sp_gram sp_block sp_flow sp_scan s_prep s' c
      h_stream h_kbc h_scf h_stack hS h_pending h_corr h_interior h_preprocess h_dn h_fv
      h_str_none h_dispatch h_bare h_base h_mono h_sound h_cf h_lkt
  have arm := q7 h_pos
  obtain ⟨d, hd⟩ : ∃ d, sc.flowLevel = d + 1 := ⟨sc.flowLevel - 1, by omega⟩
  have hmin : minContentIndentOf s' = minContentIndentOf sc :=
    L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf_congr
      (dispatchBlock_indents_of_inFlow h_pos h_preprocess h_dispatch)
  have hK' : KmSound s' km kc := dispatchBlock_km_faces h_pos hKm h_preprocess h_dispatch
  obtain ⟨hfl, hks, _⟩ := KeyArm.rides arm
  obtain ⟨ev_g, hstep⟩ := accum_step_key_trace (d := d) (ks := sc.flowStack) (km := km) (ev := ev) arm
  refine ⟨g, b, f, sn, ev_g, q1, q2, arm, ⟨q3, km, kc, hK', fun n hn => ?_⟩, q4, q5, q6⟩
  rw [hmin] at hn
  obtain ⟨hT, hcl⟩ := hTall n hn
  rw [hd] at hT hcl
  rw [hfl, hks, hd]
  exact ⟨hstep n hn hT (fun kj hkj => hcl (by omega) kj hkj),
    fun _ kj h => absurd h (KeyArm.tail_ne_value arm kj)⟩

end

end L4YAML.Proofs.Serialization.TraceOf.ContentBridge
