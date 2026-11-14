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
lemma accum_step_content_trace_in {n D : Nat} {ks : Array Bool}
    {s_ad s' : ScannerState} {c : Char} {sp_block sp_flow sp_prep sp_a : SurfPos}
    {ev : List Event}
    (arm : ContentArm s_ad s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_ad sp_prep) (hpeek : s_ad.peek? = some c)
    (h_inflow : s_ad.inFlow = true)
    (h_not_doc : s_ad.col = 0 → atDocumentBoundary s_ad = false)
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s')
    (hcol : s_ad.currentIndent < (s_ad.col : Int))
    (hn : (n : Int) ≤ max 0 (s_ad.currentIndent + 1))
    (hT : TFlowOpenStack n D ks (tailOf s_ad.tokens) sp_block sp_flow ev)
    (h_tail : ∀ kj, tailOf s_ad.tokens ≠ .value kj)
    (h_lead : SSeparateLines n sp_flow sp_prep ∨
      (sp_prep = sp_flow ∧ (tailOf s_ad.tokens).leadFree)) :
    ∃ ev_n, PushesTrace s_ad.tokens s'.tokens ev_n ∧
      ((∃ kj sp_ne, tailOf s'.tokens = .value kj ∧ GStar SSWhite sp_ne sp_a ∧
          SFlowNode n .flowIn sp_prep sp_ne ∧
          TFlowOpenStack n D ks (.value kj) sp_block sp_ne (ev ++ ev_n)) ∨
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
    refine ⟨[.useAlias name], ?_, Or.inl ⟨false, sp', h_tl', .nil _, .alias _ _ _ _ hT_alias.1, ?_⟩⟩
    · rw [htok]
      simpa [tokenEvent] using pushesTrace_push s_ad.tokens ⟨s_ad.currentPos, .alias name, s_ad.currentPos⟩ (by simp) (by simp)
    · exact hT.receiveNode h_tail h_lead (.alias _ _ _ _ _ hT_alias) (fun h => nomatch h)
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
  subst hsp_prep
  refine ⟨[], hsilent, Or.inl ⟨kj, sp_gram, h_tl', h_ws, h_node, ?_⟩⟩
  rcases SFlowNode_head_lift h_node ⟨hamp, hstar, hbang, hlb, hlc⟩ with
    ⟨hdq, hsq, hplain⟩ | ⟨hdq, hq⟩ | ⟨hsq, hq⟩
  · refine hT.receiveNode h_tail h_lead (.content _ _ _ _ _ (.plain _ _ _ _ hplain)) ?_
    intro hk
    rcases hkj hk with h | h
    · exact absurd h hdq
    · exact absurd h hsq
  · exact hT.receiveNode h_tail h_lead (.content _ _ _ _ _ (.doubleQ _ _ _ _ hq))
      (fun _ => .content _ _ _ _ _ (.doubleQ _ _ _ _ hq))
  · exact hT.receiveNode h_tail h_lead (.content _ _ _ _ _ (.singleQ _ _ _ _ hq))
      (fun _ => .content _ _ _ _ _ (.singleQ _ _ _ _ hq))

/-- The `.props` interior: a property run is held (`TCNsProperties`, item 472's lift of
    `PropsRun`), the content follows a separator, and the scalar arms land on the T flow stack
    through `receivePropsContent` with the run's events before the scalar's.  The alias arm is
    excluded by hypothesis: the dispatcher refuses `*` after a property inside a flow
    (`lastTokenIsNodeProperty`'s in-flow half; P113's two refused rows), and the property arms
    extend the run (the `_in` twin's second disjunct, run-free). -/
lemma accum_step_content_trace_in_props {n D : Nat} {ks : Array Bool}
    {s_ad s' : ScannerState} {c : Char} {sp_block sp_flow sp_p sp_e sp_prep sp_a : SurfPos}
    {ev ev_p : List Event}
    (arm : ContentArm s_ad s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_ad sp_prep) (hpeek : s_ad.peek? = some c)
    (h_inflow : s_ad.inFlow = true)
    (h_not_doc : s_ad.col = 0 → atDocumentBoundary s_ad = false)
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s')
    (hcol : s_ad.currentIndent < (s_ad.col : Int))
    (hn : (n : Int) ≤ max 0 (s_ad.currentIndent + 1))
    (hT : TFlowOpenStack n D ks (tailOf s_ad.tokens) sp_block sp_flow ev)
    (h_tail : ∀ kj, tailOf s_ad.tokens ≠ .value kj)
    (h_lead : SSeparateLines n sp_flow sp_p ∨
      (sp_p = sp_flow ∧ (tailOf s_ad.tokens).leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_e ev_p)
    (h_sep : SSeparate n .flowIn sp_e sp_prep)
    (h_val : c ≠ '&' ∧ c ≠ '!' ∧ c ≠ '*') :
    ∃ kj sp_ne, PushesTrace s_ad.tokens s'.tokens [] ∧
      tailOf s'.tokens = .value kj ∧ GStar SSWhite sp_ne sp_a ∧ SFlowNode n .flowIn sp_prep sp_ne ∧
      TFlowOpenStack n D ks (.value kj) sp_block sp_ne (ev ++ (ev_p ++ [])) := by
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
  subst hsp_prep
  refine ⟨kj, sp_gram, hsilent, h_tl', h_ws, h_node, ?_⟩
  rcases SFlowNode_head_lift h_node ⟨hamp, hstar, hbang, hlb, hlc⟩ with
    ⟨hdq, hsq, hplain⟩ | ⟨hdq, hq⟩ | ⟨hsq, hq⟩
  · refine hT.receivePropsContent h_tail h_lead h_props h_sep (.plain _ _ _ _ hplain) ?_
    intro hk
    rcases hkj hk with h | h
    · exact absurd h hdq
    · exact absurd h hsq
  · exact hT.receivePropsContent h_tail h_lead h_props h_sep (.doubleQ _ _ _ _ hq)
      (fun _ => .doubleQ _ _ _ _ hq)
  · exact hT.receivePropsContent h_tail h_lead h_props h_sep (.singleQ _ _ _ _ hq)
      (fun _ => .singleQ _ _ _ _ hq)

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
      ((ev_n = [] ∧ ∃ sp_gram, TFlowNode 0 .flowOut sp_prep sp_gram [] ∧
          GStar SSWhite sp_gram sp_a ∧ (sp_gram = sp_a → s'.peek? ≠ some '#')) ∨
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
      Or.inl ⟨rfl, sp_gram, ?_, h_ws, h_hash⟩⟩
    subst hsp_prep
    rcases SFlowNode_head_lift h_node ⟨h_amp, h_star, h_bang, hlb, hlc⟩ with
      ⟨-, -, hplain⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact .content _ _ _ _ _ (.plain _ _ _ _ hplain)
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
lemma accum_step_content_traceK {n d : Nat} {sc s_prep s' : ScannerState} {c : Char}
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
    (hT : TFlowStackB n sc.flowLevel sc.flowStack (tailOf sc.tokens) sp_block sp_flow ev)
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
          TFlowStackB n s'.flowLevel s'.flowStack (tailOf s'.tokens) sp_block sp_ne (ev ++ ev_n)) ∨
       (tailOf s'.tokens = tailOf sc.tokens ∧ (c = '&' ∨ c = '!') ∧
          TFlowStackB n s'.flowLevel s'.flowStack (tailOf s'.tokens) sp_block sp_flow ev)) := by
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
  rcases hT with _ | ⟨_, _, _, _, _, _, h_fos⟩
  rw [h_fl', h_fs', hd]
  have h_fos' := h_fos
  rw [← h_tl_eq] at h_fos'
  by_cases hprop : c = '&' ∨ c = '!'
  · -- Property arms keep the tail and the trace.
    have h_kept := content_prop_tail_kept hcorr_ad hpeek h_dispatch hprop
    refine ⟨[], sp_prep, sp_a, hcorr_ad, arm, Or.inr ⟨h_kept.trans h_tl_eq, hprop, ?_⟩⟩
    rw [h_kept]; exact .«open» _ _ _ _ _ _ h_fos'
  · have hamp : c ≠ '&' := fun h => hprop (Or.inl h)
    have hbang : c ≠ '!' := fun h => hprop (Or.inr h)
    cases h_lead with
    | white h_tail h_lead =>
      obtain ⟨ev_n, -, h | ⟨-, h⟩⟩ := accum_step_content_trace_in arm hcorr_ad hpeek h_ad_inflow h_not_doc
        h_dispatch hcol hn' h_fos' (by rw [h_tl_eq]; exact h_tail)
        (by rw [h_tl_eq]; exact h_lead n hn)
      · obtain ⟨kj, sp_ne, h_tl', h_ws, h_nd, h_open⟩ := h
        exact ⟨ev_n, sp_prep, sp_a, hcorr_ad, arm, Or.inl ⟨kj, sp_ne, h_tl', ⟨hamp, hbang⟩, h_ws, h_nd, by
          rw [h_tl']; exact .«open» _ _ _ _ _ _ h_open⟩⟩
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
      obtain ⟨kj, sp_ne, -, h_tl', h_ws, h_nd, h_open⟩ := accum_step_content_trace_in_props arm hcorr_ad hpeek
        h_ad_inflow h_not_doc h_dispatch hcol hn' h_fos' (by rw [h_tl_eq]; exact h_tail)
        (by rw [h_tl_eq]; exact h_lead_p n hn) h_props (h_sep n hn) ⟨hamp, hbang, hstar⟩
      exact ⟨ev_p ++ [], sp_prep, sp_a, hcorr_ad, arm, Or.inl ⟨kj, sp_ne, h_tl', ⟨hamp, hbang⟩, h_ws, h_nd, by
        rw [h_tl']; exact .«open» _ _ _ _ _ _ h_open⟩⟩

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

lemma accum_step_content_pairB {n d : Nat} {ev : List Event} (sc : ScannerState)
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
    (hT : TFlowStackB n sc.flowLevel sc.flowStack (tailOf sc.tokens) sp_block sp_flow ev)
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
      ∃ ev_n, TFlowStackB n s'.flowLevel s'.flowStack (tailOf s'.tokens) sp_block sp_flow' (ev ++ ev_n) := by
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

end

end L4YAML.Proofs.Serialization.TraceOf.ContentBridge
