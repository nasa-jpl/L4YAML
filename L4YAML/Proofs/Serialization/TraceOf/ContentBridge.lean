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
    refine ⟨[.useAlias name], ?_, Or.inl ⟨false, sp', h_tl', .nil _, ?_⟩⟩
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
  refine ⟨[], hsilent, Or.inl ⟨kj, sp_gram, h_tl', h_ws, ?_⟩⟩
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
      tailOf s'.tokens = .value kj ∧ GStar SSWhite sp_ne sp_a ∧
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
  refine ⟨kj, sp_gram, hsilent, h_tl', h_ws, ?_⟩
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
        SSeparate m (inFlowCtx .flowOut) sp_e sp_prep) :
      ContentLead sc tl sp_flow sp_prep

/-- The replay: `accum_step_content_core`'s derivation of the receive's premises, from the
    wrapper's hypotheses.  `s_ad` is the dispatch state (`s_prep` with `allowDirectives` cleared);
    the three `h_ad_*` equalities are `split <;> rfl` at the caller. -/
lemma contentLead_of_interior {sc s_prep s_ad s' : ScannerState} {c : Char} {d : Nat}
    {sp_flow sp_scan sp_prep : SurfPos}
    (hd : sc.flowLevel = d + 1)
    (h_corr : ScannerSurfCorr sc sp_scan) (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_str_none : scanNextToken_dispatchStructural s_prep c = .ok none)
    (h_ad_tokens : s_ad.tokens = s_prep.tokens) (h_ad_peek : s_ad.peek? = s_prep.peek?)
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
      have h_tl_eq : tailOf s_ad.tokens = tailOf sc.tokens := by
        unfold L4YAML.Proofs.StreamAccum.tailOf
        rw [h_ad_tokens,
          L4YAML.Proofs.StreamAccum.preprocess_preserves_frameTokenVal_inFlow sc s_prep c (by omega) h_preprocess,
          L4YAML.Proofs.StreamAccum.preprocess_preserves_jsonKeyBefore_inFlow sc s_prep c (by omega) h_preprocess]
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
    rcases (h_lead_at m).resolve_right (fun h => h hm) with h | ⟨h1, -⟩
    · exact h
    · exact absurd (L4YAML.Proofs.StreamAccum.NextIsSep.not_content h_next (h_peek h1) h_glue) id


/-! ## §6 The K caller — the content step on the T flow stack (item 487)

At depth ≥ 1, from `accum_step_content`'s inputs and the T stack at the pre-state: the value arms
land the T stack at `s'` through `_in` / `_in_props`, the property arms keep it (tail and trace
unchanged), the lead replayed by `contentLead_of_interior`.  Depth 0 is `_out`'s business. -/

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
      ((∃ kj sp_ne, tailOf s'.tokens = .value kj ∧ GStar SSWhite sp_ne sp_a ∧
          TFlowStackB n s'.flowLevel s'.flowStack (tailOf s'.tokens) sp_block sp_ne (ev ++ ev_n)) ∨
       (tailOf s'.tokens = tailOf sc.tokens ∧ (c = '&' ∨ c = '!') ∧
          TFlowStackB n s'.flowLevel s'.flowStack (tailOf s'.tokens) sp_block sp_flow ev)) := by
  sorry

end

end L4YAML.Proofs.Serialization.TraceOf.ContentBridge
