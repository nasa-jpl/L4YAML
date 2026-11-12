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

end

end L4YAML.Proofs.Serialization.TraceOf.ContentBridge
