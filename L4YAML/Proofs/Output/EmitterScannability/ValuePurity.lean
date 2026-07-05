/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import L4YAML.Proofs.Output.EmitterScannability.ValueLocality

/-!
# Purity of values parsed from clean token arrays

On a CLEAN token array (flow-clean tokens plus the stream framing — exactly what
`scanFiltered (emit v)` produces), the parser can never register an anchor, resolve an alias,
or attach a tag, so every parsed value is *pure*: `resolveAliases`-invariant under ANY anchor
map, `stripAnchors`-invariant, and `anchorFree`.  This is what lets `compose` collapse to the
identity on both the standalone and the whole-stream sides of the locality equation — with NO
hypotheses about the documents' anchor maps.

Token-array preservation is folded into the same induction (the loops re-arm `CleanTokens` at
the continuation states through it).
-/

namespace L4YAML.Proofs.EmitterScannability

open L4YAML
open L4YAML.TokenParser
open L4YAML.Proofs.ParserWellBehaved
open L4YAML.Proofs.ParserGrammable

/-- Clean token kinds: flow-clean plus the stream framing. -/
def CleanTok (t : YamlToken) : Bool :=
  FlowCleanTok t || t == .streamStart || t == .streamEnd

/-- A globally clean token array. -/
def CleanTokens (tokens : Array (Positioned YamlToken)) : Prop :=
  ∀ (i : Nat) (h : i < tokens.size), CleanTok tokens[i].val = true

/-- Pure value: alias-resolution-invariant (under ANY map), strip-invariant, anchor-free. -/
def PureVal (v : YamlValue) : Prop :=
  (∀ A, v.resolveAliases A = v) ∧ v.stripAnchors = v ∧ v.anchorFree = true

theorem CleanTokens.head {ps : ParseState} (h : CleanTokens ps.tokens)
    {t : YamlToken} (h_pk : ps.peek? = some t) : CleanTok t = true := by
  rw [peek?_eq_getElem?] at h_pk
  cases h_get : ps.tokens[ps.pos]? with
  | none => rw [h_get] at h_pk; simp at h_pk
  | some pt =>
    rw [h_get] at h_pk
    have h_val : pt.val = t := by simpa using h_pk
    rcases Nat.lt_or_ge ps.pos ps.tokens.size with h_lt | h_ge
    · have h_el : ps.tokens[ps.pos] = pt := by
        have h2 := getElem?_pos ps.tokens ps.pos h_lt
        rw [h_get] at h2
        exact (Option.some.inj h2).symm
      have h3 := h ps.pos h_lt
      rwa [h_el, h_val] at h3
    · rw [getElem?_neg ps.tokens ps.pos (by omega)] at h_get
      exact absurd h_get (by simp)

/-! ## Pure-value constructors -/

theorem pureVal_scalar (s : Scalar) (h : s.anchor = none) : PureVal (.scalar s) := by
  refine ⟨fun A => resolveAliases_scalar s A, ?_, ?_⟩
  · rw [stripAnchors_scalar]
    cases s
    simp_all
  · simp [YamlValue.anchorFree, h]

theorem pureVal_emptyNode : PureVal emptyNode :=
  pureVal_scalar _ rfl

theorem list_map_self {α : Type} (l : List α) (f : α → α)
    (h : ∀ x ∈ l, f x = x) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, h a (List.mem_cons_self ..), List.cons.injEq, true_and]
    exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

theorem pureVal_sequence (st : CollectionStyle) (items : Array YamlValue)
    (h : ∀ v ∈ items.toList, PureVal v) :
    PureVal (.sequence st items none none) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A
    show YamlValue.sequence st (YamlValue.resolveAliases.resolveList items.toList A).toArray
        none none = _
    rw [resolveList_eq_map, list_map_self _ _ (fun x hx => (h x hx).1 A),
      Array.toArray_toList]
  · show YamlValue.sequence st (YamlValue.stripAnchors.stripList items.toList).toArray
        none none = _
    rw [stripList_eq_map, list_map_self _ _ (fun x hx => (h x hx).2.1),
      Array.toArray_toList]
  · show (Option.isNone (none : Option String) && YamlValue.anchorFree.goList items.toList)
        = true
    rw [anchorFree_goList_of_forall items.toList (fun x hx => (h x hx).2.2)]
    rfl

theorem pureVal_mapping (st : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
    (h : ∀ p ∈ pairs.toList, PureVal p.1 ∧ PureVal p.2) :
    PureVal (.mapping st pairs none none) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A
    show YamlValue.mapping st (YamlValue.resolveAliases.resolvePairs pairs.toList A).toArray
        none none = _
    rw [resolvePairs_eq_map,
      list_map_self _ _ (fun x hx => by
        have := h x hx
        show ((x.1.resolveAliases A, x.2.resolveAliases A) : YamlValue × YamlValue) = x
        rw [this.1.1 A, this.2.1 A]),
      Array.toArray_toList]
  · show YamlValue.mapping st (YamlValue.stripAnchors.stripPairs pairs.toList).toArray
        none none = _
    rw [stripPairs_eq_map,
      list_map_self _ _ (fun x hx => by
        have := h x hx
        show ((x.1.stripAnchors, x.2.stripAnchors) : YamlValue × YamlValue) = x
        rw [this.1.2.1, this.2.2.1]),
      Array.toArray_toList]
  · show (Option.isNone (none : Option String) && YamlValue.anchorFree.goPairs pairs.toList)
        = true
    rw [anchorFree_goPairs_of_forall pairs.toList
      (fun x hx => ⟨(h x hx).1.2.2, (h x hx).2.2.2⟩)]
    rfl

/-! ## The purity clique -/

/-- Fuel-indexed purity: on a clean token array, a successful `parseNode` yields a pure value
    and preserves the token array. -/
def ParseNodePure (n : Nat) : Prop :=
  ∀ m, m ≤ n → ∀ (ps : ParseState) (v : YamlValue) (q : ParseState),
    CleanTokens ps.tokens → parseNode ps m = .ok (v, q) →
    PureVal v ∧ q.tokens = ps.tokens

theorem pairKeyStep_pure (n : Nat) (h_ih : ParseNodePure n) (g : Nat) (hg : g ≤ n)
    (ps : ParseState) (key : YamlValue) (q : ParseState)
    (h_cl : CleanTokens ps.tokens)
    (h : pairKeyStep ps g = .ok (key, q)) :
    PureVal key ∧ q.tokens = ps.tokens := by
  unfold pairKeyStep at h
  split at h
  all_goals first
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨h1, h2⟩ := h
       subst h2
       exact ⟨by rw [← h1]; exact pureVal_emptyNode, rfl⟩)
    | exact h_ih g hg ps key q h_cl h

theorem parseExplicitKey_pure (n : Nat) (h_ih : ParseNodePure n) (g : Nat) (hg : g ≤ n)
    (ps : ParseState) (key : YamlValue) (q : ParseState)
    (h_cl : CleanTokens ps.tokens)
    (h : parseExplicitKey ps g = .ok (key, q)) :
    PureVal key ∧ q.tokens = ps.tokens := by
  unfold parseExplicitKey at h
  split at h
  all_goals first
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨h1, h2⟩ := h
       subst h2
       exact ⟨by rw [← h1]; exact pureVal_emptyNode, rfl⟩)
    | exact h_ih g hg ps key q h_cl h

theorem parseFlowMappingValue_pure (n : Nat) (h_ih : ParseNodePure n) (g : Nat) (hg : g ≤ n)
    (ps : ParseState) (sp : YamlPath) (kc : String) (v : YamlValue) (q : ParseState)
    (h_cl : CleanTokens ps.tokens)
    (h : parseFlowMappingValue ps g sp kc = .ok (v, q)) :
    PureVal v ∧ q.tokens = ps.tokens := by
  obtain ⟨wk, wv, mid, psv0, val, pv, _, _, hval, _, _, _, hvt, hveq, _, hqt⟩ :=
    parseFlowMappingValue_inv ps g sp kc v q h
  have h_cl_v : CleanTokens psv0.tokens := by rw [hvt]; exact h_cl
  have h_val : PureVal val ∧ pv.tokens = psv0.tokens := by
    rcases hval with ⟨_, hve, hpe⟩ | ⟨_, _, hve, hpe⟩ | ⟨_, _, _, _, hpn⟩
    · exact ⟨by rw [hve]; exact pureVal_emptyNode, by rw [hpe]⟩
    · exact ⟨by rw [hve]; exact pureVal_emptyNode, by rw [hpe]⟩
    · exact h_ih g hg psv0 val pv h_cl_v hpn
  exact ⟨by rw [hveq]; exact h_val.1, by rw [hqt, h_val.2, hvt]⟩

theorem parseSinglePairMapping_pure (n : Nat) (h_ih : ParseNodePure n)
    (f : Nat) (hf : f ≤ n + 1) (ps : ParseState) (v : YamlValue) (q : ParseState)
    (h_cl : CleanTokens ps.tokens)
    (h : parseSinglePairMapping ps f = .ok (v, q)) :
    PureVal v ∧ q.tokens = ps.tokens := by
  cases f with
  | zero => simp only [parseSinglePairMapping, reduceCtorEq] at h
  | succ g =>
  obtain ⟨key, psk, w, psv0, val, pv, hk, _, hval, hpos, htok, hv, hqp, hqt⟩ :=
    parseSinglePairMapping_inv ps g v q h
  have h_cl_adv : CleanTokens (ps.advance : ParseState).tokens := by
    simpa [ParseState.advance] using h_cl
  obtain ⟨h_key_pure, h_ktok⟩ :=
    pairKeyStep_pure n h_ih g (by omega) ps.advance key psk h_cl_adv hk
  have h_ktok' : psk.tokens = ps.tokens := by simpa [ParseState.advance] using h_ktok
  have h_cl_v : CleanTokens psv0.tokens := by rw [htok, h_ktok']; exact h_cl
  have h_val : PureVal val ∧ pv.tokens = psv0.tokens := by
    rcases hval with ⟨_, hve, hpe⟩ | ⟨_, _, hve, hpe⟩ | ⟨_, _, _, _, hpn⟩
    · exact ⟨by rw [hve]; exact pureVal_emptyNode, by rw [hpe]⟩
    · exact ⟨by rw [hve]; exact pureVal_emptyNode, by rw [hpe]⟩
    · exact h_ih g (by omega) psv0 val pv h_cl_v hpn
  refine ⟨?_, by rw [hqt, h_val.2, htok, h_ktok']⟩
  rw [hv]
  refine pureVal_mapping .flow #[(key, val)] ?_
  intro p hp
  have hp' : p = (key, val) := by simpa using hp
  rw [hp']
  exact ⟨h_key_pure, h_val.1⟩

theorem parseFlowSequenceLoop_pure (n : Nat) (h_ih : ParseNodePure n) :
    ∀ (f : Nat), f ≤ n + 1 → ∀ (ps : ParseState) (acc : Array YamlValue)
      (r : Array YamlValue × ParseState),
      CleanTokens ps.tokens →
      (∀ v ∈ acc.toList, PureVal v) →
      parseFlowSequenceLoop ps f acc = .ok r →
      (∀ v ∈ r.1.toList, PureVal v) ∧ r.2.tokens = ps.tokens := by
  intro f
  induction f with
  | zero =>
    intro _ ps acc r h_cl h_acc h
    unfold parseFlowSequenceLoop at h
    have h_r := (Except.ok.inj h).symm
    rw [h_r]
    exact ⟨h_acc, rfl⟩
  | succ k ih =>
    intro hf ps acc r h_cl h_acc h
    rcases parseFlowSequenceLoop_step_inv ps k acc r h with
      ⟨_, h_r⟩ | ⟨_, _, _, h_r⟩
      | ⟨w0, ps', h_p', h_t', _, _, h_disp⟩
    · rw [h_r]; exact ⟨h_acc, rfl⟩
    · rw [h_r]; exact ⟨h_acc, rfl⟩
    · rcases h_disp with ⟨_, h_r⟩
        | ⟨_, psE, val, psn, psC, h_el, hpe, hte, h_cont, hpc, htc⟩
        | ⟨_, _, psE, val, psn, psC, h_el, hpe, hte, h_cont, hpc, htc⟩
      · rw [h_r]; exact ⟨h_acc, h_t'⟩
      · have h_clE : CleanTokens psE.tokens := by rw [hte, h_t']; exact h_cl
        obtain ⟨h_val, h_ntok⟩ :=
          parseSinglePairMapping_pure n h_ih k (by omega) psE val psn h_clE h_el
        have h_clC : CleanTokens psC.tokens := by rw [htc, h_ntok, hte, h_t']; exact h_cl
        obtain ⟨h_all, h_rtok⟩ := ih (by omega) psC (acc.push val) r h_clC
          (by intro x hx
              rw [Array.toList_push] at hx
              rcases List.mem_append.mp hx with hx | hx
              · exact h_acc x hx
              · rw [List.mem_singleton.mp hx]; exact h_val) h_cont
        exact ⟨h_all, by rw [h_rtok, htc, h_ntok, hte, h_t']⟩
      · have h_clE : CleanTokens psE.tokens := by rw [hte, h_t']; exact h_cl
        obtain ⟨h_val, h_ntok⟩ := h_ih k (by omega) psE val psn h_clE h_el
        have h_clC : CleanTokens psC.tokens := by rw [htc, h_ntok, hte, h_t']; exact h_cl
        obtain ⟨h_all, h_rtok⟩ := ih (by omega) psC (acc.push val) r h_clC
          (by intro x hx
              rw [Array.toList_push] at hx
              rcases List.mem_append.mp hx with hx | hx
              · exact h_acc x hx
              · rw [List.mem_singleton.mp hx]; exact h_val) h_cont
        exact ⟨h_all, by rw [h_rtok, htc, h_ntok, hte, h_t']⟩

theorem parseFlowMappingLoop_pure (n : Nat) (h_ih : ParseNodePure n) :
    ∀ (f : Nat), f ≤ n + 1 → ∀ (ps : ParseState) (acc : Array (YamlValue × YamlValue))
      (r : Array (YamlValue × YamlValue) × ParseState),
      CleanTokens ps.tokens →
      (∀ p ∈ acc.toList, PureVal p.1 ∧ PureVal p.2) →
      parseFlowMappingLoop ps f acc = .ok r →
      (∀ p ∈ r.1.toList, PureVal p.1 ∧ PureVal p.2) ∧ r.2.tokens = ps.tokens := by
  intro f
  induction f with
  | zero =>
    intro _ ps acc r h_cl h_acc h
    unfold parseFlowMappingLoop at h
    have h_r := (Except.ok.inj h).symm
    rw [h_r]
    exact ⟨h_acc, rfl⟩
  | succ k ih =>
    intro hf ps acc r h_cl h_acc h
    rcases parseFlowMappingLoop_step_inv ps k acc r h with
      ⟨_, h_r⟩ | ⟨_, _, _, h_r⟩
      | ⟨w0, ps', h_p', h_t', _, _, h_disp⟩
    · rw [h_r]; exact ⟨h_acc, rfl⟩
    · rw [h_r]; exact ⟨h_acc, rfl⟩
    · rcases h_disp with ⟨_, h_r⟩
        | ⟨_, psE, key, psn, sp, kc, psM, val, psv, psC,
            h_key, hpe, hte, h_val_eq, hmp, hmt, h_cont, hpc, htc⟩
        | ⟨_, _, psE, key, psn, sp, kc, psM, val, psv, psC,
            h_key, hpe, hte, h_val_eq, hmp, hmt, h_cont, hpc, htc⟩
      · rw [h_r]; exact ⟨h_acc, h_t'⟩
      · have h_clE : CleanTokens psE.tokens := by rw [hte, h_t']; exact h_cl
        obtain ⟨h_kp, h_ktok⟩ := parseExplicitKey_pure n h_ih k (by omega) psE key psn h_clE h_key
        have h_clM : CleanTokens psM.tokens := by rw [hmt, h_ktok, hte, h_t']; exact h_cl
        obtain ⟨h_vp, h_vtok⟩ :=
          parseFlowMappingValue_pure n h_ih k (by omega) psM sp kc val psv h_clM h_val_eq
        have h_clC : CleanTokens psC.tokens := by
          rw [htc, h_vtok, hmt, h_ktok, hte, h_t']; exact h_cl
        obtain ⟨h_all, h_rtok⟩ := ih (by omega) psC (acc.push (key, val)) r h_clC
          (by intro x hx
              rw [Array.toList_push] at hx
              rcases List.mem_append.mp hx with hx | hx
              · exact h_acc x hx
              · rw [List.mem_singleton.mp hx]; exact ⟨h_kp, h_vp⟩) h_cont
        exact ⟨h_all, by rw [h_rtok, htc, h_vtok, hmt, h_ktok, hte, h_t']⟩
      · have h_clE : CleanTokens psE.tokens := by rw [hte, h_t']; exact h_cl
        obtain ⟨h_kp, h_ktok⟩ := h_ih k (by omega) psE key psn h_clE h_key
        have h_clM : CleanTokens psM.tokens := by rw [hmt, h_ktok, hte, h_t']; exact h_cl
        obtain ⟨h_vp, h_vtok⟩ :=
          parseFlowMappingValue_pure n h_ih k (by omega) psM sp kc val psv h_clM h_val_eq
        have h_clC : CleanTokens psC.tokens := by
          rw [htc, h_vtok, hmt, h_ktok, hte, h_t']; exact h_cl
        obtain ⟨h_all, h_rtok⟩ := ih (by omega) psC (acc.push (key, val)) r h_clC
          (by intro x hx
              rw [Array.toList_push] at hx
              rcases List.mem_append.mp hx with hx | hx
              · exact h_acc x hx
              · rw [List.mem_singleton.mp hx]; exact ⟨h_kp, h_vp⟩) h_cont
        exact ⟨h_all, by rw [h_rtok, htc, h_vtok, hmt, h_ktok, hte, h_t']⟩

set_option maxHeartbeats 1600000 in
theorem parseNode_pure_all : ∀ n, ParseNodePure n := by
  intro n
  induction n with
  | zero =>
    intro m hm ps v q h_cl h
    have h0 : m = 0 := by omega
    subst h0
    simp only [parseNode, reduceCtorEq] at h
  | succ k ih =>
    intro m hm ps v q h_cl h
    by_cases h_le : m ≤ k
    · exact ih m h_le ps v q h_cl h
    · cases h_pk : ps.peek? with
      | none =>
        obtain ⟨hv, _, ht⟩ := parseNode_inert_head ps m v q (Or.inl h_pk) h
        exact ⟨by rw [hv]; exact pureVal_scalar _ rfl, ht⟩
      | some tok =>
        have h_ct := CleanTokens.head h_cl h_pk
        cases tok
        all_goals try (simp [CleanTok, FlowCleanTok] at h_ct)
        case scalar c st =>
          have hv := parseNode_scalar_produces_scalar ps m c st v q h_pk h
          have ht := parseNode_scalar_tokens_preserved ps m c st v q h_pk h
          exact ⟨by rw [hv]; exact pureVal_scalar _ rfl, ht⟩
        case flowSequenceStart =>
          obtain ⟨g, items, psl, h_m, h_loop, h_close, hv, hq, ht⟩ :=
            parseNode_flowSeqStart_decompose ps m v q h_pk h
          have h_cl_adv : CleanTokens (ps.advance : ParseState).tokens := by
            simpa [ParseState.advance] using h_cl
          obtain ⟨h_all, h_ltok⟩ := parseFlowSequenceLoop_pure k ih g (by omega)
            ps.advance #[] (items, psl) h_cl_adv (by simp) h_loop
          simp only [ParseState.advance] at h_ltok
          refine ⟨by rw [hv]; exact pureVal_sequence _ _ h_all, by rw [ht]; exact h_ltok⟩
        case flowMappingStart =>
          obtain ⟨g, pairs, psl, h_m, h_loop, h_close, hv, hq, ht⟩ :=
            parseNode_flowMapStart_decompose ps m v q h_pk h
          have h_cl_adv : CleanTokens (ps.advance : ParseState).tokens := by
            simpa [ParseState.advance] using h_cl
          obtain ⟨h_all, h_ltok⟩ := parseFlowMappingLoop_pure k ih g (by omega)
            ps.advance #[] (pairs, psl) h_cl_adv (by simp) h_loop
          simp only [ParseState.advance] at h_ltok
          refine ⟨by rw [hv]; exact pureVal_mapping _ _ h_all, by rw [ht]; exact h_ltok⟩
        all_goals (
          obtain ⟨hv, _, ht⟩ := parseNode_inert_head ps m v q (by simp [h_pk]) h
          exact ⟨by rw [hv]; exact pureVal_scalar _ rfl, ht⟩)

/-- **Purity of clean-token parses** (public form). -/
theorem parseNode_pure (f : Nat) (ps : ParseState) (v : YamlValue) (q : ParseState)
    (h_cl : CleanTokens ps.tokens) (h : parseNode ps f = .ok (v, q)) :
    PureVal v ∧ q.tokens = ps.tokens :=
  parseNode_pure_all f f (Nat.le_refl _) ps v q h_cl h

end L4YAML.Proofs.EmitterScannability
