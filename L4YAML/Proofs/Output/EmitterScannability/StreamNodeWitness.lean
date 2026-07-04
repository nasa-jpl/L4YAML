/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import L4YAML.Proofs.Output.EmitterScannability.ValueLocality
import L4YAML.Proofs.Output.EmitterScannability.ValuePurity

/-!
# The standalone-stream node witness

For a single-document stream over a pinned token array `[streamStart] ++ body ++ [streamEnd]`
(with a flow-clean, content-start-headed body — exactly what `scanFiltered (emit v)` produces,
per `TokValsPin.scanFiltered_emit_tokvals`), a successful `parseStream` with `docs.size = 1`
FORCES the document to come from one `parseNode` call at position 1 that ends exactly at the
`streamEnd` position — the run-1 FRAME the value-locality joint consumes, plus the value pin
`docs[0]!.value = val` the walks rewrite through.

The end-position exactness comes from the stream loop's second iteration: the parse cannot end
early (the next token would be a clean content token, and the loop would then either reject it
(`validNextToken`) or parse a SECOND document, contradicting `docs.size = 1`), and it cannot end
late (for collection heads, the decompose pins the token BEFORE the end to the flow close, which
the body's cleanliness separates from `streamEnd`).
-/

namespace L4YAML.Proofs.EmitterScannability

open L4YAML
open L4YAML.TokenParser
open L4YAML.Proofs.ParserWellBehaved

/-- `tryConsume` on a non-matching head is the identity (paired form). -/
theorem tryConsume_of_ne (ps : ParseState) (tok : YamlToken)
    (h : ps.peek? ≠ some tok) : ps.tryConsume tok = (false, ps) := by
  unfold ParseState.tryConsume
  cases h_pk : ps.peek? with
  | none => rfl
  | some t =>
    have h_t : t ≠ tok := fun h_e => h (h_e ▸ h_pk)
    simp [h_t]

/-- `parseStreamLoop` only grows the document accumulator. -/
theorem parseStreamLoop_docs_le (f : Nat) :
    ∀ (ps : ParseState) (docs : Array YamlDocument) (st : StreamState)
      (out : Array YamlDocument),
      parseStreamLoop ps docs st f = .ok out → docs.size ≤ out.size := by
  induction f with
  | zero =>
    intro ps docs st out h
    unfold parseStreamLoop at h
    exact Nat.le_of_eq (congrArg Array.size (Except.ok.inj h))
  | succ k ih =>
    intro ps docs st out h
    unfold parseStreamLoop at h
    split at h
    · exact Nat.le_of_eq (congrArg Array.size (Except.ok.inj h))
    · exact Nat.le_of_eq (congrArg Array.size (Except.ok.inj h))
    · exact ih _ _ _ _ h
    · dsimp only [] at h
      split at h
      · simp only [reduceCtorEq] at h
      · split at h
        all_goals try split at h
        all_goals
          first
            | simp only [reduceCtorEq] at h
            | (have := congrArg Array.size (Except.ok.inj h)
               simp only [Array.size_push] at this
               omega)
            | (have := ih _ _ _ _ h
               simp only [Array.size_push] at this
               omega)

/-- Positional `.val` read-off from a whole-array pin. -/
theorem pin_getElem?_val {tokens : Array (Positioned YamlToken)} {L : List YamlToken}
    (h_pin : tokens.toList.map (·.val) = L) (i : Nat) :
    tokens[i]?.map (·.val) = L[i]? := by
  rw [← h_pin, List.getElem?_map, ← Array.getElem?_toList]

/-- `prepareDocumentState` on a directive-free, non-`---` head: no directives, no consumption,
    only the (empty) `tagHandles` reset. -/
theorem prepareDocumentState_clean (ps : ParseState)
    (h_head : match ps.peek? with
      | some (.versionDirective _ _) | some (.tagDirective _ _) | some .documentStart => False
      | _ => True) :
    prepareDocumentState ps = .ok (#[], { ps with tagHandles := #[] }) := by
  have h_nds : ps.peek? ≠ some YamlToken.documentStart := by
    intro hc; rw [hc] at h_head; exact h_head
  have h_ndir : (match ps.peek? with
      | some (.versionDirective _ _) | some (.tagDirective _ _) => False
      | _ => True) := by
    cases h_c : ps.peek? with
    | none => trivial
    | some t =>
      rw [h_c] at h_head
      cases t <;> first | trivial | exact h_head
  unfold prepareDocumentState
  simp only [bind, Except.bind]
  rw [parseDirectives_skip ps h_ndir]
  have h_fm : ∀ (f : Directive → Option (String × String)), Array.filterMap f #[] = #[] :=
    fun f => rfl
  simp only [h_fm]
  have h_beq : ((({ ps with tagHandles := #[] } : ParseState)).peek?
      == some YamlToken.documentStart) = false := by
    have h_pk : (({ ps with tagHandles := #[] } : ParseState)).peek? = ps.peek? := rfl
    rw [h_pk]
    cases h_c : ps.peek? with
    | none => rfl
    | some t =>
      have h_t : t ≠ YamlToken.documentStart := by
        intro h_e; exact h_nds (h_e ▸ h_c)
      simp [h_t]
  rw [tryConsume_of_ne ({ ps with tagHandles := #[] } : ParseState) YamlToken.documentStart
    (fun hc => h_nds hc)]
  rw [h_beq]
  simp only []
  rfl

set_option maxHeartbeats 3200000 in
/-- **The standalone-stream node witness**: a successful single-document `parseStream` over a
    pinned `[streamStart] ++ body ++ [streamEnd]` array (flow-clean, content-start-headed body)
    comes from one `parseNode` call at position 1 that ends exactly at the `streamEnd`
    position — the run-1 frame and value pin the locality walks consume. -/
theorem parseStream_single_doc_node_witness
    (tokens : Array (Positioned YamlToken)) (docs : Array YamlDocument)
    (body : List YamlToken)
    (h_parse : parseStream tokens = .ok docs)
    (h_size : docs.size = 1)
    (h_pin : tokens.toList.map (·.val) = .streamStart :: (body ++ [.streamEnd]))
    (h_clean : ∀ t ∈ body, FlowCleanTok t = true)
    (h_head : (∃ c st, body.head? = some (.scalar c st))
      ∨ body.head? = some .flowSequenceStart ∨ body.head? = some .flowMappingStart) :
    ∃ (val : YamlValue) (ps' : ParseState),
      parseNode ({ tokens := tokens, pos := 1 } : ParseState) (4 * tokens.size + 4)
        = .ok (val, ps')
      ∧ ps'.pos = tokens.size - 1
      ∧ docs[0]!.value = val := by
  -- ## Pin-derived facts
  have h_at := pin_getElem?_val h_pin
  have h_len : tokens.size = body.length + 2 := by
    have h0 := congrArg List.length h_pin
    simp only [List.length_map, Array.length_toList, List.length_cons, List.length_append,
      List.length_nil] at h0
    omega
  obtain ⟨ht, h_bh⟩ : ∃ ht, body.head? = some ht := by
    rcases h_head with ⟨c, st, h⟩ | h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  have h_ht3 : (∃ c st, ht = .scalar c st) ∨ ht = .flowSequenceStart
      ∨ ht = .flowMappingStart := by
    rcases h_head with ⟨c, st, h⟩ | h | h
    · exact Or.inl ⟨c, st, Option.some.inj (h_bh.symm.trans h)⟩
    · exact Or.inr (Or.inl (Option.some.inj (h_bh.symm.trans h)))
    · exact Or.inr (Or.inr (Option.some.inj (h_bh.symm.trans h)))
  have h_body_ne : body ≠ [] := by
    intro h_e; rw [h_e] at h_bh; simp at h_bh
  have h_body_len : 0 < body.length := List.length_pos_iff.mpr h_body_ne
  have h_at1 : tokens[1]?.map (·.val) = some ht := by
    rw [h_at]
    rw [List.getElem?_cons_succ, List.getElem?_append_left h_body_len]
    cases body with
    | nil => simp at h_bh
    | cons a t => simpa using h_bh
  have h_at_last : tokens[body.length + 1]?.map (·.val) = some YamlToken.streamEnd := by
    rw [h_at, List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_refl _)]
    simp
  have h_ht_ne : ht ≠ .streamEnd ∧ ht ≠ .documentEnd ∧ ht ≠ .documentStart := by
    rcases h_ht3 with ⟨c, st, rfl⟩ | rfl | rfl <;>
      exact ⟨by simp, by simp, by simp⟩
  have h_val_disj : ∀ (p : Nat) (t : YamlToken), tokens[p]?.map (·.val) = some t →
      t = .streamStart ∨ t ∈ body ∨ t = .streamEnd := by
    intro p t h_v
    rw [h_at] at h_v
    have h_mem : t ∈ (YamlToken.streamStart :: (body ++ [YamlToken.streamEnd])) :=
      List.mem_of_getElem? h_v
    rcases List.mem_cons.mp h_mem with h | h
    · exact Or.inl h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (List.mem_singleton.mp h))
  have h_no_de : ∀ (p : Nat) (t : YamlToken), tokens[p]?.map (·.val) = some t →
      t ≠ .documentEnd := by
    intro p t h_v
    rcases h_val_disj p t h_v with rfl | h | rfl
    · simp
    · have h_fc := h_clean _ h
      cases t <;> simp_all [FlowCleanTok]
    · simp
  have h_cl_tokens : CleanTokens tokens := by
    intro i hi
    have h_v := h_at i
    rw [getElem?_pos tokens i hi] at h_v
    simp only [Option.map_some] at h_v
    have h_mem := List.mem_of_getElem? h_v.symm
    rcases List.mem_cons.mp h_mem with h | h
    · rw [h]; rfl
    · rcases List.mem_append.mp h with h | h
      · have h_fc := h_clean _ h
        simp [CleanTok, h_fc]
      · rw [List.mem_singleton.mp h]; rfl
  -- ## Unfold the stream skeleton: expect
  have h_pk0 : (({ tokens := tokens, trackPositions := false } : ParseState)).peek?
      = some YamlToken.streamStart := by
    rw [peek?_eq_getElem?]
    simpa using h_at 0
  unfold parseStream at h_parse
  simp only [bind, Except.bind] at h_parse
  split at h_parse
  case h_1 e heq => simp only [reduceCtorEq] at h_parse
  case h_2 ps1 heq =>
  unfold ParseState.expect at heq
  rw [h_pk0] at heq
  simp only [] at heq
  have h_ps1 : ps1 = (({ tokens := tokens, trackPositions := false } : ParseState)).advance := by
    have := Except.ok.inj heq
    exact this.symm
  subst h_ps1
  -- ## Loop iteration 1
  have h_pk1 : ((({ tokens := tokens, trackPositions := false } : ParseState)).advance).peek?
      = some ht := by
    rw [peek?_eq_getElem?]
    exact h_at1
  rw [show tokens.size = (body.length + 1) + 1 from by omega] at h_parse
  unfold parseStreamLoop at h_parse
  split at h_parse
  · rename_i heq1
    exact absurd (Option.some.inj (h_pk1.symm.trans heq1)) h_ht_ne.1
  · rename_i heq1
    exact absurd (h_pk1.symm.trans heq1) (by simp)
  · rename_i heq1
    exact absurd (Option.some.inj (h_pk1.symm.trans heq1)) h_ht_ne.2.1
  rename_i tokv hse hde heq1
  have h_tok : tokv = ht := Option.some.inj (heq1.symm.trans h_pk1)
  subst h_tok
  split at h_parse
  · simp only [reduceCtorEq] at h_parse
  split at h_parse
  · simp only [reduceCtorEq] at h_parse
  rename_i doc1 pd1 heq_doc
  -- ## Dissect the document parse
  unfold parseDocument at heq_doc
  simp only [bind, Except.bind] at heq_doc
  rw [prepareDocumentState_clean _ (by
    rw [h_pk1]
    rcases h_ht3 with ⟨c, st, rfl⟩ | rfl | rfl <;> trivial)] at heq_doc
  simp only [] at heq_doc
  -- root dispatch: kill the empty-document arms, capture the node parse
  split at heq_doc
  · rename_i heq2
    have h1 : ((({ tokens := tokens } : ParseState)).advance).peek?
        = some YamlToken.documentEnd := heq2
    rw [h_pk1] at h1
    exact absurd (Option.some.inj h1) h_ht_ne.2.1
  · rename_i heq2
    have h1 : ((({ tokens := tokens } : ParseState)).advance).peek?
        = some YamlToken.streamEnd := heq2
    rw [h_pk1] at h1
    exact absurd (Option.some.inj h1) h_ht_ne.1
  · rename_i heq2
    have h1 : ((({ tokens := tokens } : ParseState)).advance).peek? = none := heq2
    rw [h_pk1] at h1
    simp at h1
  split at heq_doc
  · simp only [reduceCtorEq] at heq_doc
  rename_i vr heq_node
  simp only [Except.ok.injEq, Prod.mk.injEq] at heq_doc
  have h_dv : doc1.value = vr.1 := by rw [← heq_doc.1]
  have h_pd : pd1 = vr.2 := heq_doc.2.symm
  subst h_pd
  have heq_node' : parseNode ({ tokens := tokens, pos := 1 } : ParseState)
      (4 * tokens.size + 4) = .ok (vr.1, vr.2) := heq_node
  have h_pk2 : (({ tokens := tokens, pos := 1 } : ParseState)).peek? = some tokv := h_pk1
  obtain ⟨h_pure, h_ptok⟩ := parseNode_pure (4 * tokens.size + 4)
    ({ tokens := tokens, pos := 1 } : ParseState) vr.1 vr.2 h_cl_tokens heq_node'
  -- advance bounds per head shape
  have h_adv : 2 ≤ vr.2.pos ∧ vr.2.pos ≤ body.length + 1 := by
    rcases h_ht3 with ⟨c, st, h_e⟩ | h_e | h_e
    · rw [h_e] at h_pk2
      have h_a := parseNode_scalar_advances_by_one _ _ c st vr.1 vr.2 h_pk2 heq_node'
      have h_a2 : vr.2.pos = 2 := h_a
      omega
    · rw [h_e] at h_pk2
      obtain ⟨g, items, psl, h_m, h_loop, h_close, hv_shape, hq_pos, hq_tok⟩ :=
        parseNode_flowSeqStart_decompose _ _ vr.1 vr.2 h_pk2 heq_node'
      have h_mono := parseFlowSequenceLoop_pos_mono g (parseNode_pos_mono_all g)
        (({ tokens := tokens, pos := 1 } : ParseState)).advance #[] (items, psl) h_loop
      have h_lo : 2 ≤ psl.pos := h_mono
      have h_psl_tok : psl.tokens = tokens := by rw [← hq_tok]; exact h_ptok
      have h_cl_pk : tokens[psl.pos]?.map (·.val) = some YamlToken.flowSequenceEnd := by
        have h1 := h_close
        rw [peek?_eq_getElem?, h_psl_tok] at h1
        exact h1
      have h_in : psl.pos < tokens.size := by
        rcases Nat.lt_or_ge psl.pos tokens.size with h | h
        · exact h
        · rw [getElem?_neg tokens psl.pos (by omega)] at h_cl_pk
          simp at h_cl_pk
      have h_ne_last : psl.pos ≠ body.length + 1 := by
        intro h_e2
        rw [h_e2, h_at_last] at h_cl_pk
        exact absurd (Option.some.inj h_cl_pk) (by simp)
      omega
    · rw [h_e] at h_pk2
      obtain ⟨g, pairs, psl, h_m, h_loop, h_close, hv_shape, hq_pos, hq_tok⟩ :=
        parseNode_flowMapStart_decompose _ _ vr.1 vr.2 h_pk2 heq_node'
      have h_mono := parseFlowMappingLoop_pos_mono g (parseNode_pos_mono_all g)
        (({ tokens := tokens, pos := 1 } : ParseState)).advance #[] (pairs, psl) h_loop
      have h_lo : 2 ≤ psl.pos := h_mono
      have h_psl_tok : psl.tokens = tokens := by rw [← hq_tok]; exact h_ptok
      have h_cl_pk : tokens[psl.pos]?.map (·.val) = some YamlToken.flowMappingEnd := by
        have h1 := h_close
        rw [peek?_eq_getElem?, h_psl_tok] at h1
        exact h1
      have h_in : psl.pos < tokens.size := by
        rcases Nat.lt_or_ge psl.pos tokens.size with h | h
        · exact h
        · rw [getElem?_neg tokens psl.pos (by omega)] at h_cl_pk
          simp at h_cl_pk
      have h_ne_last : psl.pos ≠ body.length + 1 := by
        intro h_e2
        rw [h_e2, h_at_last] at h_cl_pk
        exact absurd (Option.some.inj h_cl_pk) (by simp)
      omega
  -- loop continuation: skip the `...` consume, refute the stuck-exit
  dsimp only [] at h_parse
  rw [tryConsume_of_ne _ YamlToken.documentEnd ?hnde] at h_parse
  case hnde =>
    intro hc
    have h2 := hc
    rw [peek?_eq_getElem?] at h2
    have h3 : vr.2.tokens[vr.2.pos]?.map (·.val) = some YamlToken.documentEnd := h2
    rw [h_ptok] at h3
    exact h_no_de _ _ h3 rfl
  simp only [] at h_parse
  split at h_parse
  · rename_i hcond
    have h1 : (vr.2.pos == (1 : Nat)) = true := hcond
    have h2 : vr.2.pos = 1 := by simpa using h1
    omega
  -- second iteration
  by_cases h_end : vr.2.pos = body.length + 1
  · have h_pk4 : tokens[vr.2.pos]?.map (·.val) = some YamlToken.streamEnd := by
      rw [h_end]; exact h_at_last
    unfold parseStreamLoop at h_parse
    split at h_parse
    · have h_docs : docs = #[].push doc1 := (Except.ok.inj h_parse).symm
      refine ⟨vr.1, vr.2, heq_node', by omega, ?_⟩
      rw [h_docs]
      simpa using h_dv
    · rename_i heqx
      have h2 := heqx
      rw [peek?_eq_getElem?] at h2
      have h3 : vr.2.tokens[vr.2.pos]?.map (·.val) = none := h2
      rw [h_ptok] at h3
      rw [h_pk4] at h3
      simp at h3
    · rename_i heqx
      have h2 := heqx
      rw [peek?_eq_getElem?] at h2
      have h3 : vr.2.tokens[vr.2.pos]?.map (·.val) = some YamlToken.documentEnd := h2
      rw [h_ptok, h_pk4] at h3
      exact absurd (Option.some.inj h3) (by simp)
    · rename_i tokz hzse hzde heqz
      have h2 := heqz
      rw [peek?_eq_getElem?] at h2
      have h3 : vr.2.tokens[vr.2.pos]?.map (·.val) = some tokz := h2
      rw [h_ptok, h_pk4] at h3
      exact absurd (Option.some.inj h3).symm hzse
  · have h_lt : vr.2.pos < body.length + 1 := by omega
    obtain ⟨p', h_p'⟩ : ∃ p', vr.2.pos = p' + 1 := ⟨vr.2.pos - 1, by omega⟩
    have h_p'_lt : p' < body.length := by omega
    have h_tz0 := h_at vr.2.pos
    rw [h_p', List.getElem?_cons_succ, List.getElem?_append_left h_p'_lt,
      List.getElem?_eq_getElem h_p'_lt] at h_tz0
    have h_tz_mem : body[p'] ∈ body := List.getElem_mem h_p'_lt
    have h_tz_ne_se : body[p'] ≠ YamlToken.streamEnd := by
      have h_fc := h_clean _ h_tz_mem
      cases h_c : body[p'] <;> simp_all [FlowCleanTok]
    have h_tz_ne_de : body[p'] ≠ YamlToken.documentEnd := by
      have h_fc := h_clean _ h_tz_mem
      cases h_c : body[p'] <;> simp_all [FlowCleanTok]
    unfold parseStreamLoop at h_parse
    split at h_parse
    · rename_i heqx
      have h2 := heqx
      rw [peek?_eq_getElem?] at h2
      have h3 : vr.2.tokens[vr.2.pos]?.map (·.val) = some YamlToken.streamEnd := h2
      rw [h_ptok, h_p', h_tz0] at h3
      exact absurd (Option.some.inj h3) h_tz_ne_se
    · rename_i heqx
      have h2 := heqx
      rw [peek?_eq_getElem?] at h2
      have h3 : vr.2.tokens[vr.2.pos]?.map (·.val) = none := h2
      rw [h_ptok, h_p', h_tz0] at h3
      simp at h3
    · rename_i heqx
      have h2 := heqx
      rw [peek?_eq_getElem?] at h2
      have h3 : vr.2.tokens[vr.2.pos]?.map (·.val) = some YamlToken.documentEnd := h2
      rw [h_ptok, h_p', h_tz0] at h3
      exact absurd (Option.some.inj h3) h_tz_ne_de
    rename_i tokz hzse hzde heqz
    dsimp only [] at h_parse
    split at h_parse
    all_goals try dsimp only [] at h_parse
    all_goals try split at h_parse
    all_goals try dsimp only [] at h_parse
    all_goals try split at h_parse
    all_goals try dsimp only [] at h_parse
    all_goals try split at h_parse
    all_goals
      first
        | simp only [reduceCtorEq] at h_parse
        | (have h_x := Except.ok.inj h_parse
           have h_sz2 : docs.size = 2 := by rw [← h_x]; simp
           omega)
        | (have h_x := parseStreamLoop_docs_le _ _ _ _ _ h_parse
           simp at h_x
           omega)

end L4YAML.Proofs.EmitterScannability
