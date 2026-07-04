/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import L4YAML.Proofs.Output.EmitterScannability.TokValsPin
import L4YAML.Proofs.Output.EmitterScannability.StreamNodeWitness

/-!
# The general locality walks

The non-all-scalar generalization of R601/R608: walking the whole-stream flow loops over the
`emitTokVals`-pinned token array, each element parse is identified with its STANDALONE parse
via the value-locality joint (`parseNode_joint`) — the standalone run supplies the frame (its
`parseNode` provably ends right before `streamEnd`, by the stream witness), and the joint
returns equal values and equal advances, which both pins `result.1[j]!` to the standalone
composed value and drives the cumulative position arithmetic.
-/

namespace L4YAML.Proofs.EmitterScannability

open L4YAML
open L4YAML.Emit
open L4YAML.TokenParser
open L4YAML.Scanner
open L4YAML.Proofs.ParserWellBehaved

/-- The standalone value of an element: pure, and pinned as the composed single-document
    re-parse of `emit v`. -/
def StdVal (v sv : YamlValue) : Prop :=
  PureVal sv ∧ ∀ rd, parseYamlRaw (emit v) = .ok rd →
    rd.size = 1 ∧ (rd.map YamlDocument.compose)[0]!.value = sv

/-- The per-element standalone witness package the walks consume. -/
def StdElt (v : YamlValue) : Prop :=
  ∃ (stdToks : Array (Positioned YamlToken)) (sv : YamlValue) (q : ParseState),
    stdToks.toList.map (·.val) = .streamStart :: (emitTokVals v ++ [.streamEnd]) ∧
    parseNode ({ tokens := stdToks, pos := 1 } : ParseState) (4 * stdToks.size + 4)
      = .ok (sv, q) ∧
    q.pos = stdToks.size - 1 ∧
    StdVal v sv

/-- The remaining-window shape of the sequence loop: nothing once the body is exhausted;
    the raw body run at the first element; a `.flowEntry`-prefixed run mid-list. -/
def seqLoopWindow (acZero : Bool) (rest : List YamlValue) : List YamlToken :=
  match rest, acZero with
  | [], _ => []
  | _, true => emitTokVals.seqTokVals rest
  | _, false => .flowEntry :: emitTokVals.seqTokVals rest

/-- The mapping mirror (per-pair `.key ⟨k⟩ .value ⟨v⟩` segments). -/
def mapLoopWindow (acZero : Bool) (rest : List (YamlValue × YamlValue)) : List YamlToken :=
  match rest, acZero with
  | [], _ => []
  | _, true => emitTokVals.mapTokVals rest
  | _, false => .flowEntry :: emitTokVals.mapTokVals rest

private theorem push_getElem!_lt (a : Array YamlValue) (x : YamlValue) (j : Nat)
    (hj : j < a.size) : (a.push x)[j]! = a[j]! := by
  rw [getElem!_pos (a.push x) j (by simp; omega), getElem!_pos a j hj]
  exact Array.getElem_push_lt hj

private theorem push_getElem!_last (a : Array YamlValue) (x : YamlValue) :
    (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp)]
  exact Array.getElem_push_eq ..

private theorem pair_push_getElem!_lt (a : Array (YamlValue × YamlValue))
    (x : YamlValue × YamlValue) (j : Nat) (hj : j < a.size) : (a.push x)[j]! = a[j]! := by
  rw [getElem!_pos (a.push x) j (by simp; omega), getElem!_pos a j hj]
  exact Array.getElem_push_lt hj

private theorem pair_push_getElem!_last (a : Array (YamlValue × YamlValue))
    (x : YamlValue × YamlValue) : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp)]
  exact Array.getElem_push_eq ..

/-- The head token of an emission run, with its content-start classification. -/
private theorem emitTokVals_head_tok (v : YamlValue) :
    ∃ htk, (emitTokVals v)[0]? = some htk
      ∧ ((∃ c st, htk = .scalar c st) ∨ htk = .flowSequenceStart ∨ htk = .flowMappingStart) := by
  have h_h := emitTokVals_head v
  cases h_c : emitTokVals v with
  | nil => exact absurd h_c (emitTokVals_ne_nil v)
  | cons a t =>
    rw [h_c] at h_h
    simp only [List.head?_cons, Option.some.injEq] at h_h
    refine ⟨a, by simp, ?_⟩
    rcases h_h with ⟨c, st, h⟩ | h | h
    · exact Or.inl ⟨c, st, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

set_option maxHeartbeats 3200000 in
private theorem seq_walk_aux {tokens : Array (Positioned YamlToken)} :
    ∀ (rest : List YamlValue) (acc : Array YamlValue) (ps : ParseState) (fuel : Nat)
      (result : Array YamlValue × ParseState),
      (∀ v ∈ rest, StdElt v) →
      ps.tokens = tokens →
      (∀ i, tokens[ps.pos + i]?.map (·.val)
        = (seqLoopWindow (acc.size == 0) rest
            ++ [YamlToken.flowSequenceEnd, YamlToken.streamEnd])[i]?) →
      rest.length + 1 ≤ fuel →
      parseFlowSequenceLoop ps fuel acc = .ok result →
      result.1.size = acc.size + rest.length
      ∧ (∀ j, j < acc.size → result.1[j]! = acc[j]!)
      ∧ (∀ j (hj : j < rest.length), ∃ sv, StdVal rest[j] sv
          ∧ result.1[acc.size + j]! = sv) := by
  intro rest
  induction rest with
  | nil =>
    intro acc ps fuel result h_std h_tok h_win h_fuel h_ok
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have h_pk : ps.peek? = some YamlToken.flowSequenceEnd := by
      rw [peek?_eq_getElem?, h_tok]
      have h0 := h_win 0
      simpa [seqLoopWindow] using h0
    rcases parseFlowSequenceLoop_step_inv ps f acc result h_ok with
      ⟨_, h_r⟩ | ⟨_, h_ne, _, _⟩ | ⟨w0, ps', _, _, h_ne, _, _⟩
    · rw [h_r]
      exact ⟨by simp, fun j hj => rfl, fun j hj => absurd hj (by simp)⟩
    · exact absurd h_pk h_ne
    · exact absurd h_pk h_ne
  | cons v rest' ih =>
    intro acc ps fuel result h_std h_tok h_win h_fuel h_ok
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨htk, h_tv0, h_htk3⟩ := emitTokVals_head_tok v
    have h_tv_pos := emitTokVals_length_pos v
    have h_stv_pos : 0 < (emitTokVals.seqTokVals (v :: rest')).length := by
      have h1 := seqTokVals_length_ge (v :: rest')
      simp only [List.length_cons] at h1
      omega
    have h_seqhead : ∀ i, i < (emitTokVals v).length →
        (emitTokVals.seqTokVals (v :: rest'))[i]? = (emitTokVals v)[i]? := by
      intro i hi
      cases rest' with
      | nil => rw [seqTokVals_singleton]
      | cons w ws => rw [seqTokVals_cons_cons, List.getElem?_append_left hi]
    have h_htk_ne : htk ≠ YamlToken.flowSequenceEnd ∧ htk ≠ YamlToken.flowEntry
        ∧ htk ≠ YamlToken.key := by
      rcases h_htk3 with ⟨c, st, rfl⟩ | rfl | rfl <;> exact ⟨by simp, by simp, by simp⟩
    obtain ⟨stdToks, sv, q_std, h_spin, h_snode, h_send, h_sval⟩ :=
      h_std v (List.mem_cons_self ..)
    have h_std_at := pin_getElem?_val h_spin
    have h_std_len : stdToks.size = (emitTokVals v).length + 2 := by
      have h0 := congrArg List.length h_spin
      simp only [List.length_map, Array.length_toList, List.length_cons, List.length_append,
        List.length_nil] at h0
      omega
    have h_seq_len : (emitTokVals v).length
        ≤ (emitTokVals.seqTokVals (v :: rest')).length := by
      cases rest' with
      | nil => rw [seqTokVals_singleton]; exact Nat.le_refl _
      | cons w ws =>
        rw [seqTokVals_cons_cons]
        simp only [List.length_append, List.length_cons]
        omega
    by_cases h_acc : acc.size = 0
    case pos =>
      rw [show (acc.size == 0) = true from by simp [h_acc]] at h_win
      have h_pk : ps.peek? = some htk := by
        rw [peek?_eq_getElem?, h_tok]
        have h0 := h_win 0
        rw [show seqLoopWindow true (v :: rest') = emitTokVals.seqTokVals (v :: rest')
            from rfl, List.getElem?_append_left h_stv_pos, h_seqhead 0 h_tv_pos, h_tv0] at h0
        simpa using h0
      rcases parseFlowSequenceLoop_step_inv ps f acc result h_ok with
        ⟨h_c, _⟩ | ⟨h_sz, _, _, _⟩ | ⟨w0, ps', h_p', h_t', _, h_sep, h_disp⟩
      · exact absurd (Option.some.inj (h_pk.symm.trans h_c)) h_htk_ne.1
      · omega
      · have h_w0 : w0 = 0 := by
          rcases h_sep with ⟨h1, _, _⟩ | ⟨_, h2⟩
          · omega
          · exact h2
        subst h_w0
        have h_elt_win : ∀ i, tokens[ps'.pos + i]?.map (·.val)
            = (emitTokVals.seqTokVals (v :: rest')
                ++ [YamlToken.flowSequenceEnd, YamlToken.streamEnd])[i]? := by
          intro i
          rw [h_p', Nat.add_zero]
          exact h_win i
        have h_pk' : ps'.peek? = some htk := by
          rw [peek?_eq_getElem?, h_t', h_tok]
          have h0 := h_elt_win 0
          rw [List.getElem?_append_left h_stv_pos, h_seqhead 0 h_tv_pos, h_tv0] at h0
          simpa using h0
        rcases h_disp with ⟨h_c, _⟩
          | ⟨h_k, _, _, _, _, _, _, _, _, _, _⟩
          | ⟨_, _, psE, val, psn, psC, h_el, hpe, hte, h_cont, hpc, htc⟩
        · exact absurd (Option.some.inj (h_pk'.symm.trans h_c)) h_htk_ne.1
        · exact absurd (Option.some.inj (h_pk'.symm.trans h_k)) h_htk_ne.2.2
        · have h_psE_tok : psE.tokens = tokens := by rw [hte, h_t', h_tok]
          have h_frame : q_std.pos ≤ 1 + (emitTokVals v).length := by
            rw [h_send]; omega
          have h_ag : WAgree stdToks tokens 1 psE.pos (emitTokVals v).length := by
            intro k hk
            rw [show (1 : Nat) + k = k + 1 from by omega]
            have h_s := h_std_at (k + 1)
            rw [List.getElem?_cons_succ, List.getElem?_append_left hk] at h_s
            have h_t := h_elt_win k
            rw [List.getElem?_append_left (by omega), h_seqhead k hk] at h_t
            rw [hpe]
            exact h_s.trans h_t.symm
          have h_cl : WClean stdToks 1 (emitTokVals v).length := by
            intro k hk pt hpt
            rw [show (1 : Nat) + k = k + 1 from by omega] at hpt
            have h_s := h_std_at (k + 1)
            rw [List.getElem?_cons_succ, List.getElem?_append_left hk, hpt,
              List.getElem?_eq_getElem hk] at h_s
            simp only [Option.map_some, Option.some.injEq] at h_s
            rw [h_s]
            exact emitTokVals_flowClean v _ (List.getElem_mem hk)
          have h_psn_lo : psE.pos ≤ psn.pos :=
            parseNodePosMono_apply (parseNode_pos_mono_all f) h_el (Nat.le_refl _)
          rw [← h_psE_tok] at h_ag
          obtain ⟨h_val_eq, h_adv_eq, _, h_et2⟩ :=
            parseNode_joint (4 * stdToks.size + 4) f
              ({ tokens := stdToks, pos := 1 } : ParseState) psE
              (emitTokVals v).length sv val q_std psn
              h_tv_pos h_ag h_cl h_snode h_el h_frame
          have h_psn_pos : psn.pos = psE.pos + (emitTokVals v).length := by
            have h1 : q_std.pos - 1 = psn.pos - psE.pos := h_adv_eq
            rw [h_send, h_std_len] at h1
            omega
          have h_cont_win : ∀ i, tokens[psC.pos + i]?.map (·.val)
              = (seqLoopWindow ((acc.push val).size == 0) rest'
                  ++ [YamlToken.flowSequenceEnd, YamlToken.streamEnd])[i]? := by
            intro i
            rw [show ((acc.push val).size == 0) = false from by simp]
            have h_idx : psC.pos + i = ps'.pos + ((emitTokVals v).length + i) := by
              rw [hpc, h_psn_pos, hpe]; omega
            rw [h_idx, h_elt_win ((emitTokVals v).length + i)]
            cases rest' with
            | nil =>
              rw [seqTokVals_singleton,
                List.getElem?_append_right (Nat.le_add_right ..)]
              simp only [seqLoopWindow, List.nil_append]
              congr 1
              omega
            | cons w ws =>
              rw [seqTokVals_cons_cons, List.append_assoc,
                List.getElem?_append_right (Nat.le_add_right ..)]
              simp only [seqLoopWindow, List.cons_append]
              congr 1
              omega
          obtain ⟨h_sz_ih, h_pre_ih, h_vals_ih⟩ := ih (acc.push val) psC f result
            (fun w hw => h_std w (List.mem_cons_of_mem _ hw))
            (by rw [htc, h_et2, h_psE_tok])
            h_cont_win (by simp only [List.length_cons] at h_fuel; omega) h_cont
          refine ⟨?_, ?_, ?_⟩
          · rw [h_sz_ih]
            simp only [Array.size_push, List.length_cons]
            omega
          · intro j hj
            rw [h_pre_ih j (by simp only [Array.size_push]; omega)]
            exact push_getElem!_lt acc val j hj
          · intro j hj
            cases j with
            | zero =>
              refine ⟨sv, h_sval, ?_⟩
              rw [Nat.add_zero, h_pre_ih acc.size (by simp only [Array.size_push]; omega),
                push_getElem!_last, ← h_val_eq]
            | succ j' =>
              have hj' : j' < rest'.length := by
                simp only [List.length_cons] at hj; omega
              obtain ⟨sv', h_sv', h_at'⟩ := h_vals_ih j' hj'
              refine ⟨sv', by simpa using h_sv', ?_⟩
              rw [show acc.size + (j' + 1) = (acc.push val).size + j' from by
                simp only [Array.size_push]; omega]
              exact h_at'
    case neg =>
      rw [show (acc.size == 0) = false from by simp [h_acc]] at h_win
      have h_pk : ps.peek? = some YamlToken.flowEntry := by
        rw [peek?_eq_getElem?, h_tok]
        have h0 := h_win 0
        simpa [seqLoopWindow] using h0
      rcases parseFlowSequenceLoop_step_inv ps f acc result h_ok with
        ⟨h_c, _⟩ | ⟨_, _, h_nf, _⟩ | ⟨w0, ps', h_p', h_t', _, h_sep, h_disp⟩
      · exact absurd (Option.some.inj (h_pk.symm.trans h_c)) (by simp)
      · exact absurd h_pk h_nf
      · have h_w0 : w0 = 1 := by
          rcases h_sep with ⟨_, _, h2⟩ | ⟨h1, _⟩
          · exact h2
          · omega
        subst h_w0
        have h_elt_win : ∀ i, tokens[ps'.pos + i]?.map (·.val)
            = (emitTokVals.seqTokVals (v :: rest')
                ++ [YamlToken.flowSequenceEnd, YamlToken.streamEnd])[i]? := by
          intro i
          have h0 := h_win (1 + i)
          rw [show seqLoopWindow false (v :: rest') = YamlToken.flowEntry ::
              emitTokVals.seqTokVals (v :: rest') from rfl] at h0
          rw [show (YamlToken.flowEntry :: emitTokVals.seqTokVals (v :: rest'))
              ++ [YamlToken.flowSequenceEnd, YamlToken.streamEnd]
              = YamlToken.flowEntry :: (emitTokVals.seqTokVals (v :: rest')
                ++ [YamlToken.flowSequenceEnd, YamlToken.streamEnd]) from rfl,
            show (1 : Nat) + i = i + 1 from by omega, List.getElem?_cons_succ] at h0
          rw [h_p', show ps.pos + 1 + i = ps.pos + (i + 1) from by omega]
          exact h0
        have h_pk' : ps'.peek? = some htk := by
          rw [peek?_eq_getElem?, h_t', h_tok]
          have h0 := h_elt_win 0
          rw [List.getElem?_append_left h_stv_pos, h_seqhead 0 h_tv_pos, h_tv0] at h0
          simpa using h0
        rcases h_disp with ⟨h_c, _⟩
          | ⟨h_k, _, _, _, _, _, _, _, _, _, _⟩
          | ⟨_, _, psE, val, psn, psC, h_el, hpe, hte, h_cont, hpc, htc⟩
        · exact absurd (Option.some.inj (h_pk'.symm.trans h_c)) h_htk_ne.1
        · exact absurd (Option.some.inj (h_pk'.symm.trans h_k)) h_htk_ne.2.2
        · have h_psE_tok : psE.tokens = tokens := by rw [hte, h_t', h_tok]
          have h_frame : q_std.pos ≤ 1 + (emitTokVals v).length := by
            rw [h_send]; omega
          have h_ag : WAgree stdToks tokens 1 psE.pos (emitTokVals v).length := by
            intro k hk
            rw [show (1 : Nat) + k = k + 1 from by omega]
            have h_s := h_std_at (k + 1)
            rw [List.getElem?_cons_succ, List.getElem?_append_left hk] at h_s
            have h_t := h_elt_win k
            rw [List.getElem?_append_left (by omega), h_seqhead k hk] at h_t
            rw [hpe]
            exact h_s.trans h_t.symm
          have h_cl : WClean stdToks 1 (emitTokVals v).length := by
            intro k hk pt hpt
            rw [show (1 : Nat) + k = k + 1 from by omega] at hpt
            have h_s := h_std_at (k + 1)
            rw [List.getElem?_cons_succ, List.getElem?_append_left hk, hpt,
              List.getElem?_eq_getElem hk] at h_s
            simp only [Option.map_some, Option.some.injEq] at h_s
            rw [h_s]
            exact emitTokVals_flowClean v _ (List.getElem_mem hk)
          have h_psn_lo : psE.pos ≤ psn.pos :=
            parseNodePosMono_apply (parseNode_pos_mono_all f) h_el (Nat.le_refl _)
          rw [← h_psE_tok] at h_ag
          obtain ⟨h_val_eq, h_adv_eq, _, h_et2⟩ :=
            parseNode_joint (4 * stdToks.size + 4) f
              ({ tokens := stdToks, pos := 1 } : ParseState) psE
              (emitTokVals v).length sv val q_std psn
              h_tv_pos h_ag h_cl h_snode h_el h_frame
          have h_psn_pos : psn.pos = psE.pos + (emitTokVals v).length := by
            have h1 : q_std.pos - 1 = psn.pos - psE.pos := h_adv_eq
            rw [h_send, h_std_len] at h1
            omega
          have h_cont_win : ∀ i, tokens[psC.pos + i]?.map (·.val)
              = (seqLoopWindow ((acc.push val).size == 0) rest'
                  ++ [YamlToken.flowSequenceEnd, YamlToken.streamEnd])[i]? := by
            intro i
            rw [show ((acc.push val).size == 0) = false from by simp]
            have h_idx : psC.pos + i = ps'.pos + ((emitTokVals v).length + i) := by
              rw [hpc, h_psn_pos, hpe]; omega
            rw [h_idx, h_elt_win ((emitTokVals v).length + i)]
            cases rest' with
            | nil =>
              rw [seqTokVals_singleton,
                List.getElem?_append_right (Nat.le_add_right ..)]
              simp only [seqLoopWindow, List.nil_append]
              congr 1
              omega
            | cons w ws =>
              rw [seqTokVals_cons_cons, List.append_assoc,
                List.getElem?_append_right (Nat.le_add_right ..)]
              simp only [seqLoopWindow, List.cons_append]
              congr 1
              omega
          obtain ⟨h_sz_ih, h_pre_ih, h_vals_ih⟩ := ih (acc.push val) psC f result
            (fun w hw => h_std w (List.mem_cons_of_mem _ hw))
            (by rw [htc, h_et2, h_psE_tok])
            h_cont_win (by simp only [List.length_cons] at h_fuel; omega) h_cont
          refine ⟨?_, ?_, ?_⟩
          · rw [h_sz_ih]
            simp only [Array.size_push, List.length_cons]
            omega
          · intro j hj
            rw [h_pre_ih j (by simp only [Array.size_push]; omega)]
            exact push_getElem!_lt acc val j hj
          · intro j hj
            cases j with
            | zero =>
              refine ⟨sv, h_sval, ?_⟩
              rw [Nat.add_zero, h_pre_ih acc.size (by simp only [Array.size_push]; omega),
                push_getElem!_last, ← h_val_eq]
            | succ j' =>
              have hj' : j' < rest'.length := by
                simp only [List.length_cons] at hj; omega
              obtain ⟨sv', h_sv', h_at'⟩ := h_vals_ih j' hj'
              refine ⟨sv', by simpa using h_sv', ?_⟩
              rw [show acc.size + (j' + 1) = (acc.push val).size + j' from by
                simp only [Array.size_push]; omega]
              exact h_at'

/-- **The general sequence walk** (R601 generalized): over an `emitTokVals`-pinned whole-stream
    token array, the flow-sequence loop recovers, slot by slot, exactly the elements' standalone
    values. -/
theorem parseFlowSeqLoop_tokvals_value_at {tokens : Array (Positioned YamlToken)}
    {items : List YamlValue} (h_ne : items ≠ [])
    (h_pin : tokens.toList.map (·.val)
      = .streamStart :: (.flowSequenceStart :: (emitTokVals.seqTokVals items
          ++ [.flowSequenceEnd, .streamEnd])))
    (h_std : ∀ v ∈ items, StdElt v)
    {ps : ParseState} (h_toks : ps.tokens = tokens) (h_pos : ps.pos = 2)
    {fuel : Nat} (h_fuel : items.length + 1 ≤ fuel)
    {result : Array YamlValue × ParseState}
    (h_ok : parseFlowSequenceLoop ps fuel #[] = .ok result) :
    result.1.size = items.length
    ∧ ∀ j (hj : j < items.length), ∃ sv, StdVal items[j] sv ∧ result.1[j]! = sv := by
  have h_at := pin_getElem?_val h_pin
  have h_win : ∀ i, tokens[ps.pos + i]?.map (·.val)
      = (seqLoopWindow ((#[] : Array YamlValue).size == 0) items
          ++ [YamlToken.flowSequenceEnd, YamlToken.streamEnd])[i]? := by
    intro i
    have h0 := h_at (i + 1 + 1)
    rw [List.getElem?_cons_succ, List.getElem?_cons_succ] at h0
    rw [h_pos, show (2 : Nat) + i = i + 1 + 1 from by omega]
    cases items with
    | nil => exact absurd rfl h_ne
    | cons a t => exact h0
  obtain ⟨h_sz, h_pre, h_vals⟩ :=
    seq_walk_aux items #[] ps fuel result h_std h_toks h_win h_fuel h_ok
  constructor
  · simpa using h_sz
  · intro j hj
    obtain ⟨sv, h_sv, h_at'⟩ := h_vals j hj
    refine ⟨sv, h_sv, ?_⟩
    simpa using h_at'

set_option maxHeartbeats 6400000 in
private theorem map_walk_aux {tokens : Array (Positioned YamlToken)} :
    ∀ (rest : List (YamlValue × YamlValue)) (acc : Array (YamlValue × YamlValue))
      (ps : ParseState) (fuel : Nat)
      (result : Array (YamlValue × YamlValue) × ParseState),
      (∀ p ∈ rest, StdElt p.1) →
      (∀ p ∈ rest, StdElt p.2) →
      ps.tokens = tokens →
      (∀ i, tokens[ps.pos + i]?.map (·.val)
        = (mapLoopWindow (acc.size == 0) rest
            ++ [YamlToken.flowMappingEnd, YamlToken.streamEnd])[i]?) →
      rest.length + 1 ≤ fuel →
      parseFlowMappingLoop ps fuel acc = .ok result →
      result.1.size = acc.size + rest.length
      ∧ (∀ j, j < acc.size → result.1[j]! = acc[j]!)
      ∧ (∀ j (hj : j < rest.length), ∃ sk sv, StdVal rest[j].1 sk ∧ StdVal rest[j].2 sv
          ∧ result.1[acc.size + j]! = (sk, sv)) := by
  intro rest
  induction rest with
  | nil =>
    intro acc ps fuel result h_std_k h_std_v h_tok h_win h_fuel h_ok
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have h_pk : ps.peek? = some YamlToken.flowMappingEnd := by
      rw [peek?_eq_getElem?, h_tok]
      have h0 := h_win 0
      simpa [mapLoopWindow] using h0
    rcases parseFlowMappingLoop_step_inv ps f acc result h_ok with
      ⟨_, h_r⟩ | ⟨_, h_ne, _, _⟩ | ⟨w0, ps', _, _, h_ne, _, _⟩
    · rw [h_r]
      exact ⟨by simp, fun j hj => rfl, fun j hj => absurd hj (by simp)⟩
    · exact absurd h_pk h_ne
    · exact absurd h_pk h_ne
  | cons p rest' ih =>
    obtain ⟨kv, vv⟩ := p
    intro acc ps fuel result h_std_k h_std_v h_tok h_win h_fuel h_ok
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have h_seg_shape : emitTokVals.mapTokVals ((kv, vv) :: rest')
          ++ [YamlToken.flowMappingEnd, YamlToken.streamEnd]
        = YamlToken.key :: ((emitTokVals kv ++ (YamlToken.value :: emitTokVals vv))
            ++ (mapLoopWindow false rest'
                ++ [YamlToken.flowMappingEnd, YamlToken.streamEnd])) := by
      cases rest' with
      | nil =>
        rw [mapTokVals_singleton]
        simp only [mapLoopWindow, List.cons_append, List.nil_append, List.append_assoc]
      | cons q qs =>
        rw [mapTokVals_cons_cons]
        simp only [mapLoopWindow, List.cons_append, List.append_assoc]
    obtain ⟨htk_k, h_tvk0, h_htk3_k⟩ := emitTokVals_head_tok kv
    obtain ⟨htk_v, h_tvv0, h_htk3_v⟩ := emitTokVals_head_tok vv
    have h_tvk_pos := emitTokVals_length_pos kv
    have h_tvv_pos := emitTokVals_length_pos vv
    obtain ⟨stdK, sk, qk_std, h_kpin, h_knode, h_kend, h_ksval⟩ :=
      h_std_k (kv, vv) (List.mem_cons_self ..)
    obtain ⟨stdV, sv, qv_std, h_vpin, h_vnode, h_vend, h_vsval⟩ :=
      h_std_v (kv, vv) (List.mem_cons_self ..)
    have h_kstd_at := pin_getElem?_val h_kpin
    have h_vstd_at := pin_getElem?_val h_vpin
    have h_kstd_len : stdK.size = (emitTokVals kv).length + 2 := by
      have h0 := congrArg List.length h_kpin
      simp only [List.length_map, Array.length_toList, List.length_cons, List.length_append,
        List.length_nil] at h0
      omega
    have h_vstd_len : stdV.size = (emitTokVals vv).length + 2 := by
      have h0 := congrArg List.length h_vpin
      simp only [List.length_map, Array.length_toList, List.length_cons, List.length_append,
        List.length_nil] at h0
      omega
    have ELEM : ∀ (ps' : ParseState),
        ps'.tokens = ps.tokens →
        (∀ i, tokens[ps'.pos + i]?.map (·.val)
          = (YamlToken.key :: ((emitTokVals kv ++ (YamlToken.value :: emitTokVals vv))
              ++ (mapLoopWindow false rest'
                  ++ [YamlToken.flowMappingEnd, YamlToken.streamEnd])))[i]?) →
        ((ps'.peek? = some YamlToken.flowMappingEnd ∧ result = (acc, ps'))
          ∨ (ps'.peek? = some YamlToken.key ∧
              ∃ (psE : ParseState) (key : YamlValue) (psn : ParseState) (sp : YamlPath)
                (kc : String) (psM : ParseState) (val : YamlValue) (psv psC : ParseState),
                parseExplicitKey psE f = .ok (key, psn) ∧
                psE.pos = ps'.pos + 1 ∧ psE.tokens = ps'.tokens ∧
                parseFlowMappingValue psM f sp kc = .ok (val, psv) ∧
                psM.pos = psn.pos ∧ psM.tokens = psn.tokens ∧
                parseFlowMappingLoop psC f (acc.push (key, val)) = .ok result ∧
                psC.pos = psv.pos ∧ psC.tokens = psv.tokens)
          ∨ (ps'.peek? ≠ some YamlToken.flowMappingEnd ∧ ps'.peek? ≠ some YamlToken.key)) →
        result.1.size = acc.size + ((kv, vv) :: rest').length
        ∧ (∀ j, j < acc.size → result.1[j]! = acc[j]!)
        ∧ (∀ j (hj : j < ((kv, vv) :: rest').length),
            ∃ sk' sv', StdVal ((kv, vv) :: rest')[j].1 sk'
              ∧ StdVal ((kv, vv) :: rest')[j].2 sv'
              ∧ result.1[acc.size + j]! = (sk', sv')) := by
      intro ps' h_t' h_elt_win h_disp3
      have h_pk_key : ps'.peek? = some YamlToken.key := by
        rw [peek?_eq_getElem?, h_t', h_tok]
        have h0 := h_elt_win 0
        simpa using h0
      rcases h_disp3 with ⟨h_c, _⟩ | ⟨_, h_payload⟩ | ⟨_, h_nk⟩
      · exact absurd (Option.some.inj (h_pk_key.symm.trans h_c)) (by simp)
      case inr.inr => exact absurd h_pk_key h_nk
      obtain ⟨psE, key, psn, sp, kc, psM, val, psv, psC,
        h_key, hpe, hte, h_val, hmp, hmt, h_cont, hpc, htc⟩ := h_payload
      have h_psE_tok : psE.tokens = tokens := by rw [hte, h_t', h_tok]
      have h_pkE : psE.peek? = some htk_k := by
        rw [peek?_eq_getElem?, h_psE_tok, hpe]
        have h0 := h_elt_win (0 + 1)
        rw [List.getElem?_cons_succ,
          List.getElem?_append_left (by
            simp only [List.length_append, List.length_cons]; omega),
          List.getElem?_append_left h_tvk_pos, h_tvk0] at h0
        exact h0
      have h_keq : parseExplicitKey psE f = parseNode psE f := by
        unfold parseExplicitKey
        rcases h_htk3_k with ⟨c, st, h_e⟩ | h_e | h_e <;> rw [h_e] at h_pkE <;> rw [h_pkE]
      rw [h_keq] at h_key
      have h_kframe : qk_std.pos ≤ 1 + (emitTokVals kv).length := by
        rw [h_kend]; omega
      have h_kag : WAgree stdK psE.tokens 1 psE.pos (emitTokVals kv).length := by
        rw [h_psE_tok]
        intro j hj
        rw [show (1 : Nat) + j = j + 1 from by omega]
        have h_s := h_kstd_at (j + 1)
        rw [List.getElem?_cons_succ, List.getElem?_append_left hj] at h_s
        have h_t := h_elt_win (j + 1)
        rw [List.getElem?_cons_succ,
          List.getElem?_append_left (by
            simp only [List.length_append, List.length_cons]; omega),
          List.getElem?_append_left hj] at h_t
        rw [hpe, show ps'.pos + 1 + j = ps'.pos + (j + 1) from by omega]
        exact h_s.trans h_t.symm
      have h_kcl : WClean stdK 1 (emitTokVals kv).length := by
        intro j hj pt hpt
        rw [show (1 : Nat) + j = j + 1 from by omega] at hpt
        have h_s := h_kstd_at (j + 1)
        rw [List.getElem?_cons_succ, List.getElem?_append_left hj, hpt,
          List.getElem?_eq_getElem hj] at h_s
        simp only [Option.map_some, Option.some.injEq] at h_s
        rw [h_s]
        exact emitTokVals_flowClean kv _ (List.getElem_mem hj)
      have h_psn_lo : psE.pos ≤ psn.pos :=
        parseNodePosMono_apply (parseNode_pos_mono_all f) h_key (Nat.le_refl _)
      obtain ⟨h_key_eq, h_kadv, _, h_kt2⟩ :=
        parseNode_joint (4 * stdK.size + 4) f
          ({ tokens := stdK, pos := 1 } : ParseState) psE
          (emitTokVals kv).length sk key qk_std psn
          h_tvk_pos h_kag h_kcl h_knode h_key h_kframe
      have h_psn_pos : psn.pos = psE.pos + (emitTokVals kv).length := by
        have h1 : qk_std.pos - 1 = psn.pos - psE.pos := h_kadv
        rw [h_kend, h_kstd_len] at h1
        omega
      obtain ⟨wk, wv, mid, psv0, val0, pv, hwk, hwv, hval3, hmidp, hmidt, hv0p, hv0t,
        hveq, hqp, hqt⟩ := parseFlowMappingValue_inv psM f sp kc val psv h_val
      have h_psM_tok : psM.tokens = tokens := by rw [hmt, h_kt2, h_psE_tok]
      have h_pkM : psM.peek? = some YamlToken.value := by
        rw [peek?_eq_getElem?, h_psM_tok, hmp, h_psn_pos, hpe]
        have h0 := h_elt_win ((emitTokVals kv).length + 1)
        rw [List.getElem?_cons_succ,
          List.getElem?_append_left (by
            simp only [List.length_append, List.length_cons]; omega),
          List.getElem?_append_right (Nat.le_refl _)] at h0
        simp only [Nat.sub_self] at h0
        rw [show ps'.pos + 1 + (emitTokVals kv).length
            = ps'.pos + ((emitTokVals kv).length + 1) from by omega]
        simpa using h0
      have h_wk : wk = 0 := by
        rcases hwk with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact absurd (Option.some.inj (h_pkM.symm.trans h1)) (by simp)
        · exact h2
      subst h_wk
      have h_midpk : mid.peek? = some YamlToken.value := by
        rw [peek?_eq_getElem?, hmidt, hmidp, Nat.add_zero]
        rw [peek?_eq_getElem?] at h_pkM
        exact h_pkM
      have h_wv : wv = 1 := by
        rcases hwv with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact h2
        · exact absurd h_midpk h1
      subst h_wv
      have h_pv0_tok : psv0.tokens = tokens := by rw [hv0t, h_psM_tok]
      have h_pk_v0 : psv0.peek? = some htk_v := by
        rw [peek?_eq_getElem?, h_pv0_tok, hv0p, hmp, h_psn_pos, hpe]
        have h0 := h_elt_win (((emitTokVals kv).length + 1) + 1)
        rw [List.getElem?_cons_succ,
          List.getElem?_append_left (by
            simp only [List.length_append, List.length_cons]; omega),
          List.getElem?_append_right (by omega),
          show (emitTokVals kv).length + 1 - (emitTokVals kv).length = 0 + 1 from by omega,
          List.getElem?_cons_succ, h_tvv0] at h0
        rw [show ps'.pos + 1 + (emitTokVals kv).length + 0 + 1
            = ps'.pos + ((emitTokVals kv).length + 1 + 1) from by omega]
        exact h0
      rcases hval3 with ⟨h10, _, _⟩ | ⟨_, h_mem, _, _⟩ | ⟨_, _, _, _, h_pn⟩
      · simp at h10
      · rcases h_mem with hm | hm | hm
        all_goals rw [h_pk_v0] at hm
        · exact absurd (Option.some.inj hm)
            (by rcases h_htk3_v with ⟨c, st, rfl⟩ | rfl | rfl <;> simp)
        · exact absurd (Option.some.inj hm)
            (by rcases h_htk3_v with ⟨c, st, rfl⟩ | rfl | rfl <;> simp)
        · simp at hm
      have h_vframe : qv_std.pos ≤ 1 + (emitTokVals vv).length := by
        rw [h_vend]; omega
      have h_vag : WAgree stdV psv0.tokens 1 psv0.pos (emitTokVals vv).length := by
        rw [h_pv0_tok]
        intro j hj
        rw [show (1 : Nat) + j = j + 1 from by omega]
        have h_s := h_vstd_at (j + 1)
        rw [List.getElem?_cons_succ, List.getElem?_append_left hj] at h_s
        have h_t := h_elt_win ((((emitTokVals kv).length + 1) + j) + 1)
        rw [List.getElem?_cons_succ,
          List.getElem?_append_left (by
            simp only [List.length_append, List.length_cons]; omega),
          List.getElem?_append_right (by omega),
          show (emitTokVals kv).length + 1 + j - (emitTokVals kv).length = j + 1 from by omega,
          List.getElem?_cons_succ] at h_t
        rw [hv0p, hmp, h_psn_pos, hpe,
          show ps'.pos + 1 + (emitTokVals kv).length + 0 + 1 + j
            = ps'.pos + ((emitTokVals kv).length + 1 + j + 1) from by omega]
        exact h_s.trans h_t.symm
      have h_vcl : WClean stdV 1 (emitTokVals vv).length := by
        intro j hj pt hpt
        rw [show (1 : Nat) + j = j + 1 from by omega] at hpt
        have h_s := h_vstd_at (j + 1)
        rw [List.getElem?_cons_succ, List.getElem?_append_left hj, hpt,
          List.getElem?_eq_getElem hj] at h_s
        simp only [Option.map_some, Option.some.injEq] at h_s
        rw [h_s]
        exact emitTokVals_flowClean vv _ (List.getElem_mem hj)
      have h_pv_lo : psv0.pos ≤ pv.pos :=
        parseNodePosMono_apply (parseNode_pos_mono_all f) h_pn (Nat.le_refl _)
      obtain ⟨h_val_eq, h_vadv, _, h_vt2⟩ :=
        parseNode_joint (4 * stdV.size + 4) f
          ({ tokens := stdV, pos := 1 } : ParseState) psv0
          (emitTokVals vv).length sv val0 qv_std pv
          h_tvv_pos h_vag h_vcl h_vnode h_pn h_vframe
      have h_pv_pos : pv.pos = psv0.pos + (emitTokVals vv).length := by
        have h1 : qv_std.pos - 1 = pv.pos - psv0.pos := h_vadv
        rw [h_vend, h_vstd_len] at h1
        omega
      have h_psC_tok : psC.tokens = tokens := by
        rw [htc, hqt, h_vt2, h_pv0_tok]
      have h_psC_pos : psC.pos = ps'.pos
          + ((emitTokVals kv).length + 1 + (emitTokVals vv).length + 1) := by
        rw [hpc, hqp, h_pv_pos, hv0p, hmp, h_psn_pos, hpe]
        omega
      have h_cont_win : ∀ i, tokens[psC.pos + i]?.map (·.val)
          = (mapLoopWindow ((acc.push (key, val)).size == 0) rest'
              ++ [YamlToken.flowMappingEnd, YamlToken.streamEnd])[i]? := by
        intro i
        rw [show ((acc.push (key, val)).size == 0) = false from by simp]
        have h0 := h_elt_win ((((emitTokVals kv).length + 1 + (emitTokVals vv).length) + i) + 1)
        rw [List.getElem?_cons_succ,
          List.getElem?_append_right (by
            simp only [List.length_append, List.length_cons]; omega)] at h0
        rw [show psC.pos + i
            = ps'.pos + ((emitTokVals kv).length + 1 + (emitTokVals vv).length + i + 1) from by
          rw [h_psC_pos]; omega, h0]
        congr 1
        simp only [List.length_append, List.length_cons]
        omega
      obtain ⟨h_sz_ih, h_pre_ih, h_vals_ih⟩ := ih (acc.push (key, val)) psC f result
        (fun q hq => h_std_k q (List.mem_cons_of_mem _ hq))
        (fun q hq => h_std_v q (List.mem_cons_of_mem _ hq))
        h_psC_tok h_cont_win (by simp only [List.length_cons] at h_fuel; omega) h_cont
      refine ⟨?_, ?_, ?_⟩
      · rw [h_sz_ih]
        simp only [Array.size_push, List.length_cons]
        omega
      · intro j hj
        rw [h_pre_ih j (by simp only [Array.size_push]; omega)]
        exact pair_push_getElem!_lt acc (key, val) j hj
      · intro j hj
        cases j with
        | zero =>
          refine ⟨sk, sv, h_ksval, h_vsval, ?_⟩
          rw [Nat.add_zero, h_pre_ih acc.size (by simp only [Array.size_push]; omega),
            pair_push_getElem!_last, ← h_key_eq, hveq, ← h_val_eq]
        | succ j' =>
          have hj' : j' < rest'.length := by
            simp only [List.length_cons] at hj; omega
          obtain ⟨sk', sv', h_sk', h_sv', h_at'⟩ := h_vals_ih j' hj'
          refine ⟨sk', sv', by simpa using h_sk', by simpa using h_sv', ?_⟩
          rw [show acc.size + (j' + 1) = (acc.push (key, val)).size + j' from by
            simp only [Array.size_push]; omega]
          exact h_at'
    by_cases h_acc : acc.size = 0
    case pos =>
      rw [show (acc.size == 0) = true from by simp [h_acc]] at h_win
      have h_win' : ∀ i, tokens[ps.pos + i]?.map (·.val)
          = (YamlToken.key :: ((emitTokVals kv ++ (YamlToken.value :: emitTokVals vv))
              ++ (mapLoopWindow false rest'
                  ++ [YamlToken.flowMappingEnd, YamlToken.streamEnd])))[i]? := by
        intro i
        rw [← h_seg_shape]
        exact h_win i
      have h_pk : ps.peek? = some YamlToken.key := by
        rw [peek?_eq_getElem?, h_tok]
        have h0 := h_win' 0
        simpa using h0
      rcases parseFlowMappingLoop_step_inv ps f acc result h_ok with
        ⟨h_c, _⟩ | ⟨h_sz, _, _, _⟩ | ⟨w0, ps', h_p', h_t', _, h_sep, h_disp⟩
      · exact absurd (Option.some.inj (h_pk.symm.trans h_c)) (by simp)
      · omega
      · have h_w0 : w0 = 0 := by
          rcases h_sep with ⟨h1, _, _⟩ | ⟨_, h2⟩
          · omega
          · exact h2
        subst h_w0
        refine ELEM ps' h_t' ?_ ?_
        · intro i
          rw [h_p', Nat.add_zero]
          exact h_win' i
        · rcases h_disp with ⟨h_c, h_r⟩ | ⟨h_k, h_pl⟩ | ⟨h_nc, h_nk, _⟩
          · exact Or.inl ⟨h_c, h_r⟩
          · exact Or.inr (Or.inl ⟨h_k, h_pl⟩)
          · exact Or.inr (Or.inr ⟨h_nc, h_nk⟩)
    case neg =>
      rw [show (acc.size == 0) = false from by simp [h_acc]] at h_win
      have h_pk : ps.peek? = some YamlToken.flowEntry := by
        rw [peek?_eq_getElem?, h_tok]
        have h0 := h_win 0
        simpa [mapLoopWindow] using h0
      rcases parseFlowMappingLoop_step_inv ps f acc result h_ok with
        ⟨h_c, _⟩ | ⟨_, _, h_nf, _⟩ | ⟨w0, ps', h_p', h_t', _, h_sep, h_disp⟩
      · exact absurd (Option.some.inj (h_pk.symm.trans h_c)) (by simp)
      · exact absurd h_pk h_nf
      · have h_w0 : w0 = 1 := by
          rcases h_sep with ⟨_, _, h2⟩ | ⟨h1, _⟩
          · exact h2
          · omega
        subst h_w0
        refine ELEM ps' h_t' ?_ ?_
        · intro i
          have h0 := h_win (i + 1)
          rw [show mapLoopWindow false ((kv, vv) :: rest')
              = YamlToken.flowEntry :: emitTokVals.mapTokVals ((kv, vv) :: rest') from rfl,
            show (YamlToken.flowEntry :: emitTokVals.mapTokVals ((kv, vv) :: rest'))
              ++ [YamlToken.flowMappingEnd, YamlToken.streamEnd]
              = YamlToken.flowEntry :: (emitTokVals.mapTokVals ((kv, vv) :: rest')
                ++ [YamlToken.flowMappingEnd, YamlToken.streamEnd]) from rfl,
            List.getElem?_cons_succ, h_seg_shape] at h0
          rw [h_p', show ps.pos + 1 + i = ps.pos + (i + 1) from by omega]
          exact h0
        · rcases h_disp with ⟨h_c, h_r⟩ | ⟨h_k, h_pl⟩ | ⟨h_nc, h_nk, _⟩
          · exact Or.inl ⟨h_c, h_r⟩
          · exact Or.inr (Or.inl ⟨h_k, h_pl⟩)
          · exact Or.inr (Or.inr ⟨h_nc, h_nk⟩)

/-- **The general mapping walk** (R608 generalized). -/
theorem parseFlowMapLoop_tokvals_pair_at {tokens : Array (Positioned YamlToken)}
    {pairs : List (YamlValue × YamlValue)} (h_ne : pairs ≠ [])
    (h_pin : tokens.toList.map (·.val)
      = .streamStart :: (.flowMappingStart :: (emitTokVals.mapTokVals pairs
          ++ [.flowMappingEnd, .streamEnd])))
    (h_std_k : ∀ p ∈ pairs, StdElt p.1)
    (h_std_v : ∀ p ∈ pairs, StdElt p.2)
    {ps : ParseState} (h_toks : ps.tokens = tokens) (h_pos : ps.pos = 2)
    {fuel : Nat} (h_fuel : pairs.length + 1 ≤ fuel)
    {result : Array (YamlValue × YamlValue) × ParseState}
    (h_ok : parseFlowMappingLoop ps fuel #[] = .ok result) :
    result.1.size = pairs.length
    ∧ ∀ j (hj : j < pairs.length), ∃ sk sv, StdVal pairs[j].1 sk ∧ StdVal pairs[j].2 sv
        ∧ result.1[j]! = (sk, sv) := by
  have h_at := pin_getElem?_val h_pin
  have h_win : ∀ i, tokens[ps.pos + i]?.map (·.val)
      = (mapLoopWindow ((#[] : Array (YamlValue × YamlValue)).size == 0) pairs
          ++ [YamlToken.flowMappingEnd, YamlToken.streamEnd])[i]? := by
    intro i
    have h0 := h_at (i + 1 + 1)
    rw [List.getElem?_cons_succ, List.getElem?_cons_succ] at h0
    rw [h_pos, show (2 : Nat) + i = i + 1 + 1 from by omega]
    cases pairs with
    | nil => exact absurd rfl h_ne
    | cons a t => exact h0
  obtain ⟨h_sz, h_pre, h_vals⟩ :=
    map_walk_aux pairs #[] ps fuel result h_std_k h_std_v h_toks h_win h_fuel h_ok
  constructor
  · simpa using h_sz
  · intro j hj
    obtain ⟨sk, sv, h_sk, h_sv, h_at'⟩ := h_vals j hj
    refine ⟨sk, sv, h_sk, h_sv, ?_⟩
    simpa using h_at'

end L4YAML.Proofs.EmitterScannability
