/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import L4YAML.Proofs.Parser.ParserWellBehaved
import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity
import L4YAML.Proofs.Output.EmitterScannability.TokVals

/-!
# Value locality: the both-success token-`.val`-window joint over the parser clique

The general (non-all-scalar) Front-B locality equation compares TWO successful parser runs — the
standalone parse of `emit items[i]` and the whole-stream element parse — whose token windows
agree on `.val`s but sit at different positions, in different arrays, with different fuels.

This module proves the JOINT: if two `parseNode` runs both SUCCEED, their windows `.val`-agree
for `nn` tokens, run 1's window is *flow-clean* (`FlowCleanTok`: scalars, flow brackets,
`.flowEntry`, `.key`, `.value` — exactly what emissions produce), and run 1 stays within its
window (a ONE-SIDED frame — the standalone run supplies it from its own stream framing), then
the two runs return the SAME value and the SAME relative advance.

Design decisions (each Rule-2 grounded in `Tests/Reflections/GeneralLocalityBirth.lean`):

* **Both-success**: the Except-level `.map` form is position-dependent through error values
  (`p2b_map_form_false`); both consumption sites hold both successes as hypotheses, so errors
  never need to be compared.
* **Two fuels**: the standalone run's fuel (`4·|std|+4`) differs from the in-stream element's;
  the joint carries independent fuels (`joint_birth_two_fuel`).  At loop level a two-fuel joint
  is REFUTABLE at fuel 0 (the fuel-exhaustion exit returns `.ok` early), so the loop joints
  carry **proper-exit hypotheses** (`r.2.peek? = close`) — supplied at every invocation by the
  enclosing `parseFlowSequence`/`parseFlowMapping` close-checks.
* **Flow-clean gate instead of anchors/tagHandles hypotheses**: on success paths the parser
  reads state beyond `tokens`/`pos` only through `.alias` (anchors lookup), `.anchor`
  (registration), `.tag` (`tagHandles` resolution), and `.blockEntry` (the pre-window
  `isSeqEntry` read).  The gate excludes all four, so runs over emitted windows neither read
  nor write any of them, and the joint needs NO anchors relation at all.
* **One-sided frame, strict at loop level**: the loop exits read the token AT the final
  position (close/early exits), so the loop frame is `r1.2.pos < ps1.pos + nn`; `parseNode`
  itself never reads past its final position except zero-advance exits at the head, covered by
  `q1.pos ≤ ps1.pos + nn` plus `0 < nn`.

The clique is organized like `ParseNodePosMono` (`ParserWellBehaved.lean`): a fuel-indexed
predicate `ParseNodeJoint n`, sibling lemmas parameterized by it (the loops do their own inner
fuel induction), and a top-level `Nat.rec` (`parseNode_joint_all`).
-/

namespace L4YAML.Proofs.EmitterScannability

open L4YAML
open L4YAML.TokenParser
open L4YAML.Proofs.ParserWellBehaved

/-! ## §0  Windows: `.val`-agreement, the flow-clean gate, and transfer helpers -/

/-- `peek?` is the `.val`-projection of the positional lookup. -/
lemma peek?_eq_getElem? (ps : ParseState) :
    ps.peek? = ps.tokens[ps.pos]?.map (·.val) := by
  unfold ParseState.peek?
  split
  · rename_i h
    rw [getElem!_pos ps.tokens ps.pos h, getElem?_pos ps.tokens ps.pos h]
    rfl
  · rename_i h
    rw [getElem?_neg ps.tokens ps.pos (by omega)]
    rfl

/-- Window `.val`-agreement: the next `nn` token `.val`s at `p1` in `t1` and at `p2` in `t2`
    agree (bounds included, via the `?`-lookup). -/
def WAgree (t1 t2 : Array (Positioned YamlToken)) (p1 p2 nn : Nat) : Prop :=
  ∀ k, k < nn → (t1[p1 + k]?.map (·.val)) = (t2[p2 + k]?.map (·.val))

/-- Window gate: the next `nn` tokens at `p1` in `t1` are flow-clean. -/
def WClean (t1 : Array (Positioned YamlToken)) (p1 nn : Nat) : Prop :=
  ∀ k, k < nn → ∀ pt, t1[p1 + k]? = some pt → FlowCleanTok pt.val = true

lemma WAgree.shift {t1 t2 : Array (Positioned YamlToken)} {p1 p2 nn : Nat}
    (h : WAgree t1 t2 p1 p2 nn) (w : Nat) :
    WAgree t1 t2 (p1 + w) (p2 + w) (nn - w) := by
  intro k hk
  rw [Nat.add_assoc, Nat.add_assoc]
  exact h (w + k) (by omega)

lemma WClean.shift {t1 : Array (Positioned YamlToken)} {p1 nn : Nat}
    (h : WClean t1 p1 nn) (w : Nat) :
    WClean t1 (p1 + w) (nn - w) := by
  intro k hk pt hpt
  rw [Nat.add_assoc] at hpt
  exact h (w + k) (by omega) pt hpt

/-- A window can be weakened to a shorter one. -/
lemma WAgree.mono {t1 t2 : Array (Positioned YamlToken)} {p1 p2 nn : Nat}
    (h : WAgree t1 t2 p1 p2 nn) {nn' : Nat} (hle : nn' ≤ nn) :
    WAgree t1 t2 p1 p2 nn' :=
  fun k hk => h k (by omega)

lemma WClean.mono {t1 : Array (Positioned YamlToken)} {p1 nn : Nat}
    (h : WClean t1 p1 nn) {nn' : Nat} (hle : nn' ≤ nn) :
    WClean t1 p1 nn' :=
  fun k hk => h k (by omega)

/-- Agreement transfers `peek?` between two aligned states. -/
lemma WAgree.peek_eq {ps1 ps2 : ParseState} {nn : Nat}
    (h : WAgree ps1.tokens ps2.tokens ps1.pos ps2.pos nn) (hnn : 0 < nn) :
    ps1.peek? = ps2.peek? := by
  rw [peek?_eq_getElem?, peek?_eq_getElem?]
  have h0 := h 0 hnn
  simpa using h0

/-- The gate applies to the head token of the window. -/
lemma WClean.head {ps1 : ParseState} {nn : Nat}
    (h : WClean ps1.tokens ps1.pos nn) (hnn : 0 < nn)
    {tok : YamlToken} (h_pk : ps1.peek? = some tok) :
    FlowCleanTok tok = true := by
  rw [peek?_eq_getElem?] at h_pk
  cases h_get : ps1.tokens[ps1.pos]? with
  | none => rw [h_get] at h_pk; simp at h_pk
  | some pt =>
    rw [h_get] at h_pk
    have h_val : pt.val = tok := by
      simpa using h_pk
    rw [← h_val]
    exact h 0 hnn pt (by simpa using h_get)

/-- Aligned-offset peek transfer: two states sitting at the same offset `d` inside agreeing
    windows have equal `peek?`. -/
lemma WAgree.peek_eq_at {t1 t2 : Array (Positioned YamlToken)} {p1 p2 nn : Nat}
    (h : WAgree t1 t2 p1 p2 nn) {q1 q2 : ParseState} {d : Nat}
    (h_t1 : q1.tokens = t1) (h_t2 : q2.tokens = t2)
    (h_p1 : q1.pos = p1 + d) (h_p2 : q2.pos = p2 + d) (hd : d < nn) :
    q1.peek? = q2.peek? := by
  rw [peek?_eq_getElem?, peek?_eq_getElem?, h_t1, h_t2, h_p1, h_p2]
  exact h d hd

/-! ## §1  Single-run dispatch bricks

Per-head characterizations of one successful `parseNode` run.  The scalar bricks
(`parseNode_scalar_produces_scalar` / `_advances_by_one` / `_tokens_preserved`) are landed in
`ContentFidelity.lean`; here we add the *inert* heads (the `parseNodeContent` catch-all: empty
scalar, zero advance) and the two flow-collection DECOMPOSE lemmas that expose the inner loop
call, the close token, and the exact exit position. -/

/-- `parseNode` on an inert head (`]`, `}`, `,`, `?`-key, `:`-value, or end-of-tokens):
    the content dispatch falls to the catch-all, producing the empty plain scalar with no
    position change. -/
lemma parseNode_inert_head (ps : ParseState) (m : Nat) (v : YamlValue) (q : ParseState)
    (h_head : ps.peek? = none ∨ ps.peek? = some .flowSequenceEnd
      ∨ ps.peek? = some .flowMappingEnd ∨ ps.peek? = some .flowEntry
      ∨ ps.peek? = some .key ∨ ps.peek? = some .value
      ∨ ps.peek? = some .streamStart ∨ ps.peek? = some .streamEnd)
    (h : parseNode ps m = .ok (v, q)) :
    v = .scalar { content := "", style := .plain } ∧ q.pos = ps.pos ∧ q.tokens = ps.tokens := by
  cases m with
  | zero => simp only [parseNode, reduceCtorEq] at h
  | succ n =>
    have h_np : parseNodeProperties ps = .ok ({}, ps) :=
      parseNodeProperties_skip ps
        (by rcases h_head with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> trivial)
    have h_vnp : ∀ p, validateNodeProps ps p ({} : NodeProperties) = .ok () := by
      intro p; unfold validateNodeProps
      rcases h_head with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;>
        simp only [h1, pure, Except.pure] <;> rfl
    have h_pnc : ∀ b, parseNodeContent ps n ({} : NodeProperties) b
        = .ok (YamlValue.scalar { content := "", style := .plain }, ps) := by
      intro b; unfold parseNodeContent
      rcases h_head with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1]
    unfold parseNode at h
    rcases h_head with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;>
    · simp only [h1, bind, Except.bind, h_np, h_vnp, h_pnc] at h
      have h2 := Except.ok.inj h
      have h_v := congrArg Prod.fst h2
      simp only [applyNodeFinalization] at h_v
      have h_q : q = (applyNodeFinalization
          (YamlValue.scalar { content := "", style := .plain }) ps {}
          (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2 :=
        (congrArg Prod.snd h2).symm
      exact ⟨h_v.symm, by rw [h_q, applyNodeFinalization_pos],
        by rw [h_q, applyNodeFinalization_tokens]⟩

/-- `parseNode` on a `[` head decomposes into the inner `parseFlowSequenceLoop` run: the loop
    starts at `ps.advance` with two fuel units consumed, ends at the matching `]` (the
    close-check), and the node returns the flow sequence one past it. -/
lemma parseNode_flowSeqStart_decompose (ps : ParseState) (m : Nat)
    (v : YamlValue) (q : ParseState)
    (h_peek : ps.peek? = some .flowSequenceStart)
    (h : parseNode ps m = .ok (v, q)) :
    ∃ (g : Nat) (items : Array YamlValue) (psl : ParseState),
      m = g + 2 ∧
      parseFlowSequenceLoop ps.advance g #[] = .ok (items, psl) ∧
      psl.peek? = some .flowSequenceEnd ∧
      v = .sequence .flow items none none ∧
      q.pos = psl.pos + 1 ∧ q.tokens = psl.tokens := by
  cases m with
  | zero => simp only [parseNode, reduceCtorEq] at h
  | succ n =>
    have h_np : parseNodeProperties ps = .ok ({}, ps) :=
      parseNodeProperties_skip ps (by rw [h_peek]; trivial)
    have h_vnp : ∀ p, validateNodeProps ps p ({} : NodeProperties) = .ok () := by
      intro p; unfold validateNodeProps
      simp only [h_peek, pure, Except.pure]
      rfl
    have h_pnc : ∀ b, parseNodeContent ps n ({} : NodeProperties) b
        = parseFlowSequence ps n := by
      intro b; unfold parseNodeContent; rw [h_peek]
    unfold parseNode at h
    simp only [h_peek, bind, Except.bind, h_np, h_vnp, h_pnc] at h
    cases n with
    | zero => simp only [parseFlowSequence, reduceCtorEq] at h
    | succ g =>
      simp only [parseFlowSequence, bind, Except.bind] at h
      refine ⟨g, ?_⟩
      cases h_loop : parseFlowSequenceLoop ps.advance g #[] with
      | error e => rw [h_loop] at h; simp only [reduceCtorEq] at h
      | ok r =>
        obtain ⟨items, psl⟩ := r
        rw [h_loop] at h
        simp only [] at h
        cases h_cl : psl.peek? with
        | none => rw [h_cl] at h; simp only [reduceCtorEq] at h
        | some tok =>
          cases tok with
          | flowSequenceEnd =>
            rw [h_cl] at h
            simp only [Except.ok.injEq] at h
            have h2 := h
            have h_v := congrArg Prod.fst h2
            simp only [applyNodeFinalization] at h_v
            have h_q : q = (applyNodeFinalization
                (YamlValue.sequence .flow items) psl.advance {}
                (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2 :=
              (congrArg Prod.snd h2).symm
            refine ⟨items, psl, rfl, rfl, h_cl, h_v.symm, ?_, ?_⟩
            · rw [h_q, applyNodeFinalization_pos]; rfl
            · rw [h_q, applyNodeFinalization_tokens]; rfl
          | _ => rw [h_cl] at h <;> simp only [reduceCtorEq] at h

/-- Mapping mirror of `parseNode_flowSeqStart_decompose`. -/
lemma parseNode_flowMapStart_decompose (ps : ParseState) (m : Nat)
    (v : YamlValue) (q : ParseState)
    (h_peek : ps.peek? = some .flowMappingStart)
    (h : parseNode ps m = .ok (v, q)) :
    ∃ (g : Nat) (pairs : Array (YamlValue × YamlValue)) (psl : ParseState),
      m = g + 2 ∧
      parseFlowMappingLoop ps.advance g #[] = .ok (pairs, psl) ∧
      psl.peek? = some .flowMappingEnd ∧
      v = .mapping .flow pairs none none ∧
      q.pos = psl.pos + 1 ∧ q.tokens = psl.tokens := by
  cases m with
  | zero => simp only [parseNode, reduceCtorEq] at h
  | succ n =>
    have h_np : parseNodeProperties ps = .ok ({}, ps) :=
      parseNodeProperties_skip ps (by rw [h_peek]; trivial)
    have h_vnp : ∀ p, validateNodeProps ps p ({} : NodeProperties) = .ok () := by
      intro p; unfold validateNodeProps
      simp only [h_peek, pure, Except.pure]
      rfl
    have h_pnc : ∀ b, parseNodeContent ps n ({} : NodeProperties) b
        = parseFlowMapping ps n := by
      intro b; unfold parseNodeContent; rw [h_peek]
    unfold parseNode at h
    simp only [h_peek, bind, Except.bind, h_np, h_vnp, h_pnc] at h
    cases n with
    | zero => simp only [parseFlowMapping, reduceCtorEq] at h
    | succ g =>
      simp only [parseFlowMapping, bind, Except.bind] at h
      refine ⟨g, ?_⟩
      cases h_loop : parseFlowMappingLoop ps.advance g #[] with
      | error e => rw [h_loop] at h; simp only [reduceCtorEq] at h
      | ok r =>
        obtain ⟨pairs, psl⟩ := r
        rw [h_loop] at h
        simp only [] at h
        cases h_cl : psl.peek? with
        | none => rw [h_cl] at h; simp only [reduceCtorEq] at h
        | some tok =>
          cases tok with
          | flowMappingEnd =>
            rw [h_cl] at h
            simp only [Except.ok.injEq] at h
            have h2 := h
            have h_v := congrArg Prod.fst h2
            simp only [applyNodeFinalization] at h_v
            have h_q : q = (applyNodeFinalization
                (YamlValue.mapping .flow pairs) psl.advance {}
                (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2 :=
              (congrArg Prod.snd h2).symm
            refine ⟨pairs, psl, rfl, rfl, h_cl, h_v.symm, ?_, ?_⟩
            · rw [h_q, applyNodeFinalization_pos]; rfl
            · rw [h_q, applyNodeFinalization_tokens]; rfl
          | _ => rw [h_cl] at h <;> simp only [reduceCtorEq] at h

/-! ## §2  The joint predicate and the pair-element joint

`ParseNodeJoint n` is the fuel-indexed both-success joint for `parseNode` — the clique's
recursion interface, mirroring `ParseNodePosMono`.  The sibling lemmas below are all
parameterized by it and applied at strictly smaller fuel by the top-level `Nat.rec`
(`parseNode_joint_all`, §4). -/

/-- The both-success two-fuel value/advance joint for `parseNode` at fuel ≤ `n`:
    `.val`-agreeing windows + a flow-clean run-1 window + a one-sided run-1 frame force equal
    values, equal relative advances, and token-array preservation on both sides. -/
def ParseNodeJoint (n : Nat) : Prop :=
  ∀ (m : Nat), m ≤ n → ∀ (f2 : Nat) (ps1 ps2 : ParseState) (nn : Nat)
    (v1 v2 : YamlValue) (q1 q2 : ParseState),
    0 < nn →
    WAgree ps1.tokens ps2.tokens ps1.pos ps2.pos nn →
    WClean ps1.tokens ps1.pos nn →
    parseNode ps1 m = .ok (v1, q1) →
    parseNode ps2 f2 = .ok (v2, q2) →
    q1.pos ≤ ps1.pos + nn →
    v1 = v2 ∧ q1.pos - ps1.pos = q2.pos - ps2.pos
      ∧ q1.tokens = ps1.tokens ∧ q2.tokens = ps2.tokens

/-- The key phase of `parseSinglePairMapping`, factored: empty key on `:`/`,`/`]` heads,
    `parseNode` otherwise. -/
def pairKeyStep (ps : ParseState) (g : Nat) : Except ScanError (YamlValue × ParseState) :=
  match ps.peek? with
  | some .value | some .flowEntry | some .flowSequenceEnd =>
    .ok (emptyNode, ps)
  | _ => parseNode ps g


lemma pairKeyStep_pos_mono (ps : ParseState) (g : Nat) (key : YamlValue) (q : ParseState)
    (h : pairKeyStep ps g = .ok (key, q)) : ps.pos ≤ q.pos := by
  unfold pairKeyStep at h
  split at h <;>
    first
      | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
         exact Nat.le_of_eq (congrArg ParseState.pos h.2))
      | exact parseNodePosMono_apply (parseNode_pos_mono_all g) h (Nat.le_refl _)

/-- `tryConsume` refused: the head is not the requested token and the state is unchanged. -/
lemma tryConsume_false_facts (ps : ParseState) (tok : YamlToken)
    (h : (ps.tryConsume tok).1 = false) :
    ps.peek? ≠ some tok ∧ (ps.tryConsume tok).2 = ps := by
  unfold ParseState.tryConsume at h ⊢
  cases h_pk : ps.peek? with
  | none => exact ⟨by simp, rfl⟩
  | some t =>
    rw [h_pk] at h
    by_cases h_t : t = tok
    · simp [h_t] at h
    · exact ⟨by simp [h_t], by simp [h_t]⟩

/-- `tryConsume` fired: the head was the requested token and the state advanced by one. -/
lemma tryConsume_true_facts (ps : ParseState) (tok : YamlToken)
    (h : (ps.tryConsume tok).1 = true) :
    ps.peek? = some tok ∧ (ps.tryConsume tok).2 = ps.advance := by
  unfold ParseState.tryConsume at h ⊢
  cases h_pk : ps.peek? with
  | none => rw [h_pk] at h; simp at h
  | some t =>
    rw [h_pk] at h
    by_cases h_t : t = tok
    · simp [h_t]
    · simp [h_t] at h

/-- Joint for the factored key phase (dispatch: empty heads coincide across runs by `.val`
    agreement; otherwise both run `parseNode`). -/
lemma pairKeyStep_joint (n : Nat) (h_node : ParseNodeJoint n)
    (g1 : Nat) (hg1 : g1 ≤ n) (g2 : Nat) (ps1 ps2 : ParseState) (nn : Nat)
    (key1 key2 : YamlValue) (q1 q2 : ParseState)
    (hnn : 0 < nn)
    (h_ag : WAgree ps1.tokens ps2.tokens ps1.pos ps2.pos nn)
    (h_cl : WClean ps1.tokens ps1.pos nn)
    (h1 : pairKeyStep ps1 g1 = .ok (key1, q1))
    (h2 : pairKeyStep ps2 g2 = .ok (key2, q2))
    (h_fr : q1.pos ≤ ps1.pos + nn) :
    key1 = key2 ∧ q1.pos - ps1.pos = q2.pos - ps2.pos
      ∧ q1.tokens = ps1.tokens ∧ q2.tokens = ps2.tokens := by
  have h_pk := h_ag.peek_eq hnn
  unfold pairKeyStep at h1 h2
  rw [← h_pk] at h2
  cases h_c : ps1.peek? with
  | none =>
    rw [h_c] at h1 h2
    exact h_node g1 hg1 g2 ps1 ps2 nn key1 key2 q1 q2 hnn h_ag h_cl h1 h2 h_fr
  | some t =>
    rw [h_c] at h1 h2
    cases t
    case value =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h1 h2
      obtain ⟨hk1, hq1⟩ := h1
      obtain ⟨hk2, hq2⟩ := h2
      subst hq1; subst hq2
      exact ⟨hk1.symm.trans hk2, by omega, rfl, rfl⟩
    case flowEntry =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h1 h2
      obtain ⟨hk1, hq1⟩ := h1
      obtain ⟨hk2, hq2⟩ := h2
      subst hq1; subst hq2
      exact ⟨hk1.symm.trans hk2, by omega, rfl, rfl⟩
    case flowSequenceEnd =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h1 h2
      obtain ⟨hk1, hq1⟩ := h1
      obtain ⟨hk2, hq2⟩ := h2
      subst hq1; subst hq2
      exact ⟨hk1.symm.trans hk2, by omega, rfl, rfl⟩
    all_goals
      exact h_node g1 hg1 g2 ps1 ps2 nn key1 key2 q1 q2 hnn h_ag h_cl h1 h2 h_fr

/-- Inversion of `parseSinglePairMapping` success into aligned atomized components: the key
    phase (factored as `pairKeyStep`), the `:`-consumption width `w`, and the value phase
    (`parseNode` exposed directly, with the head classification that decided the arm). -/
lemma parseSinglePairMapping_inv (ps : ParseState) (g : Nat) (v : YamlValue) (q : ParseState)
    (h : parseSinglePairMapping ps (g + 1) = .ok (v, q)) :
    ∃ (key : YamlValue) (psk : ParseState) (w : Nat) (psv0 : ParseState)
      (val : YamlValue) (pv : ParseState),
      pairKeyStep ps.advance g = .ok (key, psk) ∧
      ((psk.peek? = some .value ∧ w = 1) ∨ (psk.peek? ≠ some .value ∧ w = 0)) ∧
      ((w = 0 ∧ val = emptyNode ∧ pv = psv0)
        ∨ (w = 1 ∧ (psv0.peek? = some .flowEntry ∨ psv0.peek? = some .flowSequenceEnd
              ∨ psv0.peek? = none) ∧ val = emptyNode ∧ pv = psv0)
        ∨ (w = 1 ∧ psv0.peek? ≠ some .flowEntry ∧ psv0.peek? ≠ some .flowSequenceEnd
              ∧ psv0.peek? ≠ none ∧ parseNode psv0 g = .ok (val, pv))) ∧
      psv0.pos = psk.pos + w ∧ psv0.tokens = psk.tokens ∧
      v = .mapping .flow #[(key, val)] ∧
      q.pos = pv.pos ∧ q.tokens = pv.tokens := by
  unfold parseSinglePairMapping at h
  simp only [bind, Except.bind] at h
  split at h
  case h_4 x hn1 hn2 hn3 =>
    have hk_eq : pairKeyStep ps.advance g = parseNode ps.advance g := by
      unfold pairKeyStep
      cases h_c : ps.advance.peek? with
      | none => rfl
      | some t =>
        cases t <;> first
          | rfl
          | exact absurd h_c (fun hx => hn1 hx)
          | exact absurd h_c (fun hx => hn2 hx)
          | exact absurd h_c (fun hx => hn3 hx)
    split at h
    case h_1 e heq5 => simp only [reduceCtorEq] at h
    case h_2 kr heq5 =>
      obtain ⟨key0, psk0⟩ := kr
      have hk : pairKeyStep ps.advance g = .ok (key0, psk0) := by rw [hk_eq]; exact heq5
      simp only [] at h
      cases key0 <;> simp only [] at h <;>
      (split at h
       · rename_i hc
         obtain ⟨h_pkv, h_st⟩ := tryConsume_true_facts _ YamlToken.value hc
         rw [h_st] at h
         split at h
         · rename_i heq3
           simp only [Except.ok.injEq, Prod.mk.injEq] at h
           exact ⟨_, _, 1, _, emptyNode, _, hk, Or.inl ⟨h_pkv, rfl⟩,
             Or.inr (Or.inl ⟨rfl, Or.inl heq3, rfl, rfl⟩), rfl, rfl, h.1.symm,
             by rw [← h.2], by rw [← h.2]⟩
         · rename_i heq3
           simp only [Except.ok.injEq, Prod.mk.injEq] at h
           exact ⟨_, _, 1, _, emptyNode, _, hk, Or.inl ⟨h_pkv, rfl⟩,
             Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl heq3), rfl, rfl⟩), rfl, rfl, h.1.symm,
             by rw [← h.2], by rw [← h.2]⟩
         · rename_i heq3
           simp only [Except.ok.injEq, Prod.mk.injEq] at h
           exact ⟨_, _, 1, _, emptyNode, _, hk, Or.inl ⟨h_pkv, rfl⟩,
             Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr heq3), rfl, rfl⟩), rfl, rfl, h.1.symm,
             by rw [← h.2], by rw [← h.2]⟩
         · rename_i hv1 hv2 hv3
           split at h
           · simp only [reduceCtorEq] at h
           · rename_i vr heq6
             simp only [Except.ok.injEq, Prod.mk.injEq] at h
             exact ⟨_, _, 1, _, vr.1, vr.2, hk, Or.inl ⟨h_pkv, rfl⟩,
               Or.inr (Or.inr ⟨rfl, fun hx => hv1 hx, fun hx => hv2 hx, fun hx => hv3 hx,
                 heq6⟩), rfl, rfl, h.1.symm, by rw [← h.2], by rw [← h.2]⟩
       · rename_i hc
         rw [Bool.not_eq_true] at hc
         obtain ⟨h_nv, h_st⟩ := tryConsume_false_facts _ YamlToken.value hc
         rw [h_st] at h
         simp only [Except.ok.injEq, Prod.mk.injEq] at h
         exact ⟨_, _, 0, psk0, emptyNode, psk0, hk, Or.inr ⟨h_nv, rfl⟩,
           Or.inl ⟨rfl, rfl, rfl⟩, rfl, rfl, h.1.symm, by rw [← h.2], by rw [← h.2]⟩)
  all_goals (
    rename_i x heq
    have hk : pairKeyStep ps.advance g = .ok (emptyNode, ps.advance) := by
      unfold pairKeyStep; rw [heq]
    simp only [emptyNode] at h
    split at h
    · rename_i hc
      obtain ⟨h_pkv, h_st⟩ := tryConsume_true_facts _ YamlToken.value hc
      rw [h_st] at h
      split at h
      · rename_i heq3
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨_, _, 1, _, emptyNode, _, hk, Or.inl ⟨h_pkv, rfl⟩,
          Or.inr (Or.inl ⟨rfl, Or.inl heq3, rfl, rfl⟩), rfl, rfl, h.1.symm,
          by rw [← h.2], by rw [← h.2]⟩
      · rename_i heq3
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨_, _, 1, _, emptyNode, _, hk, Or.inl ⟨h_pkv, rfl⟩,
          Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl heq3), rfl, rfl⟩), rfl, rfl, h.1.symm,
          by rw [← h.2], by rw [← h.2]⟩
      · rename_i heq3
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨_, _, 1, _, emptyNode, _, hk, Or.inl ⟨h_pkv, rfl⟩,
          Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr heq3), rfl, rfl⟩), rfl, rfl, h.1.symm,
          by rw [← h.2], by rw [← h.2]⟩
      · rename_i hv1 hv2 hv3
        split at h
        · simp only [reduceCtorEq] at h
        · rename_i vr heq6
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          exact ⟨_, _, 1, _, vr.1, vr.2, hk, Or.inl ⟨h_pkv, rfl⟩,
            Or.inr (Or.inr ⟨rfl, fun hx => hv1 hx, fun hx => hv2 hx, fun hx => hv3 hx,
              heq6⟩), rfl, rfl, h.1.symm, by rw [← h.2], by rw [← h.2]⟩
    · rename_i hc
      rw [Bool.not_eq_true] at hc
      obtain ⟨h_nv, h_st⟩ := tryConsume_false_facts _ YamlToken.value hc
      rw [h_st] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨_, _, 0, ps.advance, emptyNode, ps.advance, hk, Or.inr ⟨h_nv, rfl⟩,
        Or.inl ⟨rfl, rfl, rfl⟩, rfl, rfl, h.1.symm, by rw [← h.2], by rw [← h.2]⟩)

set_option maxHeartbeats 1600000 in
/-- The two-fuel both-success joint for `parseSinglePairMapping` (the `[key: value]` sugar
    element of flow sequences): equal values, equal relative advances, tokens preserved. -/
lemma parseSinglePairMapping_joint (n : Nat) (h_node : ParseNodeJoint n)
    (f1 : Nat) (hf1 : f1 ≤ n + 1) (f2 : Nat) (ps1 ps2 : ParseState) (nn : Nat)
    (v1 v2 : YamlValue) (q1 q2 : ParseState)
    (h_ag : WAgree ps1.tokens ps2.tokens ps1.pos ps2.pos nn)
    (h_cl : WClean ps1.tokens ps1.pos nn)
    (h1 : parseSinglePairMapping ps1 f1 = .ok (v1, q1))
    (h2 : parseSinglePairMapping ps2 f2 = .ok (v2, q2))
    (h_fr : q1.pos < ps1.pos + nn) :
    v1 = v2 ∧ q1.pos - ps1.pos = q2.pos - ps2.pos
      ∧ q1.tokens = ps1.tokens ∧ q2.tokens = ps2.tokens := by
  cases f1 with
  | zero => simp only [parseSinglePairMapping, reduceCtorEq] at h1
  | succ g1 =>
  cases f2 with
  | zero => simp only [parseSinglePairMapping, reduceCtorEq] at h2
  | succ g2 =>
  obtain ⟨key1, psk1, w1, psv01, val1, pv1, hk1, hw1, hval1, hpos1, htok1, hv1, hq1p, hq1t⟩ :=
    parseSinglePairMapping_inv ps1 g1 v1 q1 h1
  obtain ⟨key2, psk2, w2, psv02, val2, pv2, hk2, hw2, hval2, hpos2, htok2, hv2, hq2p, hq2t⟩ :=
    parseSinglePairMapping_inv ps2 g2 v2 q2 h2
  have h_psk1_lo : ps1.pos + 1 ≤ psk1.pos := by
    have h := pairKeyStep_pos_mono ps1.advance g1 key1 psk1 hk1
    simpa [ParseState.advance] using h
  have h_psk2_lo : ps2.pos + 1 ≤ psk2.pos := by
    have h := pairKeyStep_pos_mono ps2.advance g2 key2 psk2 hk2
    simpa [ParseState.advance] using h
  have h_pv1_lo : psv01.pos ≤ pv1.pos := by
    rcases hval1 with ⟨_, _, h_e⟩ | ⟨_, _, _, h_e⟩ | ⟨_, _, _, _, hpn⟩
    · exact Nat.le_of_eq (congrArg ParseState.pos h_e).symm
    · exact Nat.le_of_eq (congrArg ParseState.pos h_e).symm
    · exact parseNodePosMono_apply (parseNode_pos_mono_all g1) hpn (Nat.le_refl _)
  have h_pv2_lo : psv02.pos ≤ pv2.pos := by
    rcases hval2 with ⟨_, _, h_e⟩ | ⟨_, _, _, h_e⟩ | ⟨_, _, _, _, hpn⟩
    · exact Nat.le_of_eq (congrArg ParseState.pos h_e).symm
    · exact Nat.le_of_eq (congrArg ParseState.pos h_e).symm
    · exact parseNodePosMono_apply (parseNode_pos_mono_all g2) hpn (Nat.le_refl _)
  have h_nn1 : 1 < nn := by omega
  have h_ag1 : WAgree ps1.advance.tokens ps2.advance.tokens ps1.advance.pos ps2.advance.pos
      (nn - 1) := by
    simpa [ParseState.advance] using h_ag.shift 1
  have h_cl1 : WClean ps1.advance.tokens ps1.advance.pos (nn - 1) := by
    simpa [ParseState.advance] using h_cl.shift 1
  obtain ⟨h_key_eq, h_kadv, h_kt1, h_kt2⟩ :=
    pairKeyStep_joint n h_node g1 (by omega) g2 ps1.advance ps2.advance (nn - 1)
      key1 key2 psk1 psk2 (by omega) h_ag1 h_cl1 hk1 hk2
      (by simp only [ParseState.advance]; omega)
  simp only [ParseState.advance] at h_kadv h_kt1 h_kt2
  have h_psk2_pos : psk2.pos = ps2.pos + (psk1.pos - ps1.pos) := by omega
  have h_pkk : psk1.peek? = psk2.peek? :=
    h_ag.peek_eq_at (d := psk1.pos - ps1.pos) h_kt1 h_kt2 (by omega) h_psk2_pos (by omega)
  rcases hw1 with ⟨h_pv, rfl⟩ | ⟨h_npv, rfl⟩
  · -- `: ` consumed on run 1 ⇒ on run 2 too
    rcases hw2 with ⟨h_pv2, rfl⟩ | ⟨h_npv2, h_w2⟩
    case inr => exact absurd (h_pkk ▸ h_pv) h_npv2
    have h_t1c : psv01.tokens = ps1.tokens := by rw [htok1, h_kt1]
    have h_t2c : psv02.tokens = ps2.tokens := by rw [htok2, h_kt2]
    have h_pvv : psv01.peek? = psv02.peek? :=
      h_ag.peek_eq_at (d := psk1.pos - ps1.pos + 1) h_t1c h_t2c (by omega) (by omega) (by omega)
    rcases hval1 with ⟨h10, _, _⟩ | ⟨_, h_mem1, h_ve1, h_pe1⟩ | ⟨_, hne1a, hne1b, hne1c, hpn1⟩
    · simp at h10
    · rcases hval2 with ⟨h20, _, _⟩ | ⟨_, _, h_ve2, h_pe2⟩ | ⟨_, hne2a, hne2b, hne2c, _⟩
      · simp at h20
      · refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hv1, hv2, h_key_eq, h_ve1, h_ve2]
        · rw [hq1p, hq2p, h_pe1, h_pe2]; omega
        · rw [hq1t, h_pe1, h_t1c]
        · rw [hq2t, h_pe2, h_t2c]
      · rcases h_mem1 with hm | hm | hm
        · exact absurd (h_pvv.symm.trans hm) hne2a
        · exact absurd (h_pvv.symm.trans hm) hne2b
        · exact absurd (h_pvv.symm.trans hm) hne2c
    · rcases hval2 with ⟨h20, _, _⟩ | ⟨_, h_mem2, _, _⟩ | ⟨_, _, _, _, hpn2⟩
      · simp at h20
      · rcases h_mem2 with hm | hm | hm
        · exact absurd (h_pvv.trans hm) hne1a
        · exact absurd (h_pvv.trans hm) hne1b
        · exact absurd (h_pvv.trans hm) hne1c
      · have h_ag_v : WAgree psv01.tokens psv02.tokens psv01.pos psv02.pos
            (nn - (psk1.pos - ps1.pos + 1)) := by
          rw [h_t1c, h_t2c, show psv01.pos = ps1.pos + (psk1.pos - ps1.pos + 1) by omega,
            show psv02.pos = ps2.pos + (psk1.pos - ps1.pos + 1) by omega]
          exact h_ag.shift _
        have h_cl_v : WClean psv01.tokens psv01.pos (nn - (psk1.pos - ps1.pos + 1)) := by
          rw [h_t1c, show psv01.pos = ps1.pos + (psk1.pos - ps1.pos + 1) by omega]
          exact h_cl.shift _
        obtain ⟨h_val_eq, h_vadv, h_vt1, h_vt2⟩ :=
          h_node g1 (by omega) g2 psv01 psv02 (nn - (psk1.pos - ps1.pos + 1))
            val1 val2 pv1 pv2 (by omega) h_ag_v h_cl_v hpn1 hpn2 (by omega)
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hv1, hv2, h_key_eq, h_val_eq]
        · rw [hq1p, hq2p]; omega
        · rw [hq1t, h_vt1, h_t1c]
        · rw [hq2t, h_vt2, h_t2c]
  · -- `: ` not consumed on run 1 ⇒ not on run 2 either
    rcases hw2 with ⟨h_pv2, _⟩ | ⟨h_npv2, rfl⟩
    · exact absurd (h_pkk.trans h_pv2) h_npv
    rcases hval1 with ⟨_, h_ve1, h_pe1⟩ | ⟨h10, _, _, _⟩ | ⟨h10, _, _, _, _⟩
    · rcases hval2 with ⟨_, h_ve2, h_pe2⟩ | ⟨h20, _, _, _⟩ | ⟨h20, _, _, _, _⟩
      · refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hv1, hv2, h_key_eq, h_ve1, h_ve2]
        · rw [hq1p, hq2p, h_pe1, h_pe2]; omega
        · rw [hq1t, h_pe1, htok1, h_kt1]
        · rw [hq2t, h_pe2, htok2, h_kt2]
      · simp at h20
      · simp at h20
    · simp at h10
    · simp at h10

/-! ## §3  The flow-sequence loop joint

Two-fuel loop joints are refutable at fuel 0 (the fuel-exhaustion exit returns `.ok` early), so
both runs carry PROPER-EXIT hypotheses (`r.2.peek? = some .flowSequenceEnd`) — supplied at every
invocation by the enclosing `parseFlowSequence` close-check. -/

/-- A loop sitting on its close token returns immediately at ANY fuel. -/
lemma parseFlowSeqLoop_close_now (ps : ParseState) (f : Nat) (items : Array YamlValue)
    (r : Array YamlValue × ParseState)
    (h_pk : ps.peek? = some .flowSequenceEnd)
    (h : parseFlowSequenceLoop ps f items = .ok r) : r = (items, ps) := by
  cases f with
  | zero =>
    unfold parseFlowSequenceLoop at h
    exact (Except.ok.inj h).symm
  | succ k =>
    unfold parseFlowSequenceLoop at h
    rw [h_pk] at h
    simp only [] at h
    exact (Except.ok.inj h).symm

/-- One-step inversion of a successful `parseFlowSequenceLoop` at positive fuel: close now,
    early return, or (separator·element·continuation) with all states exposed through
    pos/tokens equations (the `currentPath` bookkeeping stays abstract). -/
lemma parseFlowSequenceLoop_step_inv (ps : ParseState) (k : Nat) (items : Array YamlValue)
    (r : Array YamlValue × ParseState)
    (h : parseFlowSequenceLoop ps (k + 1) items = .ok r) :
    (ps.peek? = some .flowSequenceEnd ∧ r = (items, ps))
    ∨ (0 < items.size ∧ ps.peek? ≠ some .flowSequenceEnd ∧ ps.peek? ≠ some .flowEntry
        ∧ r = (items, ps))
    ∨ (∃ (w0 : Nat) (ps' : ParseState),
        ps'.pos = ps.pos + w0 ∧ ps'.tokens = ps.tokens ∧
        ps.peek? ≠ some .flowSequenceEnd ∧
        ((0 < items.size ∧ ps.peek? = some .flowEntry ∧ w0 = 1)
          ∨ (items.size = 0 ∧ w0 = 0)) ∧
        ((ps'.peek? = some .flowSequenceEnd ∧ r = (items, ps'))
          ∨ (ps'.peek? = some .key ∧
              ∃ (psE : ParseState) (val : YamlValue) (psn psC : ParseState),
                parseSinglePairMapping psE k = .ok (val, psn) ∧
                psE.pos = ps'.pos ∧ psE.tokens = ps'.tokens ∧
                parseFlowSequenceLoop psC k (items.push val) = .ok r ∧
                psC.pos = psn.pos ∧ psC.tokens = psn.tokens)
          ∨ (ps'.peek? ≠ some .flowSequenceEnd ∧ ps'.peek? ≠ some .key ∧
              ∃ (psE : ParseState) (val : YamlValue) (psn psC : ParseState),
                parseNode psE k = .ok (val, psn) ∧
                psE.pos = ps'.pos ∧ psE.tokens = ps'.tokens ∧
                parseFlowSequenceLoop psC k (items.push val) = .ok r ∧
                psC.pos = psn.pos ∧ psC.tokens = psn.tokens))) := by
  unfold parseFlowSequenceLoop at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  case h_1 x heq => exact Or.inl ⟨heq, (Except.ok.inj h).symm⟩
  case h_2 x hne =>
    split at h
    · -- items.size > 0
      rename_i hsz
      split at h
      · -- separator present: continue at ps.advance
        rename_i heq_fe
        split at h
        · -- element head `.key`: single-pair mapping
          rename_i heq_k
          split at h
          · simp only [reduceCtorEq] at h
          · rename_i vr heq_el
            exact Or.inr (Or.inr ⟨1, ps.advance, rfl, rfl, fun hx => hne hx,
              Or.inl ⟨hsz, heq_fe, rfl⟩,
              Or.inr (Or.inl ⟨heq_k, _, _, _, _, heq_el, rfl, rfl, h, rfl, rfl⟩)⟩)
        · -- trailing close right after the separator
          rename_i heq_cl
          exact Or.inr (Or.inr ⟨1, ps.advance, rfl, rfl, fun hx => hne hx,
            Or.inl ⟨hsz, heq_fe, rfl⟩, Or.inl ⟨heq_cl, (Except.ok.inj h).symm⟩⟩)
        · -- element head: node
          rename_i hk1 hk2
          split at h
          · simp only [reduceCtorEq] at h
          · rename_i vr heq_el
            exact Or.inr (Or.inr ⟨1, ps.advance, rfl, rfl, fun hx => hne hx,
              Or.inl ⟨hsz, heq_fe, rfl⟩,
              Or.inr (Or.inr ⟨fun hx => hk2 hx, fun hx => hk1 hx,
                _, _, _, _, heq_el, rfl, rfl, h, rfl, rfl⟩)⟩)
      · -- early return (nonempty, head neither close nor separator)
        rename_i hne_fe
        exact Or.inr (Or.inl ⟨hsz, fun hx => hne hx, fun hx => hne_fe hx,
          (Except.ok.inj h).symm⟩)
    · -- items.size = 0: no separator step
      rename_i hsz
      split at h
      · rename_i heq_k
        split at h
        · simp only [reduceCtorEq] at h
        · rename_i vr heq_el
          exact Or.inr (Or.inr ⟨0, ps, rfl, rfl, fun hx => hne hx,
            Or.inr ⟨by omega, rfl⟩,
            Or.inr (Or.inl ⟨heq_k, _, _, _, _, heq_el, rfl, rfl, h, rfl, rfl⟩)⟩)
      · rename_i heq_cl
        exact absurd heq_cl (fun hx => hne hx)
      · rename_i hk1 hk2
        split at h
        · simp only [reduceCtorEq] at h
        · rename_i vr heq_el
          exact Or.inr (Or.inr ⟨0, ps, rfl, rfl, fun hx => hne hx,
            Or.inr ⟨by omega, rfl⟩,
            Or.inr (Or.inr ⟨fun hx => hk2 hx, fun hx => hk1 hx,
              _, _, _, _, heq_el, rfl, rfl, h, rfl, rfl⟩)⟩)

set_option maxHeartbeats 3200000 in
/-- The two-fuel both-success joint for `parseFlowSequenceLoop`: same accumulator, agreeing
    gated windows, a strict run-1 frame, and proper (close-token) exits on both runs force
    equal result arrays, equal relative advances, and token preservation. -/
lemma parseFlowSequenceLoop_joint (n : Nat) (h_node : ParseNodeJoint n) :
    ∀ (f1 : Nat), f1 ≤ n + 1 → ∀ (f2 : Nat) (ps1 ps2 : ParseState) (nn : Nat)
      (items : Array YamlValue) (r1 r2 : Array YamlValue × ParseState),
      WAgree ps1.tokens ps2.tokens ps1.pos ps2.pos nn →
      WClean ps1.tokens ps1.pos nn →
      parseFlowSequenceLoop ps1 f1 items = .ok r1 →
      parseFlowSequenceLoop ps2 f2 items = .ok r2 →
      r1.2.pos < ps1.pos + nn →
      r1.2.peek? = some .flowSequenceEnd →
      r2.2.peek? = some .flowSequenceEnd →
      r1.1 = r2.1 ∧ r1.2.pos - ps1.pos = r2.2.pos - ps2.pos
        ∧ r1.2.tokens = ps1.tokens ∧ r2.2.tokens = ps2.tokens := by
  intro f1
  induction f1 with
  | zero =>
    intro _ f2 ps1 ps2 nn items r1 r2 h_ag h_cl h1 h2 h_fr hx1 hx2
    unfold parseFlowSequenceLoop at h1
    have h_r1 : r1 = (items, ps1) := (Except.ok.inj h1).symm
    have h_rs1 : r1.2 = ps1 := by rw [h_r1]
    have h_ra1 : r1.1 = items := by rw [h_r1]
    rw [h_rs1] at hx1 h_fr
    have h_nn : 0 < nn := by omega
    have h_c2 : ps2.peek? = some .flowSequenceEnd := (h_ag.peek_eq h_nn) ▸ hx1
    have h_r2 := parseFlowSeqLoop_close_now ps2 f2 items r2 h_c2 h2
    have h_rs2 : r2.2 = ps2 := by rw [h_r2]
    have h_ra2 : r2.1 = items := by rw [h_r2]
    exact ⟨by rw [h_ra1, h_ra2], by rw [h_rs1, h_rs2]; omega, by rw [h_rs1], by rw [h_rs2]⟩
  | succ k ih =>
    intro hf1 f2 ps1 ps2 nn items r1 r2 h_ag h_cl h1 h2 h_fr hx1 hx2
    have h_mono1 : ps1.pos ≤ r1.2.pos :=
      parseFlowSequenceLoop_pos_mono (k + 1) (parseNode_pos_mono_all (k + 1)) ps1 items r1 h1
    have h_nn : 0 < nn := by omega
    have h_pk12 : ps1.peek? = ps2.peek? := h_ag.peek_eq h_nn
    rcases parseFlowSequenceLoop_step_inv ps1 k items r1 h1 with
      ⟨h_c1, h_r1⟩ | ⟨h_sz1, h_ne1, h_nf1, h_r1⟩
      | ⟨w0, ps1', h_p1', h_t1', h_ne1, h_sep1, h_disp1⟩
    · -- run 1 closes now ⇒ run 2 closes now
      have h_c2 : ps2.peek? = some .flowSequenceEnd := h_pk12 ▸ h_c1
      have h_r2 := parseFlowSeqLoop_close_now ps2 f2 items r2 h_c2 h2
      have h_rs1 : r1.2 = ps1 := by rw [h_r1]
      have h_ra1 : r1.1 = items := by rw [h_r1]
      have h_rs2 : r2.2 = ps2 := by rw [h_r2]
      have h_ra2 : r2.1 = items := by rw [h_r2]
      exact ⟨by rw [h_ra1, h_ra2], by rw [h_rs1, h_rs2]; omega, by rw [h_rs1], by rw [h_rs2]⟩
    · -- run 1 early-returns: contradicts its proper exit
      rw [h_r1] at hx1
      exact absurd hx1 h_ne1
    · -- run 1 steps; run 2 must step too
      cases f2 with
      | zero =>
        unfold parseFlowSequenceLoop at h2
        have h_r2 : r2 = (items, ps2) := (Except.ok.inj h2).symm
        rw [h_r2] at hx2
        exact absurd (h_pk12.trans hx2) h_ne1
      | succ k2 =>
      rcases parseFlowSequenceLoop_step_inv ps2 k2 items r2 h2 with
        ⟨h_c2, h_r2⟩ | ⟨h_sz2, h_ne2, h_nf2, h_r2⟩
        | ⟨w0₂, ps2', h_p2', h_t2', h_ne2, h_sep2, h_disp2⟩
      · exact absurd (h_pk12.trans h_c2) h_ne1
      · rw [h_r2] at hx2
        exact absurd hx2 h_ne2
      · -- both step: align the separator width
        have h_w0 : w0₂ = w0 := by
          rcases h_sep1 with ⟨hs1, hf1', rfl⟩ | ⟨hs1, rfl⟩ <;>
            rcases h_sep2 with ⟨hs2, hf2', rfl⟩ | ⟨hs2, rfl⟩ <;> omega
        rw [h_w0] at h_p2' h_sep2
        -- run-1 bound: the step's element stays within the frame
        have h_bound1 : ps1'.pos ≤ r1.2.pos := by
          rcases h_disp1 with ⟨_, h_r⟩
            | ⟨_, psE, val, psn, psC, h_el, hpe, _, h_cont, hpc, _⟩
            | ⟨_, _, psE, val, psn, psC, h_el, hpe, _, h_cont, hpc, _⟩
          · rw [h_r]; exact Nat.le_refl _
          · have h1e := parseSinglePairMapping_pos_mono k (parseNode_pos_mono_all k)
              psE (val, psn) h_el
            have h2e := parseFlowSequenceLoop_pos_mono k (parseNode_pos_mono_all k)
              psC (items.push val) r1 h_cont
            simp only [] at h1e
            omega
          · have h1e := parseNodePosMono_apply (parseNode_pos_mono_all k) h_el (Nat.le_refl _)
            have h2e := parseFlowSequenceLoop_pos_mono k (parseNode_pos_mono_all k)
              psC (items.push val) r1 h_cont
            simp only [] at h1e
            omega
        have h_w0nn : w0 < nn := by omega
        have h_pk12' : ps1'.peek? = ps2'.peek? :=
          h_ag.peek_eq_at (d := w0) h_t1' h_t2' h_p1' h_p2' h_w0nn
        rcases h_disp1 with ⟨h_cl1', h_r1⟩
          | ⟨h_k1, psE1, val1, psn1, psC1, h_el1, hpe1, hte1, h_cont1, hpc1, htc1⟩
          | ⟨h_ncl1, h_nk1, psE1, val1, psn1, psC1, h_el1, hpe1, hte1, h_cont1, hpc1, htc1⟩
        · -- trailing close on run 1 ⇒ same on run 2
          rcases h_disp2 with ⟨h_cl2', h_r2⟩
            | ⟨h_k2, _, _, _, _, _, _, _, _, _, _⟩
            | ⟨h_ncl2, _, _, _, _, _, _, _, _, _, _⟩
          · have h_rs1 : r1.2 = ps1' := by rw [h_r1]
            have h_ra1 : r1.1 = items := by rw [h_r1]
            have h_rs2 : r2.2 = ps2' := by rw [h_r2]
            have h_ra2 : r2.1 = items := by rw [h_r2]
            refine ⟨by rw [h_ra1, h_ra2], by rw [h_rs1, h_rs2]; omega,
              by rw [h_rs1]; exact h_t1', by rw [h_rs2]; exact h_t2'⟩
          · exact absurd (h_pk12'.symm.trans h_cl1') (by rw [h_k2]; simp)
          · exact absurd (h_pk12'.symm.trans h_cl1') h_ncl2
        · -- `.key` element on run 1 ⇒ same on run 2
          rcases h_disp2 with ⟨h_cl2', h_r2⟩
            | ⟨h_k2, psE2, val2, psn2, psC2, h_el2, hpe2, hte2, h_cont2, hpc2, htc2⟩
            | ⟨h_ncl2, h_nk2, _, _, _, _, _, _, _, _, _⟩
          · exact absurd (h_pk12'.trans h_cl2') (by rw [h_k1]; simp)
          · -- joint on the single-pair elements
            have h_psn1_lo : psE1.pos ≤ psn1.pos := by
              have := parseSinglePairMapping_pos_mono k (parseNode_pos_mono_all k)
                psE1 (val1, psn1) h_el1
              simpa using this
            have h_rc1_lo : psC1.pos ≤ r1.2.pos :=
              parseFlowSequenceLoop_pos_mono k (parseNode_pos_mono_all k)
                psC1 (items.push val1) r1 h_cont1
            have h_psn2_lo : psE2.pos ≤ psn2.pos := by
              have h := parseSinglePairMapping_pos_mono k2 (parseNode_pos_mono_all k2)
                psE2 (val2, psn2) h_el2
              simpa using h
            have h_ag_e : WAgree psE1.tokens psE2.tokens psE1.pos psE2.pos (nn - w0) := by
              rw [hte1, hte2, h_t1', h_t2',
                show psE1.pos = ps1.pos + w0 by omega,
                show psE2.pos = ps2.pos + w0 by omega]
              exact h_ag.shift w0
            have h_cl_e : WClean psE1.tokens psE1.pos (nn - w0) := by
              rw [hte1, h_t1', show psE1.pos = ps1.pos + w0 by omega]
              exact h_cl.shift w0
            obtain ⟨h_val_eq, h_eadv, h_et1, h_et2⟩ :=
              parseSinglePairMapping_joint n h_node k (by omega) k2 psE1 psE2 (nn - w0)
                val1 val2 psn1 psn2 h_ag_e h_cl_e h_el1 h_el2 (by omega)
            -- re-arm the IH on the continuations
            have h_ag_c : WAgree psC1.tokens psC2.tokens psC1.pos psC2.pos
                (nn - (w0 + (psn1.pos - psE1.pos))) := by
              rw [htc1, htc2, h_et1, h_et2, hte1, hte2, h_t1', h_t2',
                show psC1.pos = ps1.pos + (w0 + (psn1.pos - psE1.pos)) by omega,
                show psC2.pos = ps2.pos + (w0 + (psn1.pos - psE1.pos)) by omega]
              exact h_ag.shift _
            have h_cl_c : WClean psC1.tokens psC1.pos
                (nn - (w0 + (psn1.pos - psE1.pos))) := by
              rw [htc1, h_et1, hte1, h_t1',
                show psC1.pos = ps1.pos + (w0 + (psn1.pos - psE1.pos)) by omega]
              exact h_cl.shift _
            have h_rc2_lo : psC2.pos ≤ r2.2.pos :=
              parseFlowSequenceLoop_pos_mono k2 (parseNode_pos_mono_all k2)
                psC2 (items.push val2) r2 h_cont2
            rw [h_val_eq] at h_cont1
            obtain ⟨h_arr, h_adv, h_ct1, h_ct2⟩ :=
              ih (by omega) k2 psC1 psC2 (nn - (w0 + (psn1.pos - psE1.pos)))
                (items.push val2) r1 r2 h_ag_c h_cl_c h_cont1 h_cont2
                (by omega) hx1 hx2
            refine ⟨h_arr, by omega, ?_, ?_⟩
            · rw [h_ct1, htc1, h_et1, hte1, h_t1']
            · rw [h_ct2, htc2, h_et2, hte2, h_t2']
          · exact absurd (h_pk12'.symm.trans h_k1) h_nk2
        · -- node element on run 1 ⇒ same on run 2
          rcases h_disp2 with ⟨h_cl2', h_r2⟩
            | ⟨h_k2, _, _, _, _, _, _, _, _, _, _⟩
            | ⟨h_ncl2, h_nk2, psE2, val2, psn2, psC2, h_el2, hpe2, hte2, h_cont2, hpc2, htc2⟩
          · exact absurd (h_pk12'.trans h_cl2') h_ncl1
          · exact absurd (h_pk12'.trans h_k2) h_nk1
          · have h_psn1_lo : psE1.pos ≤ psn1.pos :=
              parseNodePosMono_apply (parseNode_pos_mono_all k) h_el1 (Nat.le_refl _)
            have h_rc1_lo : psC1.pos ≤ r1.2.pos :=
              parseFlowSequenceLoop_pos_mono k (parseNode_pos_mono_all k)
                psC1 (items.push val1) r1 h_cont1
            have h_psn2_lo : psE2.pos ≤ psn2.pos :=
              parseNodePosMono_apply (parseNode_pos_mono_all k2) h_el2 (Nat.le_refl _)
            have h_ag_e : WAgree psE1.tokens psE2.tokens psE1.pos psE2.pos (nn - w0) := by
              rw [hte1, hte2, h_t1', h_t2',
                show psE1.pos = ps1.pos + w0 by omega,
                show psE2.pos = ps2.pos + w0 by omega]
              exact h_ag.shift w0
            have h_cl_e : WClean psE1.tokens psE1.pos (nn - w0) := by
              rw [hte1, h_t1', show psE1.pos = ps1.pos + w0 by omega]
              exact h_cl.shift w0
            obtain ⟨h_val_eq, h_eadv, h_et1, h_et2⟩ :=
              h_node k (by omega) k2 psE1 psE2 (nn - w0) val1 val2 psn1 psn2
                (by omega) h_ag_e h_cl_e h_el1 h_el2 (by omega)
            have h_ag_c : WAgree psC1.tokens psC2.tokens psC1.pos psC2.pos
                (nn - (w0 + (psn1.pos - psE1.pos))) := by
              rw [htc1, htc2, h_et1, h_et2, hte1, hte2, h_t1', h_t2',
                show psC1.pos = ps1.pos + (w0 + (psn1.pos - psE1.pos)) by omega,
                show psC2.pos = ps2.pos + (w0 + (psn1.pos - psE1.pos)) by omega]
              exact h_ag.shift _
            have h_cl_c : WClean psC1.tokens psC1.pos
                (nn - (w0 + (psn1.pos - psE1.pos))) := by
              rw [htc1, h_et1, hte1, h_t1',
                show psC1.pos = ps1.pos + (w0 + (psn1.pos - psE1.pos)) by omega]
              exact h_cl.shift _
            have h_rc2_lo : psC2.pos ≤ r2.2.pos :=
              parseFlowSequenceLoop_pos_mono k2 (parseNode_pos_mono_all k2)
                psC2 (items.push val2) r2 h_cont2
            rw [h_val_eq] at h_cont1
            obtain ⟨h_arr, h_adv, h_ct1, h_ct2⟩ :=
              ih (by omega) k2 psC1 psC2 (nn - (w0 + (psn1.pos - psE1.pos)))
                (items.push val2) r1 r2 h_ag_c h_cl_c h_cont1 h_cont2
                (by omega) hx1 hx2
            refine ⟨h_arr, by omega, ?_, ?_⟩
            · rw [h_ct1, htc1, h_et1, hte1, h_t1']
            · rw [h_ct2, htc2, h_et2, hte2, h_t2']

/-! ## §5  Flow-mapping mirrors

The map side of the clique: `parseExplicitKey` mirrors `pairKeyStep` (same dispatch shape with
`.flowMappingEnd` in place of `.flowSequenceEnd`), `parseFlowMappingValue` mirrors the
`:`-consume + value phase of `parseSinglePairMapping` (with an extra retroactive-`.key`-marker
consume in front, and the `savedPath`/`keyContent` METADATA existentially absorbed), and
`parseFlowMappingLoop` mirrors `parseFlowSequenceLoop` (element = explicit/implicit key,
then value, then recurse). -/

/-- Joint for the explicit-key phase of flow-mapping entries (dispatch: empty heads coincide
    across runs by `.val` agreement; otherwise both run `parseNode`).  Mirror of
    `pairKeyStep_joint` with `.flowMappingEnd` in place of `.flowSequenceEnd`. -/
lemma parseExplicitKey_joint (n : Nat) (h_node : ParseNodeJoint n)
    (g1 : Nat) (hg1 : g1 ≤ n) (g2 : Nat) (ps1 ps2 : ParseState) (nn : Nat)
    (key1 key2 : YamlValue) (q1 q2 : ParseState)
    (hnn : 0 < nn)
    (h_ag : WAgree ps1.tokens ps2.tokens ps1.pos ps2.pos nn)
    (h_cl : WClean ps1.tokens ps1.pos nn)
    (h1 : parseExplicitKey ps1 g1 = .ok (key1, q1))
    (h2 : parseExplicitKey ps2 g2 = .ok (key2, q2))
    (h_fr : q1.pos ≤ ps1.pos + nn) :
    key1 = key2 ∧ q1.pos - ps1.pos = q2.pos - ps2.pos
      ∧ q1.tokens = ps1.tokens ∧ q2.tokens = ps2.tokens := by
  have h_pk := h_ag.peek_eq hnn
  unfold parseExplicitKey at h1 h2
  rw [← h_pk] at h2
  cases h_c : ps1.peek? with
  | none =>
    rw [h_c] at h1 h2
    exact h_node g1 hg1 g2 ps1 ps2 nn key1 key2 q1 q2 hnn h_ag h_cl h1 h2 h_fr
  | some t =>
    rw [h_c] at h1 h2
    cases t
    case value =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h1 h2
      obtain ⟨hk1, hq1⟩ := h1
      obtain ⟨hk2, hq2⟩ := h2
      subst hq1; subst hq2
      exact ⟨hk1.symm.trans hk2, by omega, rfl, rfl⟩
    case flowEntry =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h1 h2
      obtain ⟨hk1, hq1⟩ := h1
      obtain ⟨hk2, hq2⟩ := h2
      subst hq1; subst hq2
      exact ⟨hk1.symm.trans hk2, by omega, rfl, rfl⟩
    case flowMappingEnd =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h1 h2
      obtain ⟨hk1, hq1⟩ := h1
      obtain ⟨hk2, hq2⟩ := h2
      subst hq1; subst hq2
      exact ⟨hk1.symm.trans hk2, by omega, rfl, rfl⟩
    all_goals
      exact h_node g1 hg1 g2 ps1 ps2 nn key1 key2 q1 q2 hnn h_ag h_cl h1 h2 h_fr

/-- Case split on `tryConsume` when only the resulting state is consumed (the discarded-Bool
    `.key`-marker consume in `parseFlowMappingValue`). -/
lemma tryConsume_snd_cases (ps : ParseState) (tok : YamlToken) :
    (ps.peek? = some tok ∧ (ps.tryConsume tok).2 = ps.advance)
    ∨ (ps.peek? ≠ some tok ∧ (ps.tryConsume tok).2 = ps) := by
  cases h : (ps.tryConsume tok).1 with
  | true => exact Or.inl (tryConsume_true_facts ps tok h)
  | false => exact Or.inr (tryConsume_false_facts ps tok h)

/-- A mapping loop sitting on its close token returns immediately at ANY fuel.  Mirror of
    `parseFlowSeqLoop_close_now`. -/
lemma parseFlowMapLoop_close_now (ps : ParseState) (f : Nat)
    (pairs : Array (YamlValue × YamlValue))
    (r : Array (YamlValue × YamlValue) × ParseState)
    (h_pk : ps.peek? = some .flowMappingEnd)
    (h : parseFlowMappingLoop ps f pairs = .ok r) : r = (pairs, ps) := by
  cases f with
  | zero =>
    unfold parseFlowMappingLoop at h
    exact (Except.ok.inj h).symm
  | succ k =>
    unfold parseFlowMappingLoop at h
    rw [h_pk] at h
    simp only [] at h
    exact (Except.ok.inj h).symm

/-- Inversion of `parseFlowMappingValue` success into aligned atomized components: the
    retroactive-`.key`-marker consume width `wk`, the `:`-consume width `wv`, and the value
    phase (`parseNode` exposed directly, with the head classification that decided the arm).
    The `savedPath`/`keyContent` currentPath bookkeeping is METADATA: `pos`/`tokens`/`peek?`
    of the path-modified intermediate states are pinned back to `ps`'s. -/
lemma parseFlowMappingValue_inv (ps : ParseState) (g : Nat) (sp : YamlPath) (kc : String)
    (v : YamlValue) (q : ParseState)
    (h : parseFlowMappingValue ps g sp kc = .ok (v, q)) :
    ∃ (wk wv : Nat) (mid psv0 : ParseState) (val : YamlValue) (pv : ParseState),
      ((ps.peek? = some .key ∧ wk = 1) ∨ (ps.peek? ≠ some .key ∧ wk = 0)) ∧
      ((mid.peek? = some .value ∧ wv = 1) ∨ (mid.peek? ≠ some .value ∧ wv = 0)) ∧
      ((wv = 0 ∧ val = emptyNode ∧ pv = psv0)
        ∨ (wv = 1 ∧ (psv0.peek? = some .flowEntry ∨ psv0.peek? = some .flowMappingEnd
              ∨ psv0.peek? = none) ∧ val = emptyNode ∧ pv = psv0)
        ∨ (wv = 1 ∧ psv0.peek? ≠ some .flowEntry ∧ psv0.peek? ≠ some .flowMappingEnd
              ∧ psv0.peek? ≠ none ∧ parseNode psv0 g = .ok (val, pv))) ∧
      mid.pos = ps.pos + wk ∧ mid.tokens = ps.tokens ∧
      psv0.pos = ps.pos + wk + wv ∧ psv0.tokens = ps.tokens ∧
      v = val ∧ q.pos = pv.pos ∧ q.tokens = pv.tokens := by
  unfold parseFlowMappingValue at h
  simp only [bind, Except.bind] at h
  rcases tryConsume_snd_cases ({ ps with currentPath := sp.push (.key kc) }) .key with
    ⟨h_k1, h_st1⟩ | ⟨h_k1, h_st1⟩ <;> rw [h_st1] at h
  · -- `.key` marker consumed: wk = 1
    have h_k1' : ps.peek? = some YamlToken.key := h_k1
    split at h
    · rename_i hc
      obtain ⟨h_pkv, h_st2⟩ := tryConsume_true_facts _ YamlToken.value hc
      rw [h_st2] at h
      split at h
      · rename_i heq3
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨1, 1, _, _, emptyNode, _, Or.inl ⟨h_k1', rfl⟩, Or.inl ⟨h_pkv, rfl⟩,
          Or.inr (Or.inl ⟨rfl, Or.inl heq3, rfl, rfl⟩), rfl, rfl, rfl, rfl,
          h.1.symm, by rw [← h.2], by rw [← h.2]⟩
      · rename_i heq3
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨1, 1, _, _, emptyNode, _, Or.inl ⟨h_k1', rfl⟩, Or.inl ⟨h_pkv, rfl⟩,
          Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl heq3), rfl, rfl⟩), rfl, rfl, rfl, rfl,
          h.1.symm, by rw [← h.2], by rw [← h.2]⟩
      · rename_i heq3
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨1, 1, _, _, emptyNode, _, Or.inl ⟨h_k1', rfl⟩, Or.inl ⟨h_pkv, rfl⟩,
          Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr heq3), rfl, rfl⟩), rfl, rfl, rfl, rfl,
          h.1.symm, by rw [← h.2], by rw [← h.2]⟩
      · rename_i hv1 hv2 hv3
        split at h
        · simp only [reduceCtorEq] at h
        · rename_i vr heq6
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          exact ⟨1, 1, _, _, vr.1, vr.2, Or.inl ⟨h_k1', rfl⟩, Or.inl ⟨h_pkv, rfl⟩,
            Or.inr (Or.inr ⟨rfl, fun hx => hv1 hx, fun hx => hv2 hx, fun hx => hv3 hx,
              heq6⟩), rfl, rfl, rfl, rfl, h.1.symm, by rw [← h.2], by rw [← h.2]⟩
    · rename_i hc
      rw [Bool.not_eq_true] at hc
      obtain ⟨h_nv, h_st2⟩ := tryConsume_false_facts _ YamlToken.value hc
      rw [h_st2] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨1, 0, _,
        ({ ps with currentPath := sp.push (.key kc) } : ParseState).advance, emptyNode,
        ({ ps with currentPath := sp.push (.key kc) } : ParseState).advance,
        Or.inl ⟨h_k1', rfl⟩, Or.inr ⟨h_nv, rfl⟩, Or.inl ⟨rfl, rfl, rfl⟩,
        rfl, rfl, rfl, rfl, h.1.symm, by rw [← h.2], by rw [← h.2]⟩
  · -- `.key` marker refused: wk = 0
    have h_k1' : ps.peek? ≠ some YamlToken.key := fun hx => h_k1 hx
    split at h
    · rename_i hc
      obtain ⟨h_pkv, h_st2⟩ := tryConsume_true_facts _ YamlToken.value hc
      rw [h_st2] at h
      split at h
      · rename_i heq3
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨0, 1, _, _, emptyNode, _, Or.inr ⟨h_k1', rfl⟩, Or.inl ⟨h_pkv, rfl⟩,
          Or.inr (Or.inl ⟨rfl, Or.inl heq3, rfl, rfl⟩), rfl, rfl, rfl, rfl,
          h.1.symm, by rw [← h.2], by rw [← h.2]⟩
      · rename_i heq3
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨0, 1, _, _, emptyNode, _, Or.inr ⟨h_k1', rfl⟩, Or.inl ⟨h_pkv, rfl⟩,
          Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl heq3), rfl, rfl⟩), rfl, rfl, rfl, rfl,
          h.1.symm, by rw [← h.2], by rw [← h.2]⟩
      · rename_i heq3
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨0, 1, _, _, emptyNode, _, Or.inr ⟨h_k1', rfl⟩, Or.inl ⟨h_pkv, rfl⟩,
          Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr heq3), rfl, rfl⟩), rfl, rfl, rfl, rfl,
          h.1.symm, by rw [← h.2], by rw [← h.2]⟩
      · rename_i hv1 hv2 hv3
        split at h
        · simp only [reduceCtorEq] at h
        · rename_i vr heq6
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          exact ⟨0, 1, _, _, vr.1, vr.2, Or.inr ⟨h_k1', rfl⟩, Or.inl ⟨h_pkv, rfl⟩,
            Or.inr (Or.inr ⟨rfl, fun hx => hv1 hx, fun hx => hv2 hx, fun hx => hv3 hx,
              heq6⟩), rfl, rfl, rfl, rfl, h.1.symm, by rw [← h.2], by rw [← h.2]⟩
    · rename_i hc
      rw [Bool.not_eq_true] at hc
      obtain ⟨h_nv, h_st2⟩ := tryConsume_false_facts _ YamlToken.value hc
      rw [h_st2] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨0, 0, _,
        ({ ps with currentPath := sp.push (.key kc) } : ParseState), emptyNode,
        ({ ps with currentPath := sp.push (.key kc) } : ParseState),
        Or.inr ⟨h_k1', rfl⟩, Or.inr ⟨h_nv, rfl⟩, Or.inl ⟨rfl, rfl, rfl⟩,
        rfl, rfl, rfl, rfl, h.1.symm, by rw [← h.2], by rw [← h.2]⟩

set_option maxHeartbeats 1600000 in
/-- The two-fuel both-success joint for `parseFlowMappingValue` (the value part of a flow
    mapping entry): equal values, equal relative advances, tokens preserved.  The
    `savedPath`/`keyContent` arguments are METADATA and may differ across the two runs.
    Mirror of `parseSinglePairMapping_joint`. -/
lemma parseFlowMappingValue_joint (n : Nat) (h_node : ParseNodeJoint n)
    (g1 : Nat) (hg1 : g1 ≤ n) (g2 : Nat) (sp1 sp2 : YamlPath) (kc1 kc2 : String)
    (ps1 ps2 : ParseState) (nn : Nat)
    (v1 v2 : YamlValue) (q1 q2 : ParseState)
    (h_ag : WAgree ps1.tokens ps2.tokens ps1.pos ps2.pos nn)
    (h_cl : WClean ps1.tokens ps1.pos nn)
    (h1 : parseFlowMappingValue ps1 g1 sp1 kc1 = .ok (v1, q1))
    (h2 : parseFlowMappingValue ps2 g2 sp2 kc2 = .ok (v2, q2))
    (h_fr : q1.pos < ps1.pos + nn) :
    v1 = v2 ∧ q1.pos - ps1.pos = q2.pos - ps2.pos
      ∧ q1.tokens = ps1.tokens ∧ q2.tokens = ps2.tokens := by
  obtain ⟨wk1, wv1, mid1, psv01, val1, pv1, hk1, hv1c, hval1, hmp1, hmt1, hvp1, hvt1,
    hveq1, hq1p, hq1t⟩ := parseFlowMappingValue_inv ps1 g1 sp1 kc1 v1 q1 h1
  obtain ⟨wk2, wv2, mid2, psv02, val2, pv2, hk2, hv2c, hval2, hmp2, hmt2, hvp2, hvt2,
    hveq2, hq2p, hq2t⟩ := parseFlowMappingValue_inv ps2 g2 sp2 kc2 v2 q2 h2
  have h_pv1_lo : psv01.pos ≤ pv1.pos := by
    rcases hval1 with ⟨_, _, h_e⟩ | ⟨_, _, _, h_e⟩ | ⟨_, _, _, _, hpn⟩
    · exact Nat.le_of_eq (congrArg ParseState.pos h_e).symm
    · exact Nat.le_of_eq (congrArg ParseState.pos h_e).symm
    · exact parseNodePosMono_apply (parseNode_pos_mono_all g1) hpn (Nat.le_refl _)
  have h_pv2_lo : psv02.pos ≤ pv2.pos := by
    rcases hval2 with ⟨_, _, h_e⟩ | ⟨_, _, _, h_e⟩ | ⟨_, _, _, _, hpn⟩
    · exact Nat.le_of_eq (congrArg ParseState.pos h_e).symm
    · exact Nat.le_of_eq (congrArg ParseState.pos h_e).symm
    · exact parseNodePosMono_apply (parseNode_pos_mono_all g2) hpn (Nat.le_refl _)
  -- the strict frame gives the window bound on both consume widths
  have h_wbound : wk1 + wv1 < nn := by omega
  have h_nn : 0 < nn := by omega
  -- align the `.key`-marker width
  have h_pk12 : ps1.peek? = ps2.peek? := h_ag.peek_eq h_nn
  have h_wk : wk2 = wk1 := by
    rcases hk1 with ⟨h_a, rfl⟩ | ⟨h_a, rfl⟩ <;> rcases hk2 with ⟨h_b, rfl⟩ | ⟨h_b, rfl⟩
    · rfl
    · exact absurd (h_pk12 ▸ h_a) h_b
    · exact absurd (h_pk12.trans h_b) h_a
    · rfl
  subst h_wk
  -- align the `:` width
  have h_mid_pk : mid1.peek? = mid2.peek? :=
    h_ag.peek_eq_at (d := wk2) hmt1 hmt2 hmp1 hmp2 (by omega)
  have h_wv : wv2 = wv1 := by
    rcases hv1c with ⟨h_a, rfl⟩ | ⟨h_a, rfl⟩ <;> rcases hv2c with ⟨h_b, rfl⟩ | ⟨h_b, rfl⟩
    · rfl
    · exact absurd (h_mid_pk ▸ h_a) h_b
    · exact absurd (h_mid_pk.trans h_b) h_a
    · rfl
  subst h_wv
  -- transfer the value-phase head
  have h_pvv : psv01.peek? = psv02.peek? :=
    h_ag.peek_eq_at (d := wk2 + wv2) hvt1 hvt2 (by omega) (by omega) (by omega)
  -- match the value arms
  rcases hval1 with ⟨h10, h_ve1, h_pe1⟩ | ⟨h11, h_mem1, h_ve1, h_pe1⟩
    | ⟨h11, hne1a, hne1b, hne1c, hpn1⟩
  · -- run 1: no `:` consumed, empty value
    rcases hval2 with ⟨h20, h_ve2, h_pe2⟩ | ⟨h21, _, _, _⟩ | ⟨h21, _, _, _, _⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hveq1, hveq2, h_ve1, h_ve2]
      · rw [hq1p, hq2p, h_pe1, h_pe2]; omega
      · rw [hq1t, h_pe1, hvt1]
      · rw [hq2t, h_pe2, hvt2]
    · omega
    · omega
  · -- run 1: `:` consumed, empty-value head
    rcases hval2 with ⟨h20, _, _⟩ | ⟨h21, _, h_ve2, h_pe2⟩ | ⟨h21, hne2a, hne2b, hne2c, _⟩
    · omega
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hveq1, hveq2, h_ve1, h_ve2]
      · rw [hq1p, hq2p, h_pe1, h_pe2]; omega
      · rw [hq1t, h_pe1, hvt1]
      · rw [hq2t, h_pe2, hvt2]
    · rcases h_mem1 with hm | hm | hm
      · exact absurd (h_pvv.symm.trans hm) hne2a
      · exact absurd (h_pvv.symm.trans hm) hne2b
      · exact absurd (h_pvv.symm.trans hm) hne2c
  · -- run 1: `:` consumed, parseNode value
    rcases hval2 with ⟨h20, _, _⟩ | ⟨h21, h_mem2, _, _⟩ | ⟨h21, _, _, _, hpn2⟩
    · omega
    · rcases h_mem2 with hm | hm | hm
      · exact absurd (h_pvv.trans hm) hne1a
      · exact absurd (h_pvv.trans hm) hne1b
      · exact absurd (h_pvv.trans hm) hne1c
    · have h_ag_v : WAgree psv01.tokens psv02.tokens psv01.pos psv02.pos
          (nn - (wk2 + wv2)) := by
        rw [hvt1, hvt2, show psv01.pos = ps1.pos + (wk2 + wv2) by omega,
          show psv02.pos = ps2.pos + (wk2 + wv2) by omega]
        exact h_ag.shift _
      have h_cl_v : WClean psv01.tokens psv01.pos (nn - (wk2 + wv2)) := by
        rw [hvt1, show psv01.pos = ps1.pos + (wk2 + wv2) by omega]
        exact h_cl.shift _
      obtain ⟨h_val_eq, h_vadv, h_vt1, h_vt2⟩ :=
        h_node g1 (by omega) g2 psv01 psv02 (nn - (wk2 + wv2))
          val1 val2 pv1 pv2 (by omega) h_ag_v h_cl_v hpn1 hpn2 (by omega)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hveq1, hveq2, h_val_eq]
      · rw [hq1p, hq2p]; omega
      · rw [hq1t, h_vt1, hvt1]
      · rw [hq2t, h_vt2, hvt2]

/-- One-step inversion of a successful `parseFlowMappingLoop` at positive fuel: close now,
    early return, or (separator·entry·continuation) with all states exposed through
    pos/tokens equations.  The entry decomposes into the key phase (`parseExplicitKey` after
    the consumed `.key` marker, or `parseNode` for implicit keys) and the value phase
    (`parseFlowMappingValue`, its `savedPath`/`keyContent` arguments existentially absorbed).
    Mirror of `parseFlowSequenceLoop_step_inv`. -/
lemma parseFlowMappingLoop_step_inv (ps : ParseState) (k : Nat)
    (pairs : Array (YamlValue × YamlValue))
    (r : Array (YamlValue × YamlValue) × ParseState)
    (h : parseFlowMappingLoop ps (k + 1) pairs = .ok r) :
    (ps.peek? = some .flowMappingEnd ∧ r = (pairs, ps))
    ∨ (0 < pairs.size ∧ ps.peek? ≠ some .flowMappingEnd ∧ ps.peek? ≠ some .flowEntry
        ∧ r = (pairs, ps))
    ∨ (∃ (w0 : Nat) (ps' : ParseState),
        ps'.pos = ps.pos + w0 ∧ ps'.tokens = ps.tokens ∧
        ps.peek? ≠ some .flowMappingEnd ∧
        ((0 < pairs.size ∧ ps.peek? = some .flowEntry ∧ w0 = 1)
          ∨ (pairs.size = 0 ∧ w0 = 0)) ∧
        ((ps'.peek? = some .flowMappingEnd ∧ r = (pairs, ps'))
          ∨ (ps'.peek? = some .key ∧
              ∃ (psE : ParseState) (key : YamlValue) (psn : ParseState) (sp : YamlPath)
                (kc : String) (psM : ParseState) (val : YamlValue) (psv psC : ParseState),
                parseExplicitKey psE k = .ok (key, psn) ∧
                psE.pos = ps'.pos + 1 ∧ psE.tokens = ps'.tokens ∧
                parseFlowMappingValue psM k sp kc = .ok (val, psv) ∧
                psM.pos = psn.pos ∧ psM.tokens = psn.tokens ∧
                parseFlowMappingLoop psC k (pairs.push (key, val)) = .ok r ∧
                psC.pos = psv.pos ∧ psC.tokens = psv.tokens)
          ∨ (ps'.peek? ≠ some .flowMappingEnd ∧ ps'.peek? ≠ some .key ∧
              ∃ (psE : ParseState) (key : YamlValue) (psn : ParseState) (sp : YamlPath)
                (kc : String) (psM : ParseState) (val : YamlValue) (psv psC : ParseState),
                parseNode psE k = .ok (key, psn) ∧
                psE.pos = ps'.pos ∧ psE.tokens = ps'.tokens ∧
                parseFlowMappingValue psM k sp kc = .ok (val, psv) ∧
                psM.pos = psn.pos ∧ psM.tokens = psn.tokens ∧
                parseFlowMappingLoop psC k (pairs.push (key, val)) = .ok r ∧
                psC.pos = psv.pos ∧ psC.tokens = psv.tokens))) := by
  unfold parseFlowMappingLoop at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  case h_1 x heq => exact Or.inl ⟨heq, (Except.ok.inj h).symm⟩
  case h_2 x hne =>
    split at h
    · -- pairs.size > 0
      rename_i hsz
      split at h
      · -- separator present: continue at ps.advance
        rename_i heq_fe
        split at h
        · -- trailing close right after the separator
          rename_i heq_cl
          exact Or.inr (Or.inr ⟨1, ps.advance, rfl, rfl, fun hx => hne hx,
            Or.inl ⟨hsz, heq_fe, rfl⟩, Or.inl ⟨heq_cl, (Except.ok.inj h).symm⟩⟩)
        · -- entry head `.key`: explicit key then value
          rename_i heq_k
          split at h
          · simp only [reduceCtorEq] at h
          · rename_i kr heq_key
            split at h
            · simp only [reduceCtorEq] at h
            · rename_i vr heq_val
              exact Or.inr (Or.inr ⟨1, ps.advance, rfl, rfl, fun hx => hne hx,
                Or.inl ⟨hsz, heq_fe, rfl⟩,
                Or.inr (Or.inl ⟨heq_k, _, _, _, _, _, _, _, _, _, heq_key, rfl, rfl,
                  heq_val, rfl, rfl, h, rfl, rfl⟩)⟩)
        · -- entry head: implicit-key node then value
          rename_i hn1 hn2
          split at h
          · simp only [reduceCtorEq] at h
          · rename_i kr heq_key
            split at h
            · simp only [reduceCtorEq] at h
            · rename_i vr heq_val
              exact Or.inr (Or.inr ⟨1, ps.advance, rfl, rfl, fun hx => hne hx,
                Or.inl ⟨hsz, heq_fe, rfl⟩,
                Or.inr (Or.inr ⟨fun hx => hn1 hx, fun hx => hn2 hx,
                  _, _, _, _, _, _, _, _, _, heq_key, rfl, rfl,
                  heq_val, rfl, rfl, h, rfl, rfl⟩)⟩)
      · -- early return (nonempty, head neither close nor separator)
        rename_i hne_fe
        exact Or.inr (Or.inl ⟨hsz, fun hx => hne hx, fun hx => hne_fe hx,
          (Except.ok.inj h).symm⟩)
    · -- pairs.size = 0: no separator step
      rename_i hsz
      split at h
      · rename_i heq_cl
        exact absurd heq_cl (fun hx => hne hx)
      · rename_i heq_k
        split at h
        · simp only [reduceCtorEq] at h
        · rename_i kr heq_key
          split at h
          · simp only [reduceCtorEq] at h
          · rename_i vr heq_val
            exact Or.inr (Or.inr ⟨0, ps, rfl, rfl, fun hx => hne hx,
              Or.inr ⟨by omega, rfl⟩,
              Or.inr (Or.inl ⟨heq_k, _, _, _, _, _, _, _, _, _, heq_key, rfl, rfl,
                heq_val, rfl, rfl, h, rfl, rfl⟩)⟩)
      · rename_i hn1 hn2
        split at h
        · simp only [reduceCtorEq] at h
        · rename_i kr heq_key
          split at h
          · simp only [reduceCtorEq] at h
          · rename_i vr heq_val
            exact Or.inr (Or.inr ⟨0, ps, rfl, rfl, fun hx => hne hx,
              Or.inr ⟨by omega, rfl⟩,
              Or.inr (Or.inr ⟨fun hx => hn1 hx, fun hx => hn2 hx,
                _, _, _, _, _, _, _, _, _, heq_key, rfl, rfl,
                heq_val, rfl, rfl, h, rfl, rfl⟩)⟩)

set_option maxHeartbeats 3200000 in
/-- The two-fuel both-success joint for `parseFlowMappingLoop`: same accumulator, agreeing
    gated windows, a strict run-1 frame, and proper (close-token) exits on both runs force
    equal result arrays, equal relative advances, and token preservation.  Mirror of
    `parseFlowSequenceLoop_joint`. -/
lemma parseFlowMappingLoop_joint (n : Nat) (h_node : ParseNodeJoint n) :
    ∀ (f1 : Nat), f1 ≤ n + 1 → ∀ (f2 : Nat) (ps1 ps2 : ParseState) (nn : Nat)
      (pairs : Array (YamlValue × YamlValue))
      (r1 r2 : Array (YamlValue × YamlValue) × ParseState),
      WAgree ps1.tokens ps2.tokens ps1.pos ps2.pos nn →
      WClean ps1.tokens ps1.pos nn →
      parseFlowMappingLoop ps1 f1 pairs = .ok r1 →
      parseFlowMappingLoop ps2 f2 pairs = .ok r2 →
      r1.2.pos < ps1.pos + nn →
      r1.2.peek? = some .flowMappingEnd →
      r2.2.peek? = some .flowMappingEnd →
      r1.1 = r2.1 ∧ r1.2.pos - ps1.pos = r2.2.pos - ps2.pos
        ∧ r1.2.tokens = ps1.tokens ∧ r2.2.tokens = ps2.tokens := by
  intro f1
  induction f1 with
  | zero =>
    intro _ f2 ps1 ps2 nn pairs r1 r2 h_ag h_cl h1 h2 h_fr hx1 hx2
    unfold parseFlowMappingLoop at h1
    have h_r1 : r1 = (pairs, ps1) := (Except.ok.inj h1).symm
    have h_rs1 : r1.2 = ps1 := by rw [h_r1]
    have h_ra1 : r1.1 = pairs := by rw [h_r1]
    rw [h_rs1] at hx1 h_fr
    have h_nn : 0 < nn := by omega
    have h_c2 : ps2.peek? = some .flowMappingEnd := (h_ag.peek_eq h_nn) ▸ hx1
    have h_r2 := parseFlowMapLoop_close_now ps2 f2 pairs r2 h_c2 h2
    have h_rs2 : r2.2 = ps2 := by rw [h_r2]
    have h_ra2 : r2.1 = pairs := by rw [h_r2]
    exact ⟨by rw [h_ra1, h_ra2], by rw [h_rs1, h_rs2]; omega, by rw [h_rs1], by rw [h_rs2]⟩
  | succ k ih =>
    intro hf1 f2 ps1 ps2 nn pairs r1 r2 h_ag h_cl h1 h2 h_fr hx1 hx2
    have h_mono1 : ps1.pos ≤ r1.2.pos :=
      parseFlowMappingLoop_pos_mono (k + 1) (parseNode_pos_mono_all (k + 1)) ps1 pairs r1 h1
    have h_nn : 0 < nn := by omega
    have h_pk12 : ps1.peek? = ps2.peek? := h_ag.peek_eq h_nn
    rcases parseFlowMappingLoop_step_inv ps1 k pairs r1 h1 with
      ⟨h_c1, h_r1⟩ | ⟨h_sz1, h_ne1, h_nf1, h_r1⟩
      | ⟨w0, ps1', h_p1', h_t1', h_ne1, h_sep1, h_disp1⟩
    · -- run 1 closes now ⇒ run 2 closes now
      have h_c2 : ps2.peek? = some .flowMappingEnd := h_pk12 ▸ h_c1
      have h_r2 := parseFlowMapLoop_close_now ps2 f2 pairs r2 h_c2 h2
      have h_rs1 : r1.2 = ps1 := by rw [h_r1]
      have h_ra1 : r1.1 = pairs := by rw [h_r1]
      have h_rs2 : r2.2 = ps2 := by rw [h_r2]
      have h_ra2 : r2.1 = pairs := by rw [h_r2]
      exact ⟨by rw [h_ra1, h_ra2], by rw [h_rs1, h_rs2]; omega, by rw [h_rs1], by rw [h_rs2]⟩
    · -- run 1 early-returns: contradicts its proper exit
      rw [h_r1] at hx1
      exact absurd hx1 h_ne1
    · -- run 1 steps; run 2 must step too
      cases f2 with
      | zero =>
        unfold parseFlowMappingLoop at h2
        have h_r2 : r2 = (pairs, ps2) := (Except.ok.inj h2).symm
        rw [h_r2] at hx2
        exact absurd (h_pk12.trans hx2) h_ne1
      | succ k2 =>
      rcases parseFlowMappingLoop_step_inv ps2 k2 pairs r2 h2 with
        ⟨h_c2, h_r2⟩ | ⟨h_sz2, h_ne2, h_nf2, h_r2⟩
        | ⟨w0₂, ps2', h_p2', h_t2', h_ne2, h_sep2, h_disp2⟩
      · exact absurd (h_pk12.trans h_c2) h_ne1
      · rw [h_r2] at hx2
        exact absurd hx2 h_ne2
      · -- both step: align the separator width
        have h_w0 : w0₂ = w0 := by
          rcases h_sep1 with ⟨hs1, hf1', rfl⟩ | ⟨hs1, rfl⟩ <;>
            rcases h_sep2 with ⟨hs2, hf2', rfl⟩ | ⟨hs2, rfl⟩ <;> omega
        rw [h_w0] at h_p2' h_sep2
        -- run-1 bound: the step's entry stays within the frame
        have h_bound1 : ps1'.pos ≤ r1.2.pos := by
          rcases h_disp1 with ⟨_, h_r⟩
            | ⟨_, psE, key, psn, spx, kcx, psM, val, psv, psC, h_el, hpe, _,
                h_val, hpmp, _, h_cont, hpc, _⟩
            | ⟨_, _, psE, key, psn, spx, kcx, psM, val, psv, psC, h_el, hpe, _,
                h_val, hpmp, _, h_cont, hpc, _⟩
          · rw [h_r]; exact Nat.le_refl _
          · have h1e := parseExplicitKey_pos_mono k (parseNode_pos_mono_all k)
              psE (key, psn) h_el
            have h2e := parseFlowMappingValue_pos_mono k (parseNode_pos_mono_all k)
              psM spx kcx (val, psv) h_val
            have h3e := parseFlowMappingLoop_pos_mono k (parseNode_pos_mono_all k)
              psC (pairs.push (key, val)) r1 h_cont
            simp only [] at h1e h2e
            omega
          · have h1e := parseNodePosMono_apply (parseNode_pos_mono_all k) h_el (Nat.le_refl _)
            have h2e := parseFlowMappingValue_pos_mono k (parseNode_pos_mono_all k)
              psM spx kcx (val, psv) h_val
            have h3e := parseFlowMappingLoop_pos_mono k (parseNode_pos_mono_all k)
              psC (pairs.push (key, val)) r1 h_cont
            simp only [] at h1e h2e
            omega
        have h_w0nn : w0 < nn := by omega
        have h_pk12' : ps1'.peek? = ps2'.peek? :=
          h_ag.peek_eq_at (d := w0) h_t1' h_t2' h_p1' h_p2' h_w0nn
        rcases h_disp1 with ⟨h_cl1', h_r1⟩
          | ⟨h_k1, psE1, key1, psn1, spE1, kcE1, psM1, val1, psv1, psC1,
              h_el1, hpe1, hte1, h_val1, hpm1p, hpm1t, h_cont1, hpc1, htc1⟩
          | ⟨h_ncl1, h_nk1, psE1, key1, psn1, spE1, kcE1, psM1, val1, psv1, psC1,
              h_el1, hpe1, hte1, h_val1, hpm1p, hpm1t, h_cont1, hpc1, htc1⟩
        · -- trailing close on run 1 ⇒ same on run 2
          rcases h_disp2 with ⟨h_cl2', h_r2⟩ | ⟨h_k2, -⟩ | ⟨h_ncl2, -⟩
          · have h_rs1 : r1.2 = ps1' := by rw [h_r1]
            have h_ra1 : r1.1 = pairs := by rw [h_r1]
            have h_rs2 : r2.2 = ps2' := by rw [h_r2]
            have h_ra2 : r2.1 = pairs := by rw [h_r2]
            refine ⟨by rw [h_ra1, h_ra2], by rw [h_rs1, h_rs2]; omega,
              by rw [h_rs1]; exact h_t1', by rw [h_rs2]; exact h_t2'⟩
          · exact absurd (h_pk12'.symm.trans h_cl1') (by rw [h_k2]; simp)
          · exact absurd (h_pk12'.symm.trans h_cl1') h_ncl2
        · -- `.key` entry on run 1 ⇒ same on run 2
          rcases h_disp2 with ⟨h_cl2', h_r2⟩
            | ⟨h_k2, psE2, key2, psn2, spE2, kcE2, psM2, val2, psv2, psC2,
                h_el2, hpe2, hte2, h_val2, hpm2p, hpm2t, h_cont2, hpc2, htc2⟩
            | ⟨h_ncl2, h_nk2, -⟩
          · exact absurd (h_pk12'.trans h_cl2') (by rw [h_k1]; simp)
          · -- joint on the explicit-key entries
            have h1e := parseExplicitKey_pos_mono k (parseNode_pos_mono_all k)
              psE1 (key1, psn1) h_el1
            have h2e := parseFlowMappingValue_pos_mono k (parseNode_pos_mono_all k)
              psM1 spE1 kcE1 (val1, psv1) h_val1
            simp only [] at h1e h2e
            have h_rc1_lo : psC1.pos ≤ r1.2.pos :=
              parseFlowMappingLoop_pos_mono k (parseNode_pos_mono_all k)
                psC1 (pairs.push (key1, val1)) r1 h_cont1
            have h1e2 := parseExplicitKey_pos_mono k2 (parseNode_pos_mono_all k2)
              psE2 (key2, psn2) h_el2
            have h2e2 := parseFlowMappingValue_pos_mono k2 (parseNode_pos_mono_all k2)
              psM2 spE2 kcE2 (val2, psv2) h_val2
            simp only [] at h1e2 h2e2
            have h_rc2_lo : psC2.pos ≤ r2.2.pos :=
              parseFlowMappingLoop_pos_mono k2 (parseNode_pos_mono_all k2)
                psC2 (pairs.push (key2, val2)) r2 h_cont2
            -- key joint at offset w0 + 1 (the consumed `.key` marker)
            have h_ag_e : WAgree psE1.tokens psE2.tokens psE1.pos psE2.pos
                (nn - (w0 + 1)) := by
              rw [hte1, hte2, h_t1', h_t2',
                show psE1.pos = ps1.pos + (w0 + 1) by omega,
                show psE2.pos = ps2.pos + (w0 + 1) by omega]
              exact h_ag.shift _
            have h_cl_e : WClean psE1.tokens psE1.pos (nn - (w0 + 1)) := by
              rw [hte1, h_t1', show psE1.pos = ps1.pos + (w0 + 1) by omega]
              exact h_cl.shift _
            obtain ⟨h_key_eq, h_kadv, h_kt1, h_kt2⟩ :=
              parseExplicitKey_joint n h_node k (by omega) k2 psE1 psE2 (nn - (w0 + 1))
                key1 key2 psn1 psn2 (by omega) h_ag_e h_cl_e h_el1 h_el2 (by omega)
            -- value joint at offset w0 + 1 + key-advance
            have h_ag_v : WAgree psM1.tokens psM2.tokens psM1.pos psM2.pos
                (nn - (w0 + 1 + (psn1.pos - psE1.pos))) := by
              rw [hpm1t, hpm2t, h_kt1, h_kt2, hte1, hte2, h_t1', h_t2',
                show psM1.pos = ps1.pos + (w0 + 1 + (psn1.pos - psE1.pos)) by omega,
                show psM2.pos = ps2.pos + (w0 + 1 + (psn1.pos - psE1.pos)) by omega]
              exact h_ag.shift _
            have h_cl_v : WClean psM1.tokens psM1.pos
                (nn - (w0 + 1 + (psn1.pos - psE1.pos))) := by
              rw [hpm1t, h_kt1, hte1, h_t1',
                show psM1.pos = ps1.pos + (w0 + 1 + (psn1.pos - psE1.pos)) by omega]
              exact h_cl.shift _
            obtain ⟨h_val_eq, h_vadv, h_vt1, h_vt2⟩ :=
              parseFlowMappingValue_joint n h_node k (by omega) k2 spE1 spE2 kcE1 kcE2
                psM1 psM2 (nn - (w0 + 1 + (psn1.pos - psE1.pos))) val1 val2 psv1 psv2
                h_ag_v h_cl_v h_val1 h_val2 (by omega)
            -- re-arm the IH on the continuations
            have h_ag_c : WAgree psC1.tokens psC2.tokens psC1.pos psC2.pos
                (nn - (w0 + 1 + (psn1.pos - psE1.pos) + (psv1.pos - psM1.pos))) := by
              rw [htc1, htc2, h_vt1, h_vt2, hpm1t, hpm2t, h_kt1, h_kt2, hte1, hte2,
                h_t1', h_t2',
                show psC1.pos
                    = ps1.pos + (w0 + 1 + (psn1.pos - psE1.pos) + (psv1.pos - psM1.pos))
                  by omega,
                show psC2.pos
                    = ps2.pos + (w0 + 1 + (psn1.pos - psE1.pos) + (psv1.pos - psM1.pos))
                  by omega]
              exact h_ag.shift _
            have h_cl_c : WClean psC1.tokens psC1.pos
                (nn - (w0 + 1 + (psn1.pos - psE1.pos) + (psv1.pos - psM1.pos))) := by
              rw [htc1, h_vt1, hpm1t, h_kt1, hte1, h_t1',
                show psC1.pos
                    = ps1.pos + (w0 + 1 + (psn1.pos - psE1.pos) + (psv1.pos - psM1.pos))
                  by omega]
              exact h_cl.shift _
            rw [h_key_eq, h_val_eq] at h_cont1
            obtain ⟨h_arr, h_adv, h_ct1, h_ct2⟩ :=
              ih (by omega) k2 psC1 psC2
                (nn - (w0 + 1 + (psn1.pos - psE1.pos) + (psv1.pos - psM1.pos)))
                (pairs.push (key2, val2)) r1 r2 h_ag_c h_cl_c h_cont1 h_cont2
                (by omega) hx1 hx2
            refine ⟨h_arr, by omega, ?_, ?_⟩
            · rw [h_ct1, htc1, h_vt1, hpm1t, h_kt1, hte1, h_t1']
            · rw [h_ct2, htc2, h_vt2, hpm2t, h_kt2, hte2, h_t2']
          · exact absurd (h_pk12'.symm.trans h_k1) h_nk2
        · -- implicit-key node entry on run 1 ⇒ same on run 2
          rcases h_disp2 with ⟨h_cl2', h_r2⟩ | ⟨h_k2, -⟩
            | ⟨h_ncl2, h_nk2, psE2, key2, psn2, spE2, kcE2, psM2, val2, psv2, psC2,
                h_el2, hpe2, hte2, h_val2, hpm2p, hpm2t, h_cont2, hpc2, htc2⟩
          · exact absurd (h_pk12'.trans h_cl2') h_ncl1
          · exact absurd (h_pk12'.trans h_k2) h_nk1
          · -- joint on the implicit-key entries
            have h1e := parseNodePosMono_apply (parseNode_pos_mono_all k) h_el1 (Nat.le_refl _)
            have h2e := parseFlowMappingValue_pos_mono k (parseNode_pos_mono_all k)
              psM1 spE1 kcE1 (val1, psv1) h_val1
            simp only [] at h1e h2e
            have h_rc1_lo : psC1.pos ≤ r1.2.pos :=
              parseFlowMappingLoop_pos_mono k (parseNode_pos_mono_all k)
                psC1 (pairs.push (key1, val1)) r1 h_cont1
            have h1e2 := parseNodePosMono_apply (parseNode_pos_mono_all k2) h_el2
              (Nat.le_refl _)
            have h2e2 := parseFlowMappingValue_pos_mono k2 (parseNode_pos_mono_all k2)
              psM2 spE2 kcE2 (val2, psv2) h_val2
            simp only [] at h1e2 h2e2
            have h_rc2_lo : psC2.pos ≤ r2.2.pos :=
              parseFlowMappingLoop_pos_mono k2 (parseNode_pos_mono_all k2)
                psC2 (pairs.push (key2, val2)) r2 h_cont2
            -- key joint at offset w0
            have h_ag_e : WAgree psE1.tokens psE2.tokens psE1.pos psE2.pos (nn - w0) := by
              rw [hte1, hte2, h_t1', h_t2',
                show psE1.pos = ps1.pos + w0 by omega,
                show psE2.pos = ps2.pos + w0 by omega]
              exact h_ag.shift w0
            have h_cl_e : WClean psE1.tokens psE1.pos (nn - w0) := by
              rw [hte1, h_t1', show psE1.pos = ps1.pos + w0 by omega]
              exact h_cl.shift w0
            obtain ⟨h_key_eq, h_kadv, h_kt1, h_kt2⟩ :=
              h_node k (by omega) k2 psE1 psE2 (nn - w0) key1 key2 psn1 psn2
                (by omega) h_ag_e h_cl_e h_el1 h_el2 (by omega)
            -- value joint at offset w0 + key-advance
            have h_ag_v : WAgree psM1.tokens psM2.tokens psM1.pos psM2.pos
                (nn - (w0 + (psn1.pos - psE1.pos))) := by
              rw [hpm1t, hpm2t, h_kt1, h_kt2, hte1, hte2, h_t1', h_t2',
                show psM1.pos = ps1.pos + (w0 + (psn1.pos - psE1.pos)) by omega,
                show psM2.pos = ps2.pos + (w0 + (psn1.pos - psE1.pos)) by omega]
              exact h_ag.shift _
            have h_cl_v : WClean psM1.tokens psM1.pos
                (nn - (w0 + (psn1.pos - psE1.pos))) := by
              rw [hpm1t, h_kt1, hte1, h_t1',
                show psM1.pos = ps1.pos + (w0 + (psn1.pos - psE1.pos)) by omega]
              exact h_cl.shift _
            obtain ⟨h_val_eq, h_vadv, h_vt1, h_vt2⟩ :=
              parseFlowMappingValue_joint n h_node k (by omega) k2 spE1 spE2 kcE1 kcE2
                psM1 psM2 (nn - (w0 + (psn1.pos - psE1.pos))) val1 val2 psv1 psv2
                h_ag_v h_cl_v h_val1 h_val2 (by omega)
            -- re-arm the IH on the continuations
            have h_ag_c : WAgree psC1.tokens psC2.tokens psC1.pos psC2.pos
                (nn - (w0 + (psn1.pos - psE1.pos) + (psv1.pos - psM1.pos))) := by
              rw [htc1, htc2, h_vt1, h_vt2, hpm1t, hpm2t, h_kt1, h_kt2, hte1, hte2,
                h_t1', h_t2',
                show psC1.pos
                    = ps1.pos + (w0 + (psn1.pos - psE1.pos) + (psv1.pos - psM1.pos))
                  by omega,
                show psC2.pos
                    = ps2.pos + (w0 + (psn1.pos - psE1.pos) + (psv1.pos - psM1.pos))
                  by omega]
              exact h_ag.shift _
            have h_cl_c : WClean psC1.tokens psC1.pos
                (nn - (w0 + (psn1.pos - psE1.pos) + (psv1.pos - psM1.pos))) := by
              rw [htc1, h_vt1, hpm1t, h_kt1, hte1, h_t1',
                show psC1.pos
                    = ps1.pos + (w0 + (psn1.pos - psE1.pos) + (psv1.pos - psM1.pos))
                  by omega]
              exact h_cl.shift _
            rw [h_key_eq, h_val_eq] at h_cont1
            obtain ⟨h_arr, h_adv, h_ct1, h_ct2⟩ :=
              ih (by omega) k2 psC1 psC2
                (nn - (w0 + (psn1.pos - psE1.pos) + (psv1.pos - psM1.pos)))
                (pairs.push (key2, val2)) r1 r2 h_ag_c h_cl_c h_cont1 h_cont2
                (by omega) hx1 hx2
            refine ⟨h_arr, by omega, ?_, ?_⟩
            · rw [h_ct1, htc1, h_vt1, hpm1t, h_kt1, hte1, h_t1']
            · rw [h_ct2, htc2, h_vt2, hpm2t, h_kt2, hte2, h_t2']

/-! ## §6  The top assembly: `parseNode_joint_all`

One `Nat.rec` closes the clique: the per-head dispatch reduces to the single-run bricks
(inert/scalar) and to the two loop joints (collection heads), with the gate refuting the
dirty heads. -/

set_option maxHeartbeats 1600000 in
lemma parseNode_joint_all : ∀ n, ParseNodeJoint n := by
  intro n
  induction n with
  | zero =>
    intro m hm f2 ps1 ps2 nn v1 v2 q1 q2 hnn h_ag h_cl h1 h2 h_fr
    have h0 : m = 0 := by omega
    subst h0
    simp only [parseNode, reduceCtorEq] at h1
  | succ k ih =>
    intro m hm f2 ps1 ps2 nn v1 v2 q1 q2 hnn h_ag h_cl h1 h2 h_fr
    by_cases h_le : m ≤ k
    · exact ih m h_le f2 ps1 ps2 nn v1 v2 q1 q2 hnn h_ag h_cl h1 h2 h_fr
    · have h_pk12 : ps1.peek? = ps2.peek? := h_ag.peek_eq hnn
      cases h_pk1 : ps1.peek? with
      | none =>
        have h_pk2 : ps2.peek? = none := by rw [← h_pk12, h_pk1]
        obtain ⟨hv1, hq1, ht1⟩ := parseNode_inert_head ps1 m v1 q1 (Or.inl h_pk1) h1
        obtain ⟨hv2, hq2, ht2⟩ := parseNode_inert_head ps2 f2 v2 q2 (Or.inl h_pk2) h2
        exact ⟨hv1.trans hv2.symm, by omega, ht1, ht2⟩
      | some tok =>
        have h_pk2 : ps2.peek? = some tok := by rw [← h_pk12, h_pk1]
        have h_cl_tok : FlowCleanTok tok = true := h_cl.head hnn h_pk1
        cases tok
        all_goals try (simp [FlowCleanTok] at h_cl_tok)
        case scalar c st =>
          have hv1 := parseNode_scalar_produces_scalar ps1 m c st v1 q1 h_pk1 h1
          have hv2 := parseNode_scalar_produces_scalar ps2 f2 c st v2 q2 h_pk2 h2
          have ha1 := parseNode_scalar_advances_by_one ps1 m c st v1 q1 h_pk1 h1
          have ha2 := parseNode_scalar_advances_by_one ps2 f2 c st v2 q2 h_pk2 h2
          have ht1 := parseNode_scalar_tokens_preserved ps1 m c st v1 q1 h_pk1 h1
          have ht2 := parseNode_scalar_tokens_preserved ps2 f2 c st v2 q2 h_pk2 h2
          exact ⟨hv1.trans hv2.symm, by omega, ht1, ht2⟩
        case flowSequenceStart =>
          obtain ⟨g1, items1, psl1, h_m, h_loop1, h_close1, hv1, hq1, ht1⟩ :=
            parseNode_flowSeqStart_decompose ps1 m v1 q1 h_pk1 h1
          obtain ⟨g2, items2, psl2, h_f2eq, h_loop2, h_close2, hv2, hq2, ht2⟩ :=
            parseNode_flowSeqStart_decompose ps2 f2 v2 q2 h_pk2 h2
          have h_ag1 : WAgree ps1.advance.tokens ps2.advance.tokens ps1.advance.pos
              ps2.advance.pos (nn - 1) := by
            simpa [ParseState.advance] using h_ag.shift 1
          have h_cl1 : WClean ps1.advance.tokens ps1.advance.pos (nn - 1) := by
            simpa [ParseState.advance] using h_cl.shift 1
          have h_mono1 : ps1.advance.pos ≤ psl1.pos :=
            parseFlowSequenceLoop_pos_mono g1 (parseNode_pos_mono_all g1) ps1.advance #[]
              (items1, psl1) h_loop1
          have h_mono2 : ps2.advance.pos ≤ psl2.pos :=
            parseFlowSequenceLoop_pos_mono g2 (parseNode_pos_mono_all g2) ps2.advance #[]
              (items2, psl2) h_loop2
          simp only [ParseState.advance] at h_mono1 h_mono2
          obtain ⟨h_arr, h_adv, h_lt1, h_lt2⟩ :=
            parseFlowSequenceLoop_joint k ih g1 (by omega) g2 ps1.advance ps2.advance (nn - 1)
              #[] (items1, psl1) (items2, psl2) h_ag1 h_cl1 h_loop1 h_loop2
              (by show psl1.pos < ps1.advance.pos + (nn - 1)
                  simp only [ParseState.advance]; omega)
              h_close1 h_close2
          simp only [] at h_arr h_adv
          simp only [ParseState.advance] at h_adv h_lt1 h_lt2
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hv1, hv2, h_arr]
          · omega
          · rw [ht1, h_lt1]
          · rw [ht2, h_lt2]
        case flowMappingStart =>
          obtain ⟨g1, pairs1, psl1, h_m, h_loop1, h_close1, hv1, hq1, ht1⟩ :=
            parseNode_flowMapStart_decompose ps1 m v1 q1 h_pk1 h1
          obtain ⟨g2, pairs2, psl2, h_f2eq, h_loop2, h_close2, hv2, hq2, ht2⟩ :=
            parseNode_flowMapStart_decompose ps2 f2 v2 q2 h_pk2 h2
          have h_ag1 : WAgree ps1.advance.tokens ps2.advance.tokens ps1.advance.pos
              ps2.advance.pos (nn - 1) := by
            simpa [ParseState.advance] using h_ag.shift 1
          have h_cl1 : WClean ps1.advance.tokens ps1.advance.pos (nn - 1) := by
            simpa [ParseState.advance] using h_cl.shift 1
          have h_mono1 : ps1.advance.pos ≤ psl1.pos :=
            parseFlowMappingLoop_pos_mono g1 (parseNode_pos_mono_all g1) ps1.advance #[]
              (pairs1, psl1) h_loop1
          have h_mono2 : ps2.advance.pos ≤ psl2.pos :=
            parseFlowMappingLoop_pos_mono g2 (parseNode_pos_mono_all g2) ps2.advance #[]
              (pairs2, psl2) h_loop2
          simp only [ParseState.advance] at h_mono1 h_mono2
          obtain ⟨h_arr, h_adv, h_lt1, h_lt2⟩ :=
            parseFlowMappingLoop_joint k ih g1 (by omega) g2 ps1.advance ps2.advance (nn - 1)
              #[] (pairs1, psl1) (pairs2, psl2) h_ag1 h_cl1 h_loop1 h_loop2
              (by show psl1.pos < ps1.advance.pos + (nn - 1)
                  simp only [ParseState.advance]; omega)
              h_close1 h_close2
          simp only [] at h_arr h_adv
          simp only [ParseState.advance] at h_adv h_lt1 h_lt2
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hv1, hv2, h_arr]
          · omega
          · rw [ht1, h_lt1]
          · rw [ht2, h_lt2]
        all_goals (
          obtain ⟨hv1, hq1, ht1⟩ := parseNode_inert_head ps1 m v1 q1 (by simp [h_pk1]) h1
          obtain ⟨hv2, hq2, ht2⟩ := parseNode_inert_head ps2 f2 v2 q2 (by simp [h_pk2]) h2
          exact ⟨hv1.trans hv2.symm, by omega, ht1, ht2⟩)

/-- **The value-locality joint** (public form): two successful `parseNode` runs over
    `.val`-agreeing windows, with run 1's window flow-clean and framed, return the same value
    with the same relative advance, preserving both token arrays. -/
lemma parseNode_joint (f1 f2 : Nat) (ps1 ps2 : ParseState) (nn : Nat)
    (v1 v2 : YamlValue) (q1 q2 : ParseState)
    (hnn : 0 < nn)
    (h_ag : WAgree ps1.tokens ps2.tokens ps1.pos ps2.pos nn)
    (h_cl : WClean ps1.tokens ps1.pos nn)
    (h1 : parseNode ps1 f1 = .ok (v1, q1))
    (h2 : parseNode ps2 f2 = .ok (v2, q2))
    (h_fr : q1.pos ≤ ps1.pos + nn) :
    v1 = v2 ∧ q1.pos - ps1.pos = q2.pos - ps2.pos
      ∧ q1.tokens = ps1.tokens ∧ q2.tokens = ps2.tokens :=
  parseNode_joint_all f1 f1 (Nat.le_refl _) f2 ps1 ps2 nn v1 v2 q1 q2 hnn h_ag h_cl h1 h2 h_fr

end L4YAML.Proofs.EmitterScannability
