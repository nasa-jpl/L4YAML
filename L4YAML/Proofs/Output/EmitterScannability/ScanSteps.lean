/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Output.EmitterScannability.ScannerAcceptance
public import L4YAML.Proofs.Scanner.FlowAdjacency
public import L4YAML.Proofs.Scanner.ScannerFlowCollection
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey
public import L4YAML.Proofs.Scanner.ExplicitKeyCoupling

@[expose] public section Blanket

/-!
# Emitter Scannability — Chain Wrappers + Scanning Steps

Foundation module extracted 2026-05-31 from `EmitterScannability.lean`. Imports the
previous foundation layer `ScannerAcceptance`; the base imports this transitively.
Namespace reopened; contiguous prefix slice ⇒ no forward references.

Contents: §G.4 `NoColonDispatchChain` chain wrapper and the core per-step scanning
machinery (state-preservation boilerplate, flow helpers, detailed scan steps).
-/

namespace L4YAML.Proofs.EmitterScannability

open L4YAML.Proofs.CloseStaleExplicitKey

open L4YAML
open L4YAML.Emit
open L4YAML.Proofs.RoundTrip
open L4YAML.Scanner
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ParserGrammable
open L4YAML.Proofs.ParserWellBehaved
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.FlowAdjacency

/-! ### §G.4  Chain wrapper: position preservation at arbitrary `m` -/

/-- **Chain wrapper**: a `NoColonDispatchChain` preserves the token at **every**
    position `m < s.tokens.size`. Direct induction on the predicate — each step's
    non-`:` witness feeds the §G.2 capstone
    `scanNextToken_at_non_colon_preserves_positions`, which gives unconditional
    per-step preservation, transitively composed.

    Parallel to `FlowMonoChain_preserves_position_specific_flow` (substrate.e §E.6)
    and `SavedKeyDoesntResolve_preserves_position_target` (substrate.f §F.3), but
    free of both the `FlowNoOverwriteAt` side-condition and the single-target
    restriction: it covers the *whole* live prefix at once. This is the wrapper the
    blueprint sketched as `FlowMonoChain_preserves_position_when_no_colon_dispatch`. -/
lemma NoColonDispatchChain_preserves_position
    {fl₀ : Nat} {s s' : ScannerState} {n : Nat}
    (h : NoColonDispatchChain fl₀ s n s')
    (m : Nat) (h_m : m < s.tokens.size) :
    ∃ (h_size : m < s'.tokens.size),
      s'.tokens[m]'h_size = s.tokens[m]'h_m := by
  induction h with
  | zero => exact ⟨h_m, rfl⟩
  | @step s s_mid s' n h_fl h_snt h_nc h_rest ih =>
    have h_step_eq := scanNextToken_at_non_colon_preserves_positions s s_mid h_snt h_nc m h_m
    have h_adds := ScannerCorrectness.scanNextToken_adds_tokens s s_mid h_snt
    have h_step_size : m < s_mid.tokens.size := by omega
    obtain ⟨h_rest_size, h_rest_eq⟩ := ih h_step_size
    exact ⟨h_rest_size, h_rest_eq.trans h_step_eq⟩

/-- Connect a ScanChain to scanFiltered: if N steps succeed
    reaching a state where scanNextToken returns none (EOF),
    then scanFiltered on the input succeeds.
    Requires flowLevel = 0 and directivesPresent = false at the end. -/
lemma scanFiltered_of_chain (input : String)
    (s₀ s_final : ScannerState) (n : Nat)
    (h_s0 : s₀ = (ScannerState.mk' input).emit .streamStart)
    (h_no_bom : (ScannerState.mk' input).peek? ≠ some '\uFEFF')
    (h_chain : ScanChain s₀ n s_final)
    (h_eof : scanNextToken s_final = .ok none)
    (h_fl : s_final.flowLevel = 0)
    (h_dp : s_final.directivesPresent = false)
    (h_dn : scanLoop_checkDanglingNode s_final = .ok ())
    (h_fv : scanLoop_checkFlowValueIndent s_final = .ok ())
    (h_fuel : n + 1 ≤ (input.utf8ByteSize + 1) * 4) :
    ∃ tokens, scanFiltered input = .ok tokens := by
  -- scanLoop s_final 1 succeeds
  obtain ⟨toks, h_loop_final⟩ := scanLoop_eof h_eof h_fl h_dp h_dn h_fv
  -- Chain gives scanLoop s₀ (1 + n) succeeds
  have h_loop := h_chain.to_scanLoop h_loop_final
  -- Fuel monotonicity
  have h_loop_fuel := scanLoop_fuel_mono h_loop (by omega : 1 + n ≤ (input.utf8ByteSize + 1) * 4)
  -- Connect to scan
  have h_scan : scan input = scanLoop s₀ ((input.utf8ByteSize + 1) * 4) := by
    unfold scan; subst h_s0; dsimp only []
    -- BOM check: first char ≠ '\uFEFF'
    have h_pk := show ((ScannerState.mk' input).emit .streamStart).peek?
        = (ScannerState.mk' input).peek? from rfl
    rw [h_pk]
    split
    · exact absurd ‹_› h_no_bom
    · rfl
  -- Connect to scanFiltered
  simp only [scanFiltered, h_scan, h_loop_fuel]
  exact ⟨_, rfl⟩

/-- The loop consumes the chain deterministically, whatever comes after —
    stated as a plain `scanLoop` equality so ERRORS ride it too (item 180's
    inversion needs the error direction). -/
lemma ScanChain.scanLoop_eq {s s' : ScannerState} {n fuel : Nat}
    (h_chain : ScanChain s n s') :
    scanLoop s (fuel + n) = scanLoop s' fuel := by
  induction h_chain with
  | zero => rfl
  | @step s s_mid s'' k h_snt h_rest ih =>
    have h : fuel + (k + 1) = (fuel + k) + 1 := by omega
    rw [h]
    show scanLoop s ((fuel + k) + 1) = scanLoop s'' fuel
    have hstep : scanLoop s ((fuel + k) + 1) = scanLoop s_mid (fuel + k) := by
      simp only [scanLoop]
      rw [h_snt]
    rw [hstep]
    exact ih

/-- **Item 180's inversion**: on an ACCEPTED scan, the two EOF checks passed
    at the chain's final state.  The structure lemmas hold acceptance as a
    hypothesis and used to re-PROVE the checks from the sentinel stack alone;
    the crossed-block clause reads content the sentinel does not see, and this
    reads the verdicts off the acceptance instead. -/
lemma scanLoop_checks_of_scanFiltered_ok (input : String)
    (s₀ s_final : ScannerState) (n : Nat)
    (h_s0 : s₀ = (ScannerState.mk' input).emit .streamStart)
    (h_no_bom : (ScannerState.mk' input).peek? ≠ some '\uFEFF')
    (h_chain : ScanChain s₀ n s_final)
    (h_eof : scanNextToken s_final = .ok none)
    (h_fl : s_final.flowLevel = 0)
    (h_dp : s_final.directivesPresent = false)
    (h_fuel : n + 1 ≤ (input.utf8ByteSize + 1) * 4)
    {tokens : Array (Positioned YamlToken)}
    (h_ok : Scanner.scanFiltered input = .ok tokens) :
    scanLoop_checkDanglingNode s_final = .ok ()
      ∧ scanLoop_checkFlowValueIndent s_final = .ok () := by
  -- acceptance descends to the raw scan
  obtain ⟨raw, h_raw⟩ : ∃ raw, scan input = .ok raw := by
    unfold Scanner.scanFiltered at h_ok
    cases h : scan input with
    | ok raw => exact ⟨raw, rfl⟩
    | error e => rw [h] at h_ok; cases h_ok
  -- the raw scan is the loop, and the loop is the chain then the EOF step
  have h_scan_loop : scan input = scanLoop s₀ ((input.utf8ByteSize + 1) * 4) := by
    unfold scan; subst h_s0; dsimp only []
    have h_pk := show ((ScannerState.mk' input).emit .streamStart).peek?
        = (ScannerState.mk' input).peek? from rfl
    rw [h_pk]
    split
    · exact absurd ‹_› h_no_bom
    · rfl
  have h_split : (input.utf8ByteSize + 1) * 4
      = ((input.utf8ByteSize + 1) * 4 - n) + n := by omega
  have h_final_loop : scanLoop s_final ((input.utf8ByteSize + 1) * 4 - n) = .ok raw := by
    rw [← h_chain.scanLoop_eq, ← h_split, ← h_scan_loop]
    exact h_raw
  -- the final fuel is positive, so the loop is at its EOF arm: the checks decide
  obtain ⟨f, hf⟩ : ∃ f, (input.utf8ByteSize + 1) * 4 - n = f + 1 :=
    ⟨(input.utf8ByteSize + 1) * 4 - n - 1, by omega⟩
  rw [hf] at h_final_loop
  unfold scanLoop at h_final_loop
  rw [h_eof] at h_final_loop
  dsimp only [] at h_final_loop
  rw [ite_eq_right (show ¬(s_final.flowLevel > 0) from by omega)] at h_final_loop
  rw [ite_eq_right (by rw [h_dp]; exact Bool.false_ne_true)] at h_final_loop
  cases h_dn : scanLoop_checkDanglingNode s_final with
  | error e => rw [h_dn] at h_final_loop; cases h_final_loop
  | ok u =>
    cases u
    rw [h_dn] at h_final_loop
    cases h_fv : scanLoop_checkFlowValueIndent s_final with
    | error e => rw [h_fv] at h_final_loop; cases h_final_loop
    | ok w => cases w; exact ⟨rfl, rfl⟩

/-- **Equality version**: gives the exact filtered token array from a ScanChain.
    The output is the filtered version of the chain's final state tokens
    plus `streamEnd`, after unwinding indents. -/
lemma scanFiltered_of_chain_eq (input : String)
    (s₀ s_final : ScannerState) (n : Nat)
    (h_s0 : s₀ = (ScannerState.mk' input).emit .streamStart)
    (h_no_bom : (ScannerState.mk' input).peek? ≠ some '\uFEFF')
    (h_chain : ScanChain s₀ n s_final)
    (h_eof : scanNextToken s_final = .ok none)
    (h_fl : s_final.flowLevel = 0)
    (h_dp : s_final.directivesPresent = false)
    (h_dn : scanLoop_checkDanglingNode s_final = .ok ())
    (h_fv : scanLoop_checkFlowValueIndent s_final = .ok ())
    (h_fuel : n + 1 ≤ (input.utf8ByteSize + 1) * 4) :
    scanFiltered input = .ok (((unwindIndents s_final (-1)).emit .streamEnd).tokens.filter
        (fun t => t.val != .placeholder)) := by
  have h_loop := h_chain.to_scanLoop
    (scanLoop_eof_eq (fuel := 1) (by omega) h_eof h_fl h_dp h_dn h_fv)
  have h_loop_fuel := scanLoop_fuel_mono h_loop (by omega : 1 + n ≤ (input.utf8ByteSize + 1) * 4)
  have h_scan : scan input = scanLoop s₀ ((input.utf8ByteSize + 1) * 4) := by
    unfold scan; subst h_s0; dsimp only []
    have h_pk := show ((ScannerState.mk' input).emit .streamStart).peek?
        = (ScannerState.mk' input).peek? from rfl
    rw [h_pk]
    split
    · exact absurd ‹_› h_no_bom
    · rfl
  simp only [scanFiltered, h_scan, h_loop_fuel]

-- ═══ scanNextToken preprocessing equality ═══

-- If two states produce the same preprocessing result AND the same §9.2 reading,
-- scanNextToken gives the same result.  `f` captures the pre-unwind state through
-- item 140's dangling check, and `danglingNodePos?` is the whole of that capture.
-- The reading is an AUTOPARAM rather than a written argument because every caller
-- of this lemma holds the three field equalities `danglingNodePos?_congr` wants —
-- the whitespace-walk producers return `tokens`, `indents` and `flowLevel` in the
-- same bundle as the preprocessing equality — and the direction they come in
-- differs by call site.  A caller that does not hold them supplies the reading
-- itself; the first alternative is that case.
lemma scanNextToken_eq_of_preprocess (s₁ s₂ : ScannerState)
    (h : scanNextToken_preprocess s₁ = scanNextToken_preprocess s₂)
    (h_dn : danglingNodePos? s₁ = danglingNodePos? s₂ := by
      first
        | assumption
        | exact danglingNodePos?_congr (by assumption) (by assumption) (by assumption)
        | exact (danglingNodePos?_congr (by assumption) (by assumption)
            (by assumption)).symm)
    (h_fvp : underIndentedFlowValuePos? s₁ = underIndentedFlowValuePos? s₂ := by
      first
        | assumption
        | exact underIndentedFlowValuePos?_congr (by assumption) (by assumption)
            (by assumption)
        | exact (underIndentedFlowValuePos?_congr (by assumption) (by assumption)
            (by assumption)).symm) :
    scanNextToken s₁ = scanNextToken s₂ := by
  unfold scanNextToken
  simp only [bind, Except.bind]
  rw [h]
  cases scanNextToken_preprocess s₂ with
  | error e => rfl
  | ok r =>
    cases r with
    | none => rfl
    | some p =>
      obtain ⟨s_pp, c⟩ := p
      simp only [scanNextToken_checkDanglingNode, h_dn,
        scanNextToken_checkFlowValueIndent, h_fvp]

-- If scanNextToken gives the same result for two states, and the second has
-- a ScanChain of length ≥ 1, then the first does too.
lemma ScanChain_of_scanNextToken_eq {s₁ s₂ s' : ScannerState} {n : Nat}
    (h_eq : scanNextToken s₁ = scanNextToken s₂)
    (h_chain : ScanChain s₂ (n + 1) s') :
    ScanChain s₁ (n + 1) s' := by
  cases h_chain with
  | step h_snt h_rest =>
    exact .step (by rw [h_eq]; exact h_snt) h_rest

/-- `FlowMonoChain` version of `ScanChain_of_scanNextToken_eq`: if scanNextToken gives
    the same result for two states, and the second has a FlowMonoChain of length ≥ 1,
    then the first does too (given the flow-level bound at the first state). -/
lemma FlowMonoChain_of_scanNextToken_eq {fl₀ : Nat} {s₁ s₂ s' : ScannerState} {n : Nat}
    (h_eq : scanNextToken s₁ = scanNextToken s₂)
    (h_fl : s₁.flowLevel ≥ fl₀)
    (h_chain : FlowMonoChain fl₀ s₂ (n + 1) s') :
    FlowMonoChain fl₀ s₁ (n + 1) s' := by
  cases h_chain with
  | step _ h_snt h_rest =>
    exact .step h_fl (by rw [h_eq]; exact h_snt) h_rest

-- ═══ scanNextToken pipeline factoring ═══
-- The scanNextToken pipeline has 5 stages:
--   preprocess → structural → allowDirectives → flow/block/content
-- These factoring lemmas let us compose results from individual stages.

/-- The Fix-B pending-directives check passes when no directives are pending.
    Stated as an atomic rewrite so `simp` does not rewrite `directivesPresent`
    projections inside record-update expressions elsewhere in the goal. -/
lemma scanNextToken_checkNoPendingDirectives_ok (s : ScannerState)
    (h : s.directivesPresent = false) :
    scanNextToken_checkNoPendingDirectives s = .ok () := by
  simp only [scanNextToken_checkNoPendingDirectives, h, Bool.false_eq_true, ↓reduceIte]

/-- Item 133's §9.2 dangling-node check is a no-op inside a flow collection. -/
lemma danglingNodePos?_none_of_inFlow (s : ScannerState) (h : s.inFlow = true) :
    danglingNodePos? s = none := by
  simp only [danglingNodePos?, h, ↓reduceIte]

/-! Item 180's crossed-block clause fires at ANY column, the sentinel's
    included — that is the whole point of the fourth reading — so the
    sentinel discharge now carries the clause's own `none` as a premise,
    and the kit below produces it from the local token facts the sites
    already track: an emitted array never holds two same-kind properties
    in one adjacent block (the canonical emitter writes no `&`/`!` at
    all), and each site knows the one token that ends its block. -/

/-- The block scan reports nothing over an array with no property tokens at
    all — the emitted arrays' case (the canonical emitter writes no `&`/`!`),
    stated over `getElem!` so out-of-range indices need no side condition. -/
lemma propsBlockScanLoop_no_props {tokens : Array (Positioned YamlToken)}
    (h : ∀ j : Nat, tokens[j]!.val.isNodeProperty = false) :
    ∀ n, propsBlockScanLoop tokens n = (false, false, none) := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    unfold propsBlockScanLoop
    simp only [h m, Bool.false_eq_true, ↓reduceIte]
    split
    · exact ih
    · rfl

/-- …so the trailing block has no excess there either, whatever arm the
    trailing run takes. -/
lemma crossedPropsExcessIdx?_none_of_no_props {tokens : Array (Positioned YamlToken)}
    (h : ∀ j : Nat, tokens[j]!.val.isNodeProperty = false) :
    crossedPropsExcessIdx? tokens = none := by
  unfold crossedPropsExcessIdx?
  split
  · rfl
  · rename_i i _
    simp only [h i, Bool.false_eq_true, ↓reduceIte,
      propsBlockScanLoop_no_props h]
    split
    · rfl
    · split <;> first | rfl | (split <;> rfl)

/-- The stream's seed has one real token, and `streamStart` is no property. -/
lemma crossedPropsExcessIdx?_init (input : String) :
    crossedPropsExcessIdx? ((ScannerState.mk' input).emit .streamStart).tokens = none := rfl

/-- The clause's position reading is `none` exactly where its index is. -/
lemma crossedPropsExcessPos?_none {tokens : Array (Positioned YamlToken)}
    (h : crossedPropsExcessIdx? tokens = none) :
    crossedPropsExcessPos? tokens = none := by
  unfold crossedPropsExcessPos?; rw [h]

/-- The break-crossing clause (item 182) keeps its crossing only AT an open
    level's own column, so it is `none` wherever no entry carries a column a
    token could stand at — the sentinel stack included. -/
lemma runLineCrossDanglingPos?_none_of_no_level {tokens : Array (Positioned YamlToken)}
    {indents : Array IndentEntry}
    (h : ∀ n : Nat, indents.any (fun e => e.column == (n : Int)) = false) :
    runLineCrossDanglingPos? tokens indents = none := by
  unfold runLineCrossDanglingPos?
  cases hq : runLineCrossPos? tokens with
  | none => rfl
  | some q => simp [h q.col]

/-- The no-props reading survives any non-property push. -/
lemma no_props_push {tokens : Array (Positioned YamlToken)} {p : Positioned YamlToken}
    (h : ∀ j : Nat, tokens[j]!.val.isNodeProperty = false)
    (hp : p.val.isNodeProperty = false) :
    ∀ j : Nat, (tokens.push p)[j]!.val.isNodeProperty = false := by
  intro j
  by_cases hj : j < tokens.size
  · rw [getElem!_pos _ j (by rw [Array.size_push]; omega), Array.getElem_push_lt hj]
    have := h j
    rwa [getElem!_pos _ j hj] at this
  · by_cases hj' : j = tokens.size
    · subst hj'
      rw [getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]
      exact hp
    · rw [getElem!_neg _ _ (by rw [Array.size_push]; omega)]
      decide

/-- …and the two placeholder reservations a key save may push. -/
lemma no_props_saveSimpleKey {s : ScannerState}
    (h : ∀ j : Nat, s.tokens[j]!.val.isNodeProperty = false) :
    ∀ j : Nat, (saveSimpleKey s).tokens[j]!.val.isNodeProperty = false := by
  unfold saveSimpleKey
  split
  · exact h
  · split
    · exact no_props_push (no_props_push h rfl) rfl
    · exact h

/-- A FILTERED `.val`-run pin bounds the unfiltered array's properties: a
    placeholder is no property, and everything else survives the filter into
    the pinned run. -/
lemma no_props_of_filtered_pin {tokens : Array (Positioned YamlToken)}
    {vs : Array YamlToken}
    (h_pin : (tokens.filter (fun t => t.val != .placeholder)).map (·.val) = vs)
    (h_vs : ∀ v ∈ vs, v.isNodeProperty = false) :
    ∀ j : Nat, tokens[j]!.val.isNodeProperty = false := by
  intro j
  by_cases hj : j < tokens.size
  · rw [getElem!_pos tokens j hj]
    by_cases hph : tokens[j].val = .placeholder
    · rw [hph]; rfl
    · refine h_vs _ ?_
      rw [← h_pin]
      refine Array.mem_map.mpr ⟨tokens[j], ?_, rfl⟩
      refine Array.mem_filter.mpr ⟨Array.getElem_mem hj, ?_⟩
      simpa using hph
  · rw [getElem!_neg tokens j hj]
    decide

/-- The same bridge from a LIST-level pin — the shape the §F whole-array
    wrappers hold their runs in. -/
lemma no_props_of_filtered_pin_list {tokens : Array (Positioned YamlToken)}
    {l : List YamlToken}
    (h_pin : (tokens.filter (fun t => t.val != .placeholder)).toList.map (·.val) = l)
    (h_l : ∀ v ∈ l, v.isNodeProperty = false) :
    ∀ j : Nat, tokens[j]!.val.isNodeProperty = false := by
  intro j
  by_cases hj : j < tokens.size
  · rw [getElem!_pos tokens j hj]
    by_cases hph : tokens[j].val = .placeholder
    · rw [hph]; rfl
    · refine h_l _ ?_
      rw [← h_pin]
      refine List.mem_map.mpr ⟨tokens[j], ?_, rfl⟩
      have : tokens[j] ∈ tokens.filter (fun t => t.val != .placeholder) :=
        Array.mem_filter.mpr ⟨Array.getElem_mem hj, by simpa using hph⟩
      simpa using this
  · rw [getElem!_neg tokens j hj]
    decide

/-- …and wherever the indent stack holds nothing but its sentinel: a token's
    column is a `Nat`, so it can never equal a negative entry.  Item 180: the
    crossed-block clause reads no column, so the sentinel no longer closes it —
    the clause's own `none` is the second premise, produced by the kit above
    from each site's token facts. -/
lemma danglingNodePos?_none_of_sentinel (s : ScannerState)
    (h : ∀ e ∈ s.indents, e.column < 0)
    (hx : crossedPropsExcessIdx? s.tokens = none) : danglingNodePos? s = none := by
  have hnone : ∀ n : Nat, s.indents.any (fun e => e.column == (n : Int)) = false := by
    intro n
    rw [Array.any_eq_false]
    intro i hi
    have := h s.indents[i] (Array.getElem_mem hi)
    simp only [beq_iff_eq]
    omega
  unfold danglingNodePos?
  simp only [hnone, Bool.false_eq_true, ↓reduceIte, ite_self,
    crossedPropsExcessPos?_none hx, runLineCrossDanglingPos?_none_of_no_level hnone]
  split
  · rfl
  · split <;> rfl

/-- The stream's seed carries the sentinel alone, so item 140's PRE-unwind
    reading is `none` at the first landing — the pre-state's own stack, which is
    what the two-state check now reads. -/
lemma init_indents_sentinel (input : String) :
    ((ScannerState.mk' input).emit YamlToken.streamStart).indents
      = #[{ column := -1, isSequence := false }] := rfl

/-- `danglingNodePos?` reads exactly three fields — the flow level, the token
    array and the indent stack — so two states that agree on them agree on the
    reading (item 140).  This is what `scanNextToken_eq_of_preprocess` needs now
    that the check is read off the PRE-unwind state: the whitespace-walk
    producers return all three equalities already. -/
lemma danglingNodePos?_congr {s₁ s₂ : ScannerState}
    (h_fl : s₁.flowLevel = s₂.flowLevel)
    (h_tok : s₁.tokens = s₂.tokens)
    (h_ind : s₁.indents = s₂.indents) :
    danglingNodePos? s₁ = danglingNodePos? s₂ := by
  simp only [danglingNodePos?, ScannerState.inFlow, h_fl, h_tok, h_ind]

lemma scanNextToken_checkDanglingNode_ok_of_inFlow (s_run s_land : ScannerState)
    (h : s_run.inFlow = true) :
    scanNextToken_checkDanglingNode s_run s_land = .ok () := by
  unfold scanNextToken_checkDanglingNode
  rw [danglingNodePos?_none_of_inFlow s_run h]
  split <;> rfl

lemma scanNextToken_checkDanglingNode_ok_of_sentinel (s_run s_land : ScannerState)
    (h : ∀ e ∈ s_run.indents, e.column < 0)
    (hx : crossedPropsExcessIdx? s_run.tokens = none) :
    scanNextToken_checkDanglingNode s_run s_land = .ok () := by
  unfold scanNextToken_checkDanglingNode
  rw [danglingNodePos?_none_of_sentinel s_run h hx]
  split <;> rfl

/-- …and on a run's own line, where the flag is down and a `:` may still
    resolve it. -/
lemma scanNextToken_checkDanglingNode_ok_of_keyNotAllowed (s_run s_land : ScannerState)
    (h : s_land.simpleKeyAllowed = false) :
    scanNextToken_checkDanglingNode s_run s_land = .ok () := by
  simp only [scanNextToken_checkDanglingNode, h, Bool.false_eq_true, ↓reduceIte]

lemma scanLoop_checkDanglingNode_ok_of_inFlow (s : ScannerState)
    (h : s.inFlow = true) : scanLoop_checkDanglingNode s = .ok () := by
  unfold scanLoop_checkDanglingNode
  rw [danglingNodePos?_none_of_inFlow s h]

lemma scanLoop_checkDanglingNode_ok_of_sentinel (s : ScannerState)
    (h : ∀ e ∈ s.indents, e.column < 0)
    (hx : crossedPropsExcessIdx? s.tokens = none) :
    scanLoop_checkDanglingNode s = .ok () := by
  unfold scanLoop_checkDanglingNode
  rw [danglingNodePos?_none_of_sentinel s h hx]

/-- A token array whose last token heads no node run — not a `[96]` property,
    not a one-token body, and not a flow COLLECTION's close — ends in no node
    run at all.  The block indicators are in this shape.

    **The flow closes are no longer** (item 159): a `]` finishes a node whose
    run starts back at the matching `[`, so `trailingNodeRun?` reads through it
    and this lemma has to say so.  What used to be free at a close is now the
    indent stack's business — see `scanLoop_checkDanglingNode_ok_of_sentinel`. -/
lemma trailingNodeRun?_push_none (ts : Array (Positioned YamlToken))
    (p : Positioned YamlToken)
    (hb : p.val.isNodeBody = false) (hp : p.val.isNodeProperty = false)
    (hc : p.val.isFlowClose = false)
    (hph : (p.val == YamlToken.placeholder) = false) :
    trailingNodeRun? (ts.push p) = none := by
  have hget : (ts.push p)[ts.size]! = p := by
    simp [Array.getElem_push]
  have hlast : prevRealIdx? (ts.push p) (ts.push p).size = some ts.size := by
    have hsz : (ts.push p).size = ts.size + 1 := Array.size_push ..
    rw [hsz]
    show (if (ts.push p)[ts.size]!.val == .placeholder then
            prevRealIdx? (ts.push p) ts.size else some ts.size) = some ts.size
    rw [hget, hph]
    rfl
  unfold trailingNodeRun?
  rw [hlast]
  simp only [hget, hb, hp, hc, Bool.false_eq_true, ↓reduceIte]

lemma danglingNodePos?_none_of_no_run (s : ScannerState)
    (h : trailingNodeRun? s.tokens = none) : danglingNodePos? s = none := by
  unfold danglingNodePos?
  split
  · rfl
  · rw [h]

lemma scanLoop_checkDanglingNode_ok_of_no_run (s : ScannerState)
    (h : trailingNodeRun? s.tokens = none) :
    scanLoop_checkDanglingNode s = .ok () := by
  unfold scanLoop_checkDanglingNode
  rw [danglingNodePos?_none_of_no_run s h]

/-- The sentinel-only stack, in the shape the emitter-scannability init lemmas
    return it. -/
lemma sentinel_only_columns_neg {s : ScannerState}
    (h : s.indents = #[{ column := -1, isSequence := false }]) :
    ∀ e ∈ s.indents, e.column < 0 := by
  intro e he
  rw [h] at he
  have : e = { column := -1, isSequence := false } := by simpa using he
  subst this
  decide

lemma scanNextToken_checkDanglingNode_ok_of_sentinel_stack (s_run s_land : ScannerState)
    (h : s_run.indents = #[{ column := -1, isSequence := false }])
    (hx : crossedPropsExcessIdx? s_run.tokens = none) :
    scanNextToken_checkDanglingNode s_run s_land = .ok () :=
  scanNextToken_checkDanglingNode_ok_of_sentinel s_run s_land
    (sentinel_only_columns_neg h) hx

lemma scanLoop_checkDanglingNode_ok_of_sentinel_stack (s : ScannerState)
    (h : s.indents = #[{ column := -1, isSequence := false }])
    (hx : crossedPropsExcessIdx? s.tokens = none) :
    scanLoop_checkDanglingNode s = .ok () :=
  scanLoop_checkDanglingNode_ok_of_sentinel s (sentinel_only_columns_neg h) hx

/-! #### Item 172: the §8.1 flow-value floor's discharge family

`underIndentedFlowValuePos?` is `danglingNodePos?`'s slot-offered complement,
and its discharges are the same four: a flow interior, a sentinel-only stack
(a `Nat` column never equals a negative entry), a token array ending in no
node run (a fortiori not in a flow close), and a landing whose break has not
come. -/

lemma underIndentedFlowValuePos?_none_of_inFlow (s : ScannerState)
    (h : s.inFlow = true) :
    underIndentedFlowValuePos? s = none := by
  simp only [underIndentedFlowValuePos?, h, ↓reduceIte]

lemma underIndentedFlowValuePos?_none_of_sentinel (s : ScannerState)
    (h : ∀ e ∈ s.indents, e.column < 0) : underIndentedFlowValuePos? s = none := by
  have hnone : ∀ n : Nat, s.indents.any (fun e => e.column == (n : Int)) = false := by
    intro n
    rw [Array.any_eq_false]
    intro i hi
    have := h s.indents[i] (Array.getElem_mem hi)
    simp only [beq_iff_eq]
    omega
  unfold underIndentedFlowValuePos?
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · simp only [hnone, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

lemma underIndentedFlowValuePos?_none_of_no_run (s : ScannerState)
    (h : trailingNodeRun? s.tokens = none) : underIndentedFlowValuePos? s = none := by
  cases hif : s.inFlow with
  | true => exact underIndentedFlowValuePos?_none_of_inFlow s hif
  | false =>
    cases hpr : prevRealIdx? s.tokens s.tokens.size with
    | none => simp [underIndentedFlowValuePos?, hif, hpr]
    | some i =>
      cases hcl : s.tokens[i]!.val.isFlowClose with
      | false => simp [underIndentedFlowValuePos?, hif, hpr, hcl]
      | true =>
        cases hprop : s.tokens[i]!.val.isNodeProperty with
        | true => simp [trailingNodeRun?, hpr, hprop] at h
        | false =>
          cases hbody : s.tokens[i]!.val.isNodeBody with
          | true => simp [trailingNodeRun?, hpr, hprop, hbody] at h
          | false =>
            cases hfo : flowOpenIdx? s.tokens i with
            | some o => simp [trailingNodeRun?, hpr, hprop, hbody, hcl, hfo] at h
            | none => simp [underIndentedFlowValuePos?, hif, hpr, hcl, hfo]

lemma underIndentedFlowValuePos?_congr {s₁ s₂ : ScannerState}
    (h_fl : s₁.flowLevel = s₂.flowLevel)
    (h_tok : s₁.tokens = s₂.tokens)
    (h_ind : s₁.indents = s₂.indents) :
    underIndentedFlowValuePos? s₁ = underIndentedFlowValuePos? s₂ := by
  simp only [underIndentedFlowValuePos?, ScannerState.inFlow, h_fl, h_tok, h_ind]

lemma scanNextToken_checkFlowValueIndent_ok_of_keyNotAllowed (s_run s_land : ScannerState)
    (h : s_land.simpleKeyAllowed = false) :
    scanNextToken_checkFlowValueIndent s_run s_land = .ok () := by
  simp only [scanNextToken_checkFlowValueIndent, h, Bool.false_eq_true, ↓reduceIte]

lemma scanNextToken_checkFlowValueIndent_ok_of_none (s_run s_land : ScannerState)
    (h : underIndentedFlowValuePos? s_run = none) :
    scanNextToken_checkFlowValueIndent s_run s_land = .ok () := by
  unfold scanNextToken_checkFlowValueIndent
  rw [h]
  split <;> rfl

lemma scanNextToken_checkFlowValueIndent_ok_of_inFlow (s_run s_land : ScannerState)
    (h : s_run.inFlow = true) :
    scanNextToken_checkFlowValueIndent s_run s_land = .ok () :=
  scanNextToken_checkFlowValueIndent_ok_of_none s_run s_land
    (underIndentedFlowValuePos?_none_of_inFlow s_run h)

lemma scanNextToken_checkFlowValueIndent_ok_of_sentinel (s_run s_land : ScannerState)
    (h : ∀ e ∈ s_run.indents, e.column < 0) :
    scanNextToken_checkFlowValueIndent s_run s_land = .ok () :=
  scanNextToken_checkFlowValueIndent_ok_of_none s_run s_land
    (underIndentedFlowValuePos?_none_of_sentinel s_run h)

lemma scanNextToken_checkFlowValueIndent_ok_of_sentinel_stack (s_run s_land : ScannerState)
    (h : s_run.indents = #[{ column := -1, isSequence := false }]) :
    scanNextToken_checkFlowValueIndent s_run s_land = .ok () :=
  scanNextToken_checkFlowValueIndent_ok_of_sentinel s_run s_land (sentinel_only_columns_neg h)

lemma scanNextToken_checkFlowValueIndent_ok_of_no_run (s_run s_land : ScannerState)
    (h : trailingNodeRun? s_run.tokens = none) :
    scanNextToken_checkFlowValueIndent s_run s_land = .ok () :=
  scanNextToken_checkFlowValueIndent_ok_of_none s_run s_land
    (underIndentedFlowValuePos?_none_of_no_run s_run h)

lemma scanLoop_checkFlowValueIndent_ok_of_none (s : ScannerState)
    (h : underIndentedFlowValuePos? s = none) :
    scanLoop_checkFlowValueIndent s = .ok () := by
  unfold scanLoop_checkFlowValueIndent
  rw [h]

lemma scanLoop_checkFlowValueIndent_ok_of_inFlow (s : ScannerState)
    (h : s.inFlow = true) : scanLoop_checkFlowValueIndent s = .ok () :=
  scanLoop_checkFlowValueIndent_ok_of_none s (underIndentedFlowValuePos?_none_of_inFlow s h)

lemma scanLoop_checkFlowValueIndent_ok_of_sentinel (s : ScannerState)
    (h : ∀ e ∈ s.indents, e.column < 0) :
    scanLoop_checkFlowValueIndent s = .ok () :=
  scanLoop_checkFlowValueIndent_ok_of_none s (underIndentedFlowValuePos?_none_of_sentinel s h)

lemma scanLoop_checkFlowValueIndent_ok_of_sentinel_stack (s : ScannerState)
    (h : s.indents = #[{ column := -1, isSequence := false }]) :
    scanLoop_checkFlowValueIndent s = .ok () :=
  scanLoop_checkFlowValueIndent_ok_of_sentinel s (sentinel_only_columns_neg h)

lemma scanLoop_checkFlowValueIndent_ok_of_no_run (s : ScannerState)
    (h : trailingNodeRun? s.tokens = none) :
    scanLoop_checkFlowValueIndent s = .ok () :=
  scanLoop_checkFlowValueIndent_ok_of_none s (underIndentedFlowValuePos?_none_of_no_run s h)

/-- Converse extraction: a `scanNextToken` that got past PREPROCESSING got past
    this check, because the check is the very next step.  Simpler than item
    132's twin, which has to clear the structural dispatch first. -/
lemma scanNextToken_ok_checkDanglingNode
    {s s_pp : ScannerState} {c : Char} {r : Option ScannerState}
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (h_snt : scanNextToken s = .ok r) :
    scanNextToken_checkDanglingNode s s_pp = .ok () := by
  cases h_dn : scanNextToken_checkDanglingNode s s_pp with
  | ok u => cases u; rfl
  | error e =>
    exfalso
    have h_err : scanNextToken s = .error e := by
      unfold scanNextToken; dsimp only []
      simp only [bind, Except.bind, h_pp, h_dn]
    rw [h_err] at h_snt
    injection h_snt

/-- The same converse for item 172's §8.1 flow-value floor: the check is the
    dangling check's immediate successor, so a `scanNextToken` that got past
    preprocessing got past it too. -/
lemma scanNextToken_ok_checkFlowValueIndent
    {s s_pp : ScannerState} {c : Char} {r : Option ScannerState}
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (h_snt : scanNextToken s = .ok r) :
    scanNextToken_checkFlowValueIndent s s_pp = .ok () := by
  cases h_fv : scanNextToken_checkFlowValueIndent s s_pp with
  | ok u => cases u; rfl
  | error e =>
    exfalso
    have h_err : scanNextToken s = .error e := by
      unfold scanNextToken; dsimp only []
      simp only [bind, Except.bind, h_pp,
        scanNextToken_ok_checkDanglingNode h_pp h_snt, h_fv]
    rw [h_err] at h_snt
    injection h_snt

/-- Item 132's §9.2 bare-document check is a no-op inside a flow collection —
    there is no document boundary to police there. -/
lemma scanNextToken_checkBareDocument_ok_of_inFlow (s : ScannerState)
    (h : s.inFlow = true) :
    scanNextToken_checkBareDocument s = .ok () := by
  simp only [scanNextToken_checkBareDocument, h, Bool.not_true, Bool.false_and,
             Bool.false_eq_true, ↓reduceIte]

/-- …and wherever the landing stands AT an open level's own column: the
    completed node is an ENTRY's and this landing is that collection's own next
    key, so what the level is exposed to is a dangler one token later rather
    than a second document.  Item 145 made this the check's own first conjunct;
    a block collection merely being open is no longer enough, because a landing
    right of every level is what `k:⏎␣␣"x"⏎␣␣b: 2` does. -/
lemma scanNextToken_checkBareDocument_ok_of_landingLevel (s : ScannerState)
    (h : s.indents.any (fun e => e.column == (s.col : Int)) = true) :
    scanNextToken_checkBareDocument s = .ok () := by
  simp only [scanNextToken_checkBareDocument, h, Bool.not_true, Bool.and_false,
             Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- …and on the completed node's OWN line, where the flag is down and the node
    is still readable as an implicit key. -/
lemma scanNextToken_checkBareDocument_ok_of_keyNotAllowed (s : ScannerState)
    (h : s.simpleKeyAllowed = false) :
    scanNextToken_checkBareDocument s = .ok () := by
  simp only [scanNextToken_checkBareDocument, h, Bool.and_false, Bool.false_and,
             Bool.false_eq_true, ↓reduceIte]

/-- …and wherever nothing behind the cursor completes a node — the emitter's
    own heads (properties, indicators, the markers) are all in this shape. -/
lemma scanNextToken_checkBareDocument_ok_of_last (s : ScannerState)
    (h : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false) :
    scanNextToken_checkBareDocument s = .ok () := by
  unfold scanNextToken_checkBareDocument
  cases hx : lastRealTokenVal? s.tokens with
  | none => simp
  | some t => simp [h t hx]

/-- Item 47's adjacent-value check is a no-op off the `:` (the emitter's
    content heads are quotes, property markers and plain heads the dumper
    keeps off `:`). -/
lemma scanNextToken_checkAdjacentValue_ok_of_ne_colon (s : ScannerState) {c : Char}
    (h : c ≠ ':') :
    scanNextToken_checkAdjacentValue s c = .ok () := by
  have hc : (c == ':') = false := by simpa using h
  simp only [scanNextToken_checkAdjacentValue, hc, Bool.and_false, Bool.false_and,
             Bool.false_eq_true, ↓reduceIte]

/-- …and a no-op whenever a break (or an indicator) has re-armed the
    simple-key flag — every line-start dispatch. -/
lemma scanNextToken_checkAdjacentValue_ok_of_allowed (s : ScannerState) (c : Char)
    (h : s.simpleKeyAllowed = true) :
    scanNextToken_checkAdjacentValue s c = .ok () := by
  simp only [scanNextToken_checkAdjacentValue, h, Bool.not_true, Bool.and_false,
             Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- Converse dp extraction (Fix B): if `scanNextToken` succeeded and the pipeline
    reached past structural dispatch, the pending-directives check must have
    passed, so `s_pp.directivesPresent = false`.  Lets consumers that already
    hold a `scanNextToken s = .ok r` witness discharge the new `h_ndp`
    hypothesis of the `scanNextToken_via_*_dispatch` lemmas without adding a
    dp hypothesis of their own. -/
lemma scanNextToken_ok_directivesPresent_false
    {s s_pp : ScannerState} {c : Char} {r : Option ScannerState}
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_snt : scanNextToken s = .ok r) :
    s_pp.directivesPresent = false := by
  cases h_dp : s_pp.directivesPresent
  · rfl
  · exfalso
    have h_check_err : scanNextToken_checkNoPendingDirectives s_pp
        = .error (.directiveWithoutDocument s_pp.line) := by
      simp only [scanNextToken_checkNoPendingDirectives, h_dp, ↓reduceIte]
    have h_err : scanNextToken s = .error (.directiveWithoutDocument s_pp.line) := by
      unfold scanNextToken; dsimp only []
      simp only [bind, Except.bind, h_pp,
        scanNextToken_ok_checkDanglingNode h_pp h_snt,
        scanNextToken_ok_checkFlowValueIndent h_pp h_snt, h_struct, h_check_err]
    rw [h_err] at h_snt
    injection h_snt

/-- The same converse for item 132's §9.2 check: a `scanNextToken` that got
    past the structural dispatch got past this check too, so a consumer holding
    an `.ok` witness discharges the `via_*` lemmas' `h_bare` for free — exactly
    as `scanNextToken_ok_directivesPresent_false` does for `h_ndp`. -/
lemma scanNextToken_ok_checkBareDocument
    {s s_pp : ScannerState} {c : Char} {r : Option ScannerState}
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_snt : scanNextToken s = .ok r) :
    scanNextToken_checkBareDocument s_pp = .ok () := by
  cases h_bd : scanNextToken_checkBareDocument s_pp with
  | ok u => cases u; rfl
  | error e =>
    exfalso
    have h_ndp : s_pp.directivesPresent = false :=
      scanNextToken_ok_directivesPresent_false h_pp h_struct h_snt
    have h_err : scanNextToken s = .error e := by
      unfold scanNextToken; dsimp only []
      simp only [bind, Except.bind, h_pp,
        scanNextToken_ok_checkDanglingNode h_pp h_snt,
        scanNextToken_ok_checkFlowValueIndent h_pp h_snt, h_struct,
        scanNextToken_checkNoPendingDirectives_ok _ h_ndp, h_bd]
    rw [h_err] at h_snt
    injection h_snt

/-- When preprocessing succeeds, structural dispatch returns none, and flow
    indicator dispatch produces a result, then scanNextToken returns that result.
    This captures the common case for flow indicator characters [`[`, `]`, `{`, `}`, `,`].

    `s_ad` is the state after the allowDirectives update, defined as:
    `if s_pp.allowDirectives then { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp` -/
lemma scanNextToken_via_flow_dispatch (s s_pp s_ad s_result : ScannerState) (c : Char)
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (h_fv : scanNextToken_checkFlowValueIndent s s_pp = .ok ())
    (h_flow : scanNextToken_dispatchFlowIndicators s_ad c = .ok (some s_result))
    (h_ndp : s_pp.directivesPresent = false)
    (h_bare : scanNextToken_checkBareDocument s_pp = .ok ())
    (h_dang : scanNextToken_checkDanglingNode s s_pp = .ok ()) :
    scanNextToken s = .ok (some s_result) := by
  unfold scanNextToken; dsimp only []
  simp only [bind, Except.bind, h_pp, h_dang, h_fv, h_struct, pure, Except.pure,
    scanNextToken_checkNoPendingDirectives_ok _ h_ndp, h_bare]
  -- After preprocessing and structural dispatch, the allowDirectives conditional
  -- and remaining dispatch stages are visible. Substitute s_ad.
  rw [← h_ad_eq]
  simp only [h_flow]

/-- Inversion of the flow-adjacency check (Fix A): a *successful* `scanNextToken`
    forces the folded `scanNextToken_checkFlowAdjacency` guard to have passed.
    Lets value-starter head-fact lemmas that already carry `h_snt`
    (`scanNextToken s = .ok (some s')`) discharge the folded check without an
    extra last-token precondition — the successful scan is the witness. -/
lemma checkFlowAdjacency_ok_of_scanNextToken_ok
    {s s_pp s_ad : ScannerState} {c : Char} {s' : ScannerState}
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (h_ndp : s_pp.directivesPresent = false)
    (h_snt : scanNextToken s = .ok (some s')) :
    scanNextToken_checkFlowAdjacency s_ad c = .ok () := by
  cases hc : scanNextToken_checkFlowAdjacency s_ad c with
  | ok u => rfl
  | error e =>
    exfalso
    have h_disp_err : scanNextToken_dispatchFlowIndicators s_ad c = .error e := by
      unfold scanNextToken_dispatchFlowIndicators; rw [hc]; simp only [bind, Except.bind]
    have h_snt_err : scanNextToken s = .error e := by
      unfold scanNextToken; dsimp only []
      simp only [bind, Except.bind, h_pp,
        scanNextToken_ok_checkDanglingNode h_pp h_snt,
        scanNextToken_ok_checkFlowValueIndent h_pp h_snt, h_struct, pure, Except.pure,
        scanNextToken_checkNoPendingDirectives_ok _ h_ndp,
        scanNextToken_ok_checkBareDocument h_pp h_struct h_snt]
      rw [← h_ad_eq]
      simp only [h_disp_err]
    rw [h_snt_err] at h_snt; exact absurd h_snt (by simp)

-- ═══ directivesPresent preservation helpers ═══
-- None of advance/emitAt/consumeNewline/skipSpaces/skipWhitespace/processEscape/
-- foldQuotedNewlines/collectDoubleQuotedLoop modify directivesPresent.

lemma advance_preserves_dp (s : ScannerState) :
    s.advance.directivesPresent = s.directivesPresent := by
  unfold ScannerState.advance
  split
  · simp only []
    split
    · rfl
    · split <;> rfl
  · rfl

lemma consumeNewline_preserves_dp (s : ScannerState) :
    (consumeNewline s).directivesPresent = s.directivesPresent := by
  unfold consumeNewline
  split
  · exact advance_preserves_dp s
  · dsimp only []
    split
    · exact advance_preserves_dp s
    · exact advance_preserves_dp s
  · rfl

lemma skipSpaces_preserves_dp (s : ScannerState) :
    (skipSpaces s).directivesPresent = s.directivesPresent := by
  unfold skipSpaces
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ fuel' IH =>
    unfold skipSpacesLoop; split
    · rw [IH, advance_preserves_dp]
    · rfl

lemma skipWhitespace_preserves_dp (s : ScannerState) :
    (skipWhitespace s).directivesPresent = s.directivesPresent := by
  unfold skipWhitespace
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ fuel' IH =>
    unfold skipWhitespaceLoop; split
    · split
      · rw [IH, advance_preserves_dp]
      · rfl
    · rfl

lemma emitAt_preserves_dp (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).directivesPresent = s.directivesPresent := by
  unfold ScannerState.emitAt; rfl

lemma collectHexDigitsLoop_preserves_dp (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.directivesPresent = s.directivesPresent := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ n' ih =>
    unfold collectHexDigitsLoop
    split
    · split
      · rw [ih, advance_preserves_dp]
      · rfl
    · rfl

lemma parseHexEscape_preserves_dp (s : ScannerState) (digits : Nat)
    (result : Char × ScannerState) (h : parseHexEscape s digits = .ok result) :
    result.snd.directivesPresent = s.directivesPresent := by
  unfold parseHexEscape at h
  simp only [] at h
  split at h
  · contradiction
  · split at h
    · injection h with h_eq; subst h_eq
      exact collectHexDigitsLoop_preserves_dp s "" digits
    · contradiction

lemma processEscape_preserves_dp (s : ScannerState) (result : Char × ScannerState)
    (h : processEscape s = .ok result) :
    result.snd.directivesPresent = s.directivesPresent := by
  unfold processEscape at h
  split at h <;> try contradiction
  split at h
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · simp only [] at h; exact parseHexEscape_preserves_dp _ _ _ h |>.trans (advance_preserves_dp s)
  · simp only [] at h; exact parseHexEscape_preserves_dp _ _ _ h |>.trans (advance_preserves_dp s)
  · simp only [] at h; exact parseHexEscape_preserves_dp _ _ _ h |>.trans (advance_preserves_dp s)
  · contradiction

lemma foldQuotedNewlinesLoop_preserves_dp (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.directivesPresent = s.directivesPresent := by
  induction fuel generalizing s emptyCount with
  | zero => unfold foldQuotedNewlinesLoop; rfl
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop
    simp only []
    split
    · split
      · split
        · rfl
        · rw [ih, consumeNewline_preserves_dp, skipWhitespace_preserves_dp]
      · rfl
    · rfl

lemma foldQuotedNewlines_preserves_dp (s : ScannerState) (result : String × ScannerState)
    (h : foldQuotedNewlines s = .ok result) :
    result.snd.directivesPresent = s.directivesPresent := by
  unfold foldQuotedNewlines at h
  simp only [] at h
  split at h
  · split at h <;> try contradiction
    split at h
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_dp, skipSpaces_preserves_dp,
            foldQuotedNewlinesLoop_preserves_dp, consumeNewline_preserves_dp]
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_dp, skipSpaces_preserves_dp,
            foldQuotedNewlinesLoop_preserves_dp, consumeNewline_preserves_dp]
  · split at h
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_dp, skipSpaces_preserves_dp,
            foldQuotedNewlinesLoop_preserves_dp, consumeNewline_preserves_dp]
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_dp, skipSpaces_preserves_dp,
            foldQuotedNewlinesLoop_preserves_dp, consumeNewline_preserves_dp]

lemma collectDoubleQuotedLoop_preserves_dp (s : ScannerState) (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    (result : String × ScannerState)
    (h : collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result) :
    result.snd.directivesPresent = s.directivesPresent := by
  -- protectedLen (default 0) generalised so the IH covers the fold shift (B2).
  suffices H : ∀ (p : Nat) (s : ScannerState) (content : String),
      collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd p = .ok result →
      result.snd.directivesPresent = s.directivesPresent by
    exact H 0 s content h
  clear h
  intro p s content h
  induction fuel generalizing s content p with
  | zero => unfold collectDoubleQuotedLoop at h; contradiction
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at h
    split at h <;> try contradiction
    · -- Case: peek? = some '"' - closing quote
      injection h with h_eq; subst h_eq
      exact advance_preserves_dp s
    · -- Case: peek? = some '\\' - escape sequence
      simp only [] at h
      split at h <;> try contradiction
      · split at h
        · -- Escaped line break — the landing is a fold (item 87)
          simp only [bind, Except.bind] at h
          split at h <;> try contradiction
          rename_i folded_result heq_fold
          have h_dp_efold := foldQuotedNewlines_preserves_dp _ _ heq_fold
          repeat' split at h
          all_goals first
            | contradiction
            | exact ih _ _ _ h |>.trans h_dp_efold
                |>.trans (advance_preserves_dp s)
        · -- Regular escape
          simp only [bind, Except.bind] at h
          split at h <;> try contradiction
          rename_i escape_result heq_escape
          have h_dp_escape := processEscape_preserves_dp _ _ heq_escape
          exact ih _ _ _ h |>.trans h_dp_escape |>.trans (advance_preserves_dp s)
    · -- Case: peek? = some c (other character)
      split at h
      · -- Line break: fold newlines
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i folded_result heq_fold
        have h_dp_fold := foldQuotedNewlines_preserves_dp _ _ heq_fold
        split at h <;> try contradiction
        split at h <;> try contradiction
        -- 4.32.0: `== " "` guard splits into recursive branches; close each via IH
        split at h <;> (first | (exact ih _ _ _ h |>.trans h_dp_fold) | contradiction)
      · -- Regular character
        split at h <;> try contradiction
        exact ih _ _ _ h |>.trans (advance_preserves_dp s)

-- scanDoubleQuoted preserves directivesPresent (structural — only tokens/offset/line/col change)
lemma scanDoubleQuoted_preserves_dp (s s' : ScannerState)
    (h_ok : scanDoubleQuoted s = .ok s') :
    s'.directivesPresent = s.directivesPresent := by
  unfold scanDoubleQuoted at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok <;> try contradiction
  rename_i result heq
  have h_dp_collect := collectDoubleQuotedLoop_preserves_dp _ _ _ _ _ _ _ _ heq
  split at h_ok
  · split at h_ok <;> try contradiction
    injection h_ok with h_eq; subst h_eq
    simp [emitAt_preserves_dp, h_dp_collect, advance_preserves_dp]
  · injection h_ok with h_eq; subst h_eq
    simp [emitAt_preserves_dp, h_dp_collect, advance_preserves_dp]

-- ═══ indents preservation helpers ═══
-- Structurally identical to directivesPresent: none of advance/emitAt/consumeNewline/
-- skipSpaces/skipWhitespace/processEscape/foldQuotedNewlines/collectDoubleQuotedLoop
-- modify indents.

lemma advance_preserves_indents (s : ScannerState) :
    s.advance.indents = s.indents := by
  unfold ScannerState.advance
  split
  · simp only []
    split
    · rfl
    · split <;> rfl
  · rfl

lemma consumeNewline_preserves_indents (s : ScannerState) :
    (consumeNewline s).indents = s.indents := by
  unfold consumeNewline
  split
  · exact advance_preserves_indents s
  · dsimp only []
    split
    · exact advance_preserves_indents s
    · exact advance_preserves_indents s
  · rfl

lemma skipSpaces_preserves_indents (s : ScannerState) :
    (skipSpaces s).indents = s.indents := by
  unfold skipSpaces
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ _ ih =>
    unfold skipSpacesLoop; split
    · rw [ih, advance_preserves_indents]
    · rfl

lemma skipWhitespace_preserves_indents (s : ScannerState) :
    (skipWhitespace s).indents = s.indents := by
  unfold skipWhitespace
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ _ ih =>
    unfold skipWhitespaceLoop; split
    · split
      · rw [ih, advance_preserves_indents]
      · rfl
    · rfl

lemma collectHexDigitsLoop_preserves_indents (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.indents = s.indents := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ _ ih =>
    unfold collectHexDigitsLoop
    split
    · split
      · rw [ih, advance_preserves_indents]
      · rfl
    · rfl

lemma parseHexEscape_preserves_indents (s : ScannerState) (digits : Nat)
    (result : Char × ScannerState) (h : parseHexEscape s digits = .ok result) :
    result.snd.indents = s.indents := by
  unfold parseHexEscape at h
  simp only [] at h
  split at h
  · contradiction
  · split at h
    · injection h with h_eq; subst h_eq
      exact collectHexDigitsLoop_preserves_indents s "" digits
    · contradiction

lemma processEscape_preserves_indents (s : ScannerState) (result : Char × ScannerState)
    (h : processEscape s = .ok result) :
    result.snd.indents = s.indents := by
  unfold processEscape at h
  split at h <;> try contradiction
  split at h
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · simp only [] at h; exact parseHexEscape_preserves_indents _ _ _ h |>.trans (advance_preserves_indents s)
  · simp only [] at h; exact parseHexEscape_preserves_indents _ _ _ h |>.trans (advance_preserves_indents s)
  · simp only [] at h; exact parseHexEscape_preserves_indents _ _ _ h |>.trans (advance_preserves_indents s)
  · contradiction

lemma foldQuotedNewlinesLoop_preserves_indents (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.indents = s.indents := by
  induction fuel generalizing s emptyCount with
  | zero => unfold foldQuotedNewlinesLoop; rfl
  | succ _ ih =>
    unfold foldQuotedNewlinesLoop
    simp only []
    split
    · split
      · split
        · rfl
        · rw [ih, consumeNewline_preserves_indents, skipWhitespace_preserves_indents]
      · rfl
    · rfl

lemma foldQuotedNewlines_preserves_indents (s : ScannerState) (result : String × ScannerState)
    (h : foldQuotedNewlines s = .ok result) :
    result.snd.indents = s.indents := by
  unfold foldQuotedNewlines at h
  simp only [] at h
  split at h
  · split at h <;> try contradiction
    split at h
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_indents, skipSpaces_preserves_indents,
            foldQuotedNewlinesLoop_preserves_indents, consumeNewline_preserves_indents]
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_indents, skipSpaces_preserves_indents,
            foldQuotedNewlinesLoop_preserves_indents, consumeNewline_preserves_indents]
  · split at h
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_indents, skipSpaces_preserves_indents,
            foldQuotedNewlinesLoop_preserves_indents, consumeNewline_preserves_indents]
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_indents, skipSpaces_preserves_indents,
            foldQuotedNewlinesLoop_preserves_indents, consumeNewline_preserves_indents]

lemma collectDoubleQuotedLoop_preserves_indents (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    (result : String × ScannerState)
    (h : collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result) :
    result.snd.indents = s.indents := by
  -- protectedLen (default 0) generalised so the IH covers the fold shift (B2).
  suffices H : ∀ (p : Nat) (s : ScannerState) (content : String),
      collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd p = .ok result →
      result.snd.indents = s.indents by
    exact H 0 s content h
  clear h
  intro p s content h
  induction fuel generalizing s content p with
  | zero => unfold collectDoubleQuotedLoop at h; contradiction
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at h
    split at h <;> try contradiction
    · -- closing quote
      injection h with h_eq; subst h_eq
      exact advance_preserves_indents s
    · -- escape
      simp only [] at h
      split at h <;> try contradiction
      · split at h
        · -- escaped line break — the landing is a fold (item 87)
          simp only [bind, Except.bind] at h
          split at h <;> try contradiction
          rename_i fold_result heq_fold
          repeat' split at h
          all_goals first
            | contradiction
            | exact (ih _ _ _ h).trans (foldQuotedNewlines_preserves_indents _ _ heq_fold)
                |>.trans (advance_preserves_indents s)
        · simp only [bind, Except.bind] at h
          split at h <;> try contradiction
          rename_i escape_result heq_escape
          cases escape_result
          exact (ih _ _ _ h).trans (processEscape_preserves_indents _ _ heq_escape)
                |>.trans (advance_preserves_indents s)
    · -- regular character
      split at h
      · simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq_fold
        split at h <;> try contradiction
        split at h <;> try contradiction
        -- 4.32.0: `== " "` guard splits into recursive branches; close each via IH
        split at h <;> (first | (exact (ih _ _ _ h).trans (foldQuotedNewlines_preserves_indents _ _ heq_fold)) | contradiction)
      · split at h <;> try contradiction
        exact (ih _ _ _ h).trans (advance_preserves_indents s)

lemma scanDoubleQuoted_preserves_indents (s s' : ScannerState)
    (h_ok : scanDoubleQuoted s = .ok s') :
    s'.indents = s.indents := by
  unfold scanDoubleQuoted at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok <;> try contradiction
  rename_i result heq
  have h_ids_collect := collectDoubleQuotedLoop_preserves_indents _ _ _ _ _ _ _ _ heq
  split at h_ok
  · split at h_ok <;> try contradiction
    injection h_ok with h_eq; subst h_eq
    unfold ScannerState.emitAt
    exact h_ids_collect.trans (advance_preserves_indents s)
  · injection h_ok with h_eq; subst h_eq
    unfold ScannerState.emitAt
    exact h_ids_collect.trans (advance_preserves_indents s)

-- ═══ explicitKeyLine preservation helpers ═══
-- Structurally identical to directivesPresent: none of advance/emitAt/consumeNewline/
-- skipSpaces/skipWhitespace/processEscape/foldQuotedNewlines/collectDoubleQuotedLoop
-- modify explicitKeyLine.

lemma consumeNewline_preserves_ek (s : ScannerState) :
    (consumeNewline s).explicitKeyLine = s.explicitKeyLine := by
  unfold consumeNewline
  split
  · exact advance_explicitKeyLine s
  · dsimp only []
    split
    · exact advance_explicitKeyLine s
    · exact advance_explicitKeyLine s
  · rfl

lemma skipSpaces_preserves_ek (s : ScannerState) :
    (skipSpaces s).explicitKeyLine = s.explicitKeyLine := by
  unfold skipSpaces
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ fuel' IH =>
    unfold skipSpacesLoop; split
    · rw [IH, advance_explicitKeyLine]
    · rfl

lemma skipWhitespace_preserves_ek (s : ScannerState) :
    (skipWhitespace s).explicitKeyLine = s.explicitKeyLine := by
  unfold skipWhitespace
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ fuel' IH =>
    unfold skipWhitespaceLoop; split
    · split
      · rw [IH, advance_explicitKeyLine]
      · rfl
    · rfl

lemma emitAt_preserves_ek (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).explicitKeyLine = s.explicitKeyLine := by
  unfold ScannerState.emitAt; rfl

lemma collectHexDigitsLoop_preserves_ek (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.explicitKeyLine = s.explicitKeyLine := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ n' ih =>
    unfold collectHexDigitsLoop
    split
    · split
      · rw [ih, advance_explicitKeyLine]
      · rfl
    · rfl

lemma parseHexEscape_preserves_ek (s : ScannerState) (digits : Nat)
    (result : Char × ScannerState) (h : parseHexEscape s digits = .ok result) :
    result.snd.explicitKeyLine = s.explicitKeyLine := by
  unfold parseHexEscape at h
  simp only [] at h
  split at h
  · contradiction
  · split at h
    · injection h with h_eq; subst h_eq
      exact collectHexDigitsLoop_preserves_ek s "" digits
    · contradiction

lemma processEscape_preserves_ek (s : ScannerState) (result : Char × ScannerState)
    (h : processEscape s = .ok result) :
    result.snd.explicitKeyLine = s.explicitKeyLine := by
  unfold processEscape at h
  split at h <;> try contradiction
  split at h
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · simp only [] at h; exact parseHexEscape_preserves_ek _ _ _ h |>.trans (advance_explicitKeyLine s)
  · simp only [] at h; exact parseHexEscape_preserves_ek _ _ _ h |>.trans (advance_explicitKeyLine s)
  · simp only [] at h; exact parseHexEscape_preserves_ek _ _ _ h |>.trans (advance_explicitKeyLine s)
  · contradiction

lemma foldQuotedNewlinesLoop_preserves_ek (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s emptyCount with
  | zero => unfold foldQuotedNewlinesLoop; rfl
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop
    simp only []
    split
    · split
      · split
        · rfl
        · rw [ih, consumeNewline_preserves_ek, skipWhitespace_preserves_ek]
      · rfl
    · rfl

lemma foldQuotedNewlines_preserves_ek (s : ScannerState) (result : String × ScannerState)
    (h : foldQuotedNewlines s = .ok result) :
    result.snd.explicitKeyLine = s.explicitKeyLine := by
  unfold foldQuotedNewlines at h
  simp only [] at h
  split at h
  · split at h <;> try contradiction
    split at h
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_ek, skipSpaces_preserves_ek,
            foldQuotedNewlinesLoop_preserves_ek, consumeNewline_preserves_ek]
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_ek, skipSpaces_preserves_ek,
            foldQuotedNewlinesLoop_preserves_ek, consumeNewline_preserves_ek]
  · split at h
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_ek, skipSpaces_preserves_ek,
            foldQuotedNewlinesLoop_preserves_ek, consumeNewline_preserves_ek]
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_ek, skipSpaces_preserves_ek,
            foldQuotedNewlinesLoop_preserves_ek, consumeNewline_preserves_ek]

lemma collectDoubleQuotedLoop_preserves_ek (s : ScannerState) (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    (result : String × ScannerState)
    (h : collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result) :
    result.snd.explicitKeyLine = s.explicitKeyLine := by
  -- protectedLen (default 0) generalised so the IH covers the fold shift (B2).
  suffices H : ∀ (p : Nat) (s : ScannerState) (content : String),
      collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd p = .ok result →
      result.snd.explicitKeyLine = s.explicitKeyLine by
    exact H 0 s content h
  clear h
  intro p s content h
  induction fuel generalizing s content p with
  | zero => unfold collectDoubleQuotedLoop at h; contradiction
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at h
    split at h <;> try contradiction
    · -- Case: peek? = some '"' - closing quote
      injection h with h_eq; subst h_eq
      exact advance_explicitKeyLine s
    · -- Case: peek? = some '\\' - escape sequence
      simp only [] at h
      split at h <;> try contradiction
      · split at h
        · -- Escaped line break — the landing is a fold (item 87)
          simp only [bind, Except.bind] at h
          split at h <;> try contradiction
          rename_i folded_result heq_fold
          repeat' split at h
          all_goals first
            | contradiction
            | exact ih _ _ _ h |>.trans (foldQuotedNewlines_preserves_ek _ _ heq_fold)
                |>.trans (advance_explicitKeyLine s)
        · -- Regular escape
          simp only [bind, Except.bind] at h
          split at h <;> try contradiction
          rename_i escape_result heq_escape
          exact ih _ _ _ h |>.trans (processEscape_preserves_ek _ _ heq_escape)
                |>.trans (advance_explicitKeyLine s)
    · -- Case: peek? = some c (other character)
      split at h
      · -- Line break: fold newlines
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i folded_result heq_fold
        split at h <;> try contradiction
        split at h <;> try contradiction
        -- 4.32.0: `== " "` guard splits into recursive branches; close each via IH
        split at h <;> (first | (exact ih _ _ _ h |>.trans (foldQuotedNewlines_preserves_ek _ _ heq_fold)) | contradiction)
      · -- Regular character
        split at h <;> try contradiction
        exact ih _ _ _ h |>.trans (advance_explicitKeyLine s)

-- scanDoubleQuoted preserves explicitKeyLine
lemma scanDoubleQuoted_preserves_ek (s s' : ScannerState)
    (h_ok : scanDoubleQuoted s = .ok s') :
    s'.explicitKeyLine = s.explicitKeyLine := by
  unfold scanDoubleQuoted at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok <;> try contradiction
  rename_i result heq
  have h_ek_collect := collectDoubleQuotedLoop_preserves_ek _ _ _ _ _ _ _ _ heq
  split at h_ok
  · split at h_ok <;> try contradiction
    injection h_ok with h_eq; subst h_eq
    simp [emitAt_preserves_ek, h_ek_collect, advance_explicitKeyLine]
  · injection h_ok with h_eq; subst h_eq
    simp [emitAt_preserves_ek, h_ek_collect, advance_explicitKeyLine]

-- Helper: lastRealTokenVal? on array.push tok when tok.val ≠ .placeholder returns tok.val.
-- Placed here (before scanDoubleQuoted_flow_ok) so it can be used in flow proofs.
lemma lastRealTokenVal_push_non_ph'
    (tokens : Array (Positioned YamlToken))
    (tok : Positioned YamlToken) (h_nph : tok.val ≠ .placeholder) :
    lastRealTokenVal? (tokens.push tok) = some tok.val := by
  unfold lastRealTokenVal?; dsimp only []
  simp only [Array.size_push, show tokens.size + 1 > 0 from by omega, ↓reduceIte,
    show tokens.size + 1 - 1 = tokens.size from by omega]
  rw [getElem!_pos _ _ (by simp [Array.size_push])]
  simp only [Array.getElem_push_eq]
  have : (tok.val == YamlToken.placeholder) = false :=
    beq_eq_false_iff_ne.mpr h_nph
  simp [this]

-- `scanDoubleQuoted` succeeds in flow context (inFlow = true) with trailing input.
-- Simpler than `scanDoubleQuoted_emitScalar_ok` because `validateTrailingContent` is skipped.
lemma scanDoubleQuoted_flow_ok (sc : ScannerState)
    (content : String) (rest : List Char)
    (hcorr : ScannerSurfCorr sc
      ⟨['"'] ++ (escapeString content).toList ++ ['"'] ++ rest, sc.col⟩)
    (h_flow : sc.inFlow = true) :
    ∃ s', scanDoubleQuoted sc = .ok s'
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = sc.flowLevel
      ∧ s'.directivesPresent = sc.directivesPresent
      ∧ s'.indents = sc.indents
      ∧ s'.explicitKeyLine = sc.explicitKeyLine
      ∧ s'.col > 0
      ∧ lastRealTokenVal? s'.tokens = some (.scalar content .doubleQuoted)
      ∧ s'.simpleKeyAllowed = false
      ∧ s'.line = sc.line := by
  -- Surface after advancing past opening quote
  have ⟨_, h_lt⟩ := peek_of_chars_cons sc '"'
    ((escapeString content).toList ++ ['"'] ++ rest) _ hcorr
  have hcorr_adv := advance_non_newline_corr sc '"'
    ((escapeString content).toList ++ ['"'] ++ rest) hcorr h_lt (by decide) (by decide)
  have h_col_eq : (sc.col + 1 : Nat) = sc.advance.col := hcorr_adv.col_eq
  rw [h_col_eq] at hcorr_adv
  -- Fuel bound for loop
  have h_fuel : sc.advance.inputEnd - sc.advance.offset + 1 ≥ content.toList.length + 1 := by
    rw [hcorr_adv.end_eq]
    have h_cf := CharsFromOffset_length_le hcorr_adv.chars_from
    simp only [List.length_append, List.length_singleton] at h_cf
    have h_esc := escapeString_length_ge content.toList
    simp only [String.ofList_toList] at h_esc
    omega
  -- Loop succeeds and leaves scanner at rest
  have h_ie : sc.inputEnd = sc.advance.inputEnd := by rw [advance_inputEnd]
  -- Rewrite to match loop lemma signature: (escapeString ...).toList ++ ['"'] ++ rest
  have h_corr_loop : ScannerSurfCorr sc.advance
      ⟨(escapeString (String.ofList content.toList)).toList ++ ['"'] ++ rest, sc.advance.col⟩ := by
    rw [String.ofList_toList]; exact hcorr_adv
  obtain ⟨s_after, h_loop, hcorr_loop, h_col_loop, h_line_loop⟩ :=
    collectDoubleQuotedLoop_escapeString_succeeds sc.advance content.toList rest "" _
      sc.currentPos sc.inFlow sc.currentIndent
      h_corr_loop h_fuel
  -- Content string
  have h_content_eq : "" ++ String.ofList content.toList = content := by
    apply String.ext; simp
  -- Token and field preservation
  have h_tok_pres : s_after.tokens = sc.tokens :=
    (ScannerCorrectness.ScanHelpers.collectDoubleQuotedLoop_preserves_tokens
      _ _ _ _ _ _ _ _ h_loop).trans
      (ScannerCorrectness.advance_preserves_tokens sc)
  have h_fl_pres : s_after.flowLevel = sc.flowLevel :=
    (ScannerPlainScalarValid.collectDoubleQuotedLoop_preserves_flowLevel
      _ _ _ _ _ _ _ _ h_loop).trans
      (ScannerCorrectness.advance_preserves_flowLevel sc)
  have h_dp_pres : s_after.directivesPresent = sc.directivesPresent :=
    (collectDoubleQuotedLoop_preserves_dp _ _ _ _ _ _ _ _ h_loop).trans
      (advance_preserves_dp sc)
  have h_ids_pres : s_after.indents = sc.indents :=
    (collectDoubleQuotedLoop_preserves_indents _ _ _ _ _ _ _ _ h_loop).trans
      (advance_preserves_indents sc)
  have h_ek_pres : s_after.explicitKeyLine = sc.explicitKeyLine :=
    (collectDoubleQuotedLoop_preserves_ek _ _ _ _ _ _ _ _ h_loop).trans
      (advance_explicitKeyLine sc)
  -- Build the result state
  let s_result := { (s_after.emitAt sc.currentPos (.scalar content .doubleQuoted))
                     with simpleKeyAllowed := false, needIndentCheck := false }
  refine ⟨s_result, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- scanDoubleQuoted sc = .ok s_result
    simp only [scanDoubleQuoted, bind, Except.bind]
    rw [h_ie]
    rw [h_content_eq] at h_loop
    rw [h_loop]
    simp only [h_flow, Bool.not_true]
    rfl
  · -- ScannerSurfCorr s_result ⟨rest, s_result.col⟩
    exact ⟨hcorr_loop.chars_from, hcorr_loop.col_eq, hcorr_loop.end_eq,
           hcorr_loop.input_prefix, hcorr_loop.indent_cols_nonneg⟩
  · -- flowLevel preserved
    show s_after.flowLevel = sc.flowLevel
    exact h_fl_pres
  · -- directivesPresent preserved
    show s_after.directivesPresent = sc.directivesPresent
    exact h_dp_pres
  · -- indents preserved
    show s_after.indents = sc.indents
    exact h_ids_pres
  · -- explicitKeyLine preserved
    show s_after.explicitKeyLine = sc.explicitKeyLine
    exact h_ek_pres
  · -- col > 0
    show s_after.col > 0
    exact h_col_loop
  · -- lastRealTokenVal? = .scalar content .doubleQuoted
    show lastRealTokenVal? (s_after.tokens.push _) = some (.scalar content .doubleQuoted)
    exact lastRealTokenVal_push_non_ph' s_after.tokens _ nofun
  · -- simpleKeyAllowed = false
    rfl
  · -- line preserved: s_result.line = sc.line
    show s_after.line = sc.line
    have h_line_adv : sc.advance.line = sc.line :=
      advance_line_of_peek sc '"' (by exact (peek_of_chars_cons sc '"' _ _ hcorr).2)
        (by exact (peek_of_chars_cons sc '"' _ _ hcorr).1) (by decide) (by decide)
    exact h_line_loop.trans h_line_adv

-- Helper: skipWhitespace is identity when first char is not whitespace
lemma skipWhitespace_of_not_ws (s : ScannerState) (c : Char)
    (h_pk : s.peek? = some c) (h_nws : isWhiteSpaceBool c = false)
    (h_more : s.offset < s.inputEnd) :
    skipWhitespace s = s := by
  unfold skipWhitespace
  obtain ⟨n, hn⟩ : ∃ n, s.inputEnd - s.offset = n + 1 :=
    ⟨s.inputEnd - s.offset - 1, by omega⟩
  rw [hn]; unfold skipWhitespaceLoop; simp [h_pk, h_nws]

-- Helper: skipSpaces is identity when first char is not a space
lemma skipSpaces_of_not_space (s : ScannerState) (c : Char)
    (h_pk : s.peek? = some c) (h_ns : c ≠ ' ') :
    skipSpaces s = s := by
  unfold skipSpaces
  cases h_fuel : (s.inputEnd - s.offset) with
  | zero => unfold skipSpacesLoop; rfl
  | succ n =>
    unfold skipSpacesLoop
    -- match s.peek? with | some ' ' => ... | _ => s
    split
    · -- s.peek? = some ' '
      rename_i h_peek
      rw [h_pk] at h_peek; exact absurd (Option.some.inj h_peek) h_ns
    · rfl

-- Helper: skipToContent is identity when first char is content (not ws/lb/comment)
lemma skipToContent_of_content_char (s : ScannerState) (c : Char)
    (h_pk : s.peek? = some c)
    (h_nws : isWhiteSpaceBool c = false)
    (h_nlb : isLineBreakBool c = false)
    (h_nc : c ≠ '#')
    (h_more : s.offset < s.inputEnd) :
    skipToContent s = .ok s := by
  have h_ns : c ≠ ' ' := by intro h; subst h; exact absurd h_nws (by decide)
  have h_nt : c ≠ '\t' := by intro h; subst h; exact absurd h_nws (by decide)
  -- First prove skipToContentWs returns .ok s
  have h_ws : skipToContentWs s = .ok s := by
    unfold skipToContentWs
    split
    · -- needIndentCheck = true: skipSpaces then tab check
      have h_ss := skipSpaces_of_not_space s c h_pk h_ns
      rw [h_ss]; dsimp only []
      split
      · -- at/below indent level: tab check
        -- match s.peek? with | some '\t' => ... | _ => .ok s
        split
        · rename_i h_peek; rw [h_pk] at h_peek
          exact absurd (Option.some.inj h_peek) h_nt
        · rfl
      · -- past indent boundary: skipWhitespace
        exact congrArg Except.ok (skipWhitespace_of_not_ws s c h_pk h_nws h_more)
    · -- needIndentCheck = false: just skipWhitespace
      exact congrArg Except.ok (skipWhitespace_of_not_ws s c h_pk h_nws h_more)
  unfold skipToContent
  obtain ⟨n, hn⟩ : ∃ n, s.inputEnd - s.offset + 1 = n + 1 :=
    ⟨s.inputEnd - s.offset, by omega⟩
  rw [hn]; unfold skipToContentLoop
  simp only [h_ws]
  unfold skipToContentComment; rw [h_pk]; simp [h_nc, h_pk, h_nlb]

-- Helper: saveSimpleKey preserves peek?
lemma saveSimpleKey_preserves_peek (s : ScannerState) :
    (saveSimpleKey s).peek? = s.peek? := by
  unfold saveSimpleKey
  split
  · rfl
  · split
    · dsimp only []; rfl
    · rfl

-- saveSimpleKey preserves all non-token/key fields
@[simp] lemma saveSimpleKey_preserves_input (s : ScannerState) :
    (saveSimpleKey s).input = s.input := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] lemma saveSimpleKey_preserves_offset (s : ScannerState) :
    (saveSimpleKey s).offset = s.offset := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] lemma saveSimpleKey_preserves_inputEnd (s : ScannerState) :
    (saveSimpleKey s).inputEnd = s.inputEnd := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] lemma saveSimpleKey_preserves_col (s : ScannerState) :
    (saveSimpleKey s).col = s.col := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] lemma saveSimpleKey_preserves_line (s : ScannerState) :
    (saveSimpleKey s).line = s.line := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] lemma saveSimpleKey_preserves_inFlow (s : ScannerState) :
    (saveSimpleKey s).inFlow = s.inFlow := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] lemma saveSimpleKey_preserves_indents (s : ScannerState) :
    (saveSimpleKey s).indents = s.indents := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] lemma saveSimpleKey_preserves_allowDirectives (s : ScannerState) :
    (saveSimpleKey s).allowDirectives = s.allowDirectives := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] lemma saveSimpleKey_preserves_directivesPresent (s : ScannerState) :
    (saveSimpleKey s).directivesPresent = s.directivesPresent := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] lemma saveSimpleKey_preserves_flowStack (s : ScannerState) :
    (saveSimpleKey s).flowStack = s.flowStack := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] lemma saveSimpleKey_preserves_needIndentCheck (s : ScannerState) :
    (saveSimpleKey s).needIndentCheck = s.needIndentCheck := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] lemma saveSimpleKey_preserves_flowLevel (s : ScannerState) :
    (saveSimpleKey s).flowLevel = s.flowLevel := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] lemma saveSimpleKey_preserves_ek (s : ScannerState) :
    (saveSimpleKey s).explicitKeyLine = s.explicitKeyLine := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] lemma saveSimpleKey_preserves_ekc (s : ScannerState) :
    (saveSimpleKey s).explicitKeyCol = s.explicitKeyCol := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] lemma saveSimpleKey_preserves_ekStack (s : ScannerState) :
    (saveSimpleKey s).explicitKeyStack = s.explicitKeyStack := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl

-- saveSimpleKey is the identity when simpleKeyAllowed = false and the
-- flow-context explicit-key guard doesn't fire (explicitKeyLine ≠ some line).
-- In our emitter context: inFlow = true, explicitKeyLine = none, simpleKeyAllowed = false.
lemma saveSimpleKey_id_of_flow_ska_false_ek_none (s : ScannerState)
    (h_flow : s.inFlow = true) (h_ska : s.simpleKeyAllowed = false)
    (h_ek : s.explicitKeyLine = none) :
    saveSimpleKey s = s := by
  unfold saveSimpleKey
  simp only [h_flow, h_ek, show (none == some s.line) = false from by rfl,
             Bool.true_and, Bool.false_eq_true, ite_false, h_ska]

/-- The emitter always writes `": "`: a blank after `:` is never a glued `[`/`{`, so the
    `[147]` refusal in `scanValueValidate` does not fire. -/
lemma flowGluedCollectionValue_false_of_peekAt_blank (s : ScannerState)
    (h : s.peekAt? 1 = some ' ') :
    flowGluedCollectionValue s = false := by
  simp [flowGluedCollectionValue, h]

-- scanValueValidate always succeeds in flow when simpleKey.possible is false
-- and explicitKeyLine is none: the key checks short-circuit on those two
-- fields, and item 48's same-line checks (B3/B4) are `!inFlow`-gated.
lemma scanValueValidate_ok_of_not_possible_ek_none (s : ScannerState)
    (h_flow : s.inFlow = true)
    (h_ek : s.explicitKeyLine = none)
    (h_sk : s.simpleKey.possible = false)
    (h_glued : flowGluedCollectionValue s = false) :
    scanValueValidate s = .ok () := by
  unfold scanValueValidate
  simp only [h_glued, h_sk, h_flow, Bool.not_true, Bool.false_and, Bool.and_false,
             ite_false, h_ek, reduceCtorEq]
  rfl

-- All tokens in the array have pos.line equal to a given line number.
-- This captures the invariant that the emitter produces single-line output.
def AllTokensOnLine (s : ScannerState) (l : Nat) : Prop :=
  ∀ i, (h : i < s.tokens.size) → s.tokens[i].pos.line = l

-- Convenience alias: simpleKey fields track the current line when possible.
-- Both endLine and pos.line are set from s.line by saveSimpleKey; strengthening
-- to a conjunction lets us transfer AllTokensOnLine through scanValuePrepare.
def EndLineOnLine (s : ScannerState) : Prop :=
  s.simpleKey.possible → s.simpleKey.endLine = s.line ∧ s.simpleKey.pos.line = s.line

-- Stack-level EndLineOnLine: the top of simpleKeyStack satisfies EndLineOnLine
-- at a given line. Used to prove EndLineOnLine after flow close restores from stack.
def StackEndLineOnLine (s : ScannerState) (l : Nat) : Prop :=
  match s.simpleKeyStack.back? with
  | none => True
  | some sk => sk.possible → sk.endLine = l ∧ sk.pos.line = l

/-- **The entry-boundary reading of a pending simple key (item 9p).**

    `scanValueValidate`'s T833 guard rejects a `:` whose pending simple key was
    reserved directly after a value indicator — `[a: b: c]`, `[a: : b]` and
    `[a: &x : b]` all reach that state, and it is exactly "this flow entry is
    already complete".  This is the hypothesis that says the reservation sits at
    an ENTRY BOUNDARY instead, which is what the emitter always produces: the
    slot before every key `{k: v, k: v}` saves is the `{` or the `,`.

    Read as an INDEX, not as a token history (Reflection 628): the discriminator
    is `simpleKey.tokenIndex`, because a flow entry's key may be a whole
    bracketed collection and no bounded lookback can find where it started. -/
def SavedKeyAtEntryBoundary (s : ScannerState) : Prop :=
  0 < s.simpleKey.tokenIndex →
    ∀ tok, s.tokens[s.simpleKey.tokenIndex - 1]? = some tok → tok.val ≠ .value

/-- The pair-list side of `SavedKeyAtEntryBoundary`: the token a pair's key scan
    is about to reserve *after*.  Stated on the FILTERED array because that is
    the shape the saved-key scans re-anchor to (their take-side conjunct), and
    because the two reservation placeholders a previous entry left behind are
    not what the boundary is about. -/
def PairStartAtEntryBoundary (s : ScannerState) : Prop :=
  ∀ tok, (s.tokens.filter (fun t => t.val != .placeholder)).toList.getLast? = some tok →
    tok.val ≠ .value

/-- A step that pushes one real token re-opens the entry boundary, provided that
    token is no value indicator: `{`, `[` and `,` all qualify, and they are
    exactly the three places a flow pair list starts a pair. -/
lemma pairStartAtEntryBoundary_of_filtered_push {s s' : ScannerState}
    {tok : Positioned YamlToken} (h_val : tok.val ≠ .value)
    (h_eq : s'.tokens.filter (fun t => t.val != .placeholder)
      = (s.tokens.filter (fun t => t.val != .placeholder)).push tok) :
    PairStartAtEntryBoundary s' := by
  intro t ht
  rw [h_eq] at ht
  simp only [Array.toList_push, List.getLast?_concat, Option.some.injEq] at ht
  exact ht ▸ h_val

/-- Preprocessing leaves the tokens alone, so it leaves the boundary alone. -/
lemma PairStartAtEntryBoundary.of_tokens_eq {s s' : ScannerState}
    (h_toks : s'.tokens = s.tokens) (h : PairStartAtEntryBoundary s) :
    PairStartAtEntryBoundary s' := by
  intro t ht; exact h t (by rw [← h_toks]; exact ht)

/-- **The entry-boundary bridge (item 9p).**  A saved-key scan reserves at the
    incoming array's end (`h_tidx`) and re-anchors the real tokens below that
    point to the incoming ones (`h_take`), so the slot the strictened T833 guard
    reads is the incoming array's last REAL token — and "this pair starts at an
    entry boundary" is exactly `PairStartAtEntryBoundary`.

    The `s.tokens.size` slot is the first reservation placeholder (`h_ph`), which
    is what lets the take-side equation, stated one past the reservation, be
    read back one short of it. -/
lemma savedKeyAtEntryBoundary_of_take {s s' : ScannerState}
    (h_tidx : s'.simpleKey.tokenIndex = s.tokens.size)
    (h_szlt : s.tokens.size + 1 < s'.tokens.size)
    (h_ph : ∀ (h : s.tokens.size < s'.tokens.size),
      (s'.tokens[s.tokens.size]'h).val = .placeholder)
    (h_take : (s'.tokens.toList.take (s.tokens.size + 1)).filter
        (fun t => t.val != .placeholder)
      = (s.tokens.filter (fun t => t.val != .placeholder)).toList)
    (h_pse : PairStartAtEntryBoundary s) :
    SavedKeyAtEntryBoundary s' := by
  intro hpos tok htok hval
  rw [h_tidx] at htok hpos
  -- The reservation slot itself is a placeholder, so the take-side equation
  -- stated one PAST the reservation can be read back one SHORT of it.
  have h_split : s'.tokens.toList.take (s.tokens.size + 1)
      = s'.tokens.toList.take s.tokens.size ++ [s'.tokens[s.tokens.size]'(by omega)] := by
    rw [List.take_add_one,
        List.getElem?_eq_getElem (by rw [Array.length_toList]; omega)]
    simp
  have h_take0 : (s'.tokens.toList.take s.tokens.size).filter (fun t => t.val != .placeholder)
      = (s.tokens.filter (fun t => t.val != .placeholder)).toList := by
    rw [h_split, List.filter_append] at h_take
    simpa [h_ph (by omega)] using h_take
  -- The guard's slot is the LAST element of that take, and it is real.
  have hsucc : s.tokens.size - 1 + 1 = s.tokens.size := by omega
  have hget : s'.tokens.toList[s.tokens.size - 1]? = some tok := by
    rw [List.getElem?_eq_getElem (by rw [Array.length_toList]; omega)]
    rw [Array.getElem?_eq_getElem (by omega)] at htok
    simpa using htok
  have h_split0 : s'.tokens.toList.take s.tokens.size
      = s'.tokens.toList.take (s.tokens.size - 1) ++ [tok] := by
    have h := List.take_add_one (i := s.tokens.size - 1) (l := s'.tokens.toList)
    rw [hsucc, hget] at h
    simpa using h
  have hfilt : List.filter (fun t : Positioned YamlToken => t.val != .placeholder) [tok] = [tok] := by
    simp [hval]
  rw [h_split0, List.filter_append, hfilt] at h_take0
  exact h_pse tok (by rw [← h_take0]; simp) hval

/-- The RAW reading of the pair-start boundary (item 9q): the incoming array's
    last slot is no value indicator.

    Weaker to establish than `PairStartAtEntryBoundary` and — crucially —
    weaker to *consume*: it needs only a raw prefix, not the take-side
    re-anchor.  That matters because `EmitScansInFlowSavedKey`, the substrate
    the plain and keyshape assemblers use, carries the reservation index but no
    take conjunct; the raw prefix it does carry comes from
    `FlowMonoChain_preserves_raw_prefix`, whose `SimpleKeyAboveFloor` premise
    is exactly what item 9q's normalization repaired.

    A placeholder satisfies it for free, so the two reservation slots a
    previous entry left behind are not in the way. -/
def LastRawNotValue (s : ScannerState) : Prop :=
  ∀ tok, s.tokens[s.tokens.size - 1]? = some tok → tok.val ≠ .value

/-- **The entry-boundary bridge, raw-prefix form (item 9q).**  A saved-key scan
    reserves at the incoming array's end, so the slot the strictened T833 guard
    reads is the incoming array's own last slot — unchanged by the scan,
    because the scan only ever pushes. -/
lemma savedKeyAtEntryBoundary_of_raw_prefix {s s' : ScannerState}
    (h_tidx : s'.simpleKey.tokenIndex = s.tokens.size)
    (h_mono : s.tokens.size ≤ s'.tokens.size)
    (h_raw : ∀ i (h : i < s.tokens.size), s'.tokens[i]'(by omega) = s.tokens[i])
    (h_lrv : LastRawNotValue s) :
    SavedKeyAtEntryBoundary s' := by
  intro hpos tok htok
  rw [h_tidx] at hpos htok
  have hlt : s.tokens.size - 1 < s.tokens.size := by omega
  rw [Array.getElem?_eq_getElem (by omega)] at htok
  have heq : tok = s.tokens[s.tokens.size - 1]'hlt :=
    (Option.some.inj htok).symm.trans (h_raw _ hlt)
  rw [heq]
  exact h_lrv _ (by rw [Array.getElem?_eq_getElem hlt])

/-- Preprocessing leaves the tokens alone, so it leaves the raw boundary alone. -/
lemma LastRawNotValue.of_tokens_eq {s s' : ScannerState}
    (h_toks : s'.tokens = s.tokens) (h : LastRawNotValue s) : LastRawNotValue s' := by
  intro tok htok; exact h tok (by rw [← h_toks]; exact htok)

/-- A step that pushes one non-`.value` token re-opens the raw boundary: `{`,
    `[` and `,` all qualify, and they are exactly the three places a flow pair
    list starts a pair. -/
lemma lastRawNotValue_of_push {s s' : ScannerState} {tok : Positioned YamlToken}
    (h_val : tok.val ≠ .value) (h_eq : s'.tokens = s.tokens.push tok) :
    LastRawNotValue s' := by
  intro t ht
  rw [h_eq] at ht
  simp only [Array.size_push, Nat.add_sub_cancel, Array.getElem?_push_size,
    Option.some.injEq] at ht
  exact ht ▸ h_val

/-! ### Item 9q's payoff: the flow `,` no longer blocks the tower

Before the normalization, `scanFlowEntry` left `simpleKey.possible = true`
pointing at the PREVIOUS entry's reservation — below the incoming array's end,
and so below any bound a pair-list assembler wants to re-anchor at.  That
falsified `SimpleKeyAboveFloor`, the premise every prefix-preservation lemma in
the tower (`FlowMonoChain_preserves_raw_prefix` and everything above it) goes
through, at exactly one state: `emitPairList_scans_nonempty`'s recursion tail.
The two lemmas below are that state's repair, stated in the shape the
assemblers consume. -/

/-- The `,` leaves no pending key, so the current-key conjunct of
    `SimpleKeyAboveFloor` holds at EVERY bound — including the outgoing array's
    own end, which is the bound a pair-list assembler re-anchors at and the one
    that used to fail here. -/
lemma flowEntry_simpleKey_above_any (s s' : ScannerState)
    (h_entry : scanFlowEntry s = .ok s') (n : Nat) :
    s'.simpleKey.possible = true → s'.simpleKey.tokenIndex ≥ n := fun hp =>
  absurd hp (by rw [ScannerCorrectness.scanFlowEntry_clears_simpleKey s _ h_entry]; decide)

/-- …hence the full `SimpleKeyAboveFloor` after a `,` needs nothing at all
    about the incoming pending key — only the stack, which the `,` preserves. -/
lemma simpleKeyAboveFloor_of_scanFlowEntry (s s' : ScannerState)
    (h_entry : scanFlowEntry s = .ok s') (n fl₀ : Nat)
    (h_stack : ∀ j, fl₀ ≤ j → (hj : j < s.simpleKeyStack.size) →
      s.simpleKeyStack[j].possible = true → s.simpleKeyStack[j].tokenIndex ≥ n)
    (h_size : s.simpleKeyStack.size ≥ fl₀) :
    SimpleKeyAboveFloor s' n fl₀ := by
  have h_st := ScannerCorrectness.scanFlowEntry_preserves_simpleKeyStack s _ h_entry
  refine ⟨flowEntry_simpleKey_above_any s s' h_entry n, fun j hfl hj hp => ?_, ?_⟩
  · simp only [h_st] at hj hp ⊢; exact h_stack j hfl hj hp
  · rw [h_st]; exact h_size

-- scanValueValidate succeeds in flow context when endLine = line (when
-- possible) and the pending key's reservation sits at an entry boundary.
--
-- Item 9r replaced the `AllTokensOnLine` premise on the T833 arm with
-- `SavedKeyAtEntryBoundary`.  The old guard fired only ACROSS LINES, which is
-- why "every token is on the scanner's line" discharged it; the strictened
-- guard fires on the boundary itself, so what has to be supplied is the
-- boundary — see `savedKeyAtEntryBoundary_of_take` and
-- `savedKeyAtEntryBoundary_of_raw_prefix` above, which produce it from the
-- saved-key scans' layout exposures.  (The name keeps its historical
-- `allTokensOnLine` suffix so the sixteen call sites read as one-token edits.)
lemma scanValueValidate_ok_of_flow_allTokensOnLine (s : ScannerState)
    (h_flow : s.inFlow = true)
    (h_ek : s.explicitKeyLine = none)
    (h_entry : SavedKeyAtEntryBoundary s)
    (h_end : EndLineOnLine s)
    (h_glued : flowGluedCollectionValue s = false) :
    scanValueValidate s = .ok () := by
  unfold scanValueValidate EndLineOnLine SavedKeyAtEntryBoundary at *
  cases h_poss : s.simpleKey.possible
  · -- possible = false: all checks short-circuit
    simp only [h_glued, h_flow, Bool.false_and, Bool.not_true, Bool.and_false,
               ite_false, h_ek, reduceCtorEq]; rfl
  · -- possible = true: endLine = line from h_end
    have ⟨h_el, _⟩ := h_end h_poss
    -- Checks 1,3: !inFlow = false.  Check 2: endLine = line.  Check 5: ek = none.
    simp only [h_glued, h_flow, h_el, h_ek, Bool.not_true, Bool.and_false, Bool.false_and,
               Bool.true_and, bne_self_eq_false, ite_false, reduceCtorEq]
    -- Check 4: possible && inFlow && tokenIndex > 0 && slot below is `.value`
    by_cases h_ti : s.simpleKey.tokenIndex > 0
    · simp only [show (decide (s.simpleKey.tokenIndex > 0)) = true from decide_eq_true h_ti]
      -- Case analysis on `s.tokens[tokenIndex - 1]?`
      cases h_tok : s.tokens[s.simpleKey.tokenIndex - 1]? with
      | none => rfl -- no token at that index: check passes trivially
      | some tok =>
        have h_ne : tok.val ≠ .value := h_entry h_ti tok h_tok
        simp only [show (tok.val == YamlToken.value) = false from
                     beq_eq_false_iff_ne.mpr h_ne]
        rfl
    · simp only [show (decide (s.simpleKey.tokenIndex > 0)) = false from
                   decide_eq_false (by omega)]; rfl

-- saveSimpleKey only adds placeholder tokens, so filtering them out is invariant.
lemma saveSimpleKey_filter_placeholder (s : ScannerState) :
    (saveSimpleKey s).tokens.filter (fun t => t.val != .placeholder)
    = s.tokens.filter (fun t => t.val != .placeholder) := by
  unfold saveSimpleKey
  split
  · rfl
  · split
    · dsimp only []
      simp
    · rfl

-- ═══ AllTokensOnLine transfer lemmas ═══

/-- Pushing one token at `currentPos` preserves AllTokensOnLine. -/
lemma AllTokensOnLine_emit (s : ScannerState) (tok : YamlToken) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_line : s.line = l) :
    AllTokensOnLine (s.emit tok) l := by
  intro i h_bound
  unfold ScannerState.emit at h_bound ⊢; dsimp only [] at h_bound ⊢
  simp only [Array.getElem_push]; split
  · exact h_atol i (by assumption)
  · simp [ScannerState.currentPos, h_line]

/-- Advancing preserves AllTokensOnLine (tokens unchanged). -/
lemma AllTokensOnLine_advance (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) :
    AllTokensOnLine s.advance l := by
  intro i h_bound
  simp only [ScannerCorrectness.advance_preserves_tokens s] at h_bound ⊢
  exact h_atol i h_bound

/-- saveSimpleKey preserves AllTokensOnLine (pushes 0 or 2 placeholders at currentPos). -/
lemma AllTokensOnLine_saveSimpleKey (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_line : s.line = l) :
    AllTokensOnLine (saveSimpleKey s) l := by
  unfold saveSimpleKey
  split
  · exact h_atol
  · split
    · -- simpleKeyAllowed: pushes 2 placeholders at currentPos
      intro i h_bound
      simp only [] at h_bound ⊢
      simp only [Array.getElem_push]
      split
      · split
        · exact h_atol i (by omega)
        · simp [ScannerState.currentPos, h_line]
      · simp [ScannerState.currentPos, h_line]
    · exact h_atol

/-- saveSimpleKey establishes EndLineOnLine in flow context.
    Both endLine and pos.line are set from s.line when saving. -/
lemma EndLineOnLine_saveSimpleKey_flow (s : ScannerState)
    (h_prev : EndLineOnLine s) :
    EndLineOnLine (saveSimpleKey s) := by
  unfold EndLineOnLine saveSimpleKey
  split
  · exact h_prev
  · split
    · intro _; constructor
      · -- endLine = line: by definition, saveSimpleKey sets endLine := st.line
        rfl
      · -- pos.line = line: currentPos.line = line by definition
        show s.currentPos.line = s.line
        unfold ScannerState.currentPos; rfl
    · exact h_prev

/-- emitAt with a pos on line l preserves AllTokensOnLine. -/
lemma AllTokensOnLine_emitAt (s : ScannerState) (pos : YamlPos) (tok : YamlToken) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_pos_line : pos.line = l) :
    AllTokensOnLine (s.emitAt pos tok) l := by
  intro i h_bound
  unfold ScannerState.emitAt at h_bound ⊢; dsimp only [] at h_bound ⊢
  simp only [Array.getElem_push]; split
  · exact h_atol i (by assumption)
  · simp [h_pos_line]

-- ═══ AllTokensOnLine through scan operations ═══
-- Each flow-scan helper composes emit + advance (token-only changes).
-- Struct updates (flowLevel, simpleKeyAllowed, etc.) don't touch tokens
-- and are transparent to AllTokensOnLine by definitional equality.

/-- scanFlowSequenceStart preserves AllTokensOnLine. -/
lemma AllTokensOnLine_scanFlowSequenceStart (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_line : s.line = l) :
    AllTokensOnLine (scanFlowSequenceStart s) l := by
  unfold scanFlowSequenceStart
  exact AllTokensOnLine_advance _ l (AllTokensOnLine_emit _ _ l h_atol h_line)

/-- scanFlowMappingStart preserves AllTokensOnLine. -/
lemma AllTokensOnLine_scanFlowMappingStart (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_line : s.line = l) :
    AllTokensOnLine (scanFlowMappingStart s) l := by
  unfold scanFlowMappingStart
  exact AllTokensOnLine_advance _ l (AllTokensOnLine_emit _ _ l h_atol h_line)

/-- scanFlowSequenceStart sets simpleKey.possible to false. -/
lemma scanFlowSequenceStart_simpleKey_not_possible (s : ScannerState) :
    (scanFlowSequenceStart s).simpleKey.possible = false := by
  unfold scanFlowSequenceStart ScannerState.emit ScannerState.advance
  dsimp only []; split <;> (try split) <;> (try split) <;> rfl

/-- scanFlowMappingStart sets simpleKey.possible to false. -/
lemma scanFlowMappingStart_simpleKey_not_possible (s : ScannerState) :
    (scanFlowMappingStart s).simpleKey.possible = false := by
  unfold scanFlowMappingStart ScannerState.emit ScannerState.advance
  dsimp only []; split <;> (try split) <;> (try split) <;> rfl

/-- scanFlowSequenceEnd preserves AllTokensOnLine. -/
lemma AllTokensOnLine_scanFlowSequenceEnd (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_line : s.line = l) :
    AllTokensOnLine (scanFlowSequenceEnd s) l := by
  unfold scanFlowSequenceEnd
  exact AllTokensOnLine_advance _ l (AllTokensOnLine_emit _ _ l h_atol h_line)

/-- scanFlowMappingEnd preserves AllTokensOnLine. -/
lemma AllTokensOnLine_scanFlowMappingEnd (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_line : s.line = l) :
    AllTokensOnLine (scanFlowMappingEnd s) l := by
  unfold scanFlowMappingEnd
  exact AllTokensOnLine_advance _ l (AllTokensOnLine_emit _ _ l h_atol h_line)

/-- scanFlowEntry preserves AllTokensOnLine
    (emit .flowEntry → advance → set simpleKeyAllowed). -/
lemma AllTokensOnLine_scanFlowEntry (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_line : s.line = l) :
    AllTokensOnLine ({ (s.emit .flowEntry).advance with simpleKeyAllowed := true, explicitKeyLine := none, simpleKey := { possible := false } }) l := by
  exact AllTokensOnLine_advance _ l (AllTokensOnLine_emit _ _ l h_atol h_line)

/-- allowDirectives struct update preserves AllTokensOnLine (no token changes). -/
lemma AllTokensOnLine_allowDirectives (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) :
    AllTokensOnLine (if s.allowDirectives then
        { s with allowDirectives := false, documentEverStarted := true } else s) l := by
  split <;> exact h_atol

/-- scanValuePrepare in flow context preserves AllTokensOnLine.
    When simpleKey.possible, setIfInBounds replaces a token whose new pos.line
    equals the current line (from EndLineOnLine's pos.line conjunct). -/
lemma AllTokensOnLine_scanValuePrepare_flow (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_line : s.line = l)
    (h_flow : s.inFlow = true)
    (h_ek : s.explicitKeyLine = none)
    (h_endline : EndLineOnLine s) :
    AllTokensOnLine (scanValuePrepare s) l := by
  unfold AllTokensOnLine scanValuePrepare
  cases h_poss : s.simpleKey.possible <;> simp only [ite_true]
  · -- possible = false: explicitKeyLine = none, inFlow = true → identity
    simp only [h_ek, Option.isSome_none, ite_false,
               h_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    intro i h_bound
    exact h_atol i h_bound
  · -- possible = true: flow branch uses setIfInBounds
    simp only [h_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    intro i h_bound
    have h_bound' : i < s.tokens.size := by
      rwa [Array.size_setIfInBounds] at h_bound
    rw [Array.getElem_setIfInBounds h_bound']
    by_cases h_eq : s.simpleKey.tokenIndex + 1 = i
    · subst h_eq; simp only [↓reduceIte]
      have ⟨_, h_pl⟩ := h_endline h_poss
      exact h_pl.trans h_line
    · simp only [h_eq, ↓reduceIte]
      exact h_atol i h_bound'

/-- scanDoubleQuoted preserves AllTokensOnLine: the loop doesn't add tokens,
    and emitAt pushes one token at currentPos.line = s.line. -/
lemma AllTokensOnLine_scanDoubleQuoted (s s' : ScannerState)
    (h_ok : scanDoubleQuoted s = .ok s')
    (h_flow : s.inFlow = true)
    (l : Nat) (h_atol : AllTokensOnLine s l) (h_line : s.line = l) :
    AllTokensOnLine s' l := by
  unfold scanDoubleQuoted at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok <;> try contradiction
  rename_i result heq
  split at h_ok
  · -- block context: impossible since h_flow says inFlow = true
    exfalso; simp [h_flow] at *
  · -- flow context
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    apply AllTokensOnLine_emitAt
    · intro i h_bound
      have h_toks : result.snd.tokens = s.tokens :=
        (ScannerCorrectness.ScanHelpers.collectDoubleQuotedLoop_preserves_tokens
          _ _ _ _ _ _ _ _ heq).trans
          (ScannerCorrectness.advance_preserves_tokens s)
      simp only [h_toks] at h_bound ⊢
      exact h_atol i h_bound
    · simp [ScannerState.currentPos, h_line]

/-- scanDoubleQuoted preserves simpleKey: the loop, advance, and emitAt
    don't modify simpleKey. -/
lemma scanDoubleQuoted_preserves_simpleKey (s s' : ScannerState)
    (h_ok : scanDoubleQuoted s = .ok s') :
    s'.simpleKey = s.simpleKey :=
  ScannerCorrectness.scanDoubleQuoted_preserves_simpleKey s s' h_ok

-- ═══ Factored preprocessing for initial scanner state ═══

/-- Preprocessing on the initial scanner state returns the first character.

    For any non-empty input string starting with a non-blank, non-comment,
    non-line-break character `c`, preprocessing the initial state
    `(ScannerState.mk' input).emit .streamStart` succeeds and returns
    `(s_pp, c)` with all position/metadata fields preserved.

    This is the common first step for all `scanNextToken_emit*_init` proofs. -/
lemma scanNextToken_preprocess_init_state (input : String) (c : Char)
    (rest : List Char)
    (h_toList : input.toList = c :: rest)
    (h_nws : isWhiteSpaceBool c = false)
    (h_nlb : isLineBreakBool c = false)
    (h_nc : c ≠ '#') :
    ∃ s_pp, scanNextToken_preprocess ((ScannerState.mk' input).emit .streamStart)
          = .ok (some (s_pp, c))
      ∧ s_pp.flowLevel = 0
      ∧ s_pp.inFlow = false
      ∧ s_pp.currentIndent = -1
      ∧ s_pp.col = 0
      ∧ s_pp.allowDirectives = true
      ∧ s_pp.directivesPresent = false
      ∧ s_pp.indents = #[{column := -1, isSequence := false}]
      ∧ s_pp.input = input
      ∧ s_pp.offset = 0
      ∧ s_pp.inputEnd = input.utf8ByteSize
      ∧ s_pp.explicitKeyLine = none
      ∧ s_pp.line = 0
      ∧ AllTokensOnLine s_pp s_pp.line
      ∧ scanNextToken_checkBareDocument s_pp = .ok ()
      ∧ s_pp.tokens.filter (fun t => t.val != .placeholder)
          = ((ScannerState.mk' input).emit .streamStart).tokens.filter
              (fun t => t.val != .placeholder) := by
  -- Build ScannerSurfCorr for the initial state
  have h_chars := chars_from_zero_toList input
  rw [h_toList] at h_chars
  have h_corr₀ := initial_corr input _ h_chars
  have h_corr_s₀ : ScannerSurfCorr
      ((ScannerState.mk' input).emit .streamStart) ⟨c :: rest, 0⟩ :=
    ScannerSurfCorr_transfer h_corr₀ rfl rfl rfl rfl rfl
  have ⟨h_pk₀, _⟩ := peek_of_chars_cons _ c _ 0 h_corr_s₀
  have h_size : input.utf8ByteSize ≥ 1 := by
    rw [utf8ByteSize_eq_listByteSize, h_toList, listByteSize]
    have := Char.utf8Size_pos c; omega
  -- skipToContent is identity (c is not whitespace/linebreak/comment)
  have h_stc : skipToContent ((ScannerState.mk' input).emit .streamStart)
      = .ok ((ScannerState.mk' input).emit .streamStart) :=
    skipToContent_of_content_char _ c h_pk₀ h_nws h_nlb h_nc (by omega)
  -- Construct the witness
  refine ⟨saveSimpleKey { (ScannerState.mk' input).emit .streamStart
    with needIndentCheck := false },
    ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by exact AllTokensOnLine_saveSimpleKey _ 0
         (AllTokensOnLine_emit _ _ 0
           (by intro i h_bound; have : 0 = (ScannerState.mk' input).tokens.size := rfl; omega) rfl)
         rfl,
    -- §9.2 bare-document check (item 132): `streamStart` completes nothing.
    by refine scanNextToken_checkBareDocument_ok_of_last _ ?_
       unfold saveSimpleKey
       split
       · simp [ScannerState.emit, ScannerState.mk', lastRealTokenVal?,
               YamlToken.completesFlowValue]
       · split
         · simp [ScannerState.emit, ScannerState.mk', lastRealTokenVal?,
                 YamlToken.completesFlowValue]
         · simp [ScannerState.emit, ScannerState.mk', lastRealTokenVal?,
                 YamlToken.completesFlowValue],
    saveSimpleKey_filter_placeholder _⟩
  -- Prove: scanNextToken_preprocess = .ok (some (saveSimpleKey {...}, c))
  unfold scanNextToken_preprocess
  rw [h_stc]; simp only [bind, Except.bind, pure, Except.pure]
  have h_hm : ((ScannerState.mk' input).emit .streamStart).hasMore = true := by
    unfold ScannerState.hasMore; exact decide_eq_true (by omega)
  simp only [h_hm, Bool.not_true, Bool.false_eq_true, ite_false]
  -- unwindIndents is identity since currentIndent = -1 < col = 0
  have h_uwi : unwindIndents ((ScannerState.mk' input).emit .streamStart)
      ↑((ScannerState.mk' input).emit .streamStart).col
      = (ScannerState.mk' input).emit .streamStart := by
    unfold unwindIndents unwindIndentsLoop; split <;> rfl
  simp only [h_uwi]
  -- inFlow = false, needIndentCheck = true → enters the branch
  have h_inFlow : ((ScannerState.mk' input).emit .streamStart).inFlow = false := rfl
  have h_nic_true : ((ScannerState.mk' input).emit .streamStart).needIndentCheck = true := rfl
  have h_no_shrink : ¬(((ScannerState.mk' input).emit .streamStart).indents.size <
      ((ScannerState.mk' input).emit .streamStart).indents.size) := by omega
  simp only [h_inFlow, h_nic_true, Bool.not_false, Bool.true_and,
             h_no_shrink, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  -- peek? of saveSimpleKey result = some c
  have h_sk_peek : (saveSimpleKey { (ScannerState.mk' input).emit .streamStart
      with needIndentCheck := false }).peek? = some c := by
    rw [saveSimpleKey_preserves_peek]; exact h_pk₀
  rw [closeStaleExplicitKey_of_ek_none _
    (by rw [ExplicitKeyCoupling.saveSimpleKey_preserves_explicitKeyLine]; rfl), h_sk_peek]

-- The first scanNextToken call on the initial emitScalar state
-- dispatches to scanDoubleQuoted and succeeds.
lemma scanNextToken_emitScalar_init (content : String) :
    ∃ s₁, scanNextToken ((ScannerState.mk' (emitScalar content)).emit .streamStart) = .ok (some s₁)
      ∧ s₁.peek? = none ∧ s₁.flowLevel = 0 ∧ s₁.directivesPresent = false
      ∧ (∃ tok ∈ s₁.tokens, tok.val = .scalar content .doubleQuoted)
      ∧ s₁.indents = #[{column := -1, isSequence := false}]
      ∧ (s₁.tokens.filter (fun t => t.val != .placeholder)).map (·.val)
          = #[.streamStart, .scalar content .doubleQuoted] := by
  -- Build ScannerSurfCorr for the initial state
  have h_chars := chars_from_zero_toList (emitScalar content)
  rw [emitScalar_toList] at h_chars
  have h_corr₀ := initial_corr (emitScalar content) _ h_chars
  -- ═══ Step 1: preprocessing returns (s_pp, '"') with key invariants ═══
  -- The preprocessing (skipToContent → hasMore → unwindIndents → saveSimpleKey → peek?)
  -- returns a state s_pp preserving all position/metadata fields.
  have h_pp : ∃ s_pp, scanNextToken_preprocess
      ((ScannerState.mk' (emitScalar content)).emit .streamStart)
      = .ok (some (s_pp, '"'))
    ∧ s_pp.input = emitScalar content ∧ s_pp.offset = 0
    ∧ s_pp.inputEnd = (emitScalar content).utf8ByteSize
    ∧ s_pp.col = 0
    ∧ s_pp.indents = #[{column := -1, isSequence := false}]
    ∧ s_pp.flowLevel = 0 ∧ s_pp.directivesPresent = false
    ∧ s_pp.allowDirectives = true ∧ s_pp.currentIndent = -1
    ∧ scanNextToken_checkBareDocument s_pp = .ok ()
    ∧ (s_pp.tokens.filter (fun t => t.val != .placeholder)).map (·.val) = #[.streamStart] := by
    -- Get peek? for initial state
    have h_corr_s₀ : ScannerSurfCorr
        ((ScannerState.mk' (emitScalar content)).emit .streamStart)
        ⟨['"'] ++ (escapeString content).toList ++ ['"'], 0⟩ :=
      ScannerSurfCorr_transfer h_corr₀ rfl rfl rfl rfl rfl
    have ⟨h_pk₀, _⟩ := peek_of_chars_cons _ '"' _ 0 h_corr_s₀
    have h_size := emitScalar_utf8ByteSize_ge content
    -- skipToContent is identity ('"' is not whitespace/linebreak/comment)
    have h_stc : skipToContent ((ScannerState.mk' (emitScalar content)).emit .streamStart)
        = .ok ((ScannerState.mk' (emitScalar content)).emit .streamStart) :=
      skipToContent_of_content_char _ '"' h_pk₀ (by decide) (by decide) (by decide) (by omega)
    -- Construct witness: the actual preprocessing modifies needIndentCheck before saveSimpleKey
    -- (default needIndentCheck is true; the if-branch sets it to false after unwindIndents)
    refine ⟨saveSimpleKey { (ScannerState.mk' (emitScalar content)).emit .streamStart
              with needIndentCheck := false },
      ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · -- Prove: scanNextToken_preprocess = .ok (some (saveSimpleKey {...}, '"'))
      unfold scanNextToken_preprocess
      -- Step 1: resolve skipToContent bind
      rw [h_stc]; simp only [bind, Except.bind, pure, Except.pure]
      -- Step 2: resolve hasMore
      have h_hm : ((ScannerState.mk' (emitScalar content)).emit .streamStart).hasMore = true := by
        unfold ScannerState.hasMore; exact decide_eq_true (by omega)
      simp only [h_hm, Bool.not_true, Bool.false_eq_true, ite_false]
      -- Step 3: resolve unwindIndents (identity since currentIndent = -1 < col = 0)
      have h_uwi : unwindIndents ((ScannerState.mk' (emitScalar content)).emit .streamStart)
          ↑((ScannerState.mk' (emitScalar content)).emit .streamStart).col
          = (ScannerState.mk' (emitScalar content)).emit .streamStart := by
        unfold unwindIndents unwindIndentsLoop; split <;> rfl
      simp only [h_uwi]
      -- Step 4: resolve if-checks and remaining computation
      have h_inFlow : ((ScannerState.mk' (emitScalar content)).emit .streamStart).inFlow = false := by rfl
      have h_nic_true : ((ScannerState.mk' (emitScalar content)).emit .streamStart).needIndentCheck = true := by rfl
      have h_no_trailing : ¬(((ScannerState.mk' (emitScalar content)).emit .streamStart).indents.size <
          ((ScannerState.mk' (emitScalar content)).emit .streamStart).indents.size) := by omega
      simp only [h_inFlow, h_nic_true, Bool.not_false, Bool.true_and,
                 h_no_trailing, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      -- Prove peek? of saveSimpleKey result = some '"'
      have h_sk_peek : (saveSimpleKey { (ScannerState.mk' (emitScalar content)).emit .streamStart
          with needIndentCheck := false }).peek?
          = some '"' := by
        rw [saveSimpleKey_preserves_peek]
        exact h_pk₀
      -- Rewrite the peek? in the match to resolve it (the stale-key hook is
      -- the identity on a fresh state's dead register, item 333)
      rw [closeStaleExplicitKey_of_ek_none _
        (by rw [ExplicitKeyCoupling.saveSimpleKey_preserves_explicitKeyLine]; rfl), h_sk_peek]
    · -- §9.2 bare-document check (item 132): the only real token behind the
      -- cursor is `streamStart`, which completes nothing.
      refine scanNextToken_checkBareDocument_ok_of_last _ ?_
      unfold saveSimpleKey
      split
      · simp [ScannerState.emit, ScannerState.mk', lastRealTokenVal?,
              YamlToken.completesFlowValue]
      · split
        · simp [ScannerState.emit, ScannerState.mk', lastRealTokenVal?,
                YamlToken.completesFlowValue]
        · simp [ScannerState.emit, ScannerState.mk', lastRealTokenVal?,
                YamlToken.completesFlowValue]
    · -- Filter property: saveSimpleKey preserves filtered tokens
      unfold saveSimpleKey
      split
      · simp [ScannerState.emit, ScannerState.mk']
      · split
        · dsimp only []
          simp [ScannerState.emit, ScannerState.mk']
        · simp [ScannerState.emit, ScannerState.mk']
  obtain ⟨s_pp, h_pp_eq, h_inp, h_off, h_ie, h_col_pp, h_ids,
          h_fl_pp, h_dp_pp, h_ad_pp, h_ci_pp, h_bd_pp, h_filt_pp⟩ := h_pp
  -- ═══ Step 2: build ScannerSurfCorr for s_pp from field equalities ═══
  have h_corr_pp : ScannerSurfCorr s_pp
      ⟨['"'] ++ (escapeString content).toList ++ ['"'], s_pp.col⟩ := by
    rw [h_col_pp]
    exact ScannerSurfCorr_transfer h_corr₀ h_inp h_off h_ie h_col_pp h_ids
  have ⟨h_pk_pp, _⟩ := peek_of_chars_cons s_pp '"'
    ((escapeString content).toList ++ ['"']) _ h_corr_pp
  -- peekAt? 0 = peek? (definitional)
  have h_pat0 : s_pp.peekAt? 0 = s_pp.peek? := by
    unfold ScannerState.peekAt? ScannerState.peekAt?Loop ScannerState.peek?; rfl
  -- atDocumentStart/End: first char is '"' which is not '-' or '.'
  have h_ds : atDocumentStart s_pp = false := by
    unfold atDocumentStart; rw [h_pat0, h_pk_pp]
    simp only [show (some '"' == some '-') = false from by decide,
               Bool.and_false, Bool.false_and]
  have h_de : atDocumentEnd s_pp = false := by
    unfold atDocumentEnd; rw [h_pat0, h_pk_pp]
    simp only [show (some '"' == some '.') = false from by decide,
               Bool.and_false, Bool.false_and]
  -- dispatchStructural returns .ok none for '"'
  have ⟨h_disp_s, _, _⟩ :=
    dispatchContent_quote s_pp '"' rfl h_fl_pp h_ds h_de
  -- ═══ Step 3: dispatch chain on s_ad (after allowDirectives modification) ═══
  let s_ad : ScannerState := { s_pp with allowDirectives := false, documentEverStarted := true }
  have ⟨_, h_dfi_ad, h_dbi_ad⟩ :=
    dispatchContent_quote s_ad '"' rfl h_fl_pp h_ds h_de
  -- ═══ Step 4: ScannerSurfCorr for s_ad and scanDoubleQuoted setup ═══
  have h_corr_ad : ScannerSurfCorr s_ad
      ⟨['"'] ++ (escapeString content).toList ++ ['"'], s_ad.col⟩ :=
    ScannerSurfCorr_transfer h_corr_pp rfl rfl rfl rfl rfl
  have h_fl_ad : s_ad.flowLevel = 0 := h_fl_pp
  have h_inFlow : s_ad.inFlow = false := by
    unfold ScannerState.inFlow; rw [h_fl_ad]; decide
  -- ═══ Step 5: dispatchContent produces final state with right properties ═══
  have h_dc : ∃ s_final, scanNextToken_dispatchContent s_ad '"' = .ok s_final
    ∧ s_final.peek? = none ∧ s_final.flowLevel = 0
    ∧ s_final.directivesPresent = false
    ∧ (∃ tok ∈ s_final.tokens, tok.val = .scalar content .doubleQuoted)
    ∧ s_final.indents = s_ad.indents
    ∧ (s_final.tokens.filter (fun t => t.val != .placeholder)).map (·.val)
        = #[.streamStart, .scalar content .doubleQuoted] := by
    -- scanDoubleQuoted succeeds and preserves fields
    obtain ⟨s_dq, h_dq, h_pk_dq, h_tok_dq⟩ := scanDoubleQuoted_emitScalar_ok s_ad content h_corr_ad h_inFlow
    have h_fl_dq : s_dq.flowLevel = 0 :=
      (L4YAML.Proofs.ScannerPlainScalarValid.scanDoubleQuoted_preserves_flowLevel
        s_ad s_dq h_dq).trans h_fl_ad
    have h_dp_dq : s_dq.directivesPresent = false :=
      (scanDoubleQuoted_preserves_dp s_ad s_dq h_dq).trans h_dp_pp
    have h_ids_dq : s_dq.indents = s_ad.indents :=
      scanDoubleQuoted_preserves_indents s_ad s_dq h_dq
    -- Token membership: scalar is in s_dq.tokens
    have h_tok_mem : ∃ tok ∈ s_dq.tokens, tok.val = .scalar content .doubleQuoted :=
      ⟨_, by rw [h_tok_dq]; exact Array.mem_push_self, rfl⟩
    -- Extend filtered tokens: s_dq.tokens = s_ad.tokens.push {scalar}, s_ad.tokens = s_pp.tokens
    have h_filt_dq :
        (s_dq.tokens.filter (fun t => t.val != .placeholder)).map (·.val)
          = #[.streamStart, .scalar content .doubleQuoted] := by
      rw [h_tok_dq]
      simp only [Array.filter_push,
        show (YamlToken.scalar content .doubleQuoted != .placeholder) = true from rfl,
        ite_true, Array.map_push,
        show s_ad.tokens = s_pp.tokens from rfl, h_filt_pp]
      rfl
    -- Unfold dispatchContent: all if-branches except '"' are eliminated by decide
    unfold scanNextToken_dispatchContent
    simp (config := { decide := true }) only [bind, Except.bind, pure, h_dq]
    -- The simpleKey update preserves peek?/flowLevel/directivesPresent/tokens/indents.
    -- Use Bool.rec to avoid dependent elimination issues with cases.
    exact ⟨_, rfl,
      s_dq.simpleKey.possible.rec h_pk_dq h_pk_dq,
      s_dq.simpleKey.possible.rec h_fl_dq h_fl_dq,
      s_dq.simpleKey.possible.rec h_dp_dq h_dp_dq,
      s_dq.simpleKey.possible.rec h_tok_mem h_tok_mem,
      s_dq.simpleKey.possible.rec h_ids_dq h_ids_dq,
      s_dq.simpleKey.possible.rec h_filt_dq h_filt_dq⟩
  obtain ⟨s_final, h_dc_eq, h_pkf, h_flf, h_dpf, h_tokf, h_idsf, h_filtf⟩ := h_dc
  -- ═══ Step 6: compose all steps through scanNextToken ═══
  refine ⟨s_final, ?_, h_pkf, h_flf, h_dpf, h_tokf, h_idsf.trans h_ids, h_filtf⟩
  -- Reduce: scanNextToken = preprocess →ᵦ dispatchStructural →ᵦ allowDirectives →
  --   dispatchFlowIndicators →ᵦ dispatchBlockIndicators →ᵦ dispatchContent
  unfold scanNextToken
  simp only [bind, Except.bind, h_pp_eq]
  simp only [h_disp_s]
  -- §9.2 dangling-node check (item 133): the stack is the sentinel alone —
  -- and (item 180) the seed's one real token is no property.
  simp only [scanNextToken_checkDanglingNode_ok_of_sentinel_stack _ _
    (init_indents_sentinel _) (crossedPropsExcessIdx?_init _)]
  -- §8.1 flow-value floor (item 172): the same sentinel discharge.
  simp only [scanNextToken_checkFlowValueIndent_ok_of_sentinel_stack _ _ (init_indents_sentinel _)]
  -- Pending-directives check (Fix B): passes since s_pp has no pending directives.
  simp only [scanNextToken_checkNoPendingDirectives_ok _ h_dp_pp]
  -- §9.2 bare-document check (item 132): the only real token is `streamStart`.
  simp only [h_bd_pp]
  simp only [show s_pp.allowDirectives = true from h_ad_pp, ite_true]
  -- Remaining dispatch steps use s_ad = { s_pp with allowDirectives := false, ... }
  -- which is definitionally equal to the expanded struct in the goal
  simp only [scanNextToken_checkAdjacentValue_ok_of_ne_colon _
    (show ('"' : Char) ≠ ':' by decide)]
  exact h_dfi_ad ▸ h_dbi_ad ▸ h_dc_eq ▸ rfl

/-- **Scalar case**: The scanner accepts any double-quoted scalar produced
    by the emitter. -/
lemma scan_accepts_emitScalar (content : String) :
    ∃ tokens, scanFiltered (emitScalar content) = .ok tokens := by
  simp only [scanFiltered]
  suffices h : ∃ toks, scan (emitScalar content) = .ok toks by
    obtain ⟨toks, h⟩ := h
    exact ⟨toks.filter fun t => t.val != .placeholder, by rw [h]⟩
  -- First scanNextToken: dispatches to scanDoubleQuoted, succeeds
  obtain ⟨s₁, h_snt1, h_peek1, h_flow1, h_dp1, _h_tok1, h_ids1, h_filt1⟩ :=
    scanNextToken_emitScalar_init content
  -- Item 180: the filtered run holds no property token, so the crossed-block
  -- clause reads none at the final state.
  have h_np1 : crossedPropsExcessIdx? s₁.tokens = none :=
    crossedPropsExcessIdx?_none_of_no_props (no_props_of_filtered_pin h_filt1
      (by intro v hv; simp [Array.mem_def] at hv; rcases hv with rfl | rfl <;> rfl))
  -- Second scanNextToken: EOF → .ok none
  have h_snt2 : scanNextToken s₁ = .ok none := scanNextToken_eof s₁ h_peek1
  have h_size := emitScalar_utf8ByteSize_ge content
  have h_fuel : ((emitScalar content).utf8ByteSize + 1) * 4 ≥ 2 := by omega
  -- Reduce scan to scanLoop (BOM check is no-op since first char is '"' ≠ '\uFEFF')
  have h_scan_eq : scan (emitScalar content)
      = scanLoop ((ScannerState.mk' (emitScalar content)).emit .streamStart)
          (((emitScalar content).utf8ByteSize + 1) * 4) := by
    -- Derive peek? = some '"' from ScannerSurfCorr
    have h_chars := chars_from_zero_toList (emitScalar content)
    rw [emitScalar_toList] at h_chars
    have h_corr := initial_corr (emitScalar content) _ h_chars
    have ⟨h_pk, _⟩ := peek_of_chars_cons (ScannerState.mk' (emitScalar content)) '"'
      ((escapeString content).toList ++ ['"']) 0 h_corr
    -- emit doesn't change peek?
    have h_pk_emit : ((ScannerState.mk' (emitScalar content)).emit .streamStart).peek?
        = (ScannerState.mk' (emitScalar content)).peek? := rfl
    unfold scan; dsimp only []
    rw [h_pk_emit, h_pk]
    -- match some '"' with | some '\uFEFF' => ... | _ => s reduces to s
    split <;> first | exact absurd ‹_› (by decide) | rfl
  rw [h_scan_eq]
  exact scanLoop_two_iter h_fuel h_snt1 h_snt2 h_flow1 h_dp1
    (scanLoop_checkDanglingNode_ok_of_sentinel_stack _ h_ids1 h_np1)
    (scanLoop_checkFlowValueIndent_ok_of_sentinel_stack _ h_ids1)

-- ═══ Flow collection scanner acceptance ═══
-- Infrastructure for proving that the scanner accepts emitted flow collections.

-- Test: can we evaluate scanFiltered on small flow collections?
lemma scan_emptySeq_test :
    (Scanner.scanFiltered "[]").isOk = true := by native_decide

lemma scan_emptyMap_test :
    (Scanner.scanFiltered "{}").isOk = true := by native_decide

lemma scan_singleScalarSeq_test :
    (Scanner.scanFiltered "[\"hello\"]").isOk = true := by native_decide

lemma scan_twoScalarSeq_test :
    (Scanner.scanFiltered "[\"a\", \"b\"]").isOk = true := by native_decide

lemma scan_nestedSeq_test :
    (Scanner.scanFiltered "[[\"a\"]]").isOk = true := by native_decide

-- ═══ Flow-context preprocessing ═══

/-- In flow context, `scanNextToken_preprocess` with a content character
    returns `some (saveSimpleKey s, c)` unchanged.  The proof relies on:
    1. `skipToContent` is identity for non-ws/non-lb/non-comment chars
    2. `!s.inFlow = false` skips `unwindIndents`
    3. `indents.size` unchanged → trailing content check is false
    4. `saveSimpleKey` preserves peek -/
lemma scanNextToken_preprocess_flow (s : ScannerState) (c : Char)
    (rest : List Char) (col : Nat)
    (hcorr : ScannerSurfCorr s ⟨c :: rest, col⟩)
    (h_flow : s.inFlow = true)
    (h_nws : isWhiteSpaceBool c = false)
    (h_nlb : isLineBreakBool c = false)
    (h_nc : c ≠ '#') :
    scanNextToken_preprocess s = .ok (some (saveSimpleKey s, c)) := by
  have ⟨h_pk, h_lt⟩ := peek_of_chars_cons s c rest col hcorr
  -- skipToContent is identity
  have h_stc : skipToContent s = .ok s :=
    skipToContent_of_content_char s c h_pk h_nws h_nlb h_nc h_lt
  -- hasMore = true
  have h_hm : s.hasMore = true := by
    unfold ScannerState.hasMore; exact decide_eq_true h_lt
  unfold scanNextToken_preprocess
  rw [h_stc]; simp only [bind, Except.bind, pure, Except.pure]
  -- !s.inFlow = false → skip unwindIndents branch
  simp only [h_hm, h_flow, Bool.not_true, Bool.false_eq_true, ite_false]
  -- indents.size < savedIndentSize is s.indents.size < s.indents.size → false
  simp only [show ¬(s.indents.size < s.indents.size) from by omega, decide_false,
             Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  -- the stale-key hook is the identity in flow (item 333); saveSimpleKey preserves peek
  rw [closeStaleExplicitKey_of_inFlow _ (by
      simp only [ScannerState.inFlow, ScannerCorrectness.saveSimpleKey_preserves_flowLevel]
      simpa [ScannerState.inFlow] using h_flow),
    saveSimpleKey_preserves_peek, h_pk]

-- Variant with a single leading space: preprocessing of `' ' :: c :: rest`
-- yields the same result as preprocessing of the post-space state.
-- Key idea: skipToContent absorbs the space, reaching the same state s₁
-- as skipToContent on s₁ (identity for non-ws first char).
lemma scanNextToken_preprocess_flow_ws1 (s : ScannerState) (c : Char)
    (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨' ' :: c :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_nws : isWhiteSpaceBool c = false)
    (h_nlb : isLineBreakBool c = false)
    (h_nc : c ≠ '#')
    (h_indent : s.currentIndent < 0) :
    ∃ s₁, ScannerSurfCorr s₁ ⟨c :: rest, s₁.col⟩
      ∧ s₁.inFlow = true
      ∧ s₁.flowLevel = s.flowLevel
      ∧ s₁.currentIndent = s.currentIndent
      ∧ s₁.col = s.col + 1
      ∧ s₁.directivesPresent = s.directivesPresent
      ∧ s₁.indents = s.indents
      ∧ s₁.explicitKeyLine = s.explicitKeyLine
      ∧ s₁.line = s.line
      ∧ scanNextToken_preprocess s = scanNextToken_preprocess s₁
      ∧ (AllTokensOnLine s s.line → AllTokensOnLine s₁ s₁.line)
      ∧ (EndLineOnLine s → EndLineOnLine s₁)
      ∧ s₁.simpleKeyStack = s.simpleKeyStack
      ∧ s₁.tokens = s.tokens
      ∧ s₁.simpleKey = s.simpleKey
      ∧ s₁.simpleKeyAllowed = s.simpleKeyAllowed := by
  -- Key: skipToContent absorbs the single space. We decompose the proof:
  -- (a) skipToContent s = .ok s₁ for some s₁ at c :: rest with field preservation
  -- (b) skipToContent s₁ = .ok s₁ (identity, via skipToContent_of_content_char)
  -- (c) both preprocessing paths yield (saveSimpleKey s₁, c)
  -- Part (a): skipToContent s advances past the space
  -- This traces through skipToContentLoop → skipToContentWs (needIndentCheck branch) →
  -- skipWhitespace/skipSpaces → skipToContentComment (identity) → not line break → return.
  have h_stc_exists : ∃ s₁, skipToContent s = .ok s₁
      ∧ ScannerSurfCorr s₁ ⟨c :: rest, s₁.col⟩
      ∧ s₁.flowLevel = s.flowLevel
      ∧ s₁.indents = s.indents
      ∧ s₁.directivesPresent = s.directivesPresent
      ∧ s₁.explicitKeyLine = s.explicitKeyLine
      ∧ s₁.col = s.col + 1
      ∧ s₁.line = s.line
      ∧ s₁.tokens = s.tokens
      ∧ s₁.simpleKey = s.simpleKey
      ∧ s₁.simpleKeyStack = s.simpleKeyStack
      ∧ s₁.simpleKeyAllowed = s.simpleKeyAllowed := by
    -- Both needIndentCheck branches yield s.advance. Proof via advance lemmas.
    have ⟨h_pk_space, h_lt⟩ := peek_of_chars_cons s ' ' (c :: rest) s.col hcorr
    -- s.advance is at c :: rest with col + 1
    have h_adv_corr : ScannerSurfCorr s.advance ⟨c :: rest, s.col + 1⟩ :=
      advance_non_newline_corr s ' ' (c :: rest) hcorr h_lt (by decide) (by decide)
    -- advance.peek? = some c
    have ⟨h_pk_adv, h_lt_adv⟩ := peek_of_chars_cons s.advance c rest (s.col + 1) h_adv_corr
    have h_ns : c ≠ ' ' := by intro h; subst h; exact absurd h_nws (by decide)
    -- Helper: skipWhitespace s = s.advance
    have h_sw_eq : skipWhitespace s = s.advance := by
      unfold skipWhitespace
      obtain ⟨n, hn⟩ : ∃ n, s.inputEnd - s.offset = n + 1 :=
        ⟨s.inputEnd - s.offset - 1, by omega⟩
      rw [hn]; unfold skipWhitespaceLoop; simp only [h_pk_space, show isWhiteSpaceBool ' ' = true from by decide, ite_true]
      cases n with
      | zero => unfold skipWhitespaceLoop; rfl
      | succ n' => unfold skipWhitespaceLoop; simp [h_pk_adv, h_nws]
    -- Helper: skipSpaces s = s.advance
    have h_ss_eq : skipSpaces s = s.advance := by
      unfold skipSpaces
      cases h_fuel : (s.inputEnd - s.offset) with
      | zero => omega
      | succ n =>
        unfold skipSpacesLoop; simp only [h_pk_space]
        cases n with
        | zero => unfold skipSpacesLoop; rfl
        | succ n' => unfold skipSpacesLoop; rw [h_pk_adv]; simp [h_ns]
    -- advance field properties
    have h_adv_fl : s.advance.flowLevel = s.flowLevel :=
      ScannerCorrectness.advance_preserves_flowLevel s
    have h_adv_flow : s.advance.inFlow = true := by
      unfold ScannerState.inFlow
      exact decide_eq_true (by rw [h_adv_fl]; unfold ScannerState.inFlow at h_flow; exact of_decide_eq_true h_flow)
    have h_adv_ids : s.advance.indents = s.indents := advance_indents s
    have h_adv_indent : s.advance.currentIndent = s.currentIndent := by
      unfold ScannerState.currentIndent; rw [h_adv_ids]
    have h_adv_col : s.advance.col = s.col + 1 := h_adv_corr.col_eq.symm
    -- skipToContentWs s = .ok s.advance (case split on needIndentCheck)
    have h_ws : skipToContentWs s = .ok s.advance := by
      unfold skipToContentWs
      split
      · -- needIndentCheck = true: skipSpaces s = s.advance, then condition false → else
        rw [h_ss_eq]
        -- condition: (!s.advance.inFlow && ...) || (col ≤ currentIndent) both false
        simp only [h_adv_flow, Bool.not_true, Bool.false_and, Bool.false_or]
        simp only [show ¬((s.advance.col : Int) ≤ s.advance.currentIndent) from by
          rw [h_adv_col, h_adv_indent]; omega, decide_false]
        -- else: skipWhitespace s.advance = s.advance (c is non-ws)
        exact congrArg Except.ok (skipWhitespace_of_not_ws s.advance c h_pk_adv h_nws h_lt_adv)
      · -- needIndentCheck = false: skipWhitespace s = s.advance
        exact congrArg Except.ok h_sw_eq
    -- Now compose: skipToContent s = skipToContentLoop s fuel
    have h_adv_corr' : ScannerSurfCorr s.advance ⟨c :: rest, s.advance.col⟩ := by
      rw [h_adv_col]; exact h_adv_corr
    refine ⟨s.advance, ?_, h_adv_corr', ScannerCorrectness.advance_preserves_flowLevel s,
      advance_indents s, advance_preserves_dp s, advance_explicitKeyLine s, h_adv_col,
      advance_line_of_peek s ' ' h_lt h_pk_space (by decide) (by decide),
      ScannerCorrectness.advance_preserves_tokens s,
      ScannerCorrectness.advance_preserves_simpleKey s,
      ScannerCorrectness.advance_preserves_simpleKeyStack s,
      ScannerCorrectness.advance_preserves_simpleKeyAllowed s⟩
    -- skipToContent s = .ok s.advance
    unfold skipToContent
    obtain ⟨m, hm⟩ : ∃ m, s.inputEnd - s.offset + 1 = m + 1 :=
      ⟨s.inputEnd - s.offset, by omega⟩
    rw [hm]; unfold skipToContentLoop
    simp only [h_ws]
    -- skipToContentComment s.advance: c ≠ '#' → identity
    unfold skipToContentComment; rw [h_pk_adv]; simp [h_nc, h_pk_adv, h_nlb]
  obtain ⟨s₁, h_stc_ok, h_corr₁, h_fl₁, h_ids₁, h_dp₁, h_ek₁, h_col₁, h_line₁, h_toks₁, h_sk₁, h_stack₁, h_ska₁⟩ := h_stc_exists
  -- Part (b): derive further properties of s₁
  have h_flow₁ : s₁.inFlow = true := by
    unfold ScannerState.inFlow
    exact decide_eq_true (by rw [h_fl₁]; unfold ScannerState.inFlow at h_flow; exact of_decide_eq_true h_flow)
  have h_indent₁ : s₁.currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [h_ids₁]
  have ⟨h_pk₁, h_lt₁⟩ := peek_of_chars_cons s₁ c rest s₁.col h_corr₁
  have h_stc₁ : skipToContent s₁ = .ok s₁ :=
    skipToContent_of_content_char s₁ c h_pk₁ h_nws h_nlb h_nc h_lt₁
  have h_hm₁ : s₁.hasMore = true := by
    unfold ScannerState.hasMore; exact decide_eq_true h_lt₁
  -- Part (c): both preprocessing paths yield (saveSimpleKey s₁, c)
  have h_pp_s : scanNextToken_preprocess s = .ok (some (saveSimpleKey s₁, c)) := by
    unfold scanNextToken_preprocess
    rw [h_stc_ok]; simp only [bind, Except.bind, pure, Except.pure]
    simp only [h_hm₁, h_flow₁, Bool.not_true, Bool.false_eq_true, ite_false]
    simp only [show ¬(s₁.indents.size < s₁.indents.size) from by omega, decide_false,
               Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [closeStaleExplicitKey_of_inFlow _ (by
        simp only [ScannerState.inFlow, ScannerCorrectness.saveSimpleKey_preserves_flowLevel]
        simpa [ScannerState.inFlow] using h_flow₁),
      saveSimpleKey_preserves_peek, h_pk₁]
  have h_pp_s₁ : scanNextToken_preprocess s₁ = .ok (some (saveSimpleKey s₁, c)) := by
    unfold scanNextToken_preprocess
    rw [h_stc₁]; simp only [bind, Except.bind, pure, Except.pure]
    simp only [h_hm₁, h_flow₁, Bool.not_true, Bool.false_eq_true, ite_false]
    simp only [show ¬(s₁.indents.size < s₁.indents.size) from by omega, decide_false,
               Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [closeStaleExplicitKey_of_inFlow _ (by
        simp only [ScannerState.inFlow, ScannerCorrectness.saveSimpleKey_preserves_flowLevel]
        simpa [ScannerState.inFlow] using h_flow₁),
      saveSimpleKey_preserves_peek, h_pk₁]
  exact ⟨s₁, h_corr₁, h_flow₁, h_fl₁, h_indent₁, h_col₁, h_dp₁, h_ids₁, h_ek₁, h_line₁,
    by rw [h_pp_s, h_pp_s₁],
    fun h_a => by unfold AllTokensOnLine at h_a ⊢; simp only [h_line₁, h_toks₁]; exact h_a,
    fun h_e => by unfold EndLineOnLine at h_e ⊢; rw [h_sk₁, h_line₁]; exact h_e,
    h_stack₁, h_toks₁, h_sk₁, h_ska₁⟩

-- ═══ Flow-context dispatch lemmas ═══

/-- `dispatchStructural` returns `none` for non-structural characters in flow
    context when the column is past any document boundary position. -/
lemma dispatchStructural_none_flow (s : ScannerState) (c : Char)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0) :
    scanNextToken_dispatchStructural s c = .ok none := by
  have h_fl_pos : s.flowLevel > 0 := by
    unfold ScannerState.inFlow at h_flow; exact of_decide_eq_true h_flow
  unfold scanNextToken_dispatchStructural
  simp [ScannerState.inFlow, h_fl_pos, show ¬(s.currentIndent ≥ (0 : Int)) from by omega, show ¬((s.col : Int) ≤ s.currentIndent) from by omega, show s.col ≠ 0 from by omega, pure, Except.pure]

/-- `dispatchFlowIndicators` returns `none` for non-flow-indicator characters. -/
lemma dispatchFlowIndicators_none (s : ScannerState) (c : Char)
    (h1 : c ≠ '[') (h2 : c ≠ ']') (h3 : c ≠ '{') (h4 : c ≠ '}') (h5 : c ≠ ',')
    (h_adj : scanNextToken_checkFlowAdjacency s c = .ok ()) :
    scanNextToken_dispatchFlowIndicators s c = .ok none := by
  unfold scanNextToken_dispatchFlowIndicators
  rw [h_adj]
  simp only [bind, Except.bind, pure, Except.pure]
  split
  · rename_i h; exact absurd (beq_iff_eq.mp h) h1
  · split
    · rename_i h; exact absurd (beq_iff_eq.mp h) h2
    · split
      · rename_i h; exact absurd (beq_iff_eq.mp h) h3
      · split
        · rename_i h; exact absurd (beq_iff_eq.mp h) h4
        · split
          · rename_i h; exact absurd (beq_iff_eq.mp h) h5
          · rfl

/-- `dispatchBlockIndicators` returns `none` for `'"'` (and many other chars). -/
lemma dispatchBlockIndicators_none_quote (s : ScannerState) :
    scanNextToken_dispatchBlockIndicators s '"' = .ok none := by
  unfold scanNextToken_dispatchBlockIndicators
  simp only [bind, Except.bind, pure, Except.pure]
  -- '"' ≠ '-', '"' ≠ '?', '"' ≠ ':'
  split
  · rename_i h; simp at h
  · split
    · rename_i h; simp at h
    · split
      · rename_i h; simp at h
      · rfl

-- ═══ scanFlowSequenceStart detailed properties ═══

-- Field preservation through scanFlowSequenceStart
lemma scanFlowSequenceStart_preserves_dp (s : ScannerState) :
    (scanFlowSequenceStart s).directivesPresent = s.directivesPresent := by
  unfold scanFlowSequenceStart; simp only [advance_preserves_dp, ScannerState.emit]

lemma scanFlowSequenceStart_preserves_indents (s : ScannerState) :
    (scanFlowSequenceStart s).indents = s.indents := by
  unfold scanFlowSequenceStart; simp only [advance_preserves_indents, ScannerState.emit]

lemma scanFlowSequenceStart_preserves_ek (s : ScannerState) :
    (scanFlowSequenceStart s).explicitKeyLine = none := by
  unfold scanFlowSequenceStart; rfl

lemma scanFlowSequenceStart_line_eq (s : ScannerState) :
    (scanFlowSequenceStart s).line = s.advance.line := by
  -- 4.33: unfold `emit` in its own simp pass before `advance` (a combined pass
  -- leaves `advance`'s ite instances mentioning un-unfolded `emit`, the goal is
  -- then ill-typed at reducible transparency, and `split` refuses).
  simp only [scanFlowSequenceStart, ScannerState.emit]
  simp only [ScannerState.advance]
  split <;> (try split <;> (try split)) <;> rfl

lemma scanFlowSequenceStart_flowLevel_eq (s : ScannerState) :
    (scanFlowSequenceStart s).flowLevel = s.flowLevel + 1 := by
  unfold scanFlowSequenceStart
  simp only [ScannerCorrectness.advance_preserves_flowLevel, ScannerCorrectness.emit_preserves_flowLevel]

/-- `scanFlowSequenceStart` advances past `[`, giving specific ScannerSurfCorr
    and field preservation. -/
lemma scanFlowSequenceStart_detail (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'[' :: rest, s.col⟩) :
    ScannerSurfCorr (scanFlowSequenceStart s) ⟨rest, s.col + 1⟩
    ∧ (scanFlowSequenceStart s).flowLevel = s.flowLevel + 1
    ∧ (scanFlowSequenceStart s).directivesPresent = s.directivesPresent
    ∧ (scanFlowSequenceStart s).indents = s.indents
    ∧ (scanFlowSequenceStart s).col = s.col + 1 := by
  have ⟨_, h_lt⟩ := peek_of_chars_cons s '[' rest _ hcorr
  have h_emit_corr : ScannerSurfCorr
      ({ s with simpleKey := { possible := false } }.emit .flowSequenceStart)
      ⟨'[' :: rest, s.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have h_adv_corr := advance_non_newline_corr
    ({ s with simpleKey := { possible := false } }.emit .flowSequenceStart)
    '[' rest h_emit_corr h_lt (by decide) (by decide)
  -- Transfer corr from advance result to scanFlowSequenceStart result
  -- After unfold, struct-with on advance result preserves ScannerSurfCorr fields
  have h_corr_final : ScannerSurfCorr (scanFlowSequenceStart s) ⟨rest, s.col + 1⟩ := by
    unfold scanFlowSequenceStart
    exact ⟨h_adv_corr.chars_from, h_adv_corr.col_eq, h_adv_corr.end_eq,
           h_adv_corr.input_prefix, h_adv_corr.indent_cols_nonneg⟩
  exact ⟨h_corr_final,
         scanFlowSequenceStart_flowLevel_eq s,
         scanFlowSequenceStart_preserves_dp s,
         scanFlowSequenceStart_preserves_indents s,
         h_corr_final.col_eq.symm ▸ rfl⟩

-- ═══ Full scanNextToken pipeline composition ═══

/-- When preprocessing succeeds, structural dispatch returns none,
    flow indicators return none, block indicators return none,
    and content dispatch produces `s_result`, then scanNextToken
    returns `some s_result`.

    `s_ad` is the state after the allowDirectives update. -/
lemma scanNextToken_via_content_dispatch (s s_pp s_ad s_result : ScannerState) (c : Char)
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (h_fv : scanNextToken_checkFlowValueIndent s s_pp = .ok ())
    (h_flow : scanNextToken_dispatchFlowIndicators s_ad c = .ok none)
    (h_block : scanNextToken_dispatchBlockIndicators s_ad c = .ok none)
    (h_adj : scanNextToken_checkAdjacentValue s_ad c = .ok ())
    (h_content : scanNextToken_dispatchContent s_ad c = .ok s_result)
    (h_ndp : s_pp.directivesPresent = false)
    (h_bare : scanNextToken_checkBareDocument s_pp = .ok ())
    (h_dang : scanNextToken_checkDanglingNode s s_pp = .ok ()) :
    scanNextToken s = .ok (some s_result) := by
  unfold scanNextToken; dsimp only []
  simp only [bind, Except.bind, h_pp, h_dang, h_fv, h_struct, pure, Except.pure,
    scanNextToken_checkNoPendingDirectives_ok _ h_ndp, h_bare]
  rw [← h_ad_eq]
  simp only [h_flow, h_block, h_adj, h_content]

/-- Error variant of `scanNextToken_via_content_dispatch`: when content
    dispatch errors, `scanNextToken` propagates that error. -/
lemma scanNextToken_via_content_dispatch_error
    (s s_pp s_ad : ScannerState) (c : Char) (e : ScanError)
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (h_fv : scanNextToken_checkFlowValueIndent s s_pp = .ok ())
    (h_flow : scanNextToken_dispatchFlowIndicators s_ad c = .ok none)
    (h_block : scanNextToken_dispatchBlockIndicators s_ad c = .ok none)
    (h_adj : scanNextToken_checkAdjacentValue s_ad c = .ok ())
    (h_content : scanNextToken_dispatchContent s_ad c = .error e)
    (h_ndp : s_pp.directivesPresent = false)
    (h_bare : scanNextToken_checkBareDocument s_pp = .ok ())
    (h_dang : scanNextToken_checkDanglingNode s s_pp = .ok ()) :
    scanNextToken s = .error e := by
  unfold scanNextToken; dsimp only []
  simp only [bind, Except.bind, h_pp, h_dang, h_fv, h_struct, pure, Except.pure,
    scanNextToken_checkNoPendingDirectives_ok _ h_ndp, h_bare]
  rw [← h_ad_eq]
  simp only [h_flow, h_block, h_adj, h_content]

/-- When preprocessing succeeds, structural/flow dispatches return none,
    and block indicator dispatch produces a result, then scanNextToken
    returns that result. This is used for `:` (value indicator) in flow context,
    which goes through `scanNextToken_dispatchBlockIndicators`. -/
lemma scanNextToken_via_block_dispatch (s s_pp s_ad s_result : ScannerState) (c : Char)
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (h_fv : scanNextToken_checkFlowValueIndent s s_pp = .ok ())
    (h_flow : scanNextToken_dispatchFlowIndicators s_ad c = .ok none)
    (h_block : scanNextToken_dispatchBlockIndicators s_ad c = .ok (some s_result))
    (h_ndp : s_pp.directivesPresent = false)
    (h_bare : scanNextToken_checkBareDocument s_pp = .ok ())
    (h_dang : scanNextToken_checkDanglingNode s s_pp = .ok ()) :
    scanNextToken s = .ok (some s_result) := by
  unfold scanNextToken; dsimp only []
  simp only [bind, Except.bind, h_pp, h_dang, h_fv, h_struct, pure, Except.pure,
    scanNextToken_checkNoPendingDirectives_ok _ h_ndp, h_bare]
  rw [← h_ad_eq]
  simp only [h_flow, h_block]

-- ═══ Flow-context scanDoubleQuoted dispatch ═══

/-- In flow context with state at `'"'`, `scanNextToken` dispatches to
    `scanDoubleQuoted`, which succeeds and advances past the quoted scalar.
    Combines preprocessing, all-none dispatches, and content dispatch.

    This is the flow-context analog of `scanNextToken_emitScalar_init`. -/
lemma scanNextToken_flow_scanDoubleQuoted (s : ScannerState)
    (content : String) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨['"'] ++ (escapeString content).toList ++ ['"'] ++ rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_dp : s.directivesPresent = false)
    (h_last : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ (∀ t, lastRealTokenVal? s'.tokens = some t →
          t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
      ∧ s'.simpleKeyAllowed = false
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack := by
  -- Step 1: preprocessing
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '"')) :=
    scanNextToken_preprocess_flow s '"' ((escapeString content).toList ++ ['"'] ++ rest) s.col
      hcorr h_flow (by decide) (by decide) (by decide)
  -- Step 2: structural dispatch returns none
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '"' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  -- Step 3: allowDirectives update
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_ad_col : s_ad.col = s.col := by
    simp only [s_ad]; split <;> exact h_sk_col
  -- Step 5: flow dispatch returns none
  have h_ad_tokens : s_ad.tokens = (saveSimpleKey s).tokens := by
    simp only [s_ad]; split <;> rfl
  have h_flow_none : scanNextToken_dispatchFlowIndicators s_ad '"' = .ok none :=
    dispatchFlowIndicators_none _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (checkFlowAdjacency_ok_of_notCompletes (fun t ht =>
        saveSimpleKey_preserves_completesFalse s h_last t (h_ad_tokens ▸ ht)))
  -- Step 6: block dispatch returns none
  have h_block_none : scanNextToken_dispatchBlockIndicators s_ad '"' = .ok none :=
    dispatchBlockIndicators_none_quote _
  -- Step 7: content dispatch → scanDoubleQuoted
  have h_ad_corr : ScannerSurfCorr s_ad ⟨['"'] ++ (escapeString content).toList ++ ['"'] ++ rest, s_ad.col⟩ := by
    have h_ad_input : s_ad.input = s.input := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s
    have h_ad_offset : s_ad.offset = s.offset := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s
    have h_ad_inputEnd : s_ad.inputEnd = s.inputEnd := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s
    have h_ad_indents : s_ad.indents = s.indents := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
    rw [h_ad_col]
    exact ScannerSurfCorr_transfer hcorr h_ad_input h_ad_offset h_ad_inputEnd h_ad_col h_ad_indents
  have h_ad_flow_bool : s_ad.inFlow = true := h_ad_flow ▸ h_flow
  -- s_ad.flowLevel = s.flowLevel (through saveSimpleKey + allowDirectives branch)
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).flowLevel = _
      unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).explicitKeyLine = _
      unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
  obtain ⟨s_dq, h_dq, h_dq_corr, h_dq_fl, h_dq_dp, h_dq_ids, h_dq_ek, h_dq_col, h_dq_tokens, h_dq_ska, h_dq_line⟩ :=
    scanDoubleQuoted_flow_ok s_ad content rest h_ad_corr h_ad_flow_bool
  -- Content dispatch: unfold to reach scanDoubleQuoted + simpleKey update
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have h_content : ∃ s_final, scanNextToken_dispatchContent s_ad '"' = .ok s_final
      ∧ ScannerSurfCorr s_final ⟨rest, s_final.col⟩
      ∧ s_final.flowLevel = s.flowLevel
      ∧ s_final.directivesPresent = s.directivesPresent
      ∧ s_final.indents = s.indents
      ∧ s_final.explicitKeyLine = s.explicitKeyLine
      ∧ s_final.col > 0
      ∧ lastRealTokenVal? s_final.tokens = some (.scalar content .doubleQuoted)
      ∧ s_final.simpleKeyAllowed = false
      ∧ s_final.line = s.line
      ∧ AllTokensOnLine s_final s.line
      ∧ EndLineOnLine s_final
      ∧ s_final.simpleKeyStack = s.simpleKeyStack := by
    unfold scanNextToken_dispatchContent
    simp (config := { decide := true }) only [bind, Except.bind, pure, Except.pure, h_dq]
    -- AllTokensOnLine for s_dq: scanDoubleQuoted preserves AllTokensOnLine
    -- scanDoubleQuoted does emitAt startPos + collectLoop (no extra tokens)
    -- We need AllTokensOnLine s_dq s.line
    -- s_dq.tokens = s_ad tokens + emitAt at startPos = s_ad.currentPos (line = s_ad.line = s.line)
    -- For now, we'll prove it using sorry for AllTokensOnLine_scanDoubleQuoted
    have h_atol_ad : AllTokensOnLine s_ad s.line :=
      AllTokensOnLine_allowDirectives _ _
        (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl)
    have h_atol_dq : AllTokensOnLine s_dq s.line :=
      AllTokensOnLine_scanDoubleQuoted s_ad s_dq h_dq h_ad_flow_bool
        s.line h_atol_ad h_ad_line
    have h_sk_dq : s_dq.simpleKey = s_ad.simpleKey :=
      scanDoubleQuoted_preserves_simpleKey s_ad s_dq h_dq
    have h_dq_stack : s_dq.simpleKeyStack = s_ad.simpleKeyStack :=
      ScannerCorrectness.scanDoubleQuoted_preserves_simpleKeyStack s_ad s_dq h_dq
    have h_ad_stack : s_ad.simpleKeyStack = s.simpleKeyStack := by
      simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
    -- After scanDoubleQuoted, simpleKey.possible branches
    cases h_skp : s_dq.simpleKey.possible
    · -- simpleKey.possible = false: s' = s_dq
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨_, rfl, h_dq_corr,
        h_dq_fl.trans h_ad_fl, h_dq_dp.trans h_ad_dp, h_dq_ids.trans h_ad_ids,
        h_dq_ek.trans h_ad_ek, h_dq_col, h_dq_tokens, h_dq_ska,
        h_dq_line.trans h_ad_line, h_atol_dq, ?_, h_dq_stack.trans h_ad_stack⟩
      · intro h_poss; rw [h_skp] at h_poss; exact absurd h_poss (by decide)
    · -- simpleKey.possible = true: s' = { s_dq with simpleKey endLine update }
      simp only [↓reduceIte]
      refine ⟨_, rfl,
        ⟨h_dq_corr.chars_from, h_dq_corr.col_eq, h_dq_corr.end_eq,
         h_dq_corr.input_prefix, h_dq_corr.indent_cols_nonneg⟩,
        h_dq_fl.trans h_ad_fl, h_dq_dp.trans h_ad_dp, h_dq_ids.trans h_ad_ids,
        h_dq_ek.trans h_ad_ek, h_dq_col, h_dq_tokens, h_dq_ska,
        h_dq_line.trans h_ad_line, h_atol_dq, ?_, h_dq_stack.trans h_ad_stack⟩
      · -- EndLineOnLine: endLine just set to s_dq.line, pos from saveSimpleKey
        intro _
        constructor
        · rfl
        · show s_dq.simpleKey.pos.line = s_dq.line
          rw [h_sk_dq]
          have h_ad_sk : s_ad.simpleKey = (saveSimpleKey s).simpleKey := by
            simp only [s_ad]; split <;> rfl
          rw [h_ad_sk]
          have h_eol_sk := EndLineOnLine_saveSimpleKey_flow s h_endline
          have h_sk_poss : (saveSimpleKey s).simpleKey.possible = true := by
            rw [← h_ad_sk, ← h_sk_dq]; exact h_skp
          exact (h_eol_sk h_sk_poss).2 |>.trans (saveSimpleKey_preserves_line s)
            |>.trans (h_dq_line.trans h_ad_line).symm
  obtain ⟨s_final, h_dc_eq, h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_ek_f, h_col_f, h_tok_f, h_ska_f, h_line_f, h_atol_f, h_endline_f, h_stack_f⟩ := h_content
  -- Step 8: compose through scanNextToken
  exact ⟨s_final, scanNextToken_via_content_dispatch _ _ _ _ _ h_pp h_struct rfl (scanNextToken_checkFlowValueIndent_ok_of_inFlow _ _ h_flow)
    h_flow_none h_block_none
    (scanNextToken_checkAdjacentValue_ok_of_ne_colon _ (by decide)) h_dc_eq
    ((saveSimpleKey_preserves_directivesPresent s).trans h_dp)
    (scanNextToken_checkBareDocument_ok_of_inFlow _
      ((saveSimpleKey_preserves_inFlow s).trans h_flow))
    (scanNextToken_checkDanglingNode_ok_of_inFlow _ _ h_flow),
    h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_ek_f, h_col_f,
    fun t ht => by rw [h_tok_f] at ht; injection ht with ht; subst ht; exact ⟨nofun, nofun, nofun⟩,
    h_ska_f, h_line_f, (by rw [h_line_f]; exact h_atol_f), h_endline_f, h_stack_f⟩

-- ═══ scanNextToken for '[' from initial state ═══

/-- Structural dispatch returns none for `[` at initial state. -/
lemma dispatchStructural_none_bracket_init (s : ScannerState)
    (h_fl : s.flowLevel = 0)
    (h_noDocStart : atDocumentStart s = false)
    (h_noDocEnd : atDocumentEnd s = false) :
    scanNextToken_dispatchStructural s '[' = .ok none := by
  unfold scanNextToken_dispatchStructural
  simp [ScannerState.inFlow, h_fl, h_noDocStart, h_noDocEnd, pure, Except.pure]

/-- Flow dispatch for `[` returns `some (scanFlowSequenceStart s)`. -/
lemma dispatchFlowIndicators_bracket (s : ScannerState)
    (h_adj : scanNextToken_checkFlowAdjacency s '[' = .ok ()) :
    scanNextToken_dispatchFlowIndicators s '[' = .ok (some (scanFlowSequenceStart s)) := by
  unfold scanNextToken_dispatchFlowIndicators
  rw [h_adj]
  simp [pure, Except.pure, bind, Except.bind]

/-- Token property: `scanFlowSequenceStart` ends with `.flowSequenceStart` as
    last real token.  Mirrors `scanFlowSequenceEnd_lastRealTokenVal`; used to
    re-establish the `completesFlowValue = false` invariant after opening a
    flow sequence (Fix A). -/
lemma scanFlowSequenceStart_lastRealTokenVal (s : ScannerState) :
    lastRealTokenVal? (scanFlowSequenceStart s).tokens = some .flowSequenceStart := by
  have h : (scanFlowSequenceStart s).tokens =
      s.tokens.push ⟨s.currentPos, .flowSequenceStart, s.currentPos⟩ := by
    show ({ ({ s with simpleKey := _ }.emit .flowSequenceStart).advance with
        flowLevel := _, simpleKeyAllowed := _, flowStack := _, simpleKeyStack := _,
                  explicitKeyStack := _, explicitKeyLine := _, explicitKeyCol := _ }).tokens = _
    simp only [ScannerCorrectness.advance_preserves_tokens, ScannerState.emit,
               ScannerState.currentPos]
  rw [h]
  exact lastRealTokenVal_push_non_ph' s.tokens _ nofun

/-- Token property: `scanFlowMappingStart` ends with `.flowMappingStart` as
    last real token. -/
lemma scanFlowMappingStart_lastRealTokenVal (s : ScannerState) :
    lastRealTokenVal? (scanFlowMappingStart s).tokens = some .flowMappingStart := by
  have h : (scanFlowMappingStart s).tokens =
      s.tokens.push ⟨s.currentPos, .flowMappingStart, s.currentPos⟩ := by
    show ({ ({ s with simpleKey := _ }.emit .flowMappingStart).advance with
        flowLevel := _, simpleKeyAllowed := _, flowStack := _, simpleKeyStack := _,
                  explicitKeyStack := _, explicitKeyLine := _, explicitKeyCol := _ }).tokens = _
    simp only [ScannerCorrectness.advance_preserves_tokens, ScannerState.emit,
               ScannerState.currentPos]
  rw [h]
  exact lastRealTokenVal_push_non_ph' s.tokens _ nofun

/-- `scanNextToken` on the initial scanner state at `[` dispatches to
    `scanFlowSequenceStart`, entering flow context.

    Result state has `flowLevel = 1` (i.e. `inFlow = true`),
    `currentIndent = -1`, `col = 1`, and ScannerSurfCorr at rest. -/
lemma scanNextToken_flow_open_init (input : String) (rest : List Char)
    (h_toList : input.toList = '[' :: rest) :
    let s₀ := (ScannerState.mk' input).emit .streamStart
    ∃ s', scanNextToken s₀ = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = 1
      ∧ s'.directivesPresent = false
      ∧ s'.indents = s₀.indents
      ∧ s'.col = 1
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.explicitKeyLine = none
      ∧ s'.line = 0
      ∧ AllTokensOnLine s' 0
      ∧ EndLineOnLine s'
      ∧ s'.simpleKey.possible = false
      ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).map (·.val)
          = #[.streamStart, .flowSequenceStart]
      ∧ s'.simpleKeyStack.size = s'.flowLevel
      ∧ s'.simpleKeyAllowed = true
      ∧ ScannerCorrectness.SimpleKeyStackValid s'
      ∧ (∀ t, lastRealTokenVal? s'.tokens = some t → t.completesFlowValue = false)
      ∧ s'.flowStack.back? = some true := by
  intro s₀
  -- Step 1: preprocessing
  have h_pp := scanNextToken_preprocess_init_state input '[' rest h_toList
    (by decide) (by decide) (by decide)
  obtain ⟨s_pp, h_pp_eq, h_fl_pp, h_inflow_pp, h_ci_pp, h_col_pp,
          h_ad_pp, h_dp_pp, h_ids, h_inp, h_off, h_ie, h_ek_pp,
          h_line_pp, h_atol_pp, h_bd_pp, h_pp_filt⟩ := h_pp
  -- Step 2: ScannerSurfCorr for s_pp
  have h_chars := chars_from_zero_toList input
  rw [h_toList] at h_chars
  have h_corr₀ := initial_corr input _ h_chars
  have h_corr_s₀ : ScannerSurfCorr s₀ ⟨'[' :: rest, 0⟩ :=
    ScannerSurfCorr_transfer h_corr₀ rfl rfl rfl rfl rfl
  have h_corr_pp : ScannerSurfCorr s_pp ⟨'[' :: rest, s_pp.col⟩ := by
    rw [h_col_pp]
    exact ScannerSurfCorr_transfer h_corr_s₀ h_inp h_off h_ie h_col_pp h_ids
  have ⟨h_pk_pp, _⟩ := peek_of_chars_cons s_pp '[' rest _ h_corr_pp
  -- Step 3: atDocumentStart/End false for '['
  have h_pat0 : s_pp.peekAt? 0 = s_pp.peek? := by
    unfold ScannerState.peekAt? ScannerState.peekAt?Loop ScannerState.peek?; rfl
  have h_ds : atDocumentStart s_pp = false := by
    unfold atDocumentStart; rw [h_pat0, h_pk_pp]
    simp only [show (some '[' == some '-') = false from by decide,
               Bool.and_false, Bool.false_and]
  have h_de : atDocumentEnd s_pp = false := by
    unfold atDocumentEnd; rw [h_pat0, h_pk_pp]
    simp only [show (some '[' == some '.') = false from by decide,
               Bool.and_false, Bool.false_and]
  -- Step 4: structural dispatch → none
  have h_struct := dispatchStructural_none_bracket_init s_pp h_fl_pp h_ds h_de
  -- Step 5: allowDirectives update → s_ad
  -- s_pp.allowDirectives = true, so s_ad = { s_pp with ... }
  let s_ad := if s_pp.allowDirectives then
    { s_pp with allowDirectives := false, documentEverStarted := true }
  else s_pp
  have h_ad_fl : s_ad.flowLevel = 0 := by
    simp only [s_ad]; split <;> exact h_fl_pp
  have h_ad_ci : s_ad.currentIndent = -1 := by
    have : s_ad.indents = s_pp.indents := by simp only [s_ad]; split <;> rfl
    unfold ScannerState.currentIndent at h_ci_pp ⊢; rw [this]; exact h_ci_pp
  -- Step 7: flow dispatch → some (scanFlowSequenceStart s_ad)
  have h_flow := dispatchFlowIndicators_bracket s_ad
    (checkFlowAdjacency_ok_of_notInFlow (by simp [ScannerState.inFlow, h_ad_fl]))
  -- Step 8: compose through scanNextToken
  have h_snt : scanNextToken s₀ = .ok (some (scanFlowSequenceStart s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp_eq h_struct rfl (scanNextToken_checkFlowValueIndent_ok_of_sentinel_stack _ _ rfl) h_flow h_dp_pp
      h_bd_pp (scanNextToken_checkDanglingNode_ok_of_sentinel_stack _ _
        (init_indents_sentinel _) (crossedPropsExcessIdx?_init _))
  -- Step 9: field properties of scanFlowSequenceStart s_ad
  have h_ad_col : s_ad.col = 0 := by
    simp only [s_ad]; split <;> exact h_col_pp
  have h_ad_col_eq : s_ad.col = s_pp.col := by simp only [s_ad]; split <;> rfl
  have h_corr_ad : ScannerSurfCorr s_ad ⟨'[' :: rest, s_ad.col⟩ := by
    rw [h_ad_col_eq]
    exact ScannerSurfCorr_transfer h_corr_pp
      (by simp only [s_ad]; split <;> rfl)
      (by simp only [s_ad]; split <;> rfl)
      (by simp only [s_ad]; split <;> rfl)
      h_ad_col_eq
      (by simp only [s_ad]; split <;> rfl)
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ :=
    scanFlowSequenceStart_detail s_ad rest h_corr_ad
  -- Compute final field values
  have h_fl_final : (scanFlowSequenceStart s_ad).flowLevel = 1 := by
    rw [h_fl_f, h_ad_fl]
  have h_dp_final : (scanFlowSequenceStart s_ad).directivesPresent = false := by
    rw [h_dp_f]; simp only [s_ad]; split <;> exact h_dp_pp
  have h_ids_final : (scanFlowSequenceStart s_ad).indents = s₀.indents := by
    rw [h_ids_f]; simp only [s_ad]; split <;> exact h_ids
  have h_col_final : (scanFlowSequenceStart s_ad).col = 1 := by
    rw [h_col_f, h_ad_col]
  -- ScannerSurfCorr at rest with correct col
  have h_corr_result : ScannerSurfCorr (scanFlowSequenceStart s_ad)
      ⟨rest, (scanFlowSequenceStart s_ad).col⟩ := by
    rw [h_col_f]
    exact h_corr_f
  have h_ska_final : (scanFlowSequenceStart s_ad).simpleKeyAllowed = true := rfl
  have h_ssv_final : ScannerCorrectness.SimpleKeyStackValid (scanFlowSequenceStart s_ad) := by
    have h_akv₀ : ScannerCorrectness.AllKeysValid s₀ := by
      refine ⟨fun h_poss => ?_, fun j hj _ => ?_⟩
      · exfalso
        have h_p : s₀.simpleKey.possible = false := by
          show ((ScannerState.mk' input).emit .streamStart).simpleKey.possible = false
          rw [ScannerCorrectness.emit_preserves_simpleKey]; rfl
        rw [h_p] at h_poss; exact absurd h_poss (by decide)
      · exfalso
        have h_sz : s₀.simpleKeyStack.size = 0 := by
          show ((ScannerState.mk' input).emit .streamStart).simpleKeyStack.size = 0
          rw [ScannerCorrectness.emit_preserves_simpleKeyStack]; rfl
        omega
    exact (ScannerCorrectness.scanNextToken_preserves_AllKeysValid s₀
      (scanFlowSequenceStart s_ad) h_akv₀ h_snt).2
  exact ⟨scanFlowSequenceStart s_ad, h_snt, h_corr_result,
         h_fl_final, h_dp_final, h_ids_final, h_col_final,
         by unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl_final]; omega),
         by have hb : (scanFlowSequenceStart s_ad).indents.back? =
                some { column := (-1 : Int), isSequence := false } := by
              rw [h_ids_final]; rfl
            unfold ScannerState.currentIndent; rw [hb]; decide,
         scanFlowSequenceStart_preserves_ek s_ad,
         by rw [scanFlowSequenceStart_line_eq]
            have h_ad_pk : s_ad.peek? = some '[' := by
              simp only [s_ad]; split <;> exact h_pk_pp
            have h_ad_lt := (peek_of_chars_cons s_ad '[' rest _ h_corr_ad).2
            have h_ad_line : s_ad.line = 0 := by simp only [s_ad]; split <;> exact h_line_pp
            exact (advance_line_of_peek s_ad '[' h_ad_lt h_ad_pk (by decide) (by decide)).trans h_ad_line,
         by exact AllTokensOnLine_scanFlowSequenceStart s_ad 0
              (AllTokensOnLine_allowDirectives _ 0 (h_line_pp ▸ h_atol_pp))
              (by simp only [s_ad]; split <;> exact h_line_pp),
         by intro h_poss
            rw [scanFlowSequenceStart_simpleKey_not_possible] at h_poss
            exact absurd h_poss (by decide),
         scanFlowSequenceStart_simpleKey_not_possible s_ad,
         by -- Filtered token characterization:
            have h_fss_tokens : (scanFlowSequenceStart s_ad).tokens
                = s_ad.tokens.push ⟨s_ad.currentPos, .flowSequenceStart, s_ad.currentPos⟩ := by
              show ({ ({ s_ad with simpleKey := _ }.emit .flowSequenceStart).advance with
                  flowLevel := _, simpleKeyAllowed := _,
                  flowStack := _, simpleKeyStack := _,
                  explicitKeyStack := _, explicitKeyLine := _, explicitKeyCol := _ }).tokens = _
              simp only [ScannerCorrectness.advance_preserves_tokens,
                         ScannerState.emit, ScannerState.currentPos]
            have h_ad_tokens : s_ad.tokens = s_pp.tokens := by
              simp only [s_ad]; split <;> rfl
            rw [h_fss_tokens]
            simp only [Array.filter_push,
              show (YamlToken.flowSequenceStart != YamlToken.placeholder) = true from rfl,
              ite_true, Array.map_push,
              show s_ad.tokens = s_pp.tokens from h_ad_tokens,
              h_pp_filt]
            simp [ScannerState.mk', ScannerState.emit],
         by -- Stack/flowLevel sync:
            rw [h_fl_final]
            have h_pre_stack := ScannerCorrectness.preprocess_preserves_simpleKeyStack
              _ _ _ h_pp_eq
            have h_ad_stack_sz : s_ad.simpleKeyStack.size = 0 := by
              simp only [s_ad]; split
              · show s_pp.simpleKeyStack.size = 0; rw [h_pre_stack]; rfl
              · rw [h_pre_stack]; rfl
            rw [ScannerCorrectness.scanFlowSequenceStart_stack_pushed]
            simp [Array.size_push, h_ad_stack_sz],
         h_ska_final, h_ssv_final,
         fun t ht => by
           rw [scanFlowSequenceStart_lastRealTokenVal s_ad] at ht
           simp only [Option.some.injEq] at ht; subst ht; rfl,
         by -- flowStack top: '[' pushes `true` (9a kind tracking)
           rw [L4YAML.Proofs.ScannerFlowCollection.scanFlowSequenceStart_pushes_true]
           exact Array.back?_push⟩

-- Helper: Nat BEq with 0
lemma nat_beq_zero_false (n : Nat) (h : n > 0) : (n == 0) = false := by
  cases n with | zero => omega | succ => rfl

lemma nat_beq_zero_true {n : Nat} (h : n = 0) : (n == 0) = true := by
  subst h; rfl

-- ═══ Nested flow open: `[` when already in flow context ═══

/-- `scanNextToken` dispatches `[` in flow context to `scanFlowSequenceStart`,
    incrementing flowLevel. Similar to `scanNextToken_flow_open_init` but
    for the nested case where flowLevel > 0. -/
lemma scanNextToken_flow_open_nested (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'[' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_dp : s.directivesPresent = false)
    (h_last : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel + 1
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = none
      ∧ s'.col = s.col + 1
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ StackEndLineOnLine s' s'.line
      ∧ s'.simpleKeyStack.pop = s.simpleKeyStack
      ∧ s'.simpleKey.possible = false
      ∧ s.tokens.size < s'.tokens.size
      ∧ s'.simpleKeyStack = s.simpleKeyStack.push (saveSimpleKey s).simpleKey
      ∧ (∀ t, lastRealTokenVal? s'.tokens = some t → t.completesFlowValue = false)
      ∧ s'.flowStack = s.flowStack.push true
      ∧ s'.explicitKeyStack = s.explicitKeyStack.push (s.explicitKeyLine, s.explicitKeyCol) := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '[')) :=
    scanNextToken_preprocess_flow s '[' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  -- Step 2: structural dispatch → none (inFlow)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '[' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent)
      (h_sk_col ▸ h_col_pos)
  -- Step 3: allowDirectives update
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  -- Step 5: flow dispatch → some (scanFlowSequenceStart s_ad)
  have h_ad_tokens : s_ad.tokens = (saveSimpleKey s).tokens := by
    simp only [s_ad]; split <;> rfl
  have h_flow_disp := dispatchFlowIndicators_bracket s_ad
    (checkFlowAdjacency_ok_of_notCompletes (fun t ht =>
      saveSimpleKey_preserves_completesFalse s h_last t (h_ad_tokens ▸ ht)))
  -- Step 6: compose through scanNextToken
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl (scanNextToken_checkFlowValueIndent_ok_of_inFlow _ _ h_flow) h_flow_disp
    ((saveSimpleKey_preserves_directivesPresent s).trans h_dp)
    (scanNextToken_checkBareDocument_ok_of_inFlow _
      ((saveSimpleKey_preserves_inFlow s).trans h_flow))
    (scanNextToken_checkDanglingNode_ok_of_inFlow _ _ h_flow)
  -- Step 7: properties of scanFlowSequenceStart s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).explicitKeyLine = _
      unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
  have h_ad_col : s_ad.col = s.col := by
    simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨'[' :: rest, s_ad.col⟩ := by
    rw [show s_ad.col = s.col from h_ad_col]
    exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ :=
    scanFlowSequenceStart_detail s_ad rest h_ad_corr
  have h_ek_f := scanFlowSequenceStart_preserves_ek s_ad
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have ⟨h_peek_ad, h_lt_ad⟩ := peek_of_chars_cons s_ad '[' rest s_ad.col h_ad_corr
  have h_line_f : (scanFlowSequenceStart s_ad).line = s.line := by
    rw [scanFlowSequenceStart_line_eq]
    exact (advance_line_of_peek s_ad '[' h_lt_ad h_peek_ad (by decide) (by decide)).trans h_ad_line
  refine ⟨_, h_snt, ?_, h_fl_f.trans (congrArg (· + 1) h_ad_fl),
    h_dp_f.trans h_ad_dp, h_ids_f.trans h_ad_ids, h_ek_f, ?_, h_line_f, ?_, ?_, ?_, ?_,
    ScannerCorrectness.scanFlowSequenceStart_simpleKey_cleared s_ad, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_col_f]; exact h_corr_f
  · rw [h_col_f, h_ad_col]
  · rw [h_line_f]
    exact AllTokensOnLine_scanFlowSequenceStart s_ad s.line
      (AllTokensOnLine_allowDirectives _ _
        (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl)) h_ad_line
  · -- EndLineOnLine: scanFlowSequenceStart sets simpleKey.possible = false
    intro h_poss
    rw [scanFlowSequenceStart_simpleKey_not_possible] at h_poss
    exact absurd h_poss (by decide)
  · -- StackEndLineOnLine: pushed savedKey = s_ad.simpleKey satisfies EndLineOnLine at s'.line
    unfold StackEndLineOnLine
    rw [ScannerCorrectness.scanFlowSequenceStart_stack_pushed, Array.back?_push, h_line_f]
    intro h_poss
    have h_ad_endline : EndLineOnLine s_ad := by
      simp only [s_ad]; split
      · show EndLineOnLine { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
        exact EndLineOnLine_saveSimpleKey_flow s h_endline
      · exact EndLineOnLine_saveSimpleKey_flow s h_endline
    exact ⟨(h_ad_endline h_poss).1.trans h_ad_line, (h_ad_endline h_poss).2.trans h_ad_line⟩
  · -- simpleKeyStack.pop = s.simpleKeyStack
    rw [ScannerCorrectness.scanFlowSequenceStart_stack_pushed, Array.pop_push]
    show s_ad.simpleKeyStack = s.simpleKeyStack
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
  · -- s.tokens.size < s'.tokens.size
    rw [ScannerCorrectness.scanFlowSequenceStart_adds_one_token]
    have h_ad_tok : s.tokens.size ≤ s_ad.tokens.size := by
      simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_tokens_monotonic s
    omega
  · -- simpleKeyStack = s.simpleKeyStack.push (saveSimpleKey s).simpleKey
    rw [ScannerCorrectness.scanFlowSequenceStart_stack_pushed]
    have h1 : s_ad.simpleKeyStack = s.simpleKeyStack := by
      simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
    have h2 : s_ad.simpleKey = (saveSimpleKey s).simpleKey := by
      simp only [s_ad]; split <;> rfl
    rw [h1, h2]
  · -- last real token is .flowSequenceStart ⇒ does not complete a flow value
    intro t ht
    rw [scanFlowSequenceStart_lastRealTokenVal s_ad] at ht
    simp only [Option.some.injEq] at ht; subst ht; rfl
  · -- flowStack: '[' pushes `true` (9a kind tracking)
    rw [L4YAML.Proofs.ScannerFlowCollection.scanFlowSequenceStart_pushes_true]
    congr 1
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowStack s
  · -- explicitKeyStack: the open pushes the outer stamp (item 98)
    rw [ScannerCorrectness.scanFlowSequenceStart_ek_pushed]
    have h1 : s_ad.explicitKeyStack = s.explicitKeyStack := by
      simp only [s_ad]; split
      · show (saveSimpleKey s).explicitKeyStack = _
        unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
      · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    have h2 : s_ad.explicitKeyCol = s.explicitKeyCol := by
      simp only [s_ad]; split
      · show (saveSimpleKey s).explicitKeyCol = _
        unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
      · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    rw [h1, h2, h_ad_ek]

-- ═══ Block indicators: concrete none lemmas ═══

/-- `dispatchBlockIndicators` returns `none` for `,`. -/
lemma dispatchBlockIndicators_none_comma (s : ScannerState) :
    scanNextToken_dispatchBlockIndicators s ',' = .ok none := by
  unfold scanNextToken_dispatchBlockIndicators
  simp only [bind, Except.bind, pure, Except.pure]
  split
  · rename_i h; simp at h
  · split
    · rename_i h; simp at h
    · split
      · rename_i h; simp at h
      · rfl

/-- `dispatchBlockIndicators` returns `none` for `]`. -/
lemma dispatchBlockIndicators_none_close_bracket (s : ScannerState) :
    scanNextToken_dispatchBlockIndicators s ']' = .ok none := by
  unfold scanNextToken_dispatchBlockIndicators
  simp only [bind, Except.bind, pure, Except.pure]
  split
  · rename_i h; simp at h
  · split
    · rename_i h; simp at h
    · split
      · rename_i h; simp at h
      · rfl

-- ═══ Flow comma: scanFlowEntry dispatch ═══

/-- `scanFlowEntry` succeeds when the last real token is not a flow
    delimiter (flowSequenceStart, flowMappingStart, or flowEntry).
    This holds whenever we've just scanned a content token (scalar, etc.). -/
lemma scanFlowEntry_ok (s : ScannerState)
    (h_last : ∀ t, lastRealTokenVal? s.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry) :
    scanFlowEntry s =
      .ok { (s.emit .flowEntry).advance with
              simpleKeyAllowed := true
              explicitKeyLine := none
              simpleKey := { possible := false } } := by
  unfold scanFlowEntry; dsimp only [bind, Except.bind, pure, Except.pure]
  -- After unfold+dsimp, the goal has a match on lastRealTokenVal? and if-then-else
  cases h_lrt : lastRealTokenVal? s.tokens with
  | none => rfl
  | some t =>
    have ⟨h1, h2, h3⟩ := h_last t h_lrt
    -- Show the boolean condition is false by case analysis on each BEq
    have : (t == YamlToken.flowSequenceStart) = false := by
      cases h : (t == YamlToken.flowSequenceStart)
      · rfl
      · exact absurd (beq_iff_eq.mp h) h1
    have : (t == YamlToken.flowMappingStart) = false := by
      cases h : (t == YamlToken.flowMappingStart)
      · rfl
      · exact absurd (beq_iff_eq.mp h) h2
    have : (t == YamlToken.flowEntry) = false := by
      cases h : (t == YamlToken.flowEntry)
      · rfl
      · exact absurd (beq_iff_eq.mp h) h3
    simp_all

/-- Field preservation through scanFlowEntry. -/
lemma scanFlowEntry_detail (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨',' :: rest, s.col⟩)
    (h_last : ∀ t, lastRealTokenVal? s.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry) :
    let s' := { (s.emit .flowEntry).advance with simpleKeyAllowed := true, explicitKeyLine := none, simpleKey := { possible := false } }
    scanFlowEntry s = .ok s'
    ∧ ScannerSurfCorr s' ⟨rest, s.col + 1⟩
    ∧ s'.flowLevel = s.flowLevel
    ∧ s'.directivesPresent = s.directivesPresent
    ∧ s'.indents = s.indents
    ∧ s'.col = s.col + 1 := by
  have h_ok := scanFlowEntry_ok s h_last
  have ⟨_, h_lt⟩ := peek_of_chars_cons s ',' rest _ hcorr
  let s_em := s.emit .flowEntry
  have h_em_corr : ScannerSurfCorr s_em ⟨',' :: rest, s.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have h_adv_corr := advance_non_newline_corr s_em ',' rest h_em_corr
    (show s_em.offset < s_em.inputEnd from h_lt) (by decide) (by decide)
  refine ⟨h_ok, ?_, ?_, ?_, ?_, ?_⟩
  · -- ScannerSurfCorr
    exact ⟨h_adv_corr.chars_from, h_adv_corr.col_eq, h_adv_corr.end_eq,
           h_adv_corr.input_prefix, h_adv_corr.indent_cols_nonneg⟩
  · -- flowLevel: { s_em.advance with simpleKeyAllowed := true }.flowLevel = s.flowLevel
    dsimp only []
    rw [ScannerCorrectness.advance_preserves_flowLevel,
        ScannerCorrectness.emit_preserves_flowLevel]
  · -- directivesPresent
    dsimp only []
    rw [advance_preserves_dp]; rfl
  · -- indents
    dsimp only []
    rw [advance_preserves_indents]; rfl
  · -- col: { s_em.advance with ... }.col = s.col + 1
    -- h_adv_corr.col_eq : ⟨rest, s_em.col + 1⟩.col = s_em.advance.col
    -- i.e., s_em.col + 1 = s_em.advance.col, and s_em.col = s.col (emit preserves)
    dsimp only []
    exact h_adv_corr.col_eq.symm

-- Helper: lastRealTokenVal? on array.push tok when tok.val ≠ .placeholder returns tok.val.
lemma lastRealTokenVal_push_non_ph
    (tokens : Array (Positioned YamlToken))
    (tok : Positioned YamlToken) (h_nph : tok.val ≠ .placeholder) :
    lastRealTokenVal? (tokens.push tok) = some tok.val := by
  unfold lastRealTokenVal?; dsimp only []
  simp only [Array.size_push, show tokens.size + 1 > 0 from by omega, ↓reduceIte,
    show tokens.size + 1 - 1 = tokens.size from by omega]
  rw [getElem!_pos _ _ (by simp [Array.size_push])]
  simp only [Array.getElem_push_eq]
  have : (tok.val == YamlToken.placeholder) = false :=
    beq_eq_false_iff_ne.mpr h_nph
  simp [this]

-- Helper: saveSimpleKey preserves "no trailing flow delimiter" property of lastRealTokenVal?.
-- saveSimpleKey either leaves tokens unchanged or pushes exactly 2 .placeholder tokens.
-- lastRealTokenVal? skips up to 2 trailing placeholders, so either reaches the same original
-- token (which h_last covers) or returns .placeholder (which is trivially ≠ flow delimiters).
lemma saveSimpleKey_preserves_lastRealTokenVal_ne_flow (s : ScannerState)
    (h_last : ∀ t, lastRealTokenVal? s.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
    (t : YamlToken)
    (ht : lastRealTokenVal? (saveSimpleKey s).tokens = some t) :
    t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry := by
  have h_cases : (saveSimpleKey s).tokens = s.tokens ∨
      (saveSimpleKey s).tokens = ((s.tokens.push ⟨s.currentPos, .placeholder, s.currentPos⟩).push
        ⟨s.currentPos, .placeholder, s.currentPos⟩) := by
    unfold saveSimpleKey
    split
    · exact .inl rfl
    · split
      · right; dsimp only []
      · exact .inl rfl
  rcases h_cases with h_eq | h_eq
  · rw [h_eq] at ht; exact h_last t ht
  · rw [h_eq] at ht
    have h_or := lastRealTokenVal_push_two_ph s.tokens
      ⟨s.currentPos, .placeholder, s.currentPos⟩
      ⟨s.currentPos, .placeholder, s.currentPos⟩ rfl rfl t ht
    cases h_or with
    | inl h => exact h_last t h
    | inr h => subst h; exact ⟨by decide, by decide, by decide⟩

/-- Flow dispatch for `,` returns `some (scanFlowEntry result)` when flowLevel > 0. -/
lemma dispatchFlowIndicators_comma (s : ScannerState)
    (h_fl : s.flowLevel > 0)
    (h_last : ∀ t, lastRealTokenVal? s.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry) :
    scanNextToken_dispatchFlowIndicators s ',' =
      .ok (some { (s.emit .flowEntry).advance with simpleKeyAllowed := true, explicitKeyLine := none, simpleKey := { possible := false } }) := by
  unfold scanNextToken_dispatchFlowIndicators
  rw [checkFlowAdjacency_ok_of_sepChar (by decide)]
  simp only [bind, Except.bind, pure, Except.pure,
    show (',' == '[') = false from by decide,
    show (',' == ']') = false from by decide,
    show (',' == '{') = false from by decide,
    show (',' == '}') = false from by decide,
    show (',' == ',') = true from by decide, ite_true]
  simp only [show (s.flowLevel == 0) = false from nat_beq_zero_false _ (by omega)]
  -- Goal: Bind.bind (scanFlowEntry s) (pure ∘ some) = .ok (some { ... })
  rw [scanFlowEntry_ok s h_last]
  rfl

/-- Full `scanNextToken` for `,` in flow context.
    Handles preprocessing (skips nothing for non-ws `,`),
    structural dispatch (none), flow dispatch (scanFlowEntry). -/
lemma scanNextToken_flow_comma (s : ScannerState)
    (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨',' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_last : ∀ t, lastRealTokenVal? s.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
    (h_atol : AllTokensOnLine s s.line)
    (_h_endline : EndLineOnLine s)
    (h_ek : s.explicitKeyLine = none)
    (h_dp : s.directivesPresent = false) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col = s.col + 1
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ (∀ t, lastRealTokenVal? s'.tokens = some t → t.completesFlowValue = false) := by
  -- Step 1: preprocessing
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ',')) :=
    scanNextToken_preprocess_flow s ',' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  -- Step 2: structural dispatch → none
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ',' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  -- Step 3: allowDirectives update
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  -- Step 5: flow dispatch for ','
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_fl_pos : s_ad.flowLevel > 0 := by
    rw [h_ad_fl]; unfold ScannerState.inFlow at h_flow; exact of_decide_eq_true h_flow
  have h_ad_corr : ScannerSurfCorr s_ad ⟨',' :: rest, s_ad.col⟩ := by
    have h_ad_col_eq : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
    rw [h_ad_col_eq]
    exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col_eq
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  have h_ad_last : ∀ t, lastRealTokenVal? s_ad.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry := by
    intro t ht
    have h_ad_toks : s_ad.tokens = (saveSimpleKey s).tokens := by
      simp only [s_ad]; split <;> rfl
    rw [h_ad_toks] at ht
    exact saveSimpleKey_preserves_lastRealTokenVal_ne_flow s h_last t ht
  have h_flow_disp := dispatchFlowIndicators_comma s_ad h_fl_pos h_ad_last
  -- Step 6: compose
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl (scanNextToken_checkFlowValueIndent_ok_of_inFlow _ _ h_flow) h_flow_disp
    ((saveSimpleKey_preserves_directivesPresent s).trans h_dp)
    (scanNextToken_checkBareDocument_ok_of_inFlow _
      ((saveSimpleKey_preserves_inFlow s).trans h_flow))
    (scanNextToken_checkDanglingNode_ok_of_inFlow _ _ h_flow)
  -- Step 7: extract properties
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).explicitKeyLine = _
      unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
  have h_ad_col : s_ad.col = s.col := by
    simp only [s_ad]; split <;> exact h_sk_col
  have ⟨_, h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ := scanFlowEntry_detail s_ad rest h_ad_corr h_ad_last
  -- Item 9l: the `,` CLEARS the explicit-key line, so this is preservation only
  -- under the chain's standing `h_ek` (which every caller carries).
  have h_ek_f : ({ (s_ad.emit .flowEntry).advance with
      simpleKeyAllowed := true, explicitKeyLine := none, simpleKey := { possible := false } }).explicitKeyLine =
      s.explicitKeyLine := by
    dsimp only []; exact h_ek.symm
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have ⟨h_peek_ad, h_lt_ad⟩ := peek_of_chars_cons s_ad ',' rest s_ad.col h_ad_corr
  have h_line_f : ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true, explicitKeyLine := none, simpleKey := { possible := false } }).line = s.line := by
    dsimp only []
    rw [advance_line_of_peek (s_ad.emit .flowEntry) ',' h_lt_ad h_peek_ad (by decide) (by decide)]
    exact h_ad_line
  refine ⟨_, h_snt, ?_, h_fl_f.trans h_ad_fl, h_dp_f.trans h_ad_dp, h_ids_f.trans h_ad_ids,
    h_ek_f, ?_, h_line_f, ?_, ?_, ?_, ?_⟩
  · rw [h_col_f]; exact h_corr_f
  · rw [h_col_f, h_ad_col]
  · rw [h_line_f]
    exact AllTokensOnLine_advance _ _ (AllTokensOnLine_emit _ _ _
      (AllTokensOnLine_allowDirectives _ _
        (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl)) h_ad_line)
  · -- EndLineOnLine: vacuous — the `,` clears the pending simple key (item 9q)
    intro h_poss
    simp at h_poss
  · -- simpleKeyStack preserved: scanFlowEntry doesn't touch stack
    show ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true, explicitKeyLine := none, simpleKey := { possible := false } }).simpleKeyStack = s.simpleKeyStack
    dsimp only []
    rw [ScannerCorrectness.advance_preserves_simpleKeyStack, ScannerCorrectness.emit_preserves_simpleKeyStack]
    show s_ad.simpleKeyStack = s.simpleKeyStack
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
  · -- last real token is .flowEntry ⇒ does not complete a flow value
    intro t ht
    have h_tok : lastRealTokenVal?
        ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true, explicitKeyLine := none, simpleKey := { possible := false } }).tokens
          = some .flowEntry := by
      show lastRealTokenVal? ((s_ad.emit .flowEntry).advance).tokens = _
      rw [ScannerCorrectness.advance_preserves_tokens]
      show lastRealTokenVal? (s_ad.tokens.push { pos := s_ad.currentPos, val := .flowEntry }) = _
      exact lastRealTokenVal_push_non_ph' s_ad.tokens _ nofun
    rw [h_tok] at ht; simp only [Option.some.injEq] at ht; subst ht; rfl

/-- **Comma raw-push add-on** (item 9r): from a state whose simple key is not
    re-reservable (`simpleKeyAllowed = false` — every post-value state), the
    flow `,` grows the RAW token array by exactly one `.flowEntry`:
    preprocessing's `saveSimpleKey` is the identity, and `scanFlowEntry` is one
    emit.  This is what re-opens `LastRawNotValue` at a pair-list's recursion
    tail, the raw twin of `scanNextToken_flow_comma_filtered_push`. -/
lemma scanNextToken_flow_comma_raw_push (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨',' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_ska : s.simpleKeyAllowed = false)
    (h_last : ∀ t, lastRealTokenVal? s.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    (∃ tok : Positioned YamlToken, tok.val = .flowEntry ∧ s'.tokens = s.tokens.push tok)
      ∧ s'.simpleKeyAllowed = true ∧ s'.simpleKey.possible = false := by
  have h_sk_id : saveSimpleKey s = s := by
    unfold saveSimpleKey
    split
    · rfl
    · simp [h_ska]
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ',')) :=
    scanNextToken_preprocess_flow s ',' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ',' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_fl_pos : s_ad.flowLevel > 0 := by
    rw [h_ad_fl]; unfold ScannerState.inFlow at h_flow; exact of_decide_eq_true h_flow
  have h_ad_toks : s_ad.tokens = s.tokens := by
    simp only [s_ad]; split <;> rw [h_sk_id]
  have h_ad_last : ∀ t, lastRealTokenVal? s_ad.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry := by
    intro t ht
    rw [h_ad_toks] at ht
    exact h_last t ht
  have h_flow_disp := dispatchFlowIndicators_comma s_ad h_fl_pos h_ad_last
  have h_snt_eq : scanNextToken s =
      .ok (some { (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true, explicitKeyLine := none, simpleKey := { possible := false } }) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl (scanNextToken_checkFlowValueIndent_ok_of_inFlow _ _ h_flow) h_flow_disp
      (scanNextToken_ok_directivesPresent_false h_pp h_struct h_snt)
      (scanNextToken_ok_checkBareDocument h_pp h_struct h_snt)
      (scanNextToken_ok_checkDanglingNode h_pp h_snt)
  have h_s' : s' = { (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true, explicitKeyLine := none, simpleKey := { possible := false } } :=
    Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
  refine ⟨⟨{ pos := s_ad.currentPos, val := .flowEntry }, rfl, ?_⟩, by rw [h_s'], by rw [h_s']⟩
  rw [h_s']
  show ((s_ad.emit .flowEntry).advance).tokens = _
  rw [ScannerCorrectness.advance_preserves_tokens]
  show s_ad.tokens.push { pos := s_ad.currentPos, val := .flowEntry } = _
  rw [h_ad_toks]

-- ═══ Flow close bracket: scanFlowSequenceEnd dispatch ═══

/-- Field preservation through scanFlowSequenceEnd: directivesPresent. -/
lemma scanFlowSequenceEnd_preserves_dp (s : ScannerState) :
    (scanFlowSequenceEnd s).directivesPresent = s.directivesPresent := by
  unfold scanFlowSequenceEnd; dsimp only []; simp only [advance_preserves_dp, ScannerState.emit]

/-- Field preservation through scanFlowSequenceEnd: indents. -/
lemma scanFlowSequenceEnd_preserves_indents (s : ScannerState) :
    (scanFlowSequenceEnd s).indents = s.indents := by
  unfold scanFlowSequenceEnd; dsimp only []; simp only [advance_preserves_indents, ScannerState.emit]

lemma scanFlowSequenceEnd_preserves_ek (s : ScannerState) :
    (scanFlowSequenceEnd s).explicitKeyLine
      = (s.explicitKeyStack.back?.getD (none, -1)).1 :=
  ScannerCorrectness.scanFlowSequenceEnd_ek_restored s

/-- FlowLevel through scanFlowSequenceEnd: decremented by 1. -/
lemma scanFlowSequenceEnd_flowLevel (s : ScannerState) :
    (scanFlowSequenceEnd s).flowLevel =
      if s.flowLevel > 0 then s.flowLevel - 1 else 0 := by
  unfold scanFlowSequenceEnd; dsimp only []
  simp only [ScannerCorrectness.advance_preserves_flowLevel,
             ScannerCorrectness.emit_preserves_flowLevel]

/-- ScannerSurfCorr + properties through scanFlowSequenceEnd. -/
lemma scanFlowSequenceEnd_detail (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨']' :: rest, s.col⟩) :
    ScannerSurfCorr (scanFlowSequenceEnd s) ⟨rest, s.col + 1⟩
    ∧ (scanFlowSequenceEnd s).flowLevel = (if s.flowLevel > 0 then s.flowLevel - 1 else 0)
    ∧ (scanFlowSequenceEnd s).directivesPresent = s.directivesPresent
    ∧ (scanFlowSequenceEnd s).indents = s.indents
    ∧ (scanFlowSequenceEnd s).col = s.col + 1 := by
  have ⟨_, h_lt⟩ := peek_of_chars_cons s ']' rest _ hcorr
  let s_em := s.emit .flowSequenceEnd
  have h_em_corr : ScannerSurfCorr s_em ⟨']' :: rest, s.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have h_adv_corr := advance_non_newline_corr s_em ']' rest h_em_corr
    (show s_em.offset < s_em.inputEnd from h_lt) (by decide) (by decide)
  have h_col_eq : (scanFlowSequenceEnd s).col = s.col + 1 := by
    unfold scanFlowSequenceEnd; dsimp only []; exact h_adv_corr.col_eq.symm
  refine ⟨?_, scanFlowSequenceEnd_flowLevel s,
          scanFlowSequenceEnd_preserves_dp s,
          scanFlowSequenceEnd_preserves_indents s, h_col_eq⟩
  -- ScannerSurfCorr: scanFlowSequenceEnd only adds flowLevel/simpleKeyAllowed/flowStack/simpleKey/simpleKeyStack
  -- on top of (s.emit .flowSequenceEnd).advance
  unfold scanFlowSequenceEnd
  exact ⟨h_adv_corr.chars_from, h_adv_corr.col_eq, h_adv_corr.end_eq,
         h_adv_corr.input_prefix, h_adv_corr.indent_cols_nonneg⟩

/-- Token property: `scanFlowSequenceEnd` ends with `.flowSequenceEnd` as last real token. -/
lemma scanFlowSequenceEnd_lastRealTokenVal (s : ScannerState) :
    lastRealTokenVal? (scanFlowSequenceEnd s).tokens = some .flowSequenceEnd := by
  unfold scanFlowSequenceEnd; dsimp only []
  -- tokens = (s.emit .flowSequenceEnd).advance.tokens
  --        = (s.emit .flowSequenceEnd).tokens (advance preserves tokens)
  --        = s.tokens.push { pos := s.currentPos, val := .flowSequenceEnd }
  show lastRealTokenVal? (s.emit .flowSequenceEnd).advance.tokens = _
  rw [ScannerCorrectness.advance_preserves_tokens (s.emit .flowSequenceEnd)]
  show lastRealTokenVal? (s.tokens.push { pos := s.currentPos, val := .flowSequenceEnd }) = _
  exact lastRealTokenVal_push_non_ph' s.tokens _ nofun

/-- `validateFlowClose` passes when flowLevel > 0. -/
lemma validateFlowClose_pass_nested (s : ScannerState) (h_fl : s.flowLevel > 0) :
    validateFlowClose s = .ok () := by
  unfold validateFlowClose
  have := nat_beq_zero_false s.flowLevel (by omega : s.flowLevel > 0)
  simp [this, pure, Except.pure]

/-- `skipTrailingSpaces` at EOF is a no-op. -/
lemma skipTrailingSpaces_at_eof (s : ScannerState) (n : Nat) (h : s.peek? = none) :
    skipTrailingSpaces s n = s := by
  cases n with
  | zero => unfold skipTrailingSpaces; rfl
  | succ m =>
    unfold skipTrailingSpaces
    split
    · split
      · simp_all
      · rfl
    · rfl

/-- `validateFlowClose` passes at flowLevel = 0 when peek? = none (EOF). -/
lemma validateFlowClose_pass_eof (s : ScannerState)
    (h_fl : s.flowLevel = 0) (h_eof : s.peek? = none) :
    validateFlowClose s = .ok () := by
  unfold validateFlowClose
  simp only [show (s.flowLevel == 0) = true from nat_beq_zero_true h_fl]
  simp [skipTrailingSpaces_at_eof s _ h_eof, h_eof, pure, Except.pure]

/-- Flow dispatch for `]` returns `some (scanFlowSequenceEnd s)` when
    flowLevel ≥ 2 (nested case — validateFlowClose is no-op). -/
lemma dispatchFlowIndicators_close_bracket_nested (s : ScannerState)
    (h_fl : s.flowLevel ≥ 2)
    (h_kind : s.flowStack.back? = some true) :
    scanNextToken_dispatchFlowIndicators s ']' = .ok (some (scanFlowSequenceEnd s)) := by
  unfold scanNextToken_dispatchFlowIndicators
  rw [checkFlowAdjacency_ok_of_sepChar (by decide)]
  simp only [bind, Except.bind, pure, Except.pure,
    show (']' == '[') = false from by decide,
    show (']' == ']') = true from by decide]
  have h_ne := nat_beq_zero_false s.flowLevel (by omega : s.flowLevel > 0)
  simp only [h_ne, h_kind]
  have h_fl_after : (scanFlowSequenceEnd s).flowLevel > 0 := by
    rw [scanFlowSequenceEnd_flowLevel]; split <;> omega
  rw [validateFlowClose_pass_nested _ h_fl_after]
  simp

/-- Full `scanNextToken` for `]` in flow context when flowLevel ≥ 2
    (nested flow close — no validateFlowClose concern). -/
lemma scanNextToken_flow_close_seq_nested (s : ScannerState)
    (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨']' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_fl_ge2 : s.flowLevel ≥ 2)
    (h_atol : AllTokensOnLine s s.line)
    (h_stack_endline : StackEndLineOnLine s s.line)
    (h_dp : s.directivesPresent = false)
    (h_kind : s.flowStack.back? = some true) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel - 1
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = (s.explicitKeyStack.back?.getD (none, -1)).1
      ∧ s'.col = s.col + 1
      ∧ (∀ t, lastRealTokenVal? s'.tokens = some t →
          t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
      ∧ s'.simpleKeyAllowed = false
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack.pop
      ∧ s'.simpleKey = s.simpleKeyStack.back?.getD {}
      ∧ (∀ i, i < s.tokens.size → s'.tokens[i]? = s.tokens[i]?)
      ∧ s'.explicitKeyStack = s.explicitKeyStack.pop := by
  -- Step 1: preprocessing
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ']')) :=
    scanNextToken_preprocess_flow s ']' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  -- Step 2: structural dispatch → none
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ']' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  -- Step 3: allowDirectives update
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  -- Step 5: flow dispatch for ']'
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_fl_pos : s_ad.flowLevel > 0 := by rw [h_ad_fl]; omega
  have h_ad_col : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨']' :: rest, s_ad.col⟩ := by
    rw [h_ad_col]
    exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  -- Flow dispatch: nested close, flowLevel ≥ 2 so validateFlowClose is no-op
  have h_ad_fl_ge2 : s_ad.flowLevel ≥ 2 := by rw [h_ad_fl]; exact h_fl_ge2
  have h_ad_kind : s_ad.flowStack.back? = some true := by
    have h_ad_fs : s_ad.flowStack = s.flowStack := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowStack s
    rw [h_ad_fs]; exact h_kind
  have h_flow_disp := dispatchFlowIndicators_close_bracket_nested s_ad h_ad_fl_ge2 h_ad_kind
  -- Step 6: compose
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl (scanNextToken_checkFlowValueIndent_ok_of_inFlow _ _ h_flow) h_flow_disp
    ((saveSimpleKey_preserves_directivesPresent s).trans h_dp)
    (scanNextToken_checkBareDocument_ok_of_inFlow _
      ((saveSimpleKey_preserves_inFlow s).trans h_flow))
    (scanNextToken_checkDanglingNode_ok_of_inFlow _ _ h_flow)
  -- Step 7: extract properties
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).explicitKeyLine = _
      unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
  have ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ := scanFlowSequenceEnd_detail s_ad rest h_ad_corr
  have h_ad_eks : s_ad.explicitKeyStack = s.explicitKeyStack := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_ekStack s
  have h_ek_f : (scanFlowSequenceEnd s_ad).explicitKeyLine
      = (s.explicitKeyStack.back?.getD (none, -1)).1 :=
    (scanFlowSequenceEnd_preserves_ek s_ad).trans (by rw [h_ad_eks])
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have ⟨h_peek_ad, h_lt_ad⟩ := peek_of_chars_cons s_ad ']' rest s_ad.col h_ad_corr
  have h_line_f : (scanFlowSequenceEnd s_ad).line = s.line := by
    show (s_ad.emit .flowSequenceEnd).advance.line = s.line
    rw [advance_line_of_peek (s_ad.emit .flowSequenceEnd) ']' h_lt_ad h_peek_ad (by decide) (by decide)]
    exact h_ad_line
  refine ⟨_, h_snt, ?_, ?_, h_dp_f.trans h_ad_dp, h_ids_f.trans h_ad_ids, h_ek_f, ?_, ?_, ?_, h_line_f, ?_, ?_, ?_, ?_, ?_,
    (ScannerCorrectness.scanFlowSequenceEnd_ekstack_popped s_ad).trans (by rw [h_ad_eks])⟩
  · rw [h_col_f]; exact h_corr_f
  · rw [h_fl_f]; split
    · rw [h_ad_fl]
    · exfalso; omega
  · rw [h_col_f, h_ad_col]
  · -- lastRealTokenVal? = .flowSequenceEnd
    intro t ht
    have h_lrt := scanFlowSequenceEnd_lastRealTokenVal s_ad
    rw [h_lrt] at ht; injection ht with ht; subst ht
    exact ⟨by decide, by decide, by decide⟩
  · -- simpleKeyAllowed = false
    show (scanFlowSequenceEnd s_ad).simpleKeyAllowed = false
    rfl
  · -- AllTokensOnLine
    rw [h_line_f]
    exact AllTokensOnLine_scanFlowSequenceEnd s_ad s.line
      (AllTokensOnLine_allowDirectives _ _
        (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl)) h_ad_line
  · -- EndLineOnLine: simpleKey restored from stack
    intro h_poss
    rw [ScannerCorrectness.scanFlowSequenceEnd_simpleKey_restored] at h_poss ⊢
    have h_ad_stack : s_ad.simpleKeyStack = s.simpleKeyStack := by
      simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
    rw [h_ad_stack] at h_poss ⊢
    unfold StackEndLineOnLine at h_stack_endline
    rw [h_line_f]
    cases h_back : s.simpleKeyStack.back? with
    | none => rw [h_back] at h_poss; simp [Option.getD] at h_poss
    | some sk =>
      rw [h_back] at h_poss h_stack_endline; simp [Option.getD] at h_poss
      exact h_stack_endline h_poss
  · -- simpleKeyStack.pop
    show (scanFlowSequenceEnd s_ad).simpleKeyStack = s.simpleKeyStack.pop
    rw [ScannerCorrectness.scanFlowSequenceEnd_stack_popped]
    show s_ad.simpleKeyStack.pop = s.simpleKeyStack.pop
    congr 1
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
  · -- simpleKey restored from popped stack top
    rw [ScannerCorrectness.scanFlowSequenceEnd_simpleKey_restored]
    have h_ad_stack : s_ad.simpleKeyStack = s.simpleKeyStack := by
      simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
    rw [h_ad_stack]
  · -- prefix preservation: close only appends
    intro i hi
    have h_ad_tok : s_ad.tokens = (saveSimpleKey s).tokens := by
      simp only [s_ad]; split <;> rfl
    obtain ⟨tok, h_end_tok⟩ : ∃ tok, (scanFlowSequenceEnd s_ad).tokens = s_ad.tokens.push tok :=
      ⟨_, by unfold scanFlowSequenceEnd ScannerState.emit; rw [ScannerCorrectness.advance_preserves_tokens]⟩
    rw [h_end_tok, h_ad_tok, Array.getElem?_push,
        ite_eq_right (by have := ScannerCorrectness.saveSimpleKey_tokens_monotonic s; omega : i ≠ (saveSimpleKey s).tokens.size),
        Array.getElem?_eq_getElem (by have := ScannerCorrectness.saveSimpleKey_tokens_monotonic s; omega),
        Array.getElem?_eq_getElem hi, ScannerCorrectness.saveSimpleKey_preserves_prefix s i hi]

-- ═══ Outermost flow close: ] at flowLevel = 1 ═══

/-- `scanFlowSequenceEnd` preserves `peek?` from the underlying advance. -/
lemma scanFlowSequenceEnd_peek (s : ScannerState) :
    (scanFlowSequenceEnd s).peek? = (s.emit .flowSequenceEnd).advance.peek? := by
  unfold scanFlowSequenceEnd ScannerState.peek?; rfl

/-- Flow dispatch for `]` when flowLevel = 1 and at EOF (outermost close).
    After scanFlowSequenceEnd, flowLevel = 0 and validateFlowClose passes. -/
lemma dispatchFlowIndicators_close_bracket_outermost (s : ScannerState)
    (h_fl : s.flowLevel = 1)
    (hcorr : ScannerSurfCorr s ⟨[']'], s.col⟩)
    (h_kind : s.flowStack.back? = some true) :
    scanNextToken_dispatchFlowIndicators s ']' = .ok (some (scanFlowSequenceEnd s)) := by
  unfold scanNextToken_dispatchFlowIndicators
  rw [checkFlowAdjacency_ok_of_sepChar (by decide)]
  simp only [bind, Except.bind, pure, Except.pure,
    show (']' == '[') = false from by decide,
    show (']' == ']') = true from by decide]
  have h_ne := nat_beq_zero_false s.flowLevel (by omega : s.flowLevel > 0)
  simp only [h_ne, h_kind]
  -- After scanFlowSequenceEnd: flowLevel = 0
  have h_fl_after : (scanFlowSequenceEnd s).flowLevel = 0 := by
    rw [scanFlowSequenceEnd_flowLevel, h_fl]
    simp (config := { decide := true })
  -- EOF: peek? = none after advancing past ']'
  have ⟨_, h_lt⟩ := peek_of_chars_cons s ']' [] s.col hcorr
  let s_em := s.emit .flowSequenceEnd
  have h_em_corr : ScannerSurfCorr s_em ⟨[']'], s.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have h_adv_corr := advance_non_newline_corr s_em ']' [] h_em_corr
    (show s_em.offset < s_em.inputEnd from h_lt) (by decide) (by decide)
  have h_adv_peek := peek_none_of_empty_surf s_em.advance (s.col + 1) h_adv_corr
  have h_eof : (scanFlowSequenceEnd s).peek? = none := by
    rw [scanFlowSequenceEnd_peek]; exact h_adv_peek
  rw [validateFlowClose_pass_eof _ h_fl_after h_eof]
  simp

/-- Full `scanNextToken` for `]` at flowLevel = 1 (outermost flow close).
    The result has flowLevel = 0, directivesPresent = false. -/
lemma scanNextToken_flow_close_seq_outermost (s : ScannerState)
    (hcorr : ScannerSurfCorr s ⟨[']'], s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_fl : s.flowLevel = 1)
    (h_dp : s.directivesPresent = false)
    (h_kind : s.flowStack.back? = some true)
    -- Item 159: the close's own run reading is now the stack's business.
    (h_ids : s.indents = #[{ column := -1, isSequence := false }])
    -- Item 180: …and the crossed-block clause reads the array, which an
    -- emitted stream keeps property-free.
    (h_np : ∀ j : Nat, s.tokens[j]!.val.isNodeProperty = false) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ s'.flowLevel = 0
      ∧ s'.directivesPresent = false
      ∧ s'.peek? = none
      ∧ scanLoop_checkDanglingNode s' = .ok ()
      ∧ scanLoop_checkFlowValueIndent s' = .ok () := by
  -- Step 1: preprocessing
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ']')) :=
    scanNextToken_preprocess_flow s ']' [] s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  -- Step 2: structural dispatch → none
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ']' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  -- Step 3: allowDirectives update
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  -- Step 5: flow dispatch
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_col : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨[']'], s_ad.col⟩ := by
    rw [h_ad_col]; exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  have h_ad_kind : s_ad.flowStack.back? = some true := by
    have h_ad_fs : s_ad.flowStack = s.flowStack := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowStack s
    rw [h_ad_fs]; exact h_kind
  have h_flow_disp := dispatchFlowIndicators_close_bracket_outermost s_ad
    (h_ad_fl ▸ h_fl) h_ad_corr h_ad_kind
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl (scanNextToken_checkFlowValueIndent_ok_of_inFlow _ _ h_flow) h_flow_disp
    ((saveSimpleKey_preserves_directivesPresent s).trans h_dp)
    (scanNextToken_checkBareDocument_ok_of_inFlow _
      ((saveSimpleKey_preserves_inFlow s).trans h_flow))
    (scanNextToken_checkDanglingNode_ok_of_inFlow _ _ h_flow)
  -- Extract properties
  have h_result_fl : (scanFlowSequenceEnd s_ad).flowLevel = 0 := by
    rw [scanFlowSequenceEnd_flowLevel, h_ad_fl, h_fl]
    simp (config := { decide := true })
  have h_result_dp : (scanFlowSequenceEnd s_ad).directivesPresent = false := by
    rw [scanFlowSequenceEnd_preserves_dp, h_ad_dp]; exact h_dp
  have h_result_eof : (scanFlowSequenceEnd s_ad).peek? = none := by
    rw [scanFlowSequenceEnd_peek]; exact peek_none_of_empty_surf _ _ (by
      have ⟨_, h_lt⟩ := peek_of_chars_cons s_ad ']' [] s_ad.col h_ad_corr
      exact advance_non_newline_corr (s_ad.emit .flowSequenceEnd) ']' []
        ⟨h_ad_corr.chars_from, h_ad_corr.col_eq, h_ad_corr.end_eq,
         h_ad_corr.input_prefix, h_ad_corr.indent_cols_nonneg⟩
        (show (s_ad.emit .flowSequenceEnd).offset < (s_ad.emit .flowSequenceEnd).inputEnd from h_lt)
        (by decide) (by decide))
  -- Item 159: a `]`/`}` no longer ends the array in NO run — the run is read
  -- back to the matching open — so what discharges the check here is the indent
  -- stack the emitter's own output stands on, which is the sentinel alone.
  have h_result_ids : (scanFlowSequenceEnd s_ad).indents
      = #[{ column := -1, isSequence := false }] := by
    have h_ad_ids : s_ad.indents = s.indents := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
    rw [scanFlowSequenceEnd_preserves_indents s_ad, h_ad_ids]
    exact h_ids
  -- Item 180: the result array is the input's plus reservations and the
  -- close token — none of them a property.
  have h_np_res : crossedPropsExcessIdx? (scanFlowSequenceEnd s_ad).tokens = none := by
    have h_ad_toks : s_ad.tokens = (saveSimpleKey s).tokens := by
      simp only [s_ad]; split <;> rfl
    have h_res_toks : (scanFlowSequenceEnd s_ad).tokens
        = s_ad.tokens.push { pos := s_ad.currentPos, val := .flowSequenceEnd } := by
      unfold scanFlowSequenceEnd
      dsimp only []
      rw [ScannerCorrectness.advance_preserves_tokens (s_ad.emit .flowSequenceEnd)]
      unfold ScannerState.emit; rfl
    rw [h_res_toks, h_ad_toks]
    exact crossedPropsExcessIdx?_none_of_no_props
      (no_props_push (no_props_saveSimpleKey h_np) rfl)
  exact ⟨scanFlowSequenceEnd s_ad, h_snt, h_result_fl, h_result_dp, h_result_eof,
    scanLoop_checkDanglingNode_ok_of_sentinel_stack _ h_result_ids h_np_res,
    scanLoop_checkFlowValueIndent_ok_of_sentinel_stack _ h_result_ids⟩

-- ═══ Flow mapping: scanFlowMappingStart / scanFlowMappingEnd ═══
-- Symmetric to scanFlowSequenceStart/End but for `{`/`}`.

lemma scanFlowMappingStart_preserves_dp (s : ScannerState) :
    (scanFlowMappingStart s).directivesPresent = s.directivesPresent := by
  unfold scanFlowMappingStart; simp only [advance_preserves_dp, ScannerState.emit]

lemma scanFlowMappingStart_preserves_indents (s : ScannerState) :
    (scanFlowMappingStart s).indents = s.indents := by
  unfold scanFlowMappingStart; simp only [advance_preserves_indents, ScannerState.emit]

lemma scanFlowMappingStart_preserves_ek (s : ScannerState) :
    (scanFlowMappingStart s).explicitKeyLine = none := by
  unfold scanFlowMappingStart; rfl

lemma scanFlowMappingStart_line_eq (s : ScannerState) :
    (scanFlowMappingStart s).line = s.advance.line := by
  -- 4.33: sequential unfolding — see scanFlowSequenceStart_line_eq above.
  simp only [scanFlowMappingStart, ScannerState.emit]
  simp only [ScannerState.advance]
  split <;> (try split <;> (try split)) <;> rfl

lemma scanFlowMappingStart_flowLevel_eq (s : ScannerState) :
    (scanFlowMappingStart s).flowLevel = s.flowLevel + 1 := by
  unfold scanFlowMappingStart
  simp only [ScannerCorrectness.advance_preserves_flowLevel, ScannerCorrectness.emit_preserves_flowLevel]

lemma scanFlowMappingStart_detail (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'{' :: rest, s.col⟩) :
    ScannerSurfCorr (scanFlowMappingStart s) ⟨rest, s.col + 1⟩
    ∧ (scanFlowMappingStart s).flowLevel = s.flowLevel + 1
    ∧ (scanFlowMappingStart s).directivesPresent = s.directivesPresent
    ∧ (scanFlowMappingStart s).indents = s.indents
    ∧ (scanFlowMappingStart s).col = s.col + 1 := by
  have ⟨_, h_lt⟩ := peek_of_chars_cons s '{' rest _ hcorr
  have h_emit_corr : ScannerSurfCorr
      ({ s with simpleKey := { possible := false } }.emit .flowMappingStart)
      ⟨'{' :: rest, s.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have h_adv_corr := advance_non_newline_corr
    ({ s with simpleKey := { possible := false } }.emit .flowMappingStart)
    '{' rest h_emit_corr h_lt (by decide) (by decide)
  have h_corr_final : ScannerSurfCorr (scanFlowMappingStart s) ⟨rest, s.col + 1⟩ := by
    unfold scanFlowMappingStart
    exact ⟨h_adv_corr.chars_from, h_adv_corr.col_eq, h_adv_corr.end_eq,
           h_adv_corr.input_prefix, h_adv_corr.indent_cols_nonneg⟩
  exact ⟨h_corr_final,
         scanFlowMappingStart_flowLevel_eq s,
         scanFlowMappingStart_preserves_dp s,
         scanFlowMappingStart_preserves_indents s,
         h_corr_final.col_eq.symm ▸ rfl⟩

lemma dispatchFlowIndicators_brace (s : ScannerState)
    (h_adj : scanNextToken_checkFlowAdjacency s '{' = .ok ()) :
    scanNextToken_dispatchFlowIndicators s '{' = .ok (some (scanFlowMappingStart s)) := by
  unfold scanNextToken_dispatchFlowIndicators; rw [h_adj]; dsimp only []
  simp only [pure, Except.pure, bind, Except.bind,
    show ('{' == '[') = false from by decide,
    show ('{' == ']') = false from by decide,
    show ('{' == '{') = true from by decide,
    ite_true, ite_false, Bool.false_eq_true]

lemma scanFlowMappingEnd_preserves_dp (s : ScannerState) :
    (scanFlowMappingEnd s).directivesPresent = s.directivesPresent := by
  unfold scanFlowMappingEnd; dsimp only []; simp only [advance_preserves_dp, ScannerState.emit]

lemma scanFlowMappingEnd_preserves_indents (s : ScannerState) :
    (scanFlowMappingEnd s).indents = s.indents := by
  unfold scanFlowMappingEnd; dsimp only []; simp only [advance_preserves_indents, ScannerState.emit]

lemma scanFlowMappingEnd_preserves_ek (s : ScannerState) :
    (scanFlowMappingEnd s).explicitKeyLine
      = (s.explicitKeyStack.back?.getD (none, -1)).1 :=
  ScannerCorrectness.scanFlowMappingEnd_ek_restored s

lemma scanFlowMappingEnd_flowLevel (s : ScannerState) :
    (scanFlowMappingEnd s).flowLevel =
      if s.flowLevel > 0 then s.flowLevel - 1 else 0 := by
  unfold scanFlowMappingEnd; dsimp only []
  simp only [ScannerCorrectness.advance_preserves_flowLevel,
             ScannerCorrectness.emit_preserves_flowLevel]

lemma scanFlowMappingEnd_detail (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'}' :: rest, s.col⟩) :
    ScannerSurfCorr (scanFlowMappingEnd s) ⟨rest, s.col + 1⟩
    ∧ (scanFlowMappingEnd s).flowLevel = (if s.flowLevel > 0 then s.flowLevel - 1 else 0)
    ∧ (scanFlowMappingEnd s).directivesPresent = s.directivesPresent
    ∧ (scanFlowMappingEnd s).indents = s.indents
    ∧ (scanFlowMappingEnd s).col = s.col + 1 := by
  have ⟨_, h_lt⟩ := peek_of_chars_cons s '}' rest _ hcorr
  let s_em := s.emit .flowMappingEnd
  have h_em_corr : ScannerSurfCorr s_em ⟨'}' :: rest, s.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have h_adv_corr := advance_non_newline_corr s_em '}' rest h_em_corr
    (show s_em.offset < s_em.inputEnd from h_lt) (by decide) (by decide)
  have h_col_eq : (scanFlowMappingEnd s).col = s.col + 1 := by
    unfold scanFlowMappingEnd; dsimp only []; exact h_adv_corr.col_eq.symm
  refine ⟨?_, scanFlowMappingEnd_flowLevel s,
          scanFlowMappingEnd_preserves_dp s,
          scanFlowMappingEnd_preserves_indents s, h_col_eq⟩
  unfold scanFlowMappingEnd
  exact ⟨h_adv_corr.chars_from, h_adv_corr.col_eq, h_adv_corr.end_eq,
         h_adv_corr.input_prefix, h_adv_corr.indent_cols_nonneg⟩

lemma scanFlowMappingEnd_lastRealTokenVal (s : ScannerState) :
    lastRealTokenVal? (scanFlowMappingEnd s).tokens = some .flowMappingEnd := by
  unfold scanFlowMappingEnd; dsimp only []
  show lastRealTokenVal? (s.emit .flowMappingEnd).advance.tokens = _
  rw [ScannerCorrectness.advance_preserves_tokens (s.emit .flowMappingEnd)]
  show lastRealTokenVal? (s.tokens.push { pos := s.currentPos, val := .flowMappingEnd }) = _
  exact lastRealTokenVal_push_non_ph' s.tokens _ nofun

lemma scanFlowMappingEnd_peek (s : ScannerState) :
    (scanFlowMappingEnd s).peek? = (s.emit .flowMappingEnd).advance.peek? := by
  unfold scanFlowMappingEnd ScannerState.peek?; rfl

lemma dispatchFlowIndicators_close_brace_nested (s : ScannerState)
    (h_fl : s.flowLevel ≥ 2)
    (h_kind : s.flowStack.back? = some false) :
    scanNextToken_dispatchFlowIndicators s '}' = .ok (some (scanFlowMappingEnd s)) := by
  unfold scanNextToken_dispatchFlowIndicators
  rw [checkFlowAdjacency_ok_of_sepChar (by decide)]
  simp only [bind, Except.bind, pure, Except.pure,
    show ('}' == '[') = false from by decide,
    show ('}' == ']') = false from by decide,
    show ('}' == '{') = false from by decide,
    show ('}' == '}') = true from by decide]
  have h_ne := nat_beq_zero_false s.flowLevel (by omega : s.flowLevel > 0)
  simp only [h_ne, h_kind]
  have h_fl_after : (scanFlowMappingEnd s).flowLevel > 0 := by
    rw [scanFlowMappingEnd_flowLevel]; split <;> omega
  rw [validateFlowClose_pass_nested _ h_fl_after]
  simp

lemma scanNextToken_flow_close_mapping_nested (s : ScannerState)
    (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'}' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_fl_ge2 : s.flowLevel ≥ 2)
    (h_atol : AllTokensOnLine s s.line)
    (h_stack_endline : StackEndLineOnLine s s.line)
    (h_dp : s.directivesPresent = false)
    (h_kind : s.flowStack.back? = some false) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel - 1
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = (s.explicitKeyStack.back?.getD (none, -1)).1
      ∧ s'.col = s.col + 1
      ∧ (∀ t, lastRealTokenVal? s'.tokens = some t →
          t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
      ∧ s'.simpleKeyAllowed = false
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack.pop
      ∧ s'.simpleKey = s.simpleKeyStack.back?.getD {}
      ∧ (∀ i, i < s.tokens.size → s'.tokens[i]? = s.tokens[i]?)
      ∧ s'.explicitKeyStack = s.explicitKeyStack.pop := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '}')) :=
    scanNextToken_preprocess_flow s '}' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '}' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_col : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨'}' :: rest, s_ad.col⟩ := by
    rw [h_ad_col]
    exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  have h_ad_fl_ge2 : s_ad.flowLevel ≥ 2 := by rw [h_ad_fl]; exact h_fl_ge2
  have h_ad_kind : s_ad.flowStack.back? = some false := by
    have h_ad_fs : s_ad.flowStack = s.flowStack := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowStack s
    rw [h_ad_fs]; exact h_kind
  have h_flow_disp := dispatchFlowIndicators_close_brace_nested s_ad h_ad_fl_ge2 h_ad_kind
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl (scanNextToken_checkFlowValueIndent_ok_of_inFlow _ _ h_flow) h_flow_disp
    ((saveSimpleKey_preserves_directivesPresent s).trans h_dp)
    (scanNextToken_checkBareDocument_ok_of_inFlow _
      ((saveSimpleKey_preserves_inFlow s).trans h_flow))
    (scanNextToken_checkDanglingNode_ok_of_inFlow _ _ h_flow)
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).explicitKeyLine = _
      unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
  have ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ := scanFlowMappingEnd_detail s_ad rest h_ad_corr
  have h_ad_eks : s_ad.explicitKeyStack = s.explicitKeyStack := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_ekStack s
  have h_ek_f : (scanFlowMappingEnd s_ad).explicitKeyLine
      = (s.explicitKeyStack.back?.getD (none, -1)).1 :=
    (scanFlowMappingEnd_preserves_ek s_ad).trans (by rw [h_ad_eks])
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have ⟨h_peek_ad, h_lt_ad⟩ := peek_of_chars_cons s_ad '}' rest s_ad.col h_ad_corr
  have h_line_f : (scanFlowMappingEnd s_ad).line = s.line := by
    show (s_ad.emit .flowMappingEnd).advance.line = s.line
    rw [advance_line_of_peek (s_ad.emit .flowMappingEnd) '}' h_lt_ad h_peek_ad (by decide) (by decide)]
    exact h_ad_line
  refine ⟨_, h_snt, ?_, ?_, h_dp_f.trans h_ad_dp, h_ids_f.trans h_ad_ids, h_ek_f, ?_, ?_, ?_, h_line_f, ?_, ?_, ?_, ?_, ?_,
    (ScannerCorrectness.scanFlowMappingEnd_ekstack_popped s_ad).trans (by rw [h_ad_eks])⟩
  · rw [h_col_f]; exact h_corr_f
  · rw [h_fl_f]; split
    · rw [h_ad_fl]
    · exfalso; omega
  · rw [h_col_f, h_ad_col]
  · intro t ht
    have h_lrt := scanFlowMappingEnd_lastRealTokenVal s_ad
    rw [h_lrt] at ht; injection ht with ht; subst ht
    exact ⟨nofun, nofun, nofun⟩
  · -- simpleKeyAllowed = false
    show (scanFlowMappingEnd s_ad).simpleKeyAllowed = false
    rfl
  · -- AllTokensOnLine
    rw [h_line_f]
    exact AllTokensOnLine_scanFlowMappingEnd s_ad s.line
      (AllTokensOnLine_allowDirectives _ _
        (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl)) h_ad_line
  · -- EndLineOnLine: simpleKey restored from stack
    intro h_poss
    rw [ScannerCorrectness.scanFlowMappingEnd_simpleKey_restored] at h_poss ⊢
    have h_ad_stack : s_ad.simpleKeyStack = s.simpleKeyStack := by
      simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
    rw [h_ad_stack] at h_poss ⊢
    unfold StackEndLineOnLine at h_stack_endline
    rw [h_line_f]
    cases h_back : s.simpleKeyStack.back? with
    | none => rw [h_back] at h_poss; simp [Option.getD] at h_poss
    | some sk =>
      rw [h_back] at h_poss h_stack_endline; simp [Option.getD] at h_poss
      exact h_stack_endline h_poss
  · -- simpleKeyStack.pop
    show (scanFlowMappingEnd s_ad).simpleKeyStack = s.simpleKeyStack.pop
    rw [ScannerCorrectness.scanFlowMappingEnd_stack_popped]
    show s_ad.simpleKeyStack.pop = s.simpleKeyStack.pop
    congr 1
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
  · -- simpleKey restored from popped stack top
    rw [ScannerCorrectness.scanFlowMappingEnd_simpleKey_restored]
    have h_ad_stack : s_ad.simpleKeyStack = s.simpleKeyStack := by
      simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
    rw [h_ad_stack]
  · -- prefix preservation: close only appends
    intro i hi
    have h_ad_tok : s_ad.tokens = (saveSimpleKey s).tokens := by
      simp only [s_ad]; split <;> rfl
    obtain ⟨tok, h_end_tok⟩ : ∃ tok, (scanFlowMappingEnd s_ad).tokens = s_ad.tokens.push tok :=
      ⟨_, by unfold scanFlowMappingEnd ScannerState.emit; rw [ScannerCorrectness.advance_preserves_tokens]⟩
    rw [h_end_tok, h_ad_tok, Array.getElem?_push,
        ite_eq_right (by have := ScannerCorrectness.saveSimpleKey_tokens_monotonic s; omega : i ≠ (saveSimpleKey s).tokens.size),
        Array.getElem?_eq_getElem (by have := ScannerCorrectness.saveSimpleKey_tokens_monotonic s; omega),
        Array.getElem?_eq_getElem hi, ScannerCorrectness.saveSimpleKey_preserves_prefix s i hi]

lemma dispatchFlowIndicators_close_brace_outermost (s : ScannerState)
    (h_fl : s.flowLevel = 1)
    (hcorr : ScannerSurfCorr s ⟨['}'], s.col⟩)
    (h_kind : s.flowStack.back? = some false) :
    scanNextToken_dispatchFlowIndicators s '}' = .ok (some (scanFlowMappingEnd s)) := by
  unfold scanNextToken_dispatchFlowIndicators
  rw [checkFlowAdjacency_ok_of_sepChar (by decide)]
  simp only [bind, Except.bind, pure, Except.pure,
    show ('}' == '[') = false from by decide,
    show ('}' == ']') = false from by decide,
    show ('}' == '{') = false from by decide,
    show ('}' == '}') = true from by decide]
  have h_ne := nat_beq_zero_false s.flowLevel (by omega : s.flowLevel > 0)
  simp only [h_ne, h_kind]
  have h_fl_after : (scanFlowMappingEnd s).flowLevel = 0 := by
    rw [scanFlowMappingEnd_flowLevel, h_fl]
    simp (config := { decide := true })
  have ⟨_, h_lt⟩ := peek_of_chars_cons s '}' [] s.col hcorr
  let s_em := s.emit .flowMappingEnd
  have h_em_corr : ScannerSurfCorr s_em ⟨['}'], s.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have h_adv_corr := advance_non_newline_corr s_em '}' [] h_em_corr
    (show s_em.offset < s_em.inputEnd from h_lt) (by decide) (by decide)
  have h_adv_peek := peek_none_of_empty_surf s_em.advance (s.col + 1) h_adv_corr
  have h_eof : (scanFlowMappingEnd s).peek? = none := by
    rw [scanFlowMappingEnd_peek]; exact h_adv_peek
  rw [validateFlowClose_pass_eof _ h_fl_after h_eof]
  simp

lemma scanNextToken_flow_close_mapping_outermost (s : ScannerState)
    (hcorr : ScannerSurfCorr s ⟨['}'], s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_fl : s.flowLevel = 1)
    (h_dp : s.directivesPresent = false)
    (h_kind : s.flowStack.back? = some false)
    -- Item 159: the close's own run reading is now the stack's business.
    (h_ids : s.indents = #[{ column := -1, isSequence := false }])
    -- Item 180: …and the crossed-block clause reads the array, which an
    -- emitted stream keeps property-free.
    (h_np : ∀ j : Nat, s.tokens[j]!.val.isNodeProperty = false) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ s'.flowLevel = 0
      ∧ s'.directivesPresent = false
      ∧ s'.peek? = none
      ∧ scanLoop_checkDanglingNode s' = .ok ()
      ∧ scanLoop_checkFlowValueIndent s' = .ok () := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '}')) :=
    scanNextToken_preprocess_flow s '}' [] s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '}' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_col : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨['}'], s_ad.col⟩ := by
    rw [h_ad_col]; exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  have h_ad_kind : s_ad.flowStack.back? = some false := by
    have h_ad_fs : s_ad.flowStack = s.flowStack := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowStack s
    rw [h_ad_fs]; exact h_kind
  have h_flow_disp := dispatchFlowIndicators_close_brace_outermost s_ad
    (h_ad_fl ▸ h_fl) h_ad_corr h_ad_kind
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl (scanNextToken_checkFlowValueIndent_ok_of_inFlow _ _ h_flow) h_flow_disp
    ((saveSimpleKey_preserves_directivesPresent s).trans h_dp)
    (scanNextToken_checkBareDocument_ok_of_inFlow _
      ((saveSimpleKey_preserves_inFlow s).trans h_flow))
    (scanNextToken_checkDanglingNode_ok_of_inFlow _ _ h_flow)
  have h_result_fl : (scanFlowMappingEnd s_ad).flowLevel = 0 := by
    rw [scanFlowMappingEnd_flowLevel, h_ad_fl, h_fl]
    simp (config := { decide := true })
  have h_result_dp : (scanFlowMappingEnd s_ad).directivesPresent = false := by
    rw [scanFlowMappingEnd_preserves_dp, h_ad_dp]; exact h_dp
  have h_result_eof : (scanFlowMappingEnd s_ad).peek? = none := by
    rw [scanFlowMappingEnd_peek]; exact peek_none_of_empty_surf _ _ (by
      have ⟨_, h_lt⟩ := peek_of_chars_cons s_ad '}' [] s_ad.col h_ad_corr
      exact advance_non_newline_corr (s_ad.emit .flowMappingEnd) '}' []
        ⟨h_ad_corr.chars_from, h_ad_corr.col_eq, h_ad_corr.end_eq,
         h_ad_corr.input_prefix, h_ad_corr.indent_cols_nonneg⟩
        (show (s_ad.emit .flowMappingEnd).offset < (s_ad.emit .flowMappingEnd).inputEnd from h_lt)
        (by decide) (by decide))
  -- Item 159: a `]`/`}` no longer ends the array in NO run — the run is read
  -- back to the matching open — so what discharges the check here is the indent
  -- stack the emitter's own output stands on, which is the sentinel alone.
  have h_result_ids : (scanFlowMappingEnd s_ad).indents
      = #[{ column := -1, isSequence := false }] := by
    have h_ad_ids : s_ad.indents = s.indents := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
    rw [scanFlowMappingEnd_preserves_indents s_ad, h_ad_ids]
    exact h_ids
  -- Item 180: the result array is the input's plus reservations and the
  -- close token — none of them a property.
  have h_np_res : crossedPropsExcessIdx? (scanFlowMappingEnd s_ad).tokens = none := by
    have h_ad_toks : s_ad.tokens = (saveSimpleKey s).tokens := by
      simp only [s_ad]; split <;> rfl
    have h_res_toks : (scanFlowMappingEnd s_ad).tokens
        = s_ad.tokens.push { pos := s_ad.currentPos, val := .flowMappingEnd } := by
      unfold scanFlowMappingEnd
      dsimp only []
      rw [ScannerCorrectness.advance_preserves_tokens (s_ad.emit .flowMappingEnd)]
      unfold ScannerState.emit; rfl
    rw [h_res_toks, h_ad_toks]
    exact crossedPropsExcessIdx?_none_of_no_props
      (no_props_push (no_props_saveSimpleKey h_np) rfl)
  exact ⟨scanFlowMappingEnd s_ad, h_snt, h_result_fl, h_result_dp, h_result_eof,
    scanLoop_checkDanglingNode_ok_of_sentinel_stack _ h_result_ids h_np_res,
    scanLoop_checkFlowValueIndent_ok_of_sentinel_stack _ h_result_ids⟩

-- Nested flow open for `{`
lemma scanNextToken_flow_open_mapping_nested (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'{' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_dp : s.directivesPresent = false)
    (h_last : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel + 1
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = none
      ∧ s'.col = s.col + 1
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ StackEndLineOnLine s' s'.line
      ∧ s'.simpleKeyStack.pop = s.simpleKeyStack
      ∧ s'.simpleKey.possible = false
      ∧ s.tokens.size < s'.tokens.size
      ∧ s'.simpleKeyStack = s.simpleKeyStack.push (saveSimpleKey s).simpleKey
      ∧ (∀ t, lastRealTokenVal? s'.tokens = some t → t.completesFlowValue = false)
      ∧ s'.flowStack = s.flowStack.push false
      -- item 9r: the two facts a pair-list body needs at its entry state —
      -- the `{` re-enables simple-key reservation, and the `{` token itself
      -- caps the raw array, so `LastRawNotValue` holds.
      ∧ s'.simpleKeyAllowed = true
      ∧ LastRawNotValue s'
      ∧ s'.explicitKeyStack = s.explicitKeyStack.push (s.explicitKeyLine, s.explicitKeyCol) := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '{')) :=
    scanNextToken_preprocess_flow s '{' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '{' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_ad_tokens : s_ad.tokens = (saveSimpleKey s).tokens := by
    simp only [s_ad]; split <;> rfl
  have h_flow_disp := dispatchFlowIndicators_brace s_ad
    (checkFlowAdjacency_ok_of_notCompletes (fun t ht =>
      saveSimpleKey_preserves_completesFalse s h_last t (h_ad_tokens ▸ ht)))
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl (scanNextToken_checkFlowValueIndent_ok_of_inFlow _ _ h_flow) h_flow_disp
    ((saveSimpleKey_preserves_directivesPresent s).trans h_dp)
    (scanNextToken_checkBareDocument_ok_of_inFlow _
      ((saveSimpleKey_preserves_inFlow s).trans h_flow))
    (scanNextToken_checkDanglingNode_ok_of_inFlow _ _ h_flow)
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).explicitKeyLine = _
      unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
  have h_ad_col : s_ad.col = s.col := by
    simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨'{' :: rest, s_ad.col⟩ := by
    rw [show s_ad.col = s.col from h_ad_col]
    exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ :=
    scanFlowMappingStart_detail s_ad rest h_ad_corr
  have h_ek_f := scanFlowMappingStart_preserves_ek s_ad
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have ⟨h_peek_ad, h_lt_ad⟩ := peek_of_chars_cons s_ad '{' rest s_ad.col h_ad_corr
  have h_line_f : (scanFlowMappingStart s_ad).line = s.line := by
    rw [scanFlowMappingStart_line_eq]
    exact (advance_line_of_peek s_ad '{' h_lt_ad h_peek_ad (by decide) (by decide)).trans h_ad_line
  refine ⟨_, h_snt, ?_, h_fl_f.trans (congrArg (· + 1) h_ad_fl),
    h_dp_f.trans h_ad_dp, h_ids_f.trans h_ad_ids, h_ek_f, ?_, h_line_f, ?_, ?_, ?_, ?_,
    ScannerCorrectness.scanFlowMappingStart_simpleKey_cleared s_ad, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_col_f]; exact h_corr_f
  · rw [h_col_f, h_ad_col]
  · rw [h_line_f]
    exact AllTokensOnLine_scanFlowMappingStart s_ad s.line
      (AllTokensOnLine_allowDirectives _ _
        (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl)) h_ad_line
  · -- EndLineOnLine: scanFlowMappingStart sets simpleKey.possible = false
    intro h_poss
    rw [scanFlowMappingStart_simpleKey_not_possible] at h_poss
    exact absurd h_poss (by decide)
  · -- StackEndLineOnLine: pushed savedKey = s_ad.simpleKey satisfies EndLineOnLine at s'.line
    unfold StackEndLineOnLine
    rw [ScannerCorrectness.scanFlowMappingStart_stack_pushed, Array.back?_push, h_line_f]
    intro h_poss
    have h_ad_endline : EndLineOnLine s_ad := by
      simp only [s_ad]; split
      · show EndLineOnLine { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
        exact EndLineOnLine_saveSimpleKey_flow s h_endline
      · exact EndLineOnLine_saveSimpleKey_flow s h_endline
    exact ⟨(h_ad_endline h_poss).1.trans h_ad_line, (h_ad_endline h_poss).2.trans h_ad_line⟩
  · -- simpleKeyStack.pop = s.simpleKeyStack
    rw [ScannerCorrectness.scanFlowMappingStart_stack_pushed, Array.pop_push]
    show s_ad.simpleKeyStack = s.simpleKeyStack
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
  · -- s.tokens.size < s'.tokens.size
    rw [ScannerCorrectness.scanFlowMappingStart_adds_one_token]
    have h_ad_tok : s.tokens.size ≤ s_ad.tokens.size := by
      simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_tokens_monotonic s
    omega
  · -- simpleKeyStack = s.simpleKeyStack.push (saveSimpleKey s).simpleKey
    rw [ScannerCorrectness.scanFlowMappingStart_stack_pushed]
    have h1 : s_ad.simpleKeyStack = s.simpleKeyStack := by
      simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
    have h2 : s_ad.simpleKey = (saveSimpleKey s).simpleKey := by
      simp only [s_ad]; split <;> rfl
    rw [h1, h2]
  · -- last real token is .flowMappingStart ⇒ does not complete a flow value
    intro t ht
    rw [scanFlowMappingStart_lastRealTokenVal s_ad] at ht
    simp only [Option.some.injEq] at ht; subst ht; rfl
  · -- flowStack: '{' pushes `false` (9a kind tracking)
    rw [L4YAML.Proofs.ScannerFlowCollection.scanFlowMappingStart_pushes_false]
    congr 1
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowStack s
  · -- simpleKeyAllowed: literally set by scanFlowMappingStart (item 9r)
    show (scanFlowMappingStart s_ad).simpleKeyAllowed = true
    unfold scanFlowMappingStart
    rfl
  · -- LastRawNotValue: the `{` token caps the raw array (item 9r)
    have h_tok : (scanFlowMappingStart s_ad).tokens =
        s_ad.tokens.push ⟨s_ad.currentPos, .flowMappingStart, s_ad.currentPos⟩ := by
      show ({ ({ s_ad with simpleKey := _ }.emit .flowMappingStart).advance with
          flowLevel := _, simpleKeyAllowed := _, flowStack := _, simpleKeyStack := _,
                  explicitKeyStack := _, explicitKeyLine := _, explicitKeyCol := _ }).tokens = _
      simp only [ScannerCorrectness.advance_preserves_tokens, ScannerState.emit,
                 ScannerState.currentPos]
    exact lastRawNotValue_of_push (by simp) h_tok
  · -- explicitKeyStack: the open pushes the outer stamp (item 98)
    rw [ScannerCorrectness.scanFlowMappingStart_ek_pushed]
    have h1 : s_ad.explicitKeyStack = s.explicitKeyStack := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_ekStack s
    have h2 : s_ad.explicitKeyCol = s.explicitKeyCol := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_ekc s
    rw [h1, h2, h_ad_ek]

-- ═══ Init flow open: `{` — mapping at top level ═══

/-- Structural dispatch returns none for `{` at initial state. -/
lemma dispatchStructural_none_brace_init (s : ScannerState)
    (h_fl : s.flowLevel = 0)
    (h_noDocStart : atDocumentStart s = false)
    (h_noDocEnd : atDocumentEnd s = false) :
    scanNextToken_dispatchStructural s '{' = .ok none := by
  unfold scanNextToken_dispatchStructural
  simp [ScannerState.inFlow, h_fl, h_noDocStart, h_noDocEnd, pure, Except.pure]

/-- `scanNextToken` on the initial scanner state at `{` dispatches to
    `scanFlowMappingStart`, entering flow context.
    Result state has `flowLevel = 1`, `col = 1`, and ScannerSurfCorr at rest. -/
lemma scanNextToken_flow_open_mapping_init (input : String) (rest : List Char)
    (h_toList : input.toList = '{' :: rest) :
    let s₀ := (ScannerState.mk' input).emit .streamStart
    ∃ s', scanNextToken s₀ = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = 1
      ∧ s'.directivesPresent = false
      ∧ s'.indents = s₀.indents
      ∧ s'.col = 1
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.explicitKeyLine = none
      ∧ s'.line = 0
      ∧ AllTokensOnLine s' 0
      ∧ EndLineOnLine s'
      ∧ s'.simpleKey.possible = false
      ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).map (·.val)
          = #[.streamStart, .flowMappingStart]
      ∧ s'.simpleKeyStack.size = s'.flowLevel
      ∧ s'.simpleKeyAllowed = true
      ∧ ScannerCorrectness.SimpleKeyStackValid s'
      ∧ (∀ t, lastRealTokenVal? s'.tokens = some t → t.completesFlowValue = false)
      ∧ s'.flowStack.back? = some false
      -- item 9r: the `{` token caps the raw array (and the filtered one), so
      -- both entry-boundary readings hold at the pair-list body's entry state.
      ∧ LastRawNotValue s'
      ∧ PairStartAtEntryBoundary s' := by
  intro s₀
  -- Step 1: preprocessing
  have h_pp := scanNextToken_preprocess_init_state input '{' rest h_toList
    (by decide) (by decide) (by decide)
  obtain ⟨s_pp, h_pp_eq, h_fl_pp, h_inflow_pp, h_ci_pp, h_col_pp,
          h_ad_pp, h_dp_pp, h_ids, h_inp, h_off, h_ie, h_ek_pp,
          h_line_pp, h_atol_pp, h_bd_pp, h_pp_filt⟩ := h_pp
  -- Step 2: ScannerSurfCorr for s_pp
  have h_chars := chars_from_zero_toList input
  rw [h_toList] at h_chars
  have h_corr₀ := initial_corr input _ h_chars
  have h_corr_s₀ : ScannerSurfCorr s₀ ⟨'{' :: rest, 0⟩ :=
    ScannerSurfCorr_transfer h_corr₀ rfl rfl rfl rfl rfl
  have h_corr_pp : ScannerSurfCorr s_pp ⟨'{' :: rest, s_pp.col⟩ := by
    rw [h_col_pp]
    exact ScannerSurfCorr_transfer h_corr_s₀ h_inp h_off h_ie h_col_pp h_ids
  have ⟨h_pk_pp, _⟩ := peek_of_chars_cons s_pp '{' rest _ h_corr_pp
  -- Step 3: atDocumentStart/End false for '{'
  have h_pat0 : s_pp.peekAt? 0 = s_pp.peek? := by
    unfold ScannerState.peekAt? ScannerState.peekAt?Loop ScannerState.peek?; rfl
  have h_ds : atDocumentStart s_pp = false := by
    unfold atDocumentStart; rw [h_pat0, h_pk_pp]
    simp only [show (some '{' == some '-') = false from by decide,
               Bool.and_false, Bool.false_and]
  have h_de : atDocumentEnd s_pp = false := by
    unfold atDocumentEnd; rw [h_pat0, h_pk_pp]
    simp only [show (some '{' == some '.') = false from by decide,
               Bool.and_false, Bool.false_and]
  -- Step 4: structural dispatch → none
  have h_struct := dispatchStructural_none_brace_init s_pp h_fl_pp h_ds h_de
  -- Step 5: allowDirectives update → s_ad
  let s_ad := if s_pp.allowDirectives then
    { s_pp with allowDirectives := false, documentEverStarted := true }
  else s_pp
  have h_ad_fl : s_ad.flowLevel = 0 := by
    simp only [s_ad]; split <;> exact h_fl_pp
  have h_ad_ci : s_ad.currentIndent = -1 := by
    have : s_ad.indents = s_pp.indents := by simp only [s_ad]; split <;> rfl
    unfold ScannerState.currentIndent at h_ci_pp ⊢; rw [this]; exact h_ci_pp
  -- Step 7: flow dispatch → some (scanFlowMappingStart s_ad)
  have h_flow := dispatchFlowIndicators_brace s_ad
    (checkFlowAdjacency_ok_of_notInFlow (by simp [ScannerState.inFlow, h_ad_fl]))
  -- Step 8: compose through scanNextToken
  have h_snt : scanNextToken s₀ = .ok (some (scanFlowMappingStart s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp_eq h_struct rfl (scanNextToken_checkFlowValueIndent_ok_of_sentinel_stack _ _ rfl) h_flow h_dp_pp
      h_bd_pp (scanNextToken_checkDanglingNode_ok_of_sentinel_stack _ _
        (init_indents_sentinel _) (crossedPropsExcessIdx?_init _))
  -- Step 9: field properties of scanFlowMappingStart s_ad
  have h_ad_col : s_ad.col = 0 := by
    simp only [s_ad]; split <;> exact h_col_pp
  have h_ad_col_eq : s_ad.col = s_pp.col := by simp only [s_ad]; split <;> rfl
  have h_corr_ad : ScannerSurfCorr s_ad ⟨'{' :: rest, s_ad.col⟩ := by
    rw [h_ad_col_eq]
    exact ScannerSurfCorr_transfer h_corr_pp
      (by simp only [s_ad]; split <;> rfl)
      (by simp only [s_ad]; split <;> rfl)
      (by simp only [s_ad]; split <;> rfl)
      h_ad_col_eq
      (by simp only [s_ad]; split <;> rfl)
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ :=
    scanFlowMappingStart_detail s_ad rest h_corr_ad
  -- Compute final field values
  have h_fl_final : (scanFlowMappingStart s_ad).flowLevel = 1 := by
    rw [h_fl_f, h_ad_fl]
  have h_dp_final : (scanFlowMappingStart s_ad).directivesPresent = false := by
    rw [h_dp_f]; simp only [s_ad]; split <;> exact h_dp_pp
  have h_ids_final : (scanFlowMappingStart s_ad).indents = s₀.indents := by
    rw [h_ids_f]; simp only [s_ad]; split <;> exact h_ids
  have h_col_final : (scanFlowMappingStart s_ad).col = 1 := by
    rw [h_col_f, h_ad_col]
  have h_corr_result : ScannerSurfCorr (scanFlowMappingStart s_ad)
      ⟨rest, (scanFlowMappingStart s_ad).col⟩ := by
    rw [h_col_f]
    exact h_corr_f
  exact ⟨scanFlowMappingStart s_ad, h_snt, h_corr_result,
         h_fl_final, h_dp_final, h_ids_final, h_col_final,
         by unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl_final]; omega),
         by have hb : (scanFlowMappingStart s_ad).indents.back? =
                some { column := (-1 : Int), isSequence := false } := by
              rw [h_ids_final]; rfl
            unfold ScannerState.currentIndent; rw [hb]; decide,
         scanFlowMappingStart_preserves_ek s_ad,
         by rw [scanFlowMappingStart_line_eq]
            have h_ad_pk : s_ad.peek? = some '{' := by
              simp only [s_ad]; split <;> exact h_pk_pp
            have h_ad_lt := (peek_of_chars_cons s_ad '{' rest _ h_corr_ad).2
            have h_ad_line : s_ad.line = 0 := by simp only [s_ad]; split <;> exact h_line_pp
            exact (advance_line_of_peek s_ad '{' h_ad_lt h_ad_pk (by decide) (by decide)).trans h_ad_line,
         by exact AllTokensOnLine_scanFlowMappingStart s_ad 0
              (AllTokensOnLine_allowDirectives _ 0 (h_line_pp ▸ h_atol_pp))
              (by simp only [s_ad]; split <;> exact h_line_pp),
         by intro h_poss
            rw [scanFlowMappingStart_simpleKey_not_possible] at h_poss
            exact absurd h_poss (by decide),
         scanFlowMappingStart_simpleKey_not_possible s_ad,
         by -- Filtered token characterization for mapping (mirrors sequence case)
            have h_fms_tokens : (scanFlowMappingStart s_ad).tokens
                = s_ad.tokens.push ⟨s_ad.currentPos, .flowMappingStart, s_ad.currentPos⟩ := by
              show ({ ({ s_ad with simpleKey := _ }.emit .flowMappingStart).advance with
                  flowLevel := _, simpleKeyAllowed := _,
                  flowStack := _, simpleKeyStack := _,
                  explicitKeyStack := _, explicitKeyLine := _, explicitKeyCol := _ }).tokens = _
              simp only [ScannerCorrectness.advance_preserves_tokens,
                         ScannerState.emit, ScannerState.currentPos]
            have h_ad_tokens : s_ad.tokens = s_pp.tokens := by
              simp only [s_ad]; split <;> rfl
            rw [h_fms_tokens]
            simp only [Array.filter_push,
              show (YamlToken.flowMappingStart != YamlToken.placeholder) = true from rfl,
              ite_true, Array.map_push,
              show s_ad.tokens = s_pp.tokens from h_ad_tokens,
              h_pp_filt]
            simp [ScannerState.mk', ScannerState.emit],
         by -- Stack/flowLevel sync:
            rw [h_fl_final]
            have h_pre_stack := ScannerCorrectness.preprocess_preserves_simpleKeyStack
              _ _ _ h_pp_eq
            have h_ad_stack_sz : s_ad.simpleKeyStack.size = 0 := by
              simp only [s_ad]; split
              · show s_pp.simpleKeyStack.size = 0; rw [h_pre_stack]; rfl
              · rw [h_pre_stack]; rfl
            rw [ScannerCorrectness.scanFlowMappingStart_stack_pushed]
            simp [Array.size_push, h_ad_stack_sz],
         rfl,
         by -- SimpleKeyStackValid: preserved from the empty-key initial state
            have h_akv₀ : ScannerCorrectness.AllKeysValid s₀ := by
              refine ⟨fun h_poss => ?_, fun j hj _ => ?_⟩
              · exfalso
                have h_p : s₀.simpleKey.possible = false := by
                  show ((ScannerState.mk' input).emit .streamStart).simpleKey.possible = false
                  rw [ScannerCorrectness.emit_preserves_simpleKey]; rfl
                rw [h_p] at h_poss; exact absurd h_poss (by decide)
              · exfalso
                have h_sz : s₀.simpleKeyStack.size = 0 := by
                  show ((ScannerState.mk' input).emit .streamStart).simpleKeyStack.size = 0
                  rw [ScannerCorrectness.emit_preserves_simpleKeyStack]; rfl
                omega
            exact (ScannerCorrectness.scanNextToken_preserves_AllKeysValid s₀
              (scanFlowMappingStart s_ad) h_akv₀ h_snt).2,
         fun t ht => by
           rw [scanFlowMappingStart_lastRealTokenVal s_ad] at ht
           simp only [Option.some.injEq] at ht; subst ht; rfl,
         by -- flowStack top: '{' pushes `false` (9a kind tracking)
           rw [L4YAML.Proofs.ScannerFlowCollection.scanFlowMappingStart_pushes_false]
           exact Array.back?_push,
         by -- LastRawNotValue (item 9r)
           have h_tok : (scanFlowMappingStart s_ad).tokens =
               s_ad.tokens.push ⟨s_ad.currentPos, .flowMappingStart, s_ad.currentPos⟩ := by
             show ({ ({ s_ad with simpleKey := _ }.emit .flowMappingStart).advance with
                 flowLevel := _, simpleKeyAllowed := _,
                 flowStack := _, simpleKeyStack := _,
                  explicitKeyStack := _, explicitKeyLine := _, explicitKeyCol := _ }).tokens = _
             simp only [ScannerCorrectness.advance_preserves_tokens,
                        ScannerState.emit, ScannerState.currentPos]
           exact lastRawNotValue_of_push (by simp) h_tok,
         by -- PairStartAtEntryBoundary (item 9r)
           have h_tok : (scanFlowMappingStart s_ad).tokens =
               s_ad.tokens.push ⟨s_ad.currentPos, .flowMappingStart, s_ad.currentPos⟩ := by
             show ({ ({ s_ad with simpleKey := _ }.emit .flowMappingStart).advance with
                 flowLevel := _, simpleKeyAllowed := _,
                 flowStack := _, simpleKeyStack := _,
                  explicitKeyStack := _, explicitKeyLine := _, explicitKeyCol := _ }).tokens = _
             simp only [ScannerCorrectness.advance_preserves_tokens,
                        ScannerState.emit, ScannerState.currentPos]
           have h_feq : (scanFlowMappingStart s_ad).tokens.filter (fun t => t.val != .placeholder)
               = (s_ad.tokens.filter (fun t => t.val != .placeholder)).push
                   { pos := s_ad.currentPos, val := .flowMappingStart } := by
             rw [h_tok, Array.filter_push]; simp
           exact pairStartAtEntryBoundary_of_filtered_push
             (show YamlToken.flowMappingStart ≠ YamlToken.value from by decide) h_feq⟩


end L4YAML.Proofs.EmitterScannability

end Blanket
