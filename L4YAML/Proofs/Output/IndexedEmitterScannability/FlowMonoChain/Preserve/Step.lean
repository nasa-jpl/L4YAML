/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Basic

/-! # `FlowMonoChain.Preserve.Step` — Phase 3 Step 6f.3b3.flowmono.preserve.step

**Sub-session 1 of `.flowmono.preserve`** (legacy
`Proofs/Output/EmitterScannability.lean` lines 1806–2165, ~360 LOC).
Step-4 per-step + chain-level prefix preservation for `FlowMonoChainIx`,
including the sync-invariant chain that flow opens/closes are balanced
across `scanNextTokenIx` calls.

## Scope

  - **§3.1** — Inner-stage `_preserves_flowLevel` /
    `_preserves_simpleKeyStack` Ix twins for the dispatchers that
    didn't already have them in `IndexedScannerPlainScalarValid`.
  - **§3.2** — Per-dispatcher sync preservation:
    `scanNextTokenIx_dispatchStructural_preserves_flowLevel`,
    `_preserves_simpleKeyStack`, and the same for the block and
    content dispatchers (the flow dispatcher's sync proof is the
    interesting one — it has to track the push/pop balance against
    `flowLevel`).
  - **§3.3** — `scanNextTokenIx_preprocess_via_dispatchFlowIndicators`-
    style **sync** preservation:
    `scanNextTokenIx_dispatchFlowIndicators_preserves_sync` then
    `scanNextTokenIx_preserves_sync` (the central chain invariant
    `simpleKeyStack.size ≥ flowLevel`).
  - **§3.4** — `scanNextTokenIx_preserves_prefix_of_simpleKey`: per-step
    prefix preservation under only the SKAF `.1` (simpleKey) conjunct.
    Plus the bundle `scanNextTokenIx_prefix_and_SKAFIx_inv` combining
    prefix preservation with `SimpleKeyAboveFloorIx` maintenance.
  - **§3.5** — `FlowMonoChainIx_preserves_raw_prefix`: induct on a
    `FlowMonoChainIx` to obtain raw-token-prefix preservation under
    `SKAFIx` and the sync invariant.
  - **§3.6** — `scanFilteredIx_of_chain` / `_eq`: connect a
    `ScanChainIx` ending at EOF to `scanFilteredIx input`.
  - **§3.7** — Algebraic helpers: `scanNextTokenIx_eq_of_preprocess`,
    `ScanChainIx_of_scanNextTokenIx_eq`,
    `FlowMonoChainIx_of_scanNextTokenIx_eq`.
  - **§3.8** — `scanNextTokenIx_via_flow_dispatch`: pipeline-factoring
    lemma — preprocess + structural-none + flow-indicator-some ⇒
    `scanNextTokenIx`.

## Legacy mapping

Mirrors `scanNextToken_preserves_prefix_of_skFloor`,
`scanNextToken_prefix_and_skFloor_inv`,
`dispatchFlowIndicators_preserves_sync`,
`scanNextToken_preserves_sync`, `FlowMonoChain_preserves_raw_prefix`,
`scanFiltered_of_chain[_eq]`, `scanNextToken_eq_of_preprocess`,
`ScanChain_of_scanNextToken_eq`, `FlowMonoChain_of_scanNextToken_eq`,
and `scanNextToken_via_flow_dispatch`.

The indexed versions are typically shorter than their legacy
counterparts: cursor-keyed scalar scanners eliminate
per-scalar SK-preservation steps in the content dispatcher (Reflection
122), and straight-line flow open/close (no internal `if`) makes the
sync-invariant proof a one-shot `omega` instead of a five-way split.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.EmitterScannability.ScanChain
open L4YAML.Proofs.Indexed.ScannerPlainScalarValid
open L4YAML.Proofs.Indexed.ScannerCorrectness

variable {input : String}

/-! ## §3.0  Inner-stage `_preserves_flowLevel` Ix twins

These mirror the `_preserves_simpleKeyStack` twins that already live in
`Production/IndexedScannerPlainScalarValid.lean` (§12d). The inner
stage scanners (`scanDocumentStartIx`, `scanDocumentEndIx`,
`scanDirectiveIx`, `scanBlockEntryIx`, `scanKeyIx`, `scanValueIx`,
`scanFlowEntryIx`) only touch `flowLevel` via `emit` / `advance` /
`advanceN` / `unwindIndentsIx` / record-only updates — none of which
change it. These twins are consumed only by the
`scanNextTokenIx_preserves_sync` chain (§3.2). -/

@[simp] theorem advanceN_flowLevel (s : ScannerStateIx input) (n : Nat) :
    (s.advanceN n).flowLevel = s.flowLevel := rfl

@[simp] theorem advanceN_simpleKeyStack (s : ScannerStateIx input) (n : Nat) :
    (s.advanceN n).simpleKeyStack = s.simpleKeyStack := rfl

theorem pushSequenceIndentIx_preserves_flowLevel
    (s : ScannerStateIx input) (col : Int) :
    (pushSequenceIndentIx s col).flowLevel = s.flowLevel := by
  unfold pushSequenceIndentIx
  split <;> simp [emit_flowLevel]

theorem pushSequenceIndentIx_preserves_simpleKeyStack
    (s : ScannerStateIx input) (col : Int) :
    (pushSequenceIndentIx s col).simpleKeyStack = s.simpleKeyStack := by
  unfold pushSequenceIndentIx
  split <;> simp [emit_preserves_simpleKeyStack]

theorem pushMappingIndentIx_preserves_flowLevel
    (s : ScannerStateIx input) (col : Int) :
    (pushMappingIndentIx s col).flowLevel = s.flowLevel := by
  unfold pushMappingIndentIx
  split <;> simp [emit_flowLevel]

theorem pushMappingIndentIx_preserves_simpleKeyStack
    (s : ScannerStateIx input) (col : Int) :
    (pushMappingIndentIx s col).simpleKeyStack = s.simpleKeyStack := by
  unfold pushMappingIndentIx
  split <;> simp [emit_preserves_simpleKeyStack]

theorem scanValueClearKeyIx_preserves_flowLevel (s : ScannerStateIx input) :
    (scanValueClearKeyIx s).flowLevel = s.flowLevel := by
  unfold scanValueClearKeyIx
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

theorem scanValuePrepareIx_preserves_flowLevel (s : ScannerStateIx input) :
    (scanValuePrepareIx s).flowLevel = s.flowLevel := by
  unfold scanValuePrepareIx
  split
  · split
    · split <;> rfl
    · rfl
  · split
    · rfl
    · split
      · exact pushMappingIndentIx_preserves_flowLevel s s.cursor.pos.col
      · rfl

theorem scanDocumentStartIx_preserves_flowLevel (s : ScannerStateIx input) :
    (scanDocumentStartIx s).flowLevel = s.flowLevel := by
  unfold scanDocumentStartIx
  show (unwindIndentsIx s (-1)).flowLevel = s.flowLevel
  exact unwindIndentsIx_preserves_flowLevel s (-1)

theorem scanDocumentEndIx_preserves_flowLevel
    (s s' : ScannerStateIx input) (h : scanDocumentEndIx s = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanDocumentEndIx at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals
    show (unwindIndentsIx s (-1)).flowLevel = s.flowLevel
  all_goals exact unwindIndentsIx_preserves_flowLevel s (-1)

theorem scanYamlDirectiveIx_preserves_flowLevel
    (s : ScannerStateIx input) (cAfterWS : IxCursor input)
    (startPos : YamlPos) (hStart : startPos.offset ≤ cAfterWS.pos.offset)
    (s' : ScannerStateIx input)
    (h : scanYamlDirectiveIx s cAfterWS startPos hStart = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanYamlDirectiveIx at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)

theorem scanTagDirectiveIx_preserves_flowLevel
    (s : ScannerStateIx input) (cAfterWS : IxCursor input)
    (startPos : YamlPos) (hStart : startPos.offset ≤ cAfterWS.pos.offset)
    (s' : ScannerStateIx input)
    (h : scanTagDirectiveIx s cAfterWS startPos hStart = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanTagDirectiveIx at h
  simp only [Except.ok.injEq] at h; subst h; rfl

theorem scanDirectiveIx_preserves_flowLevel
    (s s' : ScannerStateIx input) (h : scanDirectiveIx s = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanDirectiveIx at h
  split at h
  · simp at h
  · dsimp only [] at h
    split at h
    · exact (scanYamlDirectiveIx_preserves_flowLevel _ _ _ _ _ h).trans rfl
    · split at h
      · exact (scanTagDirectiveIx_preserves_flowLevel _ _ _ _ _ h).trans rfl
      · simp only [Except.ok.injEq] at h; subst h; rfl

theorem scanBlockEntryIx_preserves_flowLevel
    (s s' : ScannerStateIx input) (h : scanBlockEntryIx s = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanBlockEntryIx at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals
    first
    | exact pushSequenceIndentIx_preserves_flowLevel s s.cursor.pos.col
    | rfl

theorem scanKeyIx_preserves_flowLevel
    (s s' : ScannerStateIx input) (h : scanKeyIx s = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanKeyIx at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals
    first
    | exact pushMappingIndentIx_preserves_flowLevel s s.cursor.pos.col
    | rfl

theorem scanValueIx_preserves_flowLevel
    (s s' : ScannerStateIx input) (h : scanValueIx s = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanValueIx at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Except.ok.injEq] at h; subst h
  show ((scanValuePrepareIx (scanValueClearKeyIx s)).emit
        YamlToken.value).advance.flowLevel = s.flowLevel
  rw [advance_flowLevel, emit_flowLevel,
      scanValuePrepareIx_preserves_flowLevel,
      scanValueClearKeyIx_preserves_flowLevel]

theorem scanFlowEntryIx_preserves_flowLevel
    (s s' : ScannerStateIx input) (h : scanFlowEntryIx s = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanFlowEntryIx at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_flowLevel, emit_flowLevel]

/-! ## §3.1  Per-dispatcher `_preserves_flowLevel` /
    `_preserves_simpleKeyStack` for the non-flow arms

Mirror the per-dispatcher SKAF maintenance in `FlowMonoChain.Basic`
§2.3 but project to the two fields that combine into the sync
invariant. The flow-indicator dispatcher is *not* preservation-shaped —
its proof obligation is the joint sync invariant, handled in §3.2. -/

theorem scanNextTokenIx_dispatchStructural_preserves_flowLevel
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchStructural s c = .ok (some s')) :
    s'.flowLevel = s.flowLevel := by
  unfold scanNextTokenIx_dispatchStructural at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanDocumentStartIx_preserves_flowLevel s
    | (rename_i h_eq; exact scanDocumentEndIx_preserves_flowLevel s _ h_eq)
    | (rename_i h_eq; exact scanDirectiveIx_preserves_flowLevel s _ h_eq)
    | (simp_all; done)

theorem scanNextTokenIx_dispatchStructural_preserves_simpleKeyStack
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchStructural s c = .ok (some s')) :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanNextTokenIx_dispatchStructural at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanDocumentStartIx_preserves_simpleKeyStack s
    | (rename_i h_eq; exact scanDocumentEndIx_preserves_simpleKeyStack s _ h_eq)
    | (rename_i h_eq; exact scanDirectiveIx_preserves_simpleKeyStack s _ h_eq)
    | (simp_all; done)

theorem scanNextTokenIx_dispatchBlockIndicators_preserves_flowLevel
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s')) :
    s'.flowLevel = s.flowLevel := by
  unfold scanNextTokenIx_dispatchBlockIndicators at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | (rename_i h_eq; exact scanBlockEntryIx_preserves_flowLevel s _ h_eq)
    | (rename_i h_eq; exact scanKeyIx_preserves_flowLevel s _ h_eq)
    | (rename_i h_eq; exact scanValueIx_preserves_flowLevel s _ h_eq)
    | (simp_all; done)

theorem scanNextTokenIx_dispatchBlockIndicators_preserves_simpleKeyStack
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s')) :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanNextTokenIx_dispatchBlockIndicators at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | (rename_i h_eq; exact scanBlockEntryIx_preserves_simpleKeyStack s _ h_eq)
    | (rename_i h_eq; exact scanKeyIx_preserves_simpleKeyStack s _ h_eq)
    | (rename_i h_eq; exact scanValueIx_preserves_simpleKeyStack s _ h_eq)
    | (simp_all; done)

theorem scanNextTokenIx_dispatchContent_preserves_flowLevel
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchContent s c = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanNextTokenIx_dispatchContent at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (try simp only [Except.ok.injEq] at h)
  all_goals (try contradiction)
  all_goals (try subst_vars)
  all_goals first
    | (rename_i h_eq; exact scanAnchorOrAliasIx_preserves_flowLevel s true _ h_eq)
    | (rename_i h_eq; exact scanAnchorOrAliasIx_preserves_flowLevel s false _ h_eq)
    | (rename_i h_eq; exact scanTagIx_preserves_flowLevel s _ h_eq)
    | rfl
    | (simp_all; done)

theorem scanNextTokenIx_dispatchContent_preserves_simpleKeyStack
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchContent s c = .ok s') :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanNextTokenIx_dispatchContent at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (try simp only [Except.ok.injEq] at h)
  all_goals (try contradiction)
  all_goals (try subst_vars)
  all_goals first
    | (rename_i h_eq; exact scanAnchorOrAliasIx_preserves_simpleKeyStack s true _ h_eq)
    | (rename_i h_eq; exact scanAnchorOrAliasIx_preserves_simpleKeyStack s false _ h_eq)
    | (rename_i h_eq; exact scanTagIx_preserves_simpleKeyStack s _ h_eq)
    | rfl
    | (simp_all; done)

/-! ## §3.2  Sync-invariant preservation through the flow dispatcher

`scanNextTokenIx_dispatchFlowIndicators` is the only sub-dispatcher
that *does* alter `flowLevel` and `simpleKeyStack` (in lockstep —
flow opens push + increment, flow closes pop + decrement). The proof
verifies the lockstep via `omega` on the size-push/pop tracking
identities. -/

set_option maxHeartbeats 800000 in
theorem scanNextTokenIx_dispatchFlowIndicators_preserves_sync
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s'))
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel) :
    s'.simpleKeyStack.size ≥ s'.flowLevel := by
  unfold scanNextTokenIx_dispatchFlowIndicators at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h)
  any_goals contradiction
  all_goals (try subst_vars)
  -- The remaining branches: flow open (Seq/Map), flow close (Seq/Map),
  -- flow entry.
  all_goals first
    | -- Flow sequence start: push + flowLevel + 1
      (have h_stack := scanFlowSequenceStartIx_stack_pushed s
       unfold scanFlowSequenceStartIx
       simp only [advance_preserves_simpleKeyStack, emit_preserves_simpleKeyStack,
         advance_flowLevel, emit_flowLevel, Array.size_push]
       omega)
    | -- Flow mapping start: push + flowLevel + 1
      (have h_stack := scanFlowMappingStartIx_stack_pushed s
       unfold scanFlowMappingStartIx
       simp only [advance_preserves_simpleKeyStack, emit_preserves_simpleKeyStack,
         advance_flowLevel, emit_flowLevel, Array.size_push]
       omega)
    | -- Flow sequence end: pop + flowLevel - 1 (truncating Nat sub)
      (unfold scanFlowSequenceEndIx
       simp only [advance_preserves_simpleKeyStack, emit_preserves_simpleKeyStack,
         advance_flowLevel, emit_flowLevel, Array.size_pop]
       omega)
    | -- Flow mapping end: pop + flowLevel - 1
      (unfold scanFlowMappingEndIx
       simp only [advance_preserves_simpleKeyStack, emit_preserves_simpleKeyStack,
         advance_flowLevel, emit_flowLevel, Array.size_pop]
       omega)
    | -- Flow entry: preserves both
      (rename_i h_eq
       have h_stack := scanFlowEntryIx_preserves_simpleKeyStack s _ h_eq
       have h_fl := scanFlowEntryIx_preserves_flowLevel s _ h_eq
       rw [h_stack, h_fl]; exact h_sync)
    | (simp_all; done)

/-! ## §3.3  `scanNextTokenIx_preserves_sync` — full chain

The scanner-global invariant `simpleKeyStack.size ≥ flowLevel`
threads through all five pipeline stages: preprocess (preserves both),
structural/block/content dispatchers (preserve both), allowDirectives
if-update (preserves both via record analysis), and the flow
indicator dispatcher (preserves the joint inequality via §3.2). -/

set_option maxHeartbeats 1200000 in
theorem scanNextTokenIx_preserves_sync
    (s s' : ScannerStateIx input)
    (h_next : scanNextTokenIx s = .ok (some s'))
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel) :
    s'.simpleKeyStack.size ≥ s'.flowLevel := by
  -- allowDirectives if-update preserves both fields
  have h_allow_stack : ∀ st : ScannerStateIx input,
      (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKeyStack = st.simpleKeyStack := by intro st; split <;> rfl
  have h_allow_fl : ∀ st : ScannerStateIx input,
      (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).flowLevel = st.flowLevel := by intro st; split <;> rfl
  unfold scanNextTokenIx at h_next
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_next
  -- preprocess
  split at h_next
  · contradiction
  · split at h_next
    · simp [reduceCtorEq] at h_next
    · rename_i s1 c1 hPre
      have h_pre_stack := scanNextTokenIx_preprocess_preserves_simpleKeyStack s _ _ hPre
      have h_pre_fl := scanNextTokenIx_preprocess_preserves_flowLevel s _ _ hPre
      have h_pre_sync : s1.simpleKeyStack.size ≥ s1.flowLevel := by
        rw [h_pre_stack, h_pre_fl]; exact h_sync
      -- structural
      split at h_next
      · contradiction
      · split at h_next
        · -- structural some
          rename_i s'' hStruct
          simp only [Except.ok.injEq, Option.some.injEq] at h_next
          subst h_next
          have h_d_stack := scanNextTokenIx_dispatchStructural_preserves_simpleKeyStack
            s1 c1 _ hStruct
          have h_d_fl := scanNextTokenIx_dispatchStructural_preserves_flowLevel
            s1 c1 _ hStruct
          rw [h_d_stack, h_d_fl]; exact h_pre_sync
        · -- structural none → allowDirectives update → flow/block/content
          have h_s2_sync :
              (if s1.allowDirectives then
                  { s1 with allowDirectives := false, documentEverStarted := true }
                else s1).simpleKeyStack.size ≥
                (if s1.allowDirectives then
                    { s1 with allowDirectives := false, documentEverStarted := true }
                  else s1).flowLevel := by
            rw [h_allow_stack, h_allow_fl]; exact h_pre_sync
          -- checkBlockFlowIndent
          split at h_next
          · contradiction
          · split at h_next
            · contradiction
            · split at h_next
              · -- FlowIndicators some
                rename_i s'' hFlow
                simp only [Except.ok.injEq, Option.some.injEq] at h_next
                subst h_next
                exact scanNextTokenIx_dispatchFlowIndicators_preserves_sync _ _ _ hFlow h_s2_sync
              · -- FlowIndicators none → BlockIndicators
                split at h_next
                · contradiction
                · split at h_next
                  · -- BlockIndicators some
                    rename_i s'' hBlock
                    simp only [Except.ok.injEq, Option.some.injEq] at h_next
                    subst h_next
                    have h_d_stack := scanNextTokenIx_dispatchBlockIndicators_preserves_simpleKeyStack
                      _ c1 _ hBlock
                    have h_d_fl := scanNextTokenIx_dispatchBlockIndicators_preserves_flowLevel
                      _ c1 _ hBlock
                    rw [h_d_stack, h_d_fl]
                    rw [h_allow_stack, h_allow_fl]
                    exact h_pre_sync
                  · -- BlockIndicators none → Content
                    split at h_next
                    · contradiction
                    · rename_i sC hContent
                      simp only [Except.ok.injEq, Option.some.injEq] at h_next
                      subst h_next
                      have h_d_stack := scanNextTokenIx_dispatchContent_preserves_simpleKeyStack
                        _ c1 _ hContent
                      have h_d_fl := scanNextTokenIx_dispatchContent_preserves_flowLevel
                        _ c1 _ hContent
                      rw [h_d_stack, h_d_fl]
                      rw [h_allow_stack, h_allow_fl]
                      exact h_pre_sync

/-! ## §3.4  Per-step prefix preservation under the SKAF simpleKey bound

Indexed twin of legacy `scanNextToken_preserves_prefix_of_skFloor`
(line 1817). Mirrors `scanNextTokenIx_preserves_prefix` in
`IndexedScannerCorrectness/StreamStart.lean` §7.7' but takes only the
`.1` (simpleKey) conjunct of `SimpleKeyAboveFloorIx` instead of the
full `SimpleKeyAboveIx`. This is enough because the only sub-dispatcher
that actually reads the invariant is `scanValueIx_preserves_prefix`,
and it requires only the simpleKey-bound projection. -/

set_option maxHeartbeats 400000 in
theorem scanNextTokenIx_preserves_prefix_of_simpleKey
    (s s' : ScannerStateIx input) (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_sk : s.simpleKey.possible = true → s.simpleKey.tokenIndex ≥ n)
    (h_ok : scanNextTokenIx s = .ok (some s'))
    (i : Nat) (h_i : i < n) :
    ∃ (h_size : i < s'.tokens.size),
      s'.tokens[i]'h_size = s.tokens[i]'(Nat.lt_of_lt_of_le h_i h_n) := by
  have h_orig : i < s.tokens.size := Nat.lt_of_lt_of_le h_i h_n
  unfold scanNextTokenIx at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  generalize h_pp : scanNextTokenIx_preprocess s = pp_res at h_ok
  cases pp_res with
  | error e => simp at h_ok
  | ok pp_inner =>
    cases pp_inner with
    | none => simp at h_ok
    | some pair =>
      cases pair with
      | mk s_pp c =>
        have h_sk_pp : s_pp.simpleKey.possible = true → s_pp.simpleKey.tokenIndex ≥ n :=
          scanNextTokenIx_preprocess_simpleKey_inv s s_pp c h_pp n h_n h_sk
        obtain ⟨h_i_pp, h_pre_eq⟩ :=
          _preprocess_preserves_prefix s s_pp c n h_n h_pp i h_i
        have h_n_pp : n ≤ s_pp.tokens.size :=
          Nat.le_trans h_n (scanNextTokenIx_preprocess_tokens_size_le s s_pp c h_pp)
        dsimp only [] at h_ok
        generalize h_ds : scanNextTokenIx_dispatchStructural s_pp c = ds_res at h_ok
        cases ds_res with
        | error e => simp at h_ok
        | ok ds_inner =>
          cases ds_inner with
          | some s_str =>
            simp only [Except.ok.injEq, Option.some.injEq] at h_ok
            subst h_ok
            rcases scanNextTokenIx_dispatchStructural_ok_some_cases h_ds with heq | hOk | hOk
            · subst heq
              have h_pref := scanDocumentStartIx_preserves_prefix s_pp i h_i_pp
              have h_sz : i < (scanDocumentStartIx s_pp).tokens.size := by
                have := scanDocumentStartIx_tokens_size_le s_pp; omega
              exact ⟨h_sz, h_pref.trans h_pre_eq⟩
            · have h_pref := scanDocumentEndIx_preserves_prefix s_pp _ hOk i h_i_pp
              have h_sz : i < s_str.tokens.size := by
                have := scanDocumentEndIx_tokens_size_le hOk; omega
              exact ⟨h_sz, h_pref.trans h_pre_eq⟩
            · have h_pref := scanDirectiveIx_preserves_prefix s_pp _ hOk i h_i_pp
              have h_sz : i < s_str.tokens.size := by
                have := scanDirectiveIx_tokens_size_le hOk; omega
              exact ⟨h_sz, h_pref.trans h_pre_eq⟩
          | none =>
            dsimp only [] at h_ok
            generalize h_dir_def : (if s_pp.allowDirectives = true then
                { s_pp with allowDirectives := false, documentEverStarted := true }
              else s_pp) = s_dir at h_ok
            have h_dir_tok : s_dir.tokens = s_pp.tokens := by
              rw [← h_dir_def]; exact _dir_update_tokens s_pp
            have h_i_dir : i < s_dir.tokens.size := by rw [h_dir_tok]; exact h_i_pp
            have h_dir_eq : s_dir.tokens[i]'h_i_dir = s_pp.tokens[i]'h_i_pp := by
              have : ∀ (h : i < s_pp.tokens.size),
                  s_dir.tokens[i]'(h_dir_tok ▸ h) = s_pp.tokens[i]'h := by
                intro h; congr 1
              exact this h_i_pp
            have h_sk_dir : s_dir.simpleKey.possible = true →
                s_dir.simpleKey.tokenIndex ≥ n := by
              rw [← h_dir_def]
              split <;> exact h_sk_pp
            generalize h_ck : scanNextTokenIx_checkBlockFlowIndent s_dir c = ck_res at h_ok
            cases ck_res with
            | error e => simp at h_ok
            | ok _ =>
              dsimp only [] at h_ok
              generalize h_df : scanNextTokenIx_dispatchFlowIndicators s_dir c = df_res at h_ok
              cases df_res with
              | error e => simp at h_ok
              | ok df_inner =>
                cases df_inner with
                | some s_flow =>
                  simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                  subst h_ok
                  rcases scanNextTokenIx_dispatchFlowIndicators_ok_some_cases h_df with
                    heq | heq | heq | heq | hOk
                  · subst heq
                    have h_pref := scanFlowSequenceStartIx_preserves_prefix s_dir i h_i_dir
                    have h_sz : i < (scanFlowSequenceStartIx s_dir).tokens.size := by
                      have := scanFlowSequenceStartIx_tokens_size_le s_dir; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                  · subst heq
                    have h_pref := scanFlowSequenceEndIx_preserves_prefix s_dir i h_i_dir
                    have h_sz : i < (scanFlowSequenceEndIx s_dir).tokens.size := by
                      have := scanFlowSequenceEndIx_tokens_size_le s_dir; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                  · subst heq
                    have h_pref := scanFlowMappingStartIx_preserves_prefix s_dir i h_i_dir
                    have h_sz : i < (scanFlowMappingStartIx s_dir).tokens.size := by
                      have := scanFlowMappingStartIx_tokens_size_le s_dir; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                  · subst heq
                    have h_pref := scanFlowMappingEndIx_preserves_prefix s_dir i h_i_dir
                    have h_sz : i < (scanFlowMappingEndIx s_dir).tokens.size := by
                      have := scanFlowMappingEndIx_tokens_size_le s_dir; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                  · have h_pref := scanFlowEntryIx_preserves_prefix s_dir s_flow hOk i h_i_dir
                    have h_sz : i < s_flow.tokens.size := by
                      have := scanFlowEntryIx_tokens_size_le hOk; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                | none =>
                  dsimp only [] at h_ok
                  generalize h_db : scanNextTokenIx_dispatchBlockIndicators s_dir c = db_res at h_ok
                  cases db_res with
                  | error e => simp at h_ok
                  | ok db_inner =>
                    cases db_inner with
                    | some s_blk =>
                      simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                      subst h_ok
                      have h_n_dir : n ≤ s_dir.tokens.size := by rw [h_dir_tok]; exact h_n_pp
                      rcases scanNextTokenIx_dispatchBlockIndicators_ok_some_cases h_db with
                        hOk | hOk | hOk
                      · have h_pref := scanBlockEntryIx_preserves_prefix s_dir s_blk hOk i h_i_dir
                        have h_sz : i < s_blk.tokens.size := by
                          have := scanBlockEntryIx_tokens_size_le hOk; omega
                        exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                      · have h_pref := scanKeyIx_preserves_prefix s_dir s_blk hOk i h_i_dir
                        have h_sz : i < s_blk.tokens.size := by
                          have := scanKeyIx_tokens_size_le hOk; omega
                        exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                      · -- scanValueIx: bounded form takes only the simpleKey bound
                        have h_pref := scanValueIx_preserves_prefix s_dir s_blk hOk n h_n_dir
                          h_sk_dir i h_i
                        have h_sz : i < s_blk.tokens.size := by
                          have := scanValueIx_tokens_size_le hOk; omega
                        exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                    | none =>
                      dsimp only [] at h_ok
                      generalize h_dc : scanNextTokenIx_dispatchContent s_dir c = dc_res at h_ok
                      cases dc_res with
                      | error e => simp at h_ok
                      | ok s_ct =>
                        simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                        subst h_ok
                        have h_pref :=
                          scanNextTokenIx_dispatchContent_preserves_prefix s_dir s_ct c h_dc i h_i_dir
                        have h_sz : i < s_ct.tokens.size := by
                          have := scanNextTokenIx_dispatchContent_tokens_size_le h_dc; omega
                        exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩

/-- Bundle: per-step prefix preservation + `SimpleKeyAboveFloorIx`
    maintenance through one `scanNextTokenIx` call. Indexed twin of
    legacy `scanNextToken_prefix_and_skFloor_inv` (line 1866). -/
theorem scanNextTokenIx_prefix_and_SKAFIx_inv
    (s s' : ScannerStateIx input)
    (h_next : scanNextTokenIx s = .ok (some s'))
    (n₀ fl₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveFloorIx s n₀ fl₀)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (h_fl_post : s'.flowLevel ≥ fl₀) :
    (∀ (i : Nat) (hi : i < n₀),
       ∃ (h_size : i < s'.tokens.size),
         s'.tokens[i]'h_size = s.tokens[i]'(Nat.lt_of_lt_of_le hi h_n₀)) ∧
    SimpleKeyAboveFloorIx s' n₀ fl₀ :=
  ⟨fun i hi =>
     scanNextTokenIx_preserves_prefix_of_simpleKey s s' n₀ h_n₀ h_inv.1 h_next i hi,
   scanNextTokenIx_maintains_SKAFIx s s' h_next n₀ fl₀ h_n₀ h_inv h_sync h_fl_post⟩

/-! ## §3.5  `FlowMonoChainIx_preserves_raw_prefix` — chain theorem

Token-prefix preservation through a `FlowMonoChainIx`, under
`SimpleKeyAboveFloorIx`. Mirrors legacy `FlowMonoChain_preserves_raw_prefix`
(line 2022) — induct on the chain, threading the SKAFIx invariant and
the sync invariant through each step. -/

theorem FlowMonoChainIx_preserves_raw_prefix
    {s s' : ScannerStateIx input} {n fl₀ : Nat}
    (h_fmc : FlowMonoChainIx fl₀ s n s')
    (n₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size)
    (h_stack_floor : SimpleKeyAboveFloorIx s n₀ fl₀)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (i : Nat) (hi : i < n₀) :
    ∃ (h_size : i < s'.tokens.size),
      s'.tokens[i]'h_size =
        s.tokens[i]'(Nat.lt_of_lt_of_le hi h_n₀) := by
  induction h_fmc with
  | zero => exact ⟨Nat.lt_of_lt_of_le hi h_n₀, rfl⟩
  | step _ h_snt h_rest ih =>
    have h_adds := scanNextTokenIx_tokens_size_le h_snt
    have h_fl_mid := h_rest.flowLevel_ge_start
    have h_sk_inv := scanNextTokenIx_maintains_SKAFIx _ _ h_snt n₀ fl₀
      h_n₀ h_stack_floor h_sync h_fl_mid
    have h_sync' := scanNextTokenIx_preserves_sync _ _ h_snt h_sync
    obtain ⟨h_step_size, h_step_eq⟩ :=
      scanNextTokenIx_preserves_prefix_of_simpleKey _ _ n₀ h_n₀ h_stack_floor.1 h_snt i hi
    have h_n₀_mid : n₀ ≤ _ := Nat.le_trans h_n₀ h_adds
    obtain ⟨h_rest_size, h_rest_eq⟩ := ih h_n₀_mid h_sk_inv h_sync'
    exact ⟨h_rest_size, h_rest_eq.trans h_step_eq⟩

/-! ## §3.6  `scanFilteredIx_of_chain` — top-level connection

Connect a `ScanChainIx` ending at EOF to `scanFilteredIx`. Mirrors
legacy `scanFiltered_of_chain` (line 2046) and the `_eq` variant
(line 2079).

The BOM precondition `(ScannerStateIx.mk' input).peek? ≠ some '﻿'`
is needed to skip the optional advance in `scanIx`. -/

theorem scanFilteredIx_of_chain (input : String)
    (s₀ s_final : ScannerStateIx input) (n : Nat)
    (h_s0 : s₀ = (ScannerStateIx.mk' input).emit YamlToken.streamStart)
    (h_no_bom : (ScannerStateIx.mk' input).peek? ≠ some '﻿')
    (h_chain : ScanChainIx s₀ n s_final)
    (h_eof : scanNextTokenIx s_final = .ok none)
    (h_fl : s_final.flowLevel = 0)
    (h_dp : s_final.directivesPresent = false)
    (h_fuel : n + 1 ≤ (input.utf8ByteSize + 1) * 4) :
    ∃ ts, scanFilteredIx input = .ok ts := by
  -- scanLoopIx at s_final with fuel 1 succeeds (EOF terminal step).
  obtain ⟨toks_final, h_loop_final⟩ := scanLoopIx_eof h_eof h_fl h_dp
  -- Chain lifts: scanLoopIx s₀ (1 + n) succeeds with the same result.
  have h_loop : scanLoopIx s₀ (1 + n) = .ok toks_final := h_chain.to_scanLoopIx h_loop_final
  -- Fuel monotonicity: scanLoopIx s₀ ((utf8 + 1) * 4) succeeds.
  have h_loop_fuel : scanLoopIx s₀ ((input.utf8ByteSize + 1) * 4) = .ok toks_final :=
    scanLoopIx_fuel_mono h_loop (by omega)
  -- scanIx input = scanLoopIx s₀ ((utf8 + 1) * 4).
  have h_scan : scanIx input = scanLoopIx s₀ ((input.utf8ByteSize + 1) * 4) := by
    unfold scanIx
    subst h_s0
    dsimp only []
    -- The peek? of (mk' input).emit streamStart equals (mk' input).peek?
    -- (emit only updates .tokens).
    have h_pk : ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek?
        = (ScannerStateIx.mk' input).peek? := rfl
    rw [h_pk]
    split
    · exact absurd ‹_› h_no_bom
    · rfl
  -- Connect to scanFilteredIx.
  unfold scanFilteredIx
  rw [h_scan, h_loop_fuel]
  exact ⟨_, rfl⟩

/-- **Equality version**: gives the exact filtered token array from a
    `ScanChainIx`. Mirrors legacy `scanFiltered_of_chain_eq` (line 2079). -/
theorem scanFilteredIx_of_chain_eq (input : String)
    (s₀ s_final : ScannerStateIx input) (n : Nat)
    (h_s0 : s₀ = (ScannerStateIx.mk' input).emit YamlToken.streamStart)
    (h_no_bom : (ScannerStateIx.mk' input).peek? ≠ some '﻿')
    (h_chain : ScanChainIx s₀ n s_final)
    (h_eof : scanNextTokenIx s_final = .ok none)
    (h_fl : s_final.flowLevel = 0)
    (h_dp : s_final.directivesPresent = false)
    (h_fuel : n + 1 ≤ (input.utf8ByteSize + 1) * 4) :
    scanFilteredIx input = .ok ⟨(((unwindIndentsIx s_final (-1)).emit
        YamlToken.streamEnd).tokens.tokens.filter
          (fun t => t.token != YamlToken.placeholder))⟩ := by
  have h_loop : scanLoopIx s₀ ((input.utf8ByteSize + 1) * 4) = .ok
      ((unwindIndentsIx s_final (-1)).emit YamlToken.streamEnd).tokens := by
    have h_step :=
      scanLoopIx_eof_eq (fuel := 1) (by omega) h_eof h_fl h_dp
    have h_loop_chain := h_chain.to_scanLoopIx h_step
    exact scanLoopIx_fuel_mono h_loop_chain (by omega)
  have h_scan : scanIx input = scanLoopIx s₀ ((input.utf8ByteSize + 1) * 4) := by
    unfold scanIx
    subst h_s0
    dsimp only []
    have h_pk : ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek?
        = (ScannerStateIx.mk' input).peek? := rfl
    rw [h_pk]
    split
    · exact absurd ‹_› h_no_bom
    · rfl
  unfold scanFilteredIx
  rw [h_scan, h_loop]

/-! ## §3.7  `scanNextTokenIx` preprocessing equality + chain transport

If two states produce the same preprocessing result, `scanNextTokenIx`
gives the same result. Then a chain at the second state lifts to a
chain at the first state. -/

/-- If two states produce the same preprocessing result, then
    `scanNextTokenIx` returns the same value on both. Indexed twin of
    legacy `scanNextToken_eq_of_preprocess` (line 2107). -/
theorem scanNextTokenIx_eq_of_preprocess (s₁ s₂ : ScannerStateIx input)
    (h : scanNextTokenIx_preprocess s₁ = scanNextTokenIx_preprocess s₂) :
    scanNextTokenIx s₁ = scanNextTokenIx s₂ := by
  unfold scanNextTokenIx
  simp only [bind, Except.bind]
  rw [h]

/-- If `scanNextTokenIx` gives the same result for two states and the
    second has a `ScanChainIx` of length ≥ 1, then the first does
    too. Indexed twin of legacy `ScanChain_of_scanNextToken_eq`
    (line 2116). -/
theorem ScanChainIx_of_scanNextTokenIx_eq {s₁ s₂ s' : ScannerStateIx input} {n : Nat}
    (h_eq : scanNextTokenIx s₁ = scanNextTokenIx s₂)
    (h_chain : ScanChainIx s₂ (n + 1) s') :
    ScanChainIx s₁ (n + 1) s' := by
  cases h_chain with
  | step h_snt h_rest =>
    exact .step (by rw [h_eq]; exact h_snt) h_rest

/-- `FlowMonoChainIx` version of `ScanChainIx_of_scanNextTokenIx_eq`.
    Indexed twin of legacy `FlowMonoChain_of_scanNextToken_eq`
    (line 2127). -/
theorem FlowMonoChainIx_of_scanNextTokenIx_eq {fl₀ : Nat}
    {s₁ s₂ s' : ScannerStateIx input} {n : Nat}
    (h_eq : scanNextTokenIx s₁ = scanNextTokenIx s₂)
    (h_fl : s₁.flowLevel ≥ fl₀)
    (h_chain : FlowMonoChainIx fl₀ s₂ (n + 1) s') :
    FlowMonoChainIx fl₀ s₁ (n + 1) s' := by
  cases h_chain with
  | step _ h_snt h_rest =>
    exact .step h_fl (by rw [h_eq]; exact h_snt) h_rest

/-! ## §3.8  Pipeline factoring

`scanNextTokenIx` decomposes into preprocess → dispatchStructural →
allowDirectives update → checkBlockFlowIndent → flow / block / content.
A factoring lemma lets us compose individual stage results into a
single `scanNextTokenIx = .ok (some s_result)` conclusion. -/

/-- When preprocessing succeeds, structural dispatch returns `none`,
    `checkBlockFlowIndent` succeeds, and the flow indicator dispatch
    produces a result, then `scanNextTokenIx` returns that result.
    Indexed twin of legacy `scanNextToken_via_flow_dispatch` (line 2147). -/
theorem scanNextTokenIx_via_flow_dispatch
    (s s_pp s_ad s_result : ScannerStateIx input) (c : Char)
    (h_pp : scanNextTokenIx_preprocess s = .ok (some (s_pp, c)))
    (h_struct : scanNextTokenIx_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (h_check : scanNextTokenIx_checkBlockFlowIndent s_ad c = .ok ())
    (h_flow : scanNextTokenIx_dispatchFlowIndicators s_ad c = .ok (some s_result)) :
    scanNextTokenIx s = .ok (some s_result) := by
  unfold scanNextTokenIx
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_pp]
  dsimp only []
  rw [h_struct]
  dsimp only []
  rw [← h_ad_eq]
  rw [h_check]
  dsimp only []
  rw [h_flow]

end L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
