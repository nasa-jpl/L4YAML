/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Basic

/-! # `FlowMonoChain.Preserve.Step` — Phase 3 Step 6f.3b3.flowmono.preserve.step

**Sub-session 1 of `.flowmono.preserve`** (legacy
`Proofs/Output/EmitterScannability.lean` lines 1806–2165, ~360 LOC
originally; ~140 LOC after the `.sync.invariant` retroactive move).
Per-step preservation primitives that feed the chain-level sync
proofs in `Sync/Invariant.lean`.

## Scope (after `.sync.invariant` retroactive move)

  - **§3.0** — Inner-stage `_preserves_flowLevel` /
    `_preserves_simpleKeyStack` Ix twins for sub-scanners
    (`scanDocumentStartIx`, `scanDocumentEndIx`, `scanDirectiveIx`,
    `scanBlockEntryIx`, `scanKeyIx`, `scanValueIx`,
    `scanFlowEntryIx`).
  - **§3.1** — Per-dispatcher sync preservation:
    `scanNextTokenIx_dispatchStructural_preserves_flowLevel`,
    `_preserves_simpleKeyStack`, and the same for the block and
    content dispatchers (the flow dispatcher's *joint* sync invariant
    is in `Sync/Invariant.lean` §1 — it tracks the push/pop balance
    against `flowLevel`).

## Moved to `.sync.invariant`

Sections originally numbered §3.2–§3.8 (chain-level sync
theorems, prefix preservation, `scanFilteredIx_of_chain[_eq]`,
algebraic chain transport, and `scanNextTokenIx_via_flow_dispatch`)
moved to
`Proofs/Output/IndexedEmitterScannability/FlowMonoChain/Sync/
Invariant.lean` (sub-session 1 of `.flowmono.sync`) to match the
sub-session organization. No theorem signatures, proofs, or
namespaces changed — pure relocation.

## Legacy mapping

Mirrors the inner-stage and per-dispatcher slices of
`EmitterScannability.lean` lines 1806–1885 (the per-stage
preservation primitives consumed by chain-level proofs).

The indexed versions are typically shorter than their legacy
counterparts: cursor-keyed scalar scanners eliminate
per-scalar SK-preservation steps in the content dispatcher (Reflection
122).
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
change it. These twins are consumed by the `scanNextTokenIx_
preserves_sync` chain in `Sync/Invariant.lean` §2. -/

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
its proof obligation is the joint sync invariant, handled in
`Sync/Invariant.lean` §1. -/

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

end L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
