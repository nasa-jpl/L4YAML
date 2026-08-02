/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.ScanChain

/-! # `IndexedEmitterScannability.FlowMonoChain.Basic` — Phase 3 Step 6f.3b3 core

**Status**: §1 + §2 landed 2026-05-25 (sub-sessions
`.flowmono.inductive` and `.flowmono.skaf`). Together they port the
`FlowMonoChain` core + `SimpleKeyAboveFloor` machinery from
`Proofs/Output/EmitterScannability.lean` lines 1304–1805.

This file holds the inductive type and the ghost predicate. The
prefix-preservation infrastructure (legacy lines 1806–~3300) is split
across siblings under `FlowMonoChain/Preserve/` (one file per
sub-session of `.flowmono.preserve`).

## Scope

  - **§1 `FlowMonoChainIx` inductive + immediate helpers** (legacy
    lines 1304–1387, ~70 LOC). `FlowMonoChainIx fl₀ s n s'` (a
    `ScanChainIx` where every intermediate state has
    `flowLevel ≥ fl₀`), `.toScanChainIx`, `.flowLevel_ge_start` /
    `_end`, `.single`, `.trans`, `.weaken`, `.tokens_mono`.

  - **§2 `SimpleKeyAboveFloorIx` predicate + maintenance** (legacy
    lines 1388–1805, ~420 LOC). Flow-level-aware simple-key
    invariant. Five constructors (`_of_cleared_preserved`,
    `_of_preserved`, `_of_endLine_update`, `_of_flow_open`,
    `_of_flow_close`); preprocess + dispatch maintenance + the
    `scanNextTokenIx_maintains_SKAFIx` capstone.

## Sibling files (under `FlowMonoChain/Preserve/`)

  - **`Step.lean`** (sub-session `.flowmono.preserve.step`) — Step 4
    per-step + chain prefix preservation core: per-dispatcher
    `_preserves_flowLevel` / `_preserves_simpleKeyStack`,
    `_preserves_sync`, `_preserves_prefix_of_simpleKey`,
    `_prefix_and_SKAFIx_inv`, `FlowMonoChainIx_preserves_raw_prefix`,
    `scanFilteredIx_of_chain[_eq]`, pipeline factoring.
  - **`DpInv.lean`** (sub-session `.flowmono.preserve.dpinv`, queued)
    — per-stage `_preserves_dp` / `_preserves_indents` /
    `_preserves_ek` triplet (legacy lines 2166–2745).
  - **`Helpers.lean`** (sub-session `.flowmono.preserve.helpers`,
    queued) — `AllTokensOnLine` / `EndLineOnLine` /
    `StackEndLineOnLine` definitions + supporting lemmas (legacy
    lines 2747–~3300).

## Phase 3 Step 6f cutover

See `../Basic.lean` for the directory-wide cutover plan.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.EmitterScannability.ScanChain
open L4YAML.Proofs.Indexed.ScannerPlainScalarValid

variable {input : String}

/-! ## §1  `FlowMonoChainIx` — `ScanChainIx` with flow-level lower bound

Indexed twin of legacy `FlowMonoChain` (lines 1304–1387 of
`Proofs/Output/EmitterScannability.lean`). `FlowMonoChainIx fl₀ s n s'`
is a `ScanChainIx` where every *visited* state (the start of each
step) has `flowLevel ≥ fl₀`. This captures the "flow-balanced"
property: the chain never closes brackets below the initial flow
depth, ensuring stacked simple keys from before the chain are never
restored.

**Motivation**: `ScanChainIx_filtered_prefix` (to be ported in the
`.filteredgrowth` sub-session) needs to show that `setIfInBounds`
(from `scanValuePrepareIx`) never writes at token positions below
the initial range. This holds when the simple-key stack is never
popped below its initial height, which follows from
`flowLevel ≥ fl₀` at every step (since `simpleKeyStack.size` tracks
`flowLevel` via `scanFlowStart`/`scanFlowEnd` push/pop sync).

For emitter-produced chains, `fl₀ = s.flowLevel` is always satisfied
because the emitter produces balanced bracket sequences: every
`]`/`}` matches an inner `[`/`{`.

**Differences from legacy `FlowMonoChain`**:

  - `input : String` is type-level (lifted into
    `ScannerStateIx input`), so both endpoints share the same input
    by construction.
  - `scanNextToken` → `scanNextTokenIx`; `ScanChain` → `ScanChainIx`.
  - Otherwise structurally identical to the legacy inductive: the
    `flowLevel` floor is a property of `s.flowLevel : Nat` which is
    the same field in both substrates. -/

/-- `FlowMonoChainIx fl₀ s n s'` is a `ScanChainIx` where every
    intermediate state has `flowLevel ≥ fl₀`. Indexed twin of legacy
    `FlowMonoChain` (line 1319). -/
inductive FlowMonoChainIx (fl₀ : Nat) :
    ScannerStateIx input → Nat → ScannerStateIx input → Prop where
  | zero {s : ScannerStateIx input} (h_fl : s.flowLevel ≥ fl₀) :
      FlowMonoChainIx fl₀ s 0 s
  | step {s s_mid s' : ScannerStateIx input} {n : Nat}
      (h_fl : s.flowLevel ≥ fl₀)
      (h_snt : scanNextTokenIx s = .ok (some s_mid))
      (h_rest : FlowMonoChainIx fl₀ s_mid n s') :
      FlowMonoChainIx fl₀ s (n + 1) s'

/-! ### §1.1  Degradation to `ScanChainIx` -/

/-- Degrade a `FlowMonoChainIx` to a plain `ScanChainIx` by forgetting
    flow-level bounds. Indexed twin of legacy `FlowMonoChain.toScanChain`
    (line 1329). -/
lemma FlowMonoChainIx.toScanChainIx {fl₀ : Nat}
    {s s' : ScannerStateIx input} {n : Nat}
    (h : FlowMonoChainIx fl₀ s n s') : ScanChainIx s n s' := by
  induction h with
  | zero => exact .zero
  | step _ h_snt _h_rest ih => exact .step h_snt ih

/-! ### §1.2  Flow-level endpoint bounds -/

/-- The start state of a `FlowMonoChainIx` has `flowLevel ≥ fl₀`.
    Indexed twin of legacy `FlowMonoChain.flowLevel_ge_start`
    (line 1336). -/
lemma FlowMonoChainIx.flowLevel_ge_start {fl₀ : Nat}
    {s s' : ScannerStateIx input} {n : Nat}
    (h : FlowMonoChainIx fl₀ s n s') : s.flowLevel ≥ fl₀ := by
  cases h with
  | zero h_fl => exact h_fl
  | step h_fl _ _ => exact h_fl

/-- The end state of a `FlowMonoChainIx` has `flowLevel ≥ fl₀`.
    Indexed twin of legacy `FlowMonoChain.flowLevel_ge_end`
    (line 1343). -/
lemma FlowMonoChainIx.flowLevel_ge_end {fl₀ : Nat}
    {s s' : ScannerStateIx input} {n : Nat}
    (h : FlowMonoChainIx fl₀ s n s') : s'.flowLevel ≥ fl₀ := by
  induction h with
  | zero h_fl => exact h_fl
  | step _ _ _ ih => exact ih

/-! ### §1.3  Combinators (`.single`, `.trans`) -/

/-- A single `scanNextTokenIx` step as a `FlowMonoChainIx`. Indexed
    twin of legacy `FlowMonoChain.single` (line 1350). -/
lemma FlowMonoChainIx.single {fl₀ : Nat} {s s' : ScannerStateIx input}
    (h_snt : scanNextTokenIx s = .ok (some s'))
    (h_fl : s.flowLevel ≥ fl₀)
    (h_fl' : s'.flowLevel ≥ fl₀) :
    FlowMonoChainIx fl₀ s 1 s' :=
  .step h_fl h_snt (.zero h_fl')

/-- Transitivity: concatenate two `FlowMonoChainIx`s with the same
    floor. Indexed twin of legacy `FlowMonoChain.trans` (line 1358). -/
lemma FlowMonoChainIx.trans {fl₀ : Nat}
    {s₁ s₂ s₃ : ScannerStateIx input} {n₁ n₂ : Nat}
    (h1 : FlowMonoChainIx fl₀ s₁ n₁ s₂)
    (h2 : FlowMonoChainIx fl₀ s₂ n₂ s₃) :
    FlowMonoChainIx fl₀ s₁ (n₁ + n₂) s₃ := by
  induction h1 with
  | zero => simpa using h2
  | @step s s_mid s₂ k h_fl h_snt _h_rest ih =>
    have h_ih := ih h2
    have : k + 1 + n₂ = (k + n₂) + 1 := by omega
    rw [this]
    exact .step h_fl h_snt h_ih

/-! ### §1.4  Floor weakening and token monotonicity -/

/-- Weaken the flow-level floor: if `fl₀ ≤ fl₁`, a `FlowMonoChainIx fl₁`
    is also a `FlowMonoChainIx fl₀`. Indexed twin of legacy
    `FlowMonoChain.weaken` (line 1372). -/
lemma FlowMonoChainIx.weaken {fl₀ fl₁ : Nat}
    {s s' : ScannerStateIx input} {n : Nat}
    (h : FlowMonoChainIx fl₁ s n s') (h_le : fl₀ ≤ fl₁) :
    FlowMonoChainIx fl₀ s n s' := by
  induction h with
  | zero h_fl => exact .zero (by omega)
  | step h_fl h_snt _h_rest ih => exact .step (by omega) h_snt ih

/-- Token monotonicity for `FlowMonoChainIx`: tokens only grow through
    the chain (delegates to `ScanChainIx` token monotonicity via the
    `scanNextTokenIx_tokens_size_le` step lemma). Indexed twin of
    legacy `FlowMonoChain.tokens_mono` (line 1381). -/
lemma FlowMonoChainIx.tokens_mono {fl₀ : Nat}
    {s s' : ScannerStateIx input} {n : Nat}
    (h : FlowMonoChainIx fl₀ s n s') : s'.tokens.size ≥ s.tokens.size := by
  induction h with
  | zero => omega
  | step _ h_snt _ ih =>
    have := scanNextTokenIx_tokens_size_le h_snt; omega

/-! ## §2  `SimpleKeyAboveFloorIx` — flow-level-aware simple-key invariant

Indexed twin of legacy `SimpleKeyAboveFloor` (lines 1388–1488 of
`Proofs/Output/EmitterScannability.lean`). Like `SimpleKeyAbove` but
only constrains stack entries at index ≥ `stackFloor`, with a size
guarantee. Designed for use with `FlowMonoChainIx` where the stack
floor equals the initial flow level.

Entries below the floor may have stale `tokenIndex` values from
before the chain. -/

/-- `SimpleKeyAboveFloorIx s n stackFloor` asserts that:
    1. The current `simpleKey` has `tokenIndex ≥ n` when `possible`;
    2. Every stack entry at index ≥ `stackFloor` with `possible = true`
       has `tokenIndex ≥ n`;
    3. The stack has at least `stackFloor` entries.

    Indexed twin of legacy `SimpleKeyAboveFloor` (line 1396). -/
def SimpleKeyAboveFloorIx (s : ScannerStateIx input) (n : Nat)
    (stackFloor : Nat) : Prop :=
  (s.simpleKey.possible = true → s.simpleKey.tokenIndex ≥ n) ∧
  (∀ j, stackFloor ≤ j → (h : j < s.simpleKeyStack.size) →
    s.simpleKeyStack[j].possible = true → s.simpleKeyStack[j].tokenIndex ≥ n) ∧
  (s.simpleKeyStack.size ≥ stackFloor)

/-! ### §2.1  SKAF constructors -/

/-- If `s_out` clears the simple key (`possible = false`) and preserves
    the stack, then `SimpleKeyAboveFloorIx` transports from `s_in`.
    Indexed twin of legacy `SimpleKeyAboveFloor_of_cleared_preserved`
    (line 1404). -/
lemma SimpleKeyAboveFloorIx_of_cleared_preserved
    (s_out s_in : ScannerStateIx input) (n fl₀ : Nat)
    (h_sk : s_out.simpleKey.possible = false)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : SimpleKeyAboveFloorIx s_in n fl₀) :
    SimpleKeyAboveFloorIx s_out n fl₀ :=
  ⟨fun hp => absurd hp (by rw [h_sk]; decide),
   fun j hfl hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2.1 j hfl hj hp,
   by rw [h_stack]; exact h_inv.2.2⟩

/-- If `s_out` preserves both `simpleKey` and `simpleKeyStack`, then
    `SimpleKeyAboveFloorIx` transports from `s_in`. Indexed twin of
    legacy `SimpleKeyAboveFloor_of_preserved` (line 1412). -/
lemma SimpleKeyAboveFloorIx_of_preserved
    (s_out s_in : ScannerStateIx input) (n fl₀ : Nat)
    (h_sk : s_out.simpleKey = s_in.simpleKey)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : SimpleKeyAboveFloorIx s_in n fl₀) :
    SimpleKeyAboveFloorIx s_out n fl₀ :=
  ⟨fun hp => by rw [h_sk] at hp ⊢; exact h_inv.1 hp,
   fun j hfl hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2.1 j hfl hj hp,
   by rw [h_stack]; exact h_inv.2.2⟩

/-- If `s_out` preserves `possible` and `tokenIndex` of `simpleKey` and
    the entire stack, then `SimpleKeyAboveFloorIx` transports from `s_in`.
    Useful when scalar scanners update `endLine` or `cursor` but
    preserve the key-status fields. Indexed twin of legacy
    `SimpleKeyAboveFloor_of_endLine_update` (line 1420). -/
lemma SimpleKeyAboveFloorIx_of_endLine_update
    (s_out s_in : ScannerStateIx input) (n fl₀ : Nat)
    (h_poss : s_out.simpleKey.possible = s_in.simpleKey.possible)
    (h_idx : s_out.simpleKey.tokenIndex = s_in.simpleKey.tokenIndex)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : SimpleKeyAboveFloorIx s_in n fl₀) :
    SimpleKeyAboveFloorIx s_out n fl₀ :=
  ⟨fun hp => by
    have hp' : s_in.simpleKey.possible = true := by rw [← h_poss]; exact hp
    have := h_inv.1 hp'; omega,
   fun j hfl hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2.1 j hfl hj hp,
   by rw [h_stack]; exact h_inv.2.2⟩

/-- Flow-open transport: `s_out` clears the simple key and pushes the
    old `simpleKey` onto `simpleKeyStack`. Both the floor-above
    invariant and the size lower bound carry over. Indexed twin of
    legacy `SimpleKeyAboveFloor_of_flow_open` (line 1431). -/
lemma SimpleKeyAboveFloorIx_of_flow_open
    (s_out s_in : ScannerStateIx input) (n fl₀ : Nat)
    (h_sk : s_out.simpleKey.possible = false)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack.push s_in.simpleKey)
    (h_inv : SimpleKeyAboveFloorIx s_in n fl₀) :
    SimpleKeyAboveFloorIx s_out n fl₀ := by
  refine ⟨fun hp => absurd hp (by rw [h_sk]; decide), fun j hfl hj hp => ?_, ?_⟩
  · simp only [h_stack, Array.size_push] at hj
    by_cases hlt : j < s_in.simpleKeyStack.size
    · have hp' : s_in.simpleKeyStack[j].possible = true := by
        simp only [h_stack, Array.getElem_push, dif_pos hlt] at hp; exact hp
      have h_ge := h_inv.2.1 j hfl hlt hp'
      show s_out.simpleKeyStack[j].tokenIndex ≥ n
      simp only [h_stack, Array.getElem_push, dif_pos hlt]; exact h_ge
    · have hj_eq : j = s_in.simpleKeyStack.size := by omega
      subst hj_eq
      have hp' : s_in.simpleKey.possible = true := by
        simp only [h_stack, Array.getElem_push, dif_neg hlt] at hp; exact hp
      have h_ge := h_inv.1 hp'
      show s_out.simpleKeyStack[s_in.simpleKeyStack.size].tokenIndex ≥ n
      simp only [h_stack, Array.getElem_push, dif_neg hlt]; exact h_ge
  · simp only [h_stack, Array.size_push]; have := h_inv.2.2; omega

/-- Flow-close transport: `s_out`'s `simpleKey` is restored from
    `simpleKeyStack.back?` and `simpleKeyStack` is popped. Floor
    preservation requires either `simpleKeyStack.size > fl₀` (so the
    popped slot was above the floor) or `fl₀ = 0` (so all positions are
    trivially above the floor). Indexed twin of legacy
    `SimpleKeyAboveFloor_of_flow_close` (line 1452). -/
lemma SimpleKeyAboveFloorIx_of_flow_close
    (s_out s_in : ScannerStateIx input) (n fl₀ : Nat)
    (h_sk : s_out.simpleKey =
      s_in.simpleKeyStack.back?.getD { cursor := IxCursor.start input })
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack.pop)
    (h_inv : SimpleKeyAboveFloorIx s_in n fl₀)
    (h_size : s_in.simpleKeyStack.size > fl₀ ∨ fl₀ = 0) :
    SimpleKeyAboveFloorIx s_out n fl₀ := by
  rcases h_size with h_gt | h_zero
  · -- h_gt : s_in.simpleKeyStack.size > fl₀
    refine ⟨fun hp => ?_, fun j hfl hj hp => ?_, ?_⟩
    · have h_lt : s_in.simpleKeyStack.size - 1 < s_in.simpleKeyStack.size := by omega
      have h_back : s_in.simpleKeyStack.back?.getD { cursor := IxCursor.start input } =
          s_in.simpleKeyStack[s_in.simpleKeyStack.size - 1]'h_lt := by
        simp [Array.back?, h_lt]
      rw [h_sk, h_back] at hp ⊢
      exact h_inv.2.1 _ (by omega) h_lt hp
    · simp only [h_stack, Array.size_pop] at hj
      simp only [h_stack, Array.getElem_pop] at hp ⊢
      exact h_inv.2.1 j hfl (by omega) hp
    · simp only [h_stack, Array.size_pop]; omega
  · -- h_zero : fl₀ = 0 — all conjuncts trivially use ≥ 0
    subst h_zero
    refine ⟨fun hp => ?_, fun j hfl hj hp => ?_, by omega⟩
    · by_cases h_nonempty : s_in.simpleKeyStack.size > 0
      · have h_lt : s_in.simpleKeyStack.size - 1 < s_in.simpleKeyStack.size := by omega
        have h_back : s_in.simpleKeyStack.back?.getD { cursor := IxCursor.start input } =
            s_in.simpleKeyStack[s_in.simpleKeyStack.size - 1]'h_lt := by
          simp [Array.back?, h_lt]
        rw [h_sk, h_back] at hp ⊢
        exact h_inv.2.1 _ (by omega) h_lt hp
      · -- Stack is empty: back? = none, so simpleKey = default with possible = false
        have h_empty : s_in.simpleKeyStack.size = 0 := by omega
        have h_none : s_in.simpleKeyStack.back? = none := by
          simp [Array.back?, h_empty]
        rw [h_sk, h_none] at hp
        simp at hp
    · simp only [h_stack, Array.size_pop] at hj
      simp only [h_stack, Array.getElem_pop] at hp ⊢
      exact h_inv.2.1 j (by omega) (by omega) hp

/-! ### §2.2  Preprocess preservation and SKAF maintenance

`scanNextTokenIx_preprocess` only adjusts cursor / indent stack /
simple key (the latter only by `saveSimpleKeyIx` with tokenIndex =
old `tokens.size`). It never touches `flowLevel`, and only ever
grows the token stream. -/

/-- `skipToContentS` preserves `flowLevel` (it only adjusts cursor /
    indent-check / simple-key-allowed flags). -/
@[simp] lemma skipToContentS_flowLevel {input : String}
    (s : ScannerStateIx input) : s.skipToContentS.flowLevel = s.flowLevel := by
  unfold ScannerStateIx.skipToContentS
  dsimp only
  split <;> rfl

/-- `scanNextTokenIx_preprocess` preserves `flowLevel`. Indexed twin of
    legacy `preprocess_preserves_flowLevel` (line 1492). -/
lemma scanNextTokenIx_preprocess_preserves_flowLevel {input : String}
    (s s1 : ScannerStateIx input) (c : Char)
    (h : scanNextTokenIx_preprocess s = .ok (some (s1, c))) :
    s1.flowLevel = s.flowLevel := by
  unfold scanNextTokenIx_preprocess at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          rw [saveSimpleKeyIx_flowLevel]
          show (unwindIndentsIx _ _).flowLevel = s.flowLevel
          rw [unwindIndentsIx_preserves_flowLevel, skipToContentS_flowLevel]
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          rw [saveSimpleKeyIx_flowLevel, skipToContentS_flowLevel]

/-- `skipToContentS` preserves `tokens` (cursor-only update). -/
@[simp] lemma skipToContentS_preserves_tokens {input : String}
    (s : ScannerStateIx input) : s.skipToContentS.tokens = s.tokens :=
  skipToContentS_tokens s

/-- `scanNextTokenIx_preprocess` preserves the simple-key stack. Indexed
    twin of legacy `preprocess_preserves_simpleKeyStack`. -/
lemma scanNextTokenIx_preprocess_preserves_simpleKeyStack {input : String}
    (s s1 : ScannerStateIx input) (c : Char)
    (h : scanNextTokenIx_preprocess s = .ok (some (s1, c))) :
    s1.simpleKeyStack = s.simpleKeyStack := by
  unfold scanNextTokenIx_preprocess at h
  dsimp only at h
  have h_skip := skipToContentS_preserves_simpleKeyStack s
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          rw [saveSimpleKeyIx_preserves_simpleKeyStack]
          show (unwindIndentsIx _ _).simpleKeyStack = s.simpleKeyStack
          rw [unwindIndentsIx_preserves_simpleKeyStack, h_skip]
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          rw [saveSimpleKeyIx_preserves_simpleKeyStack, h_skip]

/-- `scanNextTokenIx_preprocess` only grows the token stream. -/
lemma scanNextTokenIx_preprocess_tokens_size_le {input : String}
    (s s1 : ScannerStateIx input) (c : Char)
    (h : scanNextTokenIx_preprocess s = .ok (some (s1, c))) :
    s.tokens.size ≤ s1.tokens.size := by
  unfold scanNextTokenIx_preprocess at h
  dsimp only at h
  have h_skip : s.skipToContentS.tokens.size = s.tokens.size := by
    rw [skipToContentS_tokens]
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          have h_save := saveSimpleKeyIx_tokens_size_le
            ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col
                with needIndentCheck := false } : ScannerStateIx input)
          have h_unwind := unwindIndentsIx_tokens_size_le s.skipToContentS
            s.skipToContentS.cursor.pos.col
          have h_set :
              ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col
                  with needIndentCheck := false } : ScannerStateIx input).tokens.size
                = (unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col).tokens.size :=
            rfl
          show s.tokens.size ≤
            (saveSimpleKeyIx { unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col
                with needIndentCheck := false }).tokens.size
          omega
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          have h_save := saveSimpleKeyIx_tokens_size_le s.skipToContentS
          show s.tokens.size ≤ (saveSimpleKeyIx s.skipToContentS).tokens.size
          omega

/-- `saveSimpleKeyIx` maintains the SKAF `simpleKey` predicate:
    if `possible = true` after the call, the recorded `tokenIndex` is
    either the input one (unchanged branch) or the input `tokens.size`
    (set branch), both ≥ n₀ when `n₀ ≤ s.tokens.size`. -/
lemma saveSimpleKeyIx_simpleKey_inv {input : String}
    (st : ScannerStateIx input) (n : Nat) (h_tok : n ≤ st.tokens.size)
    (h_sk : st.simpleKey.possible = true → st.simpleKey.tokenIndex ≥ n) :
    (saveSimpleKeyIx st).simpleKey.possible = true →
    (saveSimpleKeyIx st).simpleKey.tokenIndex ≥ n := by
  unfold saveSimpleKeyIx
  split
  · exact h_sk
  · split
    · intro; dsimp only []; omega
    · exact h_sk

/-- The `simpleKey` part of SKAF carries through `scanNextTokenIx_preprocess`.
    Indexed twin of legacy `preprocess_simpleKey_inv` (line 4291). -/
lemma scanNextTokenIx_preprocess_simpleKey_inv {input : String}
    (s s1 : ScannerStateIx input) (c : Char)
    (h : scanNextTokenIx_preprocess s = .ok (some (s1, c))) (n : Nat)
    (h_n : n ≤ s.tokens.size)
    (h_inv : s.simpleKey.possible = true → s.simpleKey.tokenIndex ≥ n) :
    s1.simpleKey.possible = true → s1.simpleKey.tokenIndex ≥ n := by
  intro h_poss
  unfold scanNextTokenIx_preprocess at h
  dsimp only at h
  have h_sk_skip : s.skipToContentS.simpleKey = s.simpleKey :=
    skipToContentS_preserves_simpleKey s
  have h_tok_skip : s.skipToContentS.tokens.size = s.tokens.size := by
    rw [skipToContentS_tokens]
  split at h
  · simp at h
  · split at h
    · -- needIndentCheck path
      split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          have h_unwind_sz :=
            unwindIndentsIx_tokens_size_le s.skipToContentS s.skipToContentS.cursor.pos.col
          have h_unwind_sk :=
            unwindIndentsIx_preserves_simpleKey s.skipToContentS s.skipToContentS.cursor.pos.col
          have h_tok_post : n ≤
              ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col
                  with needIndentCheck := false } : ScannerStateIx input).tokens.size := by
            show n ≤ (unwindIndentsIx s.skipToContentS _).tokens.size; omega
          have h_sk_post :
              ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col
                  with needIndentCheck := false } : ScannerStateIx input).simpleKey.possible
                = true →
              ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col
                  with needIndentCheck := false } : ScannerStateIx input).simpleKey.tokenIndex
                ≥ n := by
            show (unwindIndentsIx s.skipToContentS _).simpleKey.possible = true → _
            rw [h_unwind_sk, h_sk_skip]; exact h_inv
          exact saveSimpleKeyIx_simpleKey_inv _ n h_tok_post h_sk_post h_poss
    · -- no needIndentCheck path
      split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          have h_tok_post : n ≤ s.skipToContentS.tokens.size := by omega
          have h_sk_post : s.skipToContentS.simpleKey.possible = true →
              s.skipToContentS.simpleKey.tokenIndex ≥ n := by
            rw [h_sk_skip]; exact h_inv
          exact saveSimpleKeyIx_simpleKey_inv s.skipToContentS n h_tok_post h_sk_post h_poss

/-- `scanNextTokenIx_preprocess` maintains `SimpleKeyAboveFloorIx`.
    Indexed twin of legacy `preprocess_maintains_SimpleKeyAboveFloor`
    (line 1523). -/
lemma scanNextTokenIx_preprocess_maintains_SKAFIx {input : String}
    (s s1 : ScannerStateIx input) (c : Char)
    (h : scanNextTokenIx_preprocess s = .ok (some (s1, c)))
    (n₀ fl₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveFloorIx s n₀ fl₀) :
    SimpleKeyAboveFloorIx s1 n₀ fl₀ := by
  refine ⟨?_, ?_, ?_⟩
  · exact scanNextTokenIx_preprocess_simpleKey_inv s s1 c h n₀ h_n₀ h_inv.1
  · intro j hfl hj hp
    have h_stack := scanNextTokenIx_preprocess_preserves_simpleKeyStack s s1 c h
    simp only [h_stack] at hj hp ⊢
    exact h_inv.2.1 j hfl hj hp
  · have h_stack := scanNextTokenIx_preprocess_preserves_simpleKeyStack s s1 c h
    rw [h_stack]; exact h_inv.2.2

/-! ### §2.3  Dispatcher SKAF maintenance -/

/-- `scanNextTokenIx_dispatchStructural` maintains `SimpleKeyAboveFloorIx`.
    Indexed twin of legacy `dispatchStructural_maintains_SimpleKeyAboveFloor`
    (line 1536). -/
lemma scanNextTokenIx_dispatchStructural_maintains_SKAFIx {input : String}
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchStructural s c = .ok (some s'))
    (n₀ fl₀ : Nat) (_h_n₀ : n₀ ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveFloorIx s n₀ fl₀) :
    SimpleKeyAboveFloorIx s' n₀ fl₀ := by
  unfold scanNextTokenIx_dispatchStructural at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact SimpleKeyAboveFloorIx_of_cleared_preserved _ s n₀ fl₀
        (scanDocumentStartIx_clears_simpleKey s)
        (scanDocumentStartIx_preserves_simpleKeyStack s) h_inv
    | (rename_i h_eq; exact SimpleKeyAboveFloorIx_of_cleared_preserved _ s n₀ fl₀
        (scanDocumentEndIx_clears_simpleKey s _ h_eq)
        (scanDocumentEndIx_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact SimpleKeyAboveFloorIx_of_preserved _ s n₀ fl₀
        (scanDirectiveIx_preserves_simpleKey s _ h_eq)
        (scanDirectiveIx_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

/-- `scanFlowSequenceEndIx` and `scanFlowMappingEndIx` decrement `flowLevel`
    by one (truncated subtraction). Used by the FlowIndicators SKAF
    dispatcher to derive the stack-size-above-floor disjunction. -/
lemma scanFlowSequenceEndIx_flowLevel_eq {input : String}
    (s : ScannerStateIx input) :
    (scanFlowSequenceEndIx s).flowLevel = s.flowLevel - 1 := by
  unfold scanFlowSequenceEndIx
  simp only [advance_flowLevel, emit_flowLevel]

lemma scanFlowMappingEndIx_flowLevel_eq {input : String}
    (s : ScannerStateIx input) :
    (scanFlowMappingEndIx s).flowLevel = s.flowLevel - 1 := by
  unfold scanFlowMappingEndIx
  simp only [advance_flowLevel, emit_flowLevel]

/-- `scanNextTokenIx_dispatchFlowIndicators` maintains `SimpleKeyAboveFloorIx`.
    Indexed twin of legacy `dispatchFlowIndicators_maintains_SimpleKeyAboveFloor`
    (line 1562). Requires:
    - `h_sync`: `simpleKeyStack.size ≥ flowLevel` (stack-flow sync invariant)
    - `h_fl_post`: `s'.flowLevel ≥ fl₀` (from `FlowMonoChainIx` continuation) -/
lemma scanNextTokenIx_dispatchFlowIndicators_maintains_SKAFIx {input : String}
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s'))
    (n₀ fl₀ : Nat) (_h_n₀ : n₀ ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveFloorIx s n₀ fl₀)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (h_fl_post : s'.flowLevel ≥ fl₀) :
    SimpleKeyAboveFloorIx s' n₀ fl₀ := by
  unfold scanNextTokenIx_dispatchFlowIndicators at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact SimpleKeyAboveFloorIx_of_flow_open _ s n₀ fl₀
        (scanFlowSequenceStartIx_simpleKey_cleared s)
        (scanFlowSequenceStartIx_stack_pushed s) h_inv
    | exact SimpleKeyAboveFloorIx_of_flow_open _ s n₀ fl₀
        (scanFlowMappingStartIx_simpleKey_cleared s)
        (scanFlowMappingStartIx_stack_pushed s) h_inv
    | (rename_i h_eq; exact SimpleKeyAboveFloorIx_of_preserved _ s n₀ fl₀
        (scanFlowEntryIx_preserves_simpleKey s _ h_eq)
        (scanFlowEntryIx_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)
    | -- Flow close (sequence end): derive size>fl₀ ∨ fl₀=0 from h_fl_post + h_sync
      (have h_fl_eq : (scanFlowSequenceEndIx s).flowLevel = s.flowLevel - 1 :=
        scanFlowSequenceEndIx_flowLevel_eq s
       have h_gt : s.simpleKeyStack.size > fl₀ ∨ fl₀ = 0 := by omega
       exact SimpleKeyAboveFloorIx_of_flow_close _ s n₀ fl₀
         (scanFlowSequenceEndIx_simpleKey_restored s)
         (scanFlowSequenceEndIx_stack_popped s) h_inv h_gt)
    | -- Flow close (mapping end)
      (have h_fl_eq : (scanFlowMappingEndIx s).flowLevel = s.flowLevel - 1 :=
        scanFlowMappingEndIx_flowLevel_eq s
       have h_gt : s.simpleKeyStack.size > fl₀ ∨ fl₀ = 0 := by omega
       exact SimpleKeyAboveFloorIx_of_flow_close _ s n₀ fl₀
         (scanFlowMappingEndIx_simpleKey_restored s)
         (scanFlowMappingEndIx_stack_popped s) h_inv h_gt)

/-- `scanNextTokenIx_dispatchBlockIndicators` maintains `SimpleKeyAboveFloorIx`.
    Indexed twin of legacy `dispatchBlockIndicators_maintains_SimpleKeyAboveFloor`
    (line 1615). -/
lemma scanNextTokenIx_dispatchBlockIndicators_maintains_SKAFIx {input : String}
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s'))
    (n₀ fl₀ : Nat) (_h_n₀ : n₀ ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveFloorIx s n₀ fl₀) :
    SimpleKeyAboveFloorIx s' n₀ fl₀ := by
  unfold scanNextTokenIx_dispatchBlockIndicators at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | (rename_i h_eq; exact SimpleKeyAboveFloorIx_of_preserved _ s n₀ fl₀
        (scanBlockEntryIx_preserves_simpleKey s _ h_eq)
        (scanBlockEntryIx_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact SimpleKeyAboveFloorIx_of_cleared_preserved _ s n₀ fl₀
        (scanKeyIx_clears_simpleKey s _ h_eq)
        (scanKeyIx_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact SimpleKeyAboveFloorIx_of_cleared_preserved _ s n₀ fl₀
        (scanValueIx_clears_simpleKey s _ h_eq)
        (scanValueIx_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

/-! The indexed `scanNextTokenIx_dispatchContent` differs structurally
from legacy: the scalar branches (block/quoted/plain) use cursor-keyed
scanners (`scanBlockScalarIx : IxCursor → ...`, etc.) whose results
are spliced back into the state via `{ s with cursor := cAfter }`
followed by `.emitAt` + `{ sEmit with simpleKeyAllowed := false }`.
This sequence preserves `simpleKey` and `simpleKeyStack` *structurally*
— no per-scanner SK-preservation lemma is needed, because the only
fields touched are `cursor`, `tokens`, and `simpleKeyAllowed`. The
anchor/alias/tag branches (`&`/`*`/`!`) still use the state-keyed
`scanAnchorOrAliasIx` / `scanTagIx` which have explicit SK-preservation
lemmas in `IndexedScannerPlainScalarValid`. -/

/-- `scanNextTokenIx_dispatchContent` maintains `SimpleKeyAboveFloorIx`.
    Indexed twin of legacy `dispatchContent_maintains_SimpleKeyAboveFloor`
    (line 1641). -/
lemma scanNextTokenIx_dispatchContent_maintains_SKAFIx {input : String}
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchContent s c = .ok s')
    (n₀ fl₀ : Nat) (_h_n₀ : n₀ ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveFloorIx s n₀ fl₀) :
    SimpleKeyAboveFloorIx s' n₀ fl₀ := by
  -- Peel the 7-way content dispatch one `if` at a time with `by_cases`/`rw` (splitting the whole
  -- dispatch at once exceeds the internal simp step budget under Lean 4.31.0); anchor/alias/tag use
  -- the explicit `_preserves_simpleKey`/`_preserves_simpleKeyStack` lemmas, the scalar branches
  -- (block/quoted/plain) are cursor-only updates so SK / stack are preserved structurally (`rfl`).
  unfold scanNextTokenIx_dispatchContent at h
  by_cases hg1 : (c == '&') = true
  · -- '&' anchor
    rw [if_pos hg1] at h
    -- 4.32.0 already reduces the anchor bind; the `cases`/`rw` below is robust either way
    try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hA : scanAnchorOrAliasIx s true with
    | error e => rw [hA] at h; cases h
    | ok v =>
      rw [hA] at h
      simp only [Except.ok.injEq] at h; subst h
      exact SimpleKeyAboveFloorIx_of_preserved _ s n₀ fl₀
        (scanAnchorOrAliasIx_preserves_simpleKey s true v hA)
        (scanAnchorOrAliasIx_preserves_simpleKeyStack s true v hA) h_inv
  · rw [if_neg hg1] at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    by_cases hg2 : (c == '*') = true
    · -- '*' alias
      rw [if_pos hg2] at h
      cases hA : scanAnchorOrAliasIx s false with
      | error e => rw [hA] at h; cases h
      | ok v =>
        rw [hA] at h
        simp only [Except.ok.injEq] at h; subst h
        exact SimpleKeyAboveFloorIx_of_preserved _ s n₀ fl₀
          (scanAnchorOrAliasIx_preserves_simpleKey s false v hA)
          (scanAnchorOrAliasIx_preserves_simpleKeyStack s false v hA) h_inv
    · rw [if_neg hg2] at h
      by_cases hg3 : (c == '!') = true
      · -- '!' tag
        rw [if_pos hg3] at h
        cases hT : scanTagIx s with
        | error e => rw [hT] at h; cases h
        | ok v =>
          rw [hT] at h
          simp only [Except.ok.injEq] at h; subst h
          exact SimpleKeyAboveFloorIx_of_preserved _ s n₀ fl₀
            (scanTagIx_preserves_simpleKey s v hT)
            (scanTagIx_preserves_simpleKeyStack s v hT) h_inv
      · rw [if_neg hg3] at h
        by_cases hg4 : (c == '|' || c == '>') = true
        · -- block scalar
          rw [if_pos hg4] at h
          split at h
          · simp only [Except.ok.injEq] at h; subst h
            exact SimpleKeyAboveFloorIx_of_preserved _ s n₀ fl₀ rfl rfl h_inv
          · cases h
        · rw [if_neg hg4] at h
          by_cases hg5 : (c == '"') = true
          · -- double-quoted
            rw [if_pos hg5] at h
            split at h
            · simp only [Except.ok.injEq] at h; subst h
              exact SimpleKeyAboveFloorIx_of_preserved _ s n₀ fl₀ rfl rfl h_inv
            · cases h
          · rw [if_neg hg5] at h
            by_cases hg6 : (c == '\'') = true
            · -- single-quoted
              rw [if_pos hg6] at h
              split at h
              · simp only [Except.ok.injEq] at h; subst h
                exact SimpleKeyAboveFloorIx_of_preserved _ s n₀ fl₀ rfl rfl h_inv
              · cases h
            · rw [if_neg hg6] at h
              -- plain scalar (success) vs error: one small inner `if`
              split at h
              · simp only [Except.ok.injEq] at h; subst h
                exact SimpleKeyAboveFloorIx_of_preserved _ s n₀ fl₀ rfl rfl h_inv
              · cases h

/-! ### §2.4  `scanNextTokenIx` capstone

`scanNextTokenIx` maintains `SimpleKeyAboveFloorIx` given:
- (1) stack-flow sync (`simpleKeyStack.size ≥ flowLevel`);
- (2) `s'.flowLevel ≥ fl₀` (from `FlowMonoChainIx` continuation).

The proof chains preprocess maintenance → allowDirectives no-op → the
four sub-dispatchers' SKAF maintenance. -/

set_option maxHeartbeats 400000 in
/-- `scanNextTokenIx` maintains `SimpleKeyAboveFloorIx`. Indexed twin
    of legacy `scanNextToken_maintains_SimpleKeyAboveFloor` (line 1721). -/
lemma scanNextTokenIx_maintains_SKAFIx {input : String}
    (s s' : ScannerStateIx input)
    (h_next : scanNextTokenIx s = .ok (some s'))
    (n₀ fl₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveFloorIx s n₀ fl₀)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (h_fl_post : s'.flowLevel ≥ fl₀) :
    SimpleKeyAboveFloorIx s' n₀ fl₀ := by
  -- allowDirectives if-update preserves all SK / SKAF / sync /
  -- flowLevel / tokens.size relevant fields
  have h_allow_sk : ∀ st : ScannerStateIx input,
      (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKey = st.simpleKey := by intro st; split <;> rfl
  have h_allow_stack : ∀ st : ScannerStateIx input,
      (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKeyStack = st.simpleKeyStack := by intro st; split <;> rfl
  have h_allow_tok : ∀ st : ScannerStateIx input,
      (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).tokens = st.tokens := by intro st; split <;> rfl
  have h_allow_fl : ∀ st : ScannerStateIx input,
      (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).flowLevel = st.flowLevel := by intro st; split <;> rfl
  unfold scanNextTokenIx at h_next
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_next
  -- Split on preprocess outcome
  split at h_next
  · contradiction
  · split at h_next
    · simp [reduceCtorEq] at h_next
    · -- preprocess returned ok (some (s1, c1))
      rename_i s1 c1 hPre
      have h_pre_inv := scanNextTokenIx_preprocess_maintains_SKAFIx s _ _ hPre
        n₀ fl₀ h_n₀ h_inv
      have h_pre_mono := scanNextTokenIx_preprocess_tokens_size_le s _ _ hPre
      have h_pre_stack := scanNextTokenIx_preprocess_preserves_simpleKeyStack s _ _ hPre
      have h_pre_fl := scanNextTokenIx_preprocess_preserves_flowLevel s _ _ hPre
      have h_pre_sync : s1.simpleKeyStack.size ≥ s1.flowLevel := by
        rw [h_pre_stack, h_pre_fl]; exact h_sync
      have h_pre_n₀ : n₀ ≤ s1.tokens.size := by omega
      -- Split on dispatchStructural outcome
      split at h_next
      · contradiction
      · split at h_next
        · -- Structural dispatch produced some s''
          rename_i s'' hStruct
          simp only [Except.ok.injEq, Option.some.injEq] at h_next
          subst h_next
          exact scanNextTokenIx_dispatchStructural_maintains_SKAFIx _ _ _ hStruct
            n₀ fl₀ h_pre_n₀ h_pre_inv
        · -- Structural returned none → continue
          rename_i hStructNone
          have h_s2_inv : SimpleKeyAboveFloorIx
              (if s1.allowDirectives then
                  { s1 with allowDirectives := false, documentEverStarted := true }
                else s1) n₀ fl₀ :=
            SimpleKeyAboveFloorIx_of_preserved _ s1 n₀ fl₀
              (h_allow_sk s1) (h_allow_stack s1) h_pre_inv
          have h_s2_sync :
              (if s1.allowDirectives then
                  { s1 with allowDirectives := false, documentEverStarted := true }
                else s1).simpleKeyStack.size ≥
                (if s1.allowDirectives then
                    { s1 with allowDirectives := false, documentEverStarted := true }
                  else s1).flowLevel := by
            rw [h_allow_stack, h_allow_fl]; exact h_pre_sync
          have h_s2_tok : n₀ ≤
              (if s1.allowDirectives then
                  { s1 with allowDirectives := false, documentEverStarted := true }
                else s1).tokens.size := by
            rw [h_allow_tok]; omega
          -- Split on checkNoPendingDirectives (Fix B)
          split at h_next
          · contradiction
          · -- Split on checkBlockFlowIndent
            split at h_next
            · contradiction
            · split at h_next
              · contradiction
              · split at h_next
                · -- FlowIndicators dispatch produced some s''
                  rename_i s'' hFlow
                  simp only [Except.ok.injEq, Option.some.injEq] at h_next
                  subst h_next
                  exact scanNextTokenIx_dispatchFlowIndicators_maintains_SKAFIx _ _ _ hFlow
                    n₀ fl₀ h_s2_tok h_s2_inv h_s2_sync h_fl_post
                · -- FlowIndicators returned none → BlockIndicators
                  rename_i hFlowNone
                  split at h_next
                  · contradiction
                  · split at h_next
                    · -- BlockIndicators dispatch produced some s''
                      rename_i s'' hBlock
                      simp only [Except.ok.injEq, Option.some.injEq] at h_next
                      subst h_next
                      exact scanNextTokenIx_dispatchBlockIndicators_maintains_SKAFIx _ _ _ hBlock
                        n₀ fl₀ h_s2_tok h_s2_inv
                    · -- BlockIndicators returned none → Content
                      rename_i hBlockNone
                      split at h_next
                      · contradiction
                      · rename_i sC hContent
                        simp only [Except.ok.injEq, Option.some.injEq] at h_next
                        subst h_next
                        exact scanNextTokenIx_dispatchContent_maintains_SKAFIx _ _ _ hContent
                          n₀ fl₀ h_s2_tok h_s2_inv

/-! ## Fix-B pending-directives check helpers (indexed twins of
`scanNextToken_checkNoPendingDirectives_ok` / `scanNextToken_ok_directivesPresent_false`). -/

/-- The Fix-B pending-directives check passes when no directives are pending.
    Stated as an atomic rewrite so `simp` does not rewrite `directivesPresent`
    projections inside record-update expressions elsewhere in the goal. -/
lemma scanNextTokenIx_checkNoPendingDirectives_ok {input : String}
    (s : ScannerStateIx input) (h : s.directivesPresent = false) :
    scanNextTokenIx_checkNoPendingDirectives s = .ok () := by
  simp only [scanNextTokenIx_checkNoPendingDirectives, h, Bool.false_eq_true, ↓reduceIte]

/-- Converse dp extraction (Fix B): if `scanNextTokenIx` succeeded and the
    pipeline reached past structural dispatch, the pending-directives check
    must have passed, so `s_pp.directivesPresent = false`. -/
lemma scanNextTokenIx_ok_directivesPresent_false {input : String}
    {s s_pp : ScannerStateIx input} {c : Char} {r : Option (ScannerStateIx input)}
    (h_pp : scanNextTokenIx_preprocess s = .ok (some (s_pp, c)))
    (h_struct : scanNextTokenIx_dispatchStructural s_pp c = .ok none)
    (h_snt : scanNextTokenIx s = .ok r) :
    s_pp.directivesPresent = false := by
  cases h_dp : s_pp.directivesPresent
  · rfl
  · exfalso
    have h_check_err : scanNextTokenIx_checkNoPendingDirectives s_pp
        = .error (.directiveWithoutDocument s_pp.cursor.pos.line) := by
      simp only [scanNextTokenIx_checkNoPendingDirectives, h_dp, ↓reduceIte]
    have h_err : scanNextTokenIx s
        = .error (.directiveWithoutDocument s_pp.cursor.pos.line) := by
      unfold scanNextTokenIx
      simp only [bind, Except.bind, h_pp, h_struct, h_check_err]
    rw [h_err] at h_snt
    injection h_snt

end L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
