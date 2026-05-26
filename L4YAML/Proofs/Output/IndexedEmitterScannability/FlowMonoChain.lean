/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.ScanChain

/-! # `IndexedEmitterScannability.FlowMonoChain` — Phase 3 Step 6f.3b3 staging

**Status**: partially populated. §1 (`FlowMonoChainIx` inductive +
immediate helpers — landed 2026-05-25, sub-session
`.flowmono.inductive`) ports the legacy `FlowMonoChain` core (lines
1304–1387 of `Proofs/Output/EmitterScannability.lean`). §2 onwards
(`SimpleKeyAboveFloor`, prefix preservation) remain to be ported in
the subsequent `.flowmono.{skaf, preserve, maintenance, sync}`
sub-sessions.

## Scope (mapping to legacy `EmitterScannability.lean`)

  - **§1 `FlowMonoChainIx` inductive + immediate helpers** (legacy
    lines 1304–1387, ~70 LOC, **landed**). `FlowMonoChainIx fl₀ s n s'`
    (a `ScanChainIx` where every intermediate state has
    `flowLevel ≥ fl₀`), `.toScanChainIx`, `.flowLevel_ge_start` /
    `_end`, `.single`, `.trans`, `.weaken`, `.tokens_mono`.

  - **§2 `SimpleKeyAboveFloor` predicate + maintenance** (legacy lines
    1388–1805, ~420 LOC). Flow-level-aware simple-key invariant.
    Constructors (`SimpleKeyAboveFloor_of_cleared_preserved`,
    `_of_preserved`, `_of_endLine_update`, `_of_flow_open`,
    `_of_flow_close`); preprocess + dispatch maintenance
    (`preprocess_preserves_flowLevel`, `preprocess_maintains_SKAF`,
    `dispatchStructural_maintains_SKAF`,
    `dispatchFlowIndicators_maintains_SKAF`,
    `dispatchBlockIndicators_maintains_SKAF`,
    `dispatchContent_maintains_SKAF`); `scanNextToken_maintains_SKAF`.

  - **§3 FlowMonoChain prefix preservation** (legacy lines 1806–5586,
    ~3780 LOC — the *single biggest section* of the legacy file).
    Per-stage `_preserves_dp`, `_preserves_indents`, sync proofs,
    Step-4 prefix preservation: `scanNextToken_preserves_prefix_of_SKAF`,
    `scanNextToken_prefix_and_SKAF_inv`,
    `dispatchFlowIndicators_preserves_sync`,
    `scanNextToken_preserves_sync`,
    `FlowMonoChain_preserves_raw_prefix`, `scanFiltered_of_chain`,
    `scanFiltered_of_chain_eq`, etc.

## Why this sub-file is the largest

The flow-monotonic-chain machinery is the proof framework's most
complex single concern: it tracks scanner state through arbitrarily
long sequences of `scanNextTokenIx` calls while preserving multiple
simultaneous invariants (flow level, simple-key stack floor,
emitted-token prefix, indent stack, dispatch-presence). Splitting it
further would fragment a cohesive proof skeleton (each preservation
lemma chains into the next via shared invariant accumulators), but
the indexed port may sub-divide once the structure is concrete —
e.g. `FlowMonoChain/Preserve.lean` (~1500 LOC),
`FlowMonoChain/Maintenance.lean` (~1100 LOC),
`FlowMonoChain/Sync.lean` (~1200 LOC).

## Phase 3 Step 6f cutover

See `Basic.lean` for the directory-wide cutover plan.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain

open L4YAML
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.EmitterScannability.ScanChain

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
theorem FlowMonoChainIx.toScanChainIx {fl₀ : Nat}
    {s s' : ScannerStateIx input} {n : Nat}
    (h : FlowMonoChainIx fl₀ s n s') : ScanChainIx s n s' := by
  induction h with
  | zero => exact .zero
  | step _ h_snt _h_rest ih => exact .step h_snt ih

/-! ### §1.2  Flow-level endpoint bounds -/

/-- The start state of a `FlowMonoChainIx` has `flowLevel ≥ fl₀`.
    Indexed twin of legacy `FlowMonoChain.flowLevel_ge_start`
    (line 1336). -/
theorem FlowMonoChainIx.flowLevel_ge_start {fl₀ : Nat}
    {s s' : ScannerStateIx input} {n : Nat}
    (h : FlowMonoChainIx fl₀ s n s') : s.flowLevel ≥ fl₀ := by
  cases h with
  | zero h_fl => exact h_fl
  | step h_fl _ _ => exact h_fl

/-- The end state of a `FlowMonoChainIx` has `flowLevel ≥ fl₀`.
    Indexed twin of legacy `FlowMonoChain.flowLevel_ge_end`
    (line 1343). -/
theorem FlowMonoChainIx.flowLevel_ge_end {fl₀ : Nat}
    {s s' : ScannerStateIx input} {n : Nat}
    (h : FlowMonoChainIx fl₀ s n s') : s'.flowLevel ≥ fl₀ := by
  induction h with
  | zero h_fl => exact h_fl
  | step _ _ _ ih => exact ih

/-! ### §1.3  Combinators (`.single`, `.trans`) -/

/-- A single `scanNextTokenIx` step as a `FlowMonoChainIx`. Indexed
    twin of legacy `FlowMonoChain.single` (line 1350). -/
theorem FlowMonoChainIx.single {fl₀ : Nat} {s s' : ScannerStateIx input}
    (h_snt : scanNextTokenIx s = .ok (some s'))
    (h_fl : s.flowLevel ≥ fl₀)
    (h_fl' : s'.flowLevel ≥ fl₀) :
    FlowMonoChainIx fl₀ s 1 s' :=
  .step h_fl h_snt (.zero h_fl')

/-- Transitivity: concatenate two `FlowMonoChainIx`s with the same
    floor. Indexed twin of legacy `FlowMonoChain.trans` (line 1358). -/
theorem FlowMonoChainIx.trans {fl₀ : Nat}
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
theorem FlowMonoChainIx.weaken {fl₀ fl₁ : Nat}
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
theorem FlowMonoChainIx.tokens_mono {fl₀ : Nat}
    {s s' : ScannerStateIx input} {n : Nat}
    (h : FlowMonoChainIx fl₀ s n s') : s'.tokens.size ≥ s.tokens.size := by
  induction h with
  | zero => omega
  | step _ h_snt _ ih =>
    have := scanNextTokenIx_tokens_size_le h_snt; omega

end L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
