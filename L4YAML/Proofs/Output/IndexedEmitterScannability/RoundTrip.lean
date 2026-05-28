/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.ParseStream

/-! # `IndexedEmitterScannability.RoundTrip` — Phase 3 Step 6f.3b3.roundtrip.fidelity

**Status**: §5.1 (compose invariance for scalars) + §5.4.G prefix-and-tokens
infrastructure landed. Indexed twins of legacy `EmitterScannability.lean`
lines 8490–8530 (§5.1) and 8875–8968 (§5.4.G prefix/tokens fragment).

## Scope (mapping to legacy `EmitterScannability.lean`)

  - **§5.1  Compose invariance for scalars** (legacy lines 8490–8530):
    `resolveAliases_scalarIx`, `stripAnchors_scalarIx`,
    `compose_scalar_contentIx`, `contentEq_scalar_contentIx`,
    `contentEq_scalar_composeIx`. **Value-level** — these lemmas
    operate on `YamlValue`, `Scalar`, `YamlDocument` and don't
    depend on the indexed scanner state; they port verbatim.

  - **§5.4.G  Filtered-tokens / prefix-preservation tracking** (legacy
    lines 8875–8967): `unwindIndents_noop_short_stackIx`,
    `scanFiltered_tokens_eq_of_chain_short_stackIx`,
    `ScanChainIx_tokens_mono`, `scanNextTokenIx_prefix_and_sk_inv`,
    `ScanChainIx_preserves_raw_prefix`. **Indexed-substrate**.
    These bridge `scanFilteredIx_of_chain_eq` (FlowMonoChain §5
    Invariant) into the emitter-state setting where the indent
    stack is at most a singleton sentinel.

Subsequent sub-steps populate §5.4.G's filtered-token tracking
(`filterinfra`), the main filtered-growth theorem (`maintheorem`),
and the universal round-trip capstone (`universal`).

## Phase 3 Step 6f cutover

See `Basic.lean` for the directory-wide cutover plan. Note that
**this file inherits the 7 pre-existing `sorry` warnings** carried
forward from the legacy file; whether to discharge them on the
indexed substrate or preserve carry-forward is decided per-`sorry`
at port time in the `maintheorem`/`universal` sub-sessions.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.RoundTrip

open L4YAML
open L4YAML.Grammar
open L4YAML.Indexed
open L4YAML.Emit
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.TokenParser.Indexed
open L4YAML.Proofs.Indexed.EmitterScannability.EmitScans
open L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
open L4YAML.Proofs.Indexed.EmitterScannability.ScanChain
open L4YAML.Proofs.Indexed.Composition
open L4YAML.Proofs.Indexed.Grammable
open L4YAML.Proofs.Indexed.ScannerCorrectness

/-! ## §5  Content Fidelity Infrastructure

Helper lemmas for the content fidelity proof (`emit_roundtrip_content_eqIx`).
-/

/-! ### §5.1  Compose invariance for scalars

`YamlDocument.compose` applies `resolveAliases` and `stripAnchors`.
For scalars, `resolveAliases` is identity and `stripAnchors` only
clears the anchor field. Since `contentEq` ignores anchors, compose
doesn't affect content equivalence for scalars.

These are **value-level** facts and port verbatim from legacy
(lines 8503–8529). They don't depend on the indexed substrate. -/

/-- `resolveAliases` is identity on scalars. -/
theorem resolveAliases_scalarIx (s : Scalar)
    (anchors : Array (String × YamlValue)) :
    (YamlValue.scalar s).resolveAliases anchors = .scalar s := by
  unfold YamlValue.resolveAliases; rfl

/-- `stripAnchors` on a scalar just clears the anchor field. -/
theorem stripAnchors_scalarIx (s : Scalar) :
    (YamlValue.scalar s).stripAnchors = .scalar { s with anchor := none } := by
  unfold YamlValue.stripAnchors; rfl

/-- `compose` on a scalar document preserves the content field. -/
theorem compose_scalar_contentIx (doc : YamlDocument) (s : Scalar)
    (h_val : doc.value = .scalar s) :
    (doc.compose).value = .scalar { s with anchor := none } := by
  unfold YamlDocument.compose; dsimp only []
  rw [h_val, resolveAliases_scalarIx, stripAnchors_scalarIx]

/-- `contentEq` for scalars only depends on the content string. -/
theorem contentEq_scalar_contentIx (s₁ s₂ : Scalar)
    (h : s₁.content = s₂.content) : contentEq (.scalar s₁) (.scalar s₂) = true := by
  unfold contentEq; simp [h]

/-- `contentEq` through compose for scalars: original vs composed. -/
theorem contentEq_scalar_composeIx (s_orig : Scalar) (s_parsed : Scalar)
    (h_content : s_orig.content = s_parsed.content) :
    contentEq (.scalar s_orig) (.scalar { s_parsed with anchor := none }) = true :=
  contentEq_scalar_contentIx s_orig { s_parsed with anchor := none } h_content

/-! ### §5.4.G  Infrastructure for filtered token tracking (indexed)

The legacy `EmitterScannability.lean` §5.4.G groups five infrastructure
lemmas that bridge `scanFiltered_of_chain_eq` (the FlowMonoChain
Invariant §5 export) into the emitter-state setting. The indexed
substrate has matching predicates and primitives:

  - `unwindIndentsIx_tokens_size_le` (Dispatch §1.7) — ≤-monotone,
    parallel to legacy `unwindIndents_adds_tokens`.
  - `unwindIndentsIx_preserves_prefix` (Production
    `IndexedScannerPlainScalarValid` §3) — token-index preservation.
  - `scanNextTokenIx_tokens_size_le` (Dispatch §6) — single-step
    monotone, parallel to legacy `scanNextToken_adds_tokens`.
  - `SimpleKeyAboveIx` + `scanNextTokenIx_preserves_prefix` +
    `scanNextTokenIx_maintains_SimpleKeyAboveIx` (StreamStart §2.1).
  - `scanFilteredIx_of_chain_eq` (FlowMonoChain Sync Invariant §5).

The five lemmas below repackage these primitives in the shape
the round-trip cluster's downstream consumers expect. -/

/-- `unwindIndentsIx` is identity when the indent stack has at most
    one entry. This covers emitter output where `indents = #[]` (the
    default from `ScannerStateIx.mk'`). `unwindIndentsLoopIx` checks
    `s.indents.size > 1` before unwinding; with size ≤ 1, the
    condition fails immediately and the state is returned unchanged.

    **Verbatim port** from legacy `unwindIndents_noop_short_stack`
    (line 8881) — the proof structure is identical because
    `unwindIndentsIx` shares the legacy's `match`/`if` skeleton. -/
theorem unwindIndents_noop_short_stackIx {input : String}
    (s : ScannerStateIx input) (h_stack : s.indents.size ≤ 1) :
    unwindIndentsIx s (-1) = s := by
  unfold unwindIndentsIx
  unfold unwindIndentsLoopIx
  split
  · -- fuel = 0 case (s.indents.size = 0): match returns s directly.
    rfl
  · -- fuel = fuel' + 1 case (s.indents.size ≥ 1): the if-condition
    -- `s.currentIndent > -1 && s.indents.size > 1` must be false.
    split
    · -- if-then branch: requires `s.indents.size > 1`, contradicting
      -- `h_stack : s.indents.size ≤ 1`.
      exfalso
      rename_i h_cond
      simp only [Bool.and_eq_true, decide_eq_true_iff] at h_cond
      omega
    · rfl

/-- When a `ScanChainIx` starts from `s₀ = (mk' input).emit streamStart`
    via `scanFilteredIx`, the token-array equation simplifies to the
    direct `s_final.emit streamEnd` form provided the final indent stack
    is at most a singleton. Combines `scanFilteredIx_of_chain_eq` (the
    FlowMonoChain Sync Invariant §5 export) with `unwindIndents_noop_
    short_stackIx`. -/
theorem scanFiltered_tokens_eq_of_chain_short_stackIx
    (input : String) (s₀ s_final : ScannerStateIx input) (n : Nat)
    (h_s0 : s₀ = (ScannerStateIx.mk' input).emit YamlToken.streamStart)
    (h_no_bom : (ScannerStateIx.mk' input).peek? ≠ some '﻿')
    (h_chain : ScanChainIx s₀ n s_final)
    (h_eof : scanNextTokenIx s_final = .ok none)
    (h_fl : s_final.flowLevel = 0)
    (h_dp : s_final.directivesPresent = false)
    (h_fuel : n + 1 ≤ (input.utf8ByteSize + 1) * 4)
    (h_stack : s_final.indents.size ≤ 1) :
    scanFilteredIx input = .ok ⟨((s_final.emit YamlToken.streamEnd).tokens.tokens.filter
      (fun t => t.token != YamlToken.placeholder))⟩ := by
  have h_eq := scanFilteredIx_of_chain_eq input s₀ s_final n h_s0 h_no_bom h_chain
    h_eof h_fl h_dp h_fuel
  rwa [unwindIndents_noop_short_stackIx s_final h_stack] at h_eq

/-- `ScanChainIx` token-stream monotonicity: the token array grows
    (non-strictly) through any scan chain. Inducts on the chain,
    discharging each step with `scanNextTokenIx_tokens_size_le`. -/
theorem ScanChainIx_tokens_mono {input : String} {s s' : ScannerStateIx input}
    {n : Nat} (h_chain : ScanChainIx s n s') : s'.tokens.size ≥ s.tokens.size := by
  induction h_chain with
  | zero => exact Nat.le_refl _
  | step h_snt _h_rest ih =>
    exact Nat.le_trans (scanNextTokenIx_tokens_size_le h_snt) ih

/-- Combined per-step prefix preservation and simpleKey-invariant
    maintenance. Bundles `scanNextTokenIx_preserves_prefix` (extracting
    the equality from its existential conclusion) with
    `scanNextTokenIx_maintains_SimpleKeyAboveIx` so consumers can pull
    both facts from a single chain step.

    **Precondition shape**: `SimpleKeyAboveIx s n` says all active
    simple keys (current + stacked) have token indices ≥ `n`, which
    keeps simple-key placeholder writes from clobbering the
    prefix. **Conclusion shape**: returns the direct equality
    `s'.tokens[i] = s.tokens[i]` (the implicit size bound is computed
    from `scanNextTokenIx_tokens_size_le`) plus `SimpleKeyAboveIx s' n`,
    enabling straightforward induction in
    `ScanChainIx_preserves_raw_prefix`. -/
theorem scanNextTokenIx_prefix_and_sk_inv {input : String}
    (s s' : ScannerStateIx input)
    (h_next : scanNextTokenIx s = .ok (some s'))
    (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveIx s n) :
    (∀ (i : Nat) (hi : i < n),
      s'.tokens[i]'(by
        have := scanNextTokenIx_tokens_size_le h_next; omega) =
      s.tokens[i]'(by omega)) ∧
    SimpleKeyAboveIx s' n := by
  refine ⟨?_, scanNextTokenIx_maintains_SimpleKeyAboveIx s s' n h_n h_inv h_next⟩
  intro i hi
  obtain ⟨_, h_eq⟩ := scanNextTokenIx_preserves_prefix s s' n h_n h_inv h_next i hi
  exact h_eq

/-- Through a `ScanChainIx` of `k` steps, all raw token positions below
    `n₀` are preserved, provided `n₀ ≤ s.tokens.size` and
    `SimpleKeyAboveIx s n₀` holds. The `SimpleKeyAboveIx` invariant is
    maintained through each step by `scanNextTokenIx_prefix_and_sk_inv`,
    making the induction straightforward. -/
theorem ScanChainIx_preserves_raw_prefix {input : String}
    {s s' : ScannerStateIx input} {k : Nat}
    (h_chain : ScanChainIx s k s')
    (n₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveIx s n₀)
    (i : Nat) (hi : i < n₀) :
    s'.tokens[i]'(by have := ScanChainIx_tokens_mono h_chain; omega) =
    s.tokens[i]'(by omega) := by
  induction h_chain with
  | zero => rfl
  | step h_snt _h_rest ih =>
    rename_i s_mid s'_inner n
    have h_adds := scanNextTokenIx_tokens_size_le h_snt
    have ⟨h_pres, h_inv'⟩ := scanNextTokenIx_prefix_and_sk_inv _ _ h_snt n₀ h_n₀ h_inv
    exact (ih (Nat.le_trans h_n₀ h_adds) h_inv').trans (h_pres i hi)

end L4YAML.Proofs.Indexed.EmitterScannability.RoundTrip
