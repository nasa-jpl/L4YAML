/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FilteredGrowth

/-! # `IndexedEmitterScannability.EmitScans` — Phase 3 Step 6f.3b3 staging

**Status**: staging file. Populated incrementally as the
`ScanChainGrewIx` strict-variant track + the `EmitScansInFlowIx` main
theorem family are ported to the indexed substrate.

  - ✅ **`ScanChainGrewIx` (strict-variant track)** — landed
    (Step `6f.3b3.emitscans.chaingrew`, see §1 below).
  - ✅ **`EmitScansInFlowIx`/`EmitListScansInFlowIx` predicates + light
    helpers** — landed (Step `6f.3b3.emitscans.flowvalue` sub-session 1,
    see §2 below): `emitList_scans_emptyIx`, `emitPairList_first_charIx`,
    `isValueCandidate_of_peekAt_blankIx`.
  - ⏳ Per-value-form bodies (`.flowvalue` sub-session 2):
    `emitList_scans_nonemptyIx`, `scanNextToken_flow_valueIx` (+ the
    missing twin `scanNextTokenIx_preprocess_flow_ws1`).
  - ⏳ `EmitPairListScansInFlowIx` + `emit_scans_in_flowIx`.
  - ⏳ `emit_produces_valid_yamlIx` top-level composition.

## Scope (mapping to legacy `EmitterScannability.lean`)

  - **`ScanChainGrew` inductive (strict-variant track)** (legacy lines
    6909–7002, ~95 LOC). `ScanChainGrewIx p s n s'` (a `ScanChainIx`
    plus a witness that *at least one* `p`-satisfying token was added).
    Helpers: `.toScanChainIx`, `.single`, `.trans`,
    `ScanChainGrewIx_filtered_grows`, `ScanChainGrewIx_of_scanNextTokenIx_eq`.

  - **`EmitScansInFlow` predicate + per-value-form lemmas** (legacy
    lines 7003–7625, ~623 LOC). The main predicate
    `EmitScansInFlow v`: scanning `emit v` (inside a flow context)
    produces a non-empty `ScanChainGrew`. Body lemmas:
    `emit_list_scans_in_flow` family — `emitList_scans_empty`,
    `emitList_scans_nonempty`, `emitPairList_first_char`,
    `isValueCandidate_of_peekAt_blank`,
    `scanNextToken_flow_value` (the dispatcher's flow-value entry
    point).

  - **`EmitPairListScansInFlow` + main proof** (legacy lines
    7626–8013, ~388 LOC). The dual predicate for key-value pair
    lists; `emitPairList_scans_empty`, `emitPairList_scans_nonempty`,
    and the main theorem `emit_scans_in_flow` (induction over
    `Grammable v inFlow`).

  - **`emit_produces_valid_yaml`** (legacy lines 8281–8399, ~120 LOC).
    Top-level composition: `scanFiltered (emit v)` succeeds and
    produces a valid token stream.

This sub-file is the heart of the emitter-scannability proof — it
shows that the canonical emitter's output is exactly what the
scanner accepts.

## Phase 3 Step 6f cutover

See `Basic.lean` for the directory-wide cutover plan.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.EmitScans

open L4YAML
open L4YAML.CharPredicates
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.EmitterScannability.ScanChain
open L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
open L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth

variable {input : String}

/-! ## §1  Strict-variant track: `ScanChainGrewIx`

`ScanChainGrewIx p` is `ScanChainIx` augmented with a per-step witness
that the filtered count under predicate `p` strictly increases at each
step. Built constructively at the call site, it sidesteps the loose
`scanNextTokenIx_filtered_grows` family (the legacy `scanNextToken`
variant carries a sorry on the RESERVED directive branch — see Turn 1's
`scanDirective_filtered_grows` for the honest precondition; the indexed
in-flow corollary `scanNextTokenIx_filtered_grows_in_flow` is sorry-free
because `dispatchStructural_none_flow` rules that branch out).

Existing `ScanChainIx` / its filtered-growth bound are unchanged; this
predicate runs alongside them. The forgetful `.toScanChainIx` lets a
strict chain be passed wherever a `ScanChainIx` was expected.

Indexed twin of legacy `ScanChainGrew` (lines 6909–7002 of
`Proofs/Output/EmitterScannability.lean`). The only delta from legacy is
the substrate bridge: the predicate ranges over `IxToken input` and the
filtered count is `(_.tokens.tokens.filter p).size` (`TokenStream` wraps
`Array (IxToken input)`); `input` is type-level. The proofs transfer
verbatim. -/

/-- `ScanChainGrewIx p s n s'` means `n` successive `scanNextTokenIx`
    steps from `s` reach `s'`, and at each step the filtered token count
    under `p` strictly increases. Indexed twin of `ScanChainGrew`. -/
inductive ScanChainGrewIx (p : IxToken input → Bool) :
    ScannerStateIx input → Nat → ScannerStateIx input → Prop where
  | zero {s : ScannerStateIx input} : ScanChainGrewIx p s 0 s
  | step {s s_mid s' : ScannerStateIx input} {n : Nat} :
         scanNextTokenIx s = .ok (some s_mid) →
         (s_mid.tokens.tokens.filter p).size > (s.tokens.tokens.filter p).size →
         ScanChainGrewIx p s_mid n s' →
         ScanChainGrewIx p s (n + 1) s'

/-- Forgetful map: a `ScanChainGrewIx` is, in particular, a `ScanChainIx`.
    Mirrors legacy `ScanChainGrew.toScanChain`. -/
theorem ScanChainGrewIx.toScanChainIx {p : IxToken input → Bool}
    {s s' : ScannerStateIx input} {n : Nat}
    (h : ScanChainGrewIx p s n s') : ScanChainIx s n s' := by
  induction h with
  | zero => exact .zero
  | step h_snt _h_grew _h_rest ih => exact .step h_snt ih

/-- Single-step constructor for `ScanChainGrewIx`. Mirrors legacy
    `ScanChainGrew.single`. -/
theorem ScanChainGrewIx.single {p : IxToken input → Bool}
    {s s' : ScannerStateIx input}
    (h : scanNextTokenIx s = .ok (some s'))
    (h_grew : (s'.tokens.tokens.filter p).size > (s.tokens.tokens.filter p).size) :
    ScanChainGrewIx p s 1 s' :=
  .step h h_grew .zero

/-- Transitivity for `ScanChainGrewIx`: concatenate two strict chains.
    Mirrors legacy `ScanChainGrew.trans`. -/
theorem ScanChainGrewIx.trans {p : IxToken input → Bool}
    {s₁ s₂ s₃ : ScannerStateIx input} {n₁ n₂ : Nat}
    (h1 : ScanChainGrewIx p s₁ n₁ s₂) (h2 : ScanChainGrewIx p s₂ n₂ s₃) :
    ScanChainGrewIx p s₁ (n₁ + n₂) s₃ := by
  induction h1 with
  | zero => simpa using h2
  | @step s s_mid s₂ k h_snt h_grew _h_rest ih =>
    have h_ih := ih h2
    have hk : k + 1 + n₂ = (k + n₂) + 1 := by omega
    rw [hk]
    exact .step h_snt h_grew h_ih

/-- Strict-chain growth: through a `ScanChainGrewIx p` of `n` steps, the
    filtered token array grows by at least `n`. Same conclusion as the
    plain `ScanChainIx` filtered-growth bound, but proven directly from
    the per-step witness — does not depend on a loose
    `scanNextTokenIx_filtered_grows` (and so does not depend on any
    sorry). Mirrors legacy `ScanChainGrew_filtered_grows`. -/
theorem ScanChainGrewIx_filtered_grows {p : IxToken input → Bool}
    {s s' : ScannerStateIx input} {n : Nat}
    (h_chain : ScanChainGrewIx p s n s') :
    (s'.tokens.tokens.filter p).size ≥ (s.tokens.tokens.filter p).size + n := by
  induction h_chain with
  | zero => omega
  | step _h_snt h_grew _h_rest ih => omega

/-- Lift a `ScanChainGrewIx` through a `scanNextTokenIx` equality. Used
    when `s₂` is derived from `s₁` by preprocessing whitespace (which
    preserves the dispatch result and is monotone on filtered token
    count via `preprocess_filtered_monoIx`). The chain must be non-empty
    (length ≥ 1) so the first step's witness can be transitively weakened
    from `s₂.tokens.filter` down to `s₁.tokens.filter`. Mirrors legacy
    `ScanChainGrew_of_scanNextToken_eq`. -/
theorem ScanChainGrewIx_of_scanNextTokenIx_eq {p : IxToken input → Bool}
    {s₁ s₂ s' : ScannerStateIx input} {n : Nat}
    (h_eq : scanNextTokenIx s₁ = scanNextTokenIx s₂)
    (h_le : (s₁.tokens.tokens.filter p).size ≤ (s₂.tokens.tokens.filter p).size)
    (h_chain : ScanChainGrewIx p s₂ (n + 1) s') :
    ScanChainGrewIx p s₁ (n + 1) s' := by
  cases h_chain with
  | step h_snt h_grew h_rest =>
    refine .step (by rw [h_eq]; exact h_snt) ?_ h_rest
    omega

/-! ## §2  In-flow emit-scannability predicates + light helpers

Step `6f.3b3.emitscans.flowvalue`, **sub-session 1** (predicate + light
helpers). Ports the predicate layer and three small helpers; the two
heavy per-value-form bodies (`emitList_scans_nonemptyIx`,
`scanNextToken_flow_valueIx`) and the one missing supporting twin
(`scanNextTokenIx_preprocess_flow_ws1`) land in sub-session 2.

Indexed twin of legacy `Proofs/Output/EmitterScannability.lean`
lines 7003–7254. Substrate bridge: `ScannerState` → `ScannerStateIx input`;
`s.col`/`s.line` → `s.cursor.pos.col`/`s.cursor.pos.line`;
`ScannerSurfCorr` → `ScannerSurfCorrIx`; `AllTokensOnLine`/`EndLineOnLine`
→ `…Ix`; `ScanChainGrew`/`FlowMonoChain` → `…Ix`; the token predicate's
`t.val` → `t.token`; `lastRealTokenVal?` → `lastRealTokenValIx?`;
`isValueCandidate` → `isValueCandidateIx`. -/

/-- `EmitScansInFlowIx v`: scanning `emit v` inside a flow context (from a
    state surface-corresponding to `(emit v).toList ++ rest`) produces a
    non-empty `ScanChainGrewIx`, preserves the flow invariants, and leaves
    the cursor at `rest`. Indexed twin of legacy `EmitScansInFlow`
    (lines 7003–7029); note the two conjuncts absent from
    `EmitListScansInFlowIx`: `simpleKeyAllowed = false` and the
    `lastRealTokenValIx?` non-flow-opener clause. -/
def EmitScansInFlowIx (v : YamlValue) : Prop :=
  ∀ (s : ScannerStateIx input) (rest : List Char),
    ScannerSurfCorrIx s ⟨(L4YAML.Emit.emit v).toList ++ rest, s.cursor.pos.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.cursor.pos.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLineIx s s.cursor.pos.line →
    EndLineOnLineIx s →
    ∃ n s', ScanChainGrewIx (fun t => t.token != .placeholder) s n s'
      ∧ ScannerSurfCorrIx s' ⟨rest, s'.cursor.pos.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.cursor.pos.col > 0
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.cursor.pos.line = s.cursor.pos.line
      ∧ s'.simpleKeyAllowed = false
      ∧ (∀ t, lastRealTokenValIx? s'.tokens = some t →
          t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
      ∧ AllTokensOnLineIx s' s'.cursor.pos.line
      ∧ EndLineOnLineIx s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ FlowMonoChainIx s.flowLevel s n s'

/-- `EmitListScansInFlowIx items`: scanning the comma-separated `emitList`
    output (the body between `[` and `]` in a flow sequence) succeeds in
    flow context, preserving invariants. Indexed twin of legacy
    `EmitListScansInFlow` (lines 7031–7057). -/
def EmitListScansInFlowIx (items : List YamlValue) : Prop :=
  ∀ (s : ScannerStateIx input) (rest : List Char),
    ScannerSurfCorrIx s ⟨(L4YAML.Emit.emit.emitList items).toList ++ rest, s.cursor.pos.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.cursor.pos.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLineIx s s.cursor.pos.line →
    EndLineOnLineIx s →
    ∃ n s', ScanChainGrewIx (fun t => t.token != .placeholder) s n s'
      ∧ ScannerSurfCorrIx s' ⟨rest, s'.cursor.pos.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.cursor.pos.col > 0
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.cursor.pos.line = s.cursor.pos.line
      ∧ AllTokensOnLineIx s' s'.cursor.pos.line
      ∧ EndLineOnLineIx s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ FlowMonoChainIx s.flowLevel s n s'

/-- Empty list body is trivially scanned (0-step chain). Indexed twin of
    legacy `emitList_scans_empty` (lines 7059–7066). -/
theorem emitList_scans_emptyIx : EmitListScansInFlowIx (input := input) [] := by
  intro s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
  have h_eq : (L4YAML.Emit.emit.emitList ([] : List YamlValue)).toList ++ rest = rest := by
    simp only [L4YAML.Emit.emit.emitList]; rfl
  rw [h_eq] at hcorr
  exact ⟨0, s, .zero, hcorr, rfl, rfl, rfl, rfl, h_col, h_flow, h_indent, rfl,
         h_atol, h_endline, rfl, .zero (Nat.le_refl _)⟩

/-- The first char of `emitPairList (p :: ps)` is the first char of the key
    `emit p.1` — a non-whitespace, non-`#` content char. Indexed twin of
    legacy `emitPairList_first_char` (lines 7211–7229). -/
theorem emitPairList_first_charIx (p : YamlValue × YamlValue)
    (ps : List (YamlValue × YamlValue)) :
    ∃ c rest', (L4YAML.Emit.emit.emitPairList (p :: ps)).toList = c :: rest' ∧
      isWhiteSpaceBool c = false ∧ isLineBreakBool c = false ∧ c ≠ '#' := by
  obtain ⟨c, ev_rest, h_emit_eq, h_nws, h_nlb, h_nc⟩ := emit_first_char p.1
  match ps with
  | [] =>
    simp only [L4YAML.Emit.emit.emitPairList]
    rw [show (L4YAML.Emit.emit p.1 ++ ": " ++ L4YAML.Emit.emit p.2).toList =
        (L4YAML.Emit.emit p.1).toList ++ (": " ++ L4YAML.Emit.emit p.2).toList from by
      simp [String.toList_append]]
    rw [h_emit_eq]
    exact ⟨c, ev_rest ++ (": " ++ L4YAML.Emit.emit p.2).toList, by simp, h_nws, h_nlb, h_nc⟩
  | p' :: ps' =>
    have h_ep : (L4YAML.Emit.emit.emitPairList (p :: p' :: ps')).toList =
        (L4YAML.Emit.emit p.1).toList ++
          (": " ++ L4YAML.Emit.emit p.2 ++ ", " ++ L4YAML.Emit.emit.emitPairList (p' :: ps')).toList := by
      simp [L4YAML.Emit.emit.emitPairList, String.toList_append, List.append_assoc]
    rw [h_ep, h_emit_eq]
    exact ⟨c, ev_rest ++ (": " ++ L4YAML.Emit.emit p.2 ++ ", " ++ L4YAML.Emit.emit.emitPairList (p' :: ps')).toList,
      by simp, h_nws, h_nlb, h_nc⟩

/-- `isValueCandidateIx` returns true when `peekAt? 1` is a space (blank):
    every branch of `isValueCandidateIx` has a `peekAt? 1` fallback whose
    blank-acceptance (`isBlankBool ' ' = true`) collapses the result to
    `true`. Indexed twin of legacy `isValueCandidate_of_peekAt_blank`
    (lines 7234–7254). -/
theorem isValueCandidate_of_peekAt_blankIx (s : ScannerStateIx input)
    (h : s.peekAt? 1 = some ' ') :
    isValueCandidateIx s = true := by
  unfold isValueCandidateIx
  rw [h]
  simp only [show isBlankBool ' ' = true from by decide, Bool.true_or, ite_self]

end L4YAML.Proofs.Indexed.EmitterScannability.EmitScans
