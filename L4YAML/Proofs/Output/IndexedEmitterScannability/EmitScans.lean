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
  - ✅ **`emitList_scans_nonemptyIx`** — landed (`.flowvalue` sub-session
    2a, see §2 below). Its one missing supporting twin,
    `scanNextTokenIx_preprocess_flow_ws1` (the one-leading-space
    preprocess-equality lemma), landed alongside in `FlowMonoChain/Sync/
    Scenarios/Preflow.lean` §1b.
  - ⏳ `scanNextToken_flow_valueIx` (`.flowvalue` sub-session 2b): the
    value-indicator (`:`) flow dispatcher (legacy 7256–7621, ~360 LOC;
    needs the missing twins `scanNextTokenIx_via_block_dispatch`,
    `scanValueTabCheckIx`, `AllTokensOnLine_scanValuePrepare_flowIx`, …).
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
open L4YAML.Proofs.CouplingBridge
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

/-! ## §2  In-flow emit-scannability predicates + light helpers + list body

Step `6f.3b3.emitscans.flowvalue`, **sub-sessions 1 and 2a**. SS1 ported
the predicate layer and three small helpers (`emitList_scans_emptyIx`,
`emitPairList_first_charIx`, `isValueCandidate_of_peekAt_blankIx`); SS2a
ported the comma-path list body `emitList_scans_nonemptyIx` (legacy
7068–7207), after building its one missing supporting twin
`scanNextTokenIx_preprocess_flow_ws1` (in `Preflow.lean` §1b). The
remaining heavy body `scanNextToken_flow_valueIx` (the `:` value-indicator
dispatcher, legacy 7256–7621) lands in sub-session 2b.

Indexed twin of legacy `Proofs/Output/EmitterScannability.lean`
lines 7003–7254 (SS1) and 7068–7207 (SS2a). Substrate bridge:
`ScannerState` → `ScannerStateIx input`;
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

/-- Non-empty list scanning via induction on the item list. Singleton case
    uses `EmitScansInFlowIx` directly; the multi-item case chains
    `emit v` + `", "` + recursive `emitList`. Indexed twin of legacy
    `emitList_scans_nonempty` (lines 7068–7207). -/
theorem emitList_scans_nonemptyIx (items : List YamlValue) (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, EmitScansInFlowIx (input := input) v) :
    EmitListScansInFlowIx (input := input) items := by
  induction items with
  | nil => contradiction
  | cons v tail ih =>
    intro s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
    match tail, ih with
    | [], _ =>
      -- Singleton [v]: emitList [v] = emit v
      have h_eq : (L4YAML.Emit.emit.emitList [v]).toList = (L4YAML.Emit.emit v).toList := by
        simp only [L4YAML.Emit.emit.emitList]
      rw [h_eq] at hcorr
      obtain ⟨n, s', h_chain, h_corr, h_fl', h_dp, h_ids, h_ek', h_col', h_flow', h_indent',
              h_line_v, _, _, h_atol', h_endline', h_stack', h_fmc'⟩ :=
        h_all v (.head _) s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
      exact ⟨n, s', h_chain, h_corr, h_fl', h_dp, h_ids, h_ek', h_col', h_flow', h_indent',
             h_line_v, h_atol', h_endline', h_stack', h_fmc'⟩
    | v' :: vs, ih =>
      -- Multi-item: emitList (v :: v' :: vs) = emit v ++ ", " ++ emitList (v' :: vs)
      have h_eq : (L4YAML.Emit.emit.emitList (v :: v' :: vs)).toList ++ rest_chars =
          (L4YAML.Emit.emit v).toList ++
            ([',', ' '] ++ (L4YAML.Emit.emit.emitList (v' :: vs)).toList ++ rest_chars) := by
        simp [L4YAML.Emit.emit.emitList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: scan emit v via EmitScansInFlowIx
      have h_ev : EmitScansInFlowIx (input := input) v := h_all v (.head _)
      obtain ⟨n₁, s₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, h_flow₁,
              h_indent₁, _h_line₁, _, h_last₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁⟩ :=
        h_ev s ([',', ' '] ++ (L4YAML.Emit.emit.emitList (v' :: vs)).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
      -- Step 2: scan ',' via scanNextTokenIx_flow_comma
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, _h_line₂,
              h_atol₂, h_endline₂, h_stack₂⟩ :=
        scanNextTokenIx_flow_comma s₁
          (' ' :: (L4YAML.Emit.emit.emitList (v' :: vs)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ h_last₁ h_atol₁ h_endline₁
      -- Step 3: handle the leading space via the preprocessing-equality twin
      obtain ⟨c, rest', h_first, h_nws, h_nlb, h_nc⟩ := emitList_first_char v' vs
      have h_corr₂_ws : ScannerSurfCorrIx s₂
          ⟨' ' :: c :: (rest' ++ rest_chars), s₂.cursor.pos.col⟩ := by
        have : ' ' :: (L4YAML.Emit.emit.emitList (v' :: vs)).toList ++ rest_chars =
            ' ' :: c :: (rest' ++ rest_chars) := by
          rw [h_first]; simp only [List.cons_append]
        rwa [this] at h_corr₂
      have h_s2_flow : s₂.inFlow = true := by
        unfold ScannerStateIx.inFlow; exact decide_eq_true (by rw [h_fl₂, h_fl₁]; exact h_fl)
      have h_s2_indent : s₂.currentIndent < 0 := by
        unfold ScannerStateIx.currentIndent; rw [h_ids₂]; exact h_indent₁
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃,
              _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃⟩ :=
        scanNextTokenIx_preprocess_flow_ws1 s₂ c (rest' ++ rest_chars) h_corr₂_ws
          h_s2_flow h_nws h_nlb h_nc h_s2_indent
      -- s₃ at c :: rest' ++ rest_chars = (emitList (v' :: vs)).toList ++ rest_chars
      have h_corr₃' : ScannerSurfCorrIx s₃
          ⟨(L4YAML.Emit.emit.emitList (v' :: vs)).toList ++ rest_chars, s₃.cursor.pos.col⟩ := by
        have : c :: (rest' ++ rest_chars) =
            (L4YAML.Emit.emit.emitList (v' :: vs)).toList ++ rest_chars := by
          rw [h_first]; simp only [List.cons_append]
        rwa [this] at h_corr₃
      -- Step 4: recursive scan of emitList (v' :: vs) from s₃
      have h_tail_all : ∀ w ∈ v' :: vs, EmitScansInFlowIx (input := input) w :=
        fun w hw => h_all w (.tail _ hw)
      have h_ih_list : EmitListScansInFlowIx (input := input) (v' :: vs) :=
        ih (by simp) h_tail_all
      obtain ⟨n₃, s_end, h_chain₃, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end,
              h_endline_end, h_stack_end, h_fmc₃⟩ :=
        h_ih_list s₃ rest_chars h_corr₃'
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_s2_indent)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃, h_ek₂, h_ek₁]; exact h_ek)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
      -- Step 5: lift chain for s₂ via the preprocessing equality
      have h_snt_eq : scanNextTokenIx s₂ = scanNextTokenIx s₃ :=
        scanNextTokenIx_eq_of_preprocess s₂ s₃ h_pp_eq
      -- The recursive chain has n₃ ≥ 1 (emitList is non-empty)
      have h_n₃_pos : n₃ ≥ 1 := by
        match n₃, h_chain₃ with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique h_corr₃'.chars_from h_corr_end.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (L4YAML.Emit.emit.emitList (v' :: vs)).toList = [] := by
            match h_list : (L4YAML.Emit.emit.emitList (v' :: vs)).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          exact absurd h_nil (emitList_toList_ne_nil v' vs)
        | _ + 1, _ => omega
      obtain ⟨n₃', rfl⟩ : ∃ k, n₃ = k + 1 := ⟨n₃ - 1, by omega⟩
      -- Lift the recursive ScanChainGrewIx through the preprocess equality.
      -- preprocess_flow_ws1 preserves tokens (h_toks_pp₃ : s₃.tokens = s₂.tokens),
      -- so the per-step witness from h_chain₃ at s₃ remains valid at s₂.
      have h_filt_le :
          (s₂.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≤
          (s₃.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws : ScanChainGrewIx (fun t => t.token != .placeholder)
            s₂ (n₃' + 1) s_end :=
        ScanChainGrewIx_of_scanNextTokenIx_eq h_snt_eq h_filt_le h_chain₃
      -- Per-step witness for the comma step (s₁ → s₂): the next char is ','.
      have h_grew₂ :
          (s₂.tokens.tokens.filter (fun t => t.token != .placeholder)).size >
          (s₁.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorrIx s₁
            ⟨',' :: (' ' :: (L4YAML.Emit.emit.emitList (v' :: vs)).toList ++ rest_chars),
              s₁.cursor.pos.col⟩ := by
          have : [',', ' '] ++ (L4YAML.Emit.emit.emitList (v' :: vs)).toList ++ rest_chars =
              ',' :: (' ' :: (L4YAML.Emit.emit.emitList (v' :: vs)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextTokenIx_filtered_grows_in_flow s₁ s₂ ','
          (' ' :: (L4YAML.Emit.emit.emitList (v' :: vs)).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      -- FlowMonoChainIx: lift recursive chain through preprocessing, then compose
      have h_fmc₃' : FlowMonoChainIx s.flowLevel s₃ (n₃' + 1) s_end :=
        (show s.flowLevel = s₃.flowLevel from by
          rw [h_fl₃, h_fl₂, h_fl₁]) ▸ h_fmc₃
      have h_fmc_ws : FlowMonoChainIx s.flowLevel s₂ (n₃' + 1) s_end :=
        FlowMonoChainIx_of_scanNextTokenIx_eq h_snt_eq (by omega) h_fmc₃'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChainIx.single h_snt₂ (by omega) (by omega)).trans h_fmc_ws)
      -- Compose strict chains: emit v (n₁) + comma (1) + space+rest (n₃'+1)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrewIx.single h_snt₂ h_grew₂).trans h_chain_ws)
      have h_arith : n₁ + (1 + (n₃' + 1)) = n₁ + 1 + (n₃' + 1) := by omega
      refine ⟨n₁ + 1 + (n₃' + 1), s_end, h_arith ▸ h_chain_all,
        h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end, ?_,
        h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all⟩
      · rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek₃, h_ek₂, h_ek₁]
      · rw [h_line_end, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp₃, h_stack₂, h_stack₁]

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
