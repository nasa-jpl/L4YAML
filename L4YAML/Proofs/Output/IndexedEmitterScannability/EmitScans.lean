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
  - ✅ **`scanNextToken_flow_valueIx`** — landed (`.flowvalue` sub-session
    2b, see §2b below): the value-indicator (`:`) flow dispatcher
    (legacy 7256–7621). Almost all of legacy's field-tracking collapsed
    onto the indexed `@[simp]` cursor lemmas; the only new twins needed
    were `scanValuePrepareIx_{indents,directivesPresent}_of_inFlow`,
    `AllTokensOnLineIx_{overwriteAtCursor,scanValuePrepare_flow}` (the
    pipeline lemmas `scanNextTokenIx_via_block_dispatch`,
    `scanValueTabCheckIx`, `dispatchStructural_none_flow`, … already
    existed). The legacy `h_sv` (scanValueValidate) precondition was
    *dropped* — derived internally from `AllTokensOnLineIx`/`EndLineOnLineIx`.
  - ✅ **`EmitPairListScansInFlowIx` + pair-list body** — landed
    (`.flowpair` sub-session 1, see §2c below): the dual of the `emitList`
    track, `emitPairList_scans_emptyIx` / `emitPairList_scans_nonemptyIx`.
    Every twin already existed (`scanNextToken_flow_valueIx` from §2b,
    `scanNextTokenIx_flow_comma`, `scanNextTokenIx_preprocess_flow_ws1`,
    `emitPairList_first_charIx`); the legacy `h_sv` plumbing is dropped
    (see §2b). Zero new infra; built clean 89/89, sorry-free, axioms OK.
  - ⏳ `emit_scans_in_flowIx` (`Grammable` induction, legacy 8014–8255) —
    **now unblocked** (`.flowpair` SS2 landed both scenario prerequisites:
    `scanNextTokenIx_flow_open_seq_nested` in `Scenarios/FlowSeqOpen.lean`
    and `scanNextTokenIx_flow_scanDoubleQuoted` in `Scenarios/FlowScalar.lean`).
    Deferred to `.flowpair` sub-session 3 (the induction, §2d). NB: its scalar
    case inherits SS2b's `native_decide` budget (Reflection 142).
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
          have h_chars_eq := CouplingBridge.CharsFromOffset_unique h_corr₃'.chars_from h_corr_end.chars_from
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

/-! ### §2b  `scanNextToken_flow_valueIx` (the `:` value dispatcher)

The remaining heavy body of the `EmitScansInFlow` family (legacy
7256–7621). It threads preprocessing → structural dispatch (none) →
`checkBlockFlowIndent` (ok in flow) → flow dispatch (none) → block
dispatch (`:` → `scanValueIx`). The supporting twins below all exploit
the indexed substrate's `@[simp]` cursor/field lemmas: `scanValuePrepareIx`
preserves the cursor outright, and `overwriteAtCursor`/`emit`/`advance`
are pure record updates, so the legacy proof's ~15 field-tracking
`have`s collapse to a handful of `rw`s. -/

/-- `scanValuePrepareIx` preserves `indents` in flow context: the two
    indent-pushing branches (`col > currentIndent` and the
    `pushMappingIndentIx` fall-through) both require `!s.inFlow`. -/
theorem scanValuePrepareIx_indents_of_inFlow (s : ScannerStateIx input)
    (h_flow : s.inFlow = true) :
    (scanValuePrepareIx s).indents = s.indents := by
  unfold scanValuePrepareIx
  simp only [h_flow, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  split
  · rfl
  · split <;> rfl

/-- `scanValuePrepareIx` preserves `directivesPresent` in flow context
    (`overwriteAtCursor` and the simple-key record update are both
    `directivesPresent`-invariant). -/
theorem scanValuePrepareIx_directivesPresent_of_inFlow (s : ScannerStateIx input)
    (h_flow : s.inFlow = true) :
    (scanValuePrepareIx s).directivesPresent = s.directivesPresent := by
  unfold scanValuePrepareIx
  simp only [h_flow, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  split
  · rfl
  · split <;> rfl

/-- Overwriting the token at index `i` with a zero-width token whose
    saved cursor sits on line `l` preserves `AllTokensOnLineIx`. -/
theorem AllTokensOnLineIx_overwriteAtCursor (s : ScannerStateIx input)
    (i : Nat) (sk : IxCursor input) (tok : YamlToken) (l : Nat)
    (h_atol : AllTokensOnLineIx s l) (h_sk_line : sk.pos.line = l) :
    AllTokensOnLineIx (s.overwriteAtCursor i sk tok) l := by
  intro j h_bound
  have h_bound' : j < s.tokens.tokens.size := by
    have h_sz : (s.overwriteAtCursor i sk tok).tokens.size = s.tokens.tokens.size := by
      rw [show (s.overwriteAtCursor i sk tok).tokens.size
            = (s.overwriteAtCursor i sk tok).tokens.tokens.size from rfl,
          overwriteAtCursor_tokens_tokens, Array.size_setIfInBounds]
    rwa [h_sz] at h_bound
  change ((s.tokens.tokens.setIfInBounds i
      (IxToken.mk' sk.pos tok sk.pos (Nat.le_refl _) sk.posBound))[j]'
        (by rw [Array.size_setIfInBounds]; exact h_bound')).start.line = l
  rw [Array.getElem_setIfInBounds h_bound']
  by_cases h_eq : i = j
  · simp only [h_eq, ↓reduceIte]; exact h_sk_line
  · simp only [h_eq, ↓reduceIte]; exact h_atol j h_bound'

/-- `scanValuePrepareIx` preserves `AllTokensOnLineIx` in flow context.
    In the `simpleKey.possible` branch it overwrites the placeholder at
    `tokenIndex + 1` with a `.key` token saved at `simpleKey.cursor`,
    whose line is `s.cursor.pos.line` by `EndLineOnLineIx`. Indexed twin
    of legacy `AllTokensOnLine_scanValuePrepare_flow` (lines 3189–3213). -/
theorem AllTokensOnLineIx_scanValuePrepare_flow (s : ScannerStateIx input) (l : Nat)
    (h_atol : AllTokensOnLineIx s l) (h_line : s.cursor.pos.line = l)
    (h_flow : s.inFlow = true)
    (h_ek : s.explicitKeyLine = none)
    (h_endline : EndLineOnLineIx s) :
    AllTokensOnLineIx (scanValuePrepareIx s) l := by
  unfold scanValuePrepareIx
  cases h_poss : s.simpleKey.possible
  · -- possible = false: `explicitKeyLine = none` + in flow → identity.
    simp only [h_ek, Option.isSome_none, h_flow, Bool.not_true, Bool.false_eq_true,
               ↓reduceIte]
    exact h_atol
  · -- possible = true, flow branch: overwrite the key placeholder.
    have h_sk_line : s.simpleKey.cursor.pos.line = l := by
      have ⟨_, h_pl⟩ := h_endline h_poss
      show s.simpleKey.pos.line = l
      rw [h_pl]; exact h_line
    simp only [h_flow, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    intro j h_bound
    exact AllTokensOnLineIx_overwriteAtCursor s (s.simpleKey.tokenIndex + 1)
      s.simpleKey.cursor YamlToken.key l h_atol h_sk_line j h_bound

/-- Value indicator `:` scanning in flow context. After a key, the `:`
    dispatches through `isValueCandidateIx → scanValueIx`, emitting a
    `.value` token and advancing past `:`. The space after `:` (the
    emitter always produces `": "`) makes `isValueCandidateIx` hold via
    the `peekAt? 1` blank fallback. The result state sits at `' ' :: rest'`
    (the space is not yet consumed). Indexed twin of legacy
    `scanNextToken_flow_value` (lines 7256–7621). Unlike legacy, the
    `scanValueValidate` precondition is *derived* internally from the
    `AllTokensOnLineIx`/`EndLineOnLineIx` invariants (via
    `scanValueValidateIx_ok_of_flow_allTokensOnLine`), so no `h_sv`
    hypothesis is needed. -/
theorem scanNextToken_flow_valueIx (s : ScannerStateIx input)
    (rest' : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨':' :: ' ' :: rest', s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.cursor.pos.col > 0)
    (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLineIx s s.cursor.pos.line)
    (h_endline : EndLineOnLineIx s) :
    ∃ s', scanNextTokenIx s = .ok (some s')
      ∧ ScannerSurfCorrIx s' ⟨' ' :: rest', s'.cursor.pos.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.cursor.pos.col = s.cursor.pos.col + 1
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.explicitKeyLine = none
      ∧ s'.cursor.pos.line = s.cursor.pos.line
      ∧ AllTokensOnLineIx s' s'.cursor.pos.line
      ∧ EndLineOnLineIx s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack := by
  -- Surface facts at `s` and at the post-`:` state `s.advance`.
  have ⟨h_pk_colon, h_lt_colon⟩ :=
    peek_of_chars_consIx_state s ':' (' ' :: rest') s.cursor.pos.col hcorr
  have h_pk_colon' : s.cursor.peek? = some ':' := h_pk_colon
  have h_corr_adv : ScannerSurfCorrIx s.advance ⟨' ' :: rest', s.cursor.pos.col + 1⟩ :=
    advance_non_newline_corrIx_state s s.advance ':' (' ' :: rest') hcorr rfl rfl
      h_lt_colon (by decide) (by decide)
  have ⟨h_pk_space, _⟩ :=
    peek_of_chars_consIx_state s.advance ' ' rest' (s.cursor.pos.col + 1) h_corr_adv
  -- Step 1: preprocessing.
  have h_pp : scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s, ':')) :=
    scanNextTokenIx_preprocess_flow s ':' (' ' :: rest') s.cursor.pos.col hcorr h_flow
      (by decide) (by decide) (by decide)
  -- Step 2: structural dispatch → none.
  have h_sk_flow : (saveSimpleKeyIx s).inFlow = s.inFlow := saveSimpleKeyIx_inFlow s
  have h_sk_indent : (saveSimpleKeyIx s).currentIndent = s.currentIndent := by
    unfold ScannerStateIx.currentIndent; rw [saveSimpleKeyIx_indents]
  have h_sk_col : (saveSimpleKeyIx s).cursor.pos.col = s.cursor.pos.col := by
    rw [saveSimpleKeyIx_cursor]
  have h_struct : scanNextTokenIx_dispatchStructural (saveSimpleKeyIx s) ':' = .ok none :=
    dispatchStructural_none_flow _ _
      (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  -- Step 3: introduce `s_ad` opaquely + derive its field equalities.
  obtain ⟨s_ad, h_s_ad_def⟩ : ∃ s_ad : ScannerStateIx input,
      s_ad = if (saveSimpleKeyIx s).allowDirectives then
        { saveSimpleKeyIx s with allowDirectives := false, documentEverStarted := true }
      else saveSimpleKeyIx s := ⟨_, rfl⟩
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_explicitKeyLine s
  have h_ad_cursor : s_ad.cursor = s.cursor := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_cursor s
  have h_ad_tokens : s_ad.tokens = (saveSimpleKeyIx s).tokens := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_simpleKey : s_ad.simpleKey = (saveSimpleKeyIx s).simpleKey := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_stack : s_ad.simpleKeyStack = s.simpleKeyStack := by
    have h1 : (saveSimpleKeyIx s).simpleKeyStack = s.simpleKeyStack :=
      ScannerPlainScalarValid.saveSimpleKeyIx_preserves_simpleKeyStack s
    rw [h_s_ad_def]; split <;> exact h1
  have h_ad_flow : s_ad.inFlow = true := by
    unfold ScannerStateIx.inFlow; rw [h_ad_fl]; exact h_flow
  have h_ad_ek_none : s_ad.explicitKeyLine = none := by rw [h_ad_ek]; exact h_ek
  have h_ad_line : s_ad.cursor.pos.line = s.cursor.pos.line := by rw [h_ad_cursor]
  -- Step 4: checkBlockFlowIndent (vacuous in flow) + flow dispatch → none.
  have h_check : scanNextTokenIx_checkBlockFlowIndent s_ad ':' = .ok () :=
    checkBlockFlowIndent_ok_flow s_ad ':' h_ad_flow
  have h_flow_none : scanNextTokenIx_dispatchFlowIndicators s_ad ':' = .ok none :=
    dispatchFlowIndicators_none s_ad ':'
      (by decide) (by decide) (by decide) (by decide) (by decide)
  -- Step 5: `isValueCandidateIx s_ad = true` via the `peekAt? 1 = ' '` fallback.
  have h_vc : isValueCandidateIx s_ad = true := by
    apply isValueCandidate_of_peekAt_blankIx
    show s_ad.cursor.peekAt? 1 = some ' '
    rw [h_ad_cursor, ← IxCursor.advance_peek_eq_peekAt_one s.cursor h_pk_colon']
    exact h_pk_space
  -- Step 6: the scanValue pipeline reduces to a single result state.
  have h_clearKey : scanValueClearKeyIx s_ad = s_ad := by
    unfold scanValueClearKeyIx; rw [h_ad_ek_none]
  have h_atol_sk : AllTokensOnLineIx (saveSimpleKeyIx s) s.cursor.pos.line :=
    AllTokensOnLineIx_saveSimpleKeyIx s s.cursor.pos.line h_atol rfl
  have h_atol_ad : AllTokensOnLineIx s_ad s.cursor.pos.line :=
    AllTokensOnLineIx_of_tokens_eq h_ad_tokens h_atol_sk
  have h_endline_sk : EndLineOnLineIx (saveSimpleKeyIx s) :=
    EndLineOnLineIx_saveSimpleKeyIx s h_endline
  have h_endline_ad : EndLineOnLineIx s_ad := by
    intro h_poss
    rw [h_ad_simpleKey] at h_poss
    obtain ⟨h1, h2⟩ := h_endline_sk h_poss
    rw [saveSimpleKeyIx_cursor] at h1 h2
    rw [h_ad_simpleKey, h_ad_cursor]; exact ⟨h1, h2⟩
  have h_validate : scanValueValidateIx s_ad = .ok () :=
    scanValueValidateIx_ok_of_flow_allTokensOnLine s_ad h_ad_flow h_ad_ek_none
      (by rw [h_ad_line]; exact h_atol_ad) h_endline_ad
  have h_adv_inflow :
      (((scanValuePrepareIx s_ad).emit YamlToken.value).advance).inFlow = true := by
    rw [advance_inFlow, emit_inFlow]
    unfold ScannerStateIx.inFlow
    rw [scanValuePrepareIx_preserves_flowLevel]; exact h_ad_flow
  have h_tabCheck : scanValueTabCheckIx (s_ad.cursor.pos.col : Int) s_ad.currentIndent
      (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) = .ok () := by
    unfold scanValueTabCheckIx
    simp only [h_adv_inflow, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  have h_scanValue_ok : scanValueIx s_ad =
      .ok { (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
            simpleKeyAllowed := true, explicitKeyLine := none } := by
    unfold scanValueIx
    simp only [h_clearKey, h_validate, h_tabCheck, bind, Except.bind]
  -- Step 7: block dispatch produces the result; compose the pipeline.
  have h_block : scanNextTokenIx_dispatchBlockIndicators s_ad ':' =
      .ok (some { (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
                  simpleKeyAllowed := true, explicitKeyLine := none }) := by
    unfold scanNextTokenIx_dispatchBlockIndicators
    simp only [show (':' == '-') = false from by decide, Bool.false_and,
      show (':' == '?') = false from by decide,
      show (':' == ':') = true from by decide, Bool.true_and, h_vc, ↓reduceIte]
    rw [h_scanValue_ok]; rfl
  have h_snt : scanNextTokenIx s =
      .ok (some { (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
                  simpleKeyAllowed := true, explicitKeyLine := none }) :=
    scanNextTokenIx_via_block_dispatch s (saveSimpleKeyIx s) s_ad _ ':'
      h_pp h_struct h_s_ad_def h_check h_flow_none h_block
  -- Step 8: result-state field equalities (all via `@[simp]` cursor lemmas).
  have h_R_cursor :
      ({ (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
         simpleKeyAllowed := true, explicitKeyLine := none } : ScannerStateIx input).cursor
        = s.cursor.advance := by
    show ((scanValuePrepareIx s_ad).emit YamlToken.value).advance.cursor = s.cursor.advance
    rw [advance_cursor, emit_cursor, scanValuePrepareIx_cursor, h_ad_cursor]
  have h_R_indents :
      ({ (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
         simpleKeyAllowed := true, explicitKeyLine := none } : ScannerStateIx input).indents
        = s.indents := by
    show ((scanValuePrepareIx s_ad).emit YamlToken.value).advance.indents = s.indents
    rw [advance_indents, emit_indents, scanValuePrepareIx_indents_of_inFlow s_ad h_ad_flow,
        h_ad_ids]
  have h_R_corr : ScannerSurfCorrIx
      ({ (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
         simpleKeyAllowed := true, explicitKeyLine := none } : ScannerStateIx input)
      ⟨' ' :: rest', s.cursor.pos.col + 1⟩ :=
    advance_non_newline_corrIx_state s _ ':' (' ' :: rest') hcorr h_R_cursor h_R_indents
      h_lt_colon (by decide) (by decide)
  have h_R_col :
      ({ (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
         simpleKeyAllowed := true, explicitKeyLine := none } : ScannerStateIx input).cursor.pos.col
        = s.cursor.pos.col + 1 := h_R_corr.col_eq.symm
  have h_R_fl :
      ({ (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
         simpleKeyAllowed := true, explicitKeyLine := none } : ScannerStateIx input).flowLevel
        = s.flowLevel := by
    show ((scanValuePrepareIx s_ad).emit YamlToken.value).advance.flowLevel = s.flowLevel
    rw [advance_flowLevel, emit_flowLevel, scanValuePrepareIx_preserves_flowLevel, h_ad_fl]
  have h_R_dp :
      ({ (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
         simpleKeyAllowed := true, explicitKeyLine := none } : ScannerStateIx input).directivesPresent
        = s.directivesPresent := by
    show ((scanValuePrepareIx s_ad).emit YamlToken.value).advance.directivesPresent
        = s.directivesPresent
    rw [advance_directivesPresent, emit_directivesPresent,
        scanValuePrepareIx_directivesPresent_of_inFlow s_ad h_ad_flow, h_ad_dp]
  have h_R_flow :
      ({ (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
         simpleKeyAllowed := true, explicitKeyLine := none } : ScannerStateIx input).inFlow
        = true := by
    unfold ScannerStateIx.inFlow; rw [h_R_fl]; exact h_flow
  have h_R_indent :
      ({ (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
         simpleKeyAllowed := true, explicitKeyLine := none } : ScannerStateIx input).currentIndent
        < 0 := by
    unfold ScannerStateIx.currentIndent; rw [h_R_indents]; exact h_indent
  have h_R_line :
      ({ (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
         simpleKeyAllowed := true, explicitKeyLine := none } : ScannerStateIx input).cursor.pos.line
        = s.cursor.pos.line := by
    rw [h_R_cursor]
    exact advance_line_of_peekIx_state s ':' h_lt_colon h_pk_colon (by decide) (by decide)
  have h_R_stack :
      ({ (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
         simpleKeyAllowed := true, explicitKeyLine := none } : ScannerStateIx input).simpleKeyStack
        = s.simpleKeyStack := by
    show (scanValuePrepareIx s_ad).simpleKeyStack = s.simpleKeyStack
    rw [ScannerPlainScalarValid.scanValuePrepareIx_preserves_simpleKeyStack, h_ad_stack]
  have h_prep_line : (scanValuePrepareIx s_ad).cursor.pos.line = s.cursor.pos.line := by
    rw [scanValuePrepareIx_cursor, h_ad_cursor]
  have h_R_atol : AllTokensOnLineIx
      ({ (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
         simpleKeyAllowed := true, explicitKeyLine := none } : ScannerStateIx input)
      ({ (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
         simpleKeyAllowed := true, explicitKeyLine := none } : ScannerStateIx input).cursor.pos.line := by
    rw [h_R_line]
    have step1 : AllTokensOnLineIx (scanValuePrepareIx s_ad) s.cursor.pos.line :=
      AllTokensOnLineIx_scanValuePrepare_flow s_ad s.cursor.pos.line h_atol_ad h_ad_line
        h_ad_flow h_ad_ek_none h_endline_ad
    have step2 : AllTokensOnLineIx ((scanValuePrepareIx s_ad).emit YamlToken.value)
        s.cursor.pos.line :=
      AllTokensOnLineIx_emit (scanValuePrepareIx s_ad) YamlToken.value s.cursor.pos.line
        step1 h_prep_line
    exact AllTokensOnLineIx_advance ((scanValuePrepareIx s_ad).emit YamlToken.value)
      s.cursor.pos.line step2
  have h_R_endline : EndLineOnLineIx
      ({ (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
         simpleKeyAllowed := true, explicitKeyLine := none } : ScannerStateIx input) := by
    intro h_poss
    rw [show ({ (((scanValuePrepareIx s_ad).emit YamlToken.value).advance) with
               simpleKeyAllowed := true, explicitKeyLine := none }
              : ScannerStateIx input).simpleKey.possible
            = (scanValuePrepareIx s_ad).simpleKey.possible from rfl,
        ScannerPlainScalarValid.scanValuePrepareIx_clears_simpleKey] at h_poss
    exact absurd h_poss (by decide)
  refine ⟨_, h_snt, ?_, h_R_fl, h_R_dp, h_R_indents, h_R_col, h_R_flow, h_R_indent, rfl,
    h_R_line, h_R_atol, h_R_endline, h_R_stack⟩
  rw [h_R_col]; exact h_R_corr

/-! ### §2c  `EmitPairListScansInFlowIx` + the pair-list body

Step `6f.3b3.emitscans.flowpair`, **sub-session 1** (the pair-list track,
legacy lines 7626–8013). The dual of the `emitList` track: scanning the
comma-separated key-value entries between `{` and `}` in a flow mapping.
Each pair contributes a key (`EmitScansInFlowIx`), a `:` value indicator
(`scanNextToken_flow_valueIx`, §2b), a value (`EmitScansInFlowIx`), and —
for the multi-pair tail — a `,` separator (`scanNextTokenIx_flow_comma`).
The leading space after each `:` and `,` is absorbed by the one-space
preprocessing-equality twin `scanNextTokenIx_preprocess_flow_ws1` (§2a).

Indexed twin of legacy `EmitPairListScansInFlow` / `emitPairList_scans_*`
(lines 7626–8011). Substrate bridge as in §2. One contract simplification
inherited from §2b: the legacy Step 2 (deriving `saveSimpleKey` identity +
the `scanValueValidate` precondition `h_sv`) is **dropped** — `scanNextToken_flow_valueIx`
derives validate-success internally, so the `:` step needs no `h_sv`.

The dependent main theorem `emit_scans_in_flowIx` (legacy 8014–8255) is
deferred to sub-session 3 (§2d). Its scanner-scenario prerequisites
`scanNextTokenIx_flow_scanDoubleQuoted` and `scanNextTokenIx_flow_open_seq_nested`
(the `[` opener) **landed in SS2** under
`FlowMonoChain/Sync/Scenarios/{FlowScalar,FlowSeqOpen}.lean`, so SS3 is now
unblocked. -/

/-- `EmitPairListScansInFlowIx pairs`: scanning the comma-separated
    `emitPairList` output (the body between `{` and `}` in a flow mapping)
    succeeds in flow context, preserving invariants. Indexed twin of legacy
    `EmitPairListScansInFlow` (lines 7626–7649); same conclusion shape as
    `EmitListScansInFlowIx`. -/
def EmitPairListScansInFlowIx (pairs : List (YamlValue × YamlValue)) : Prop :=
  ∀ (s : ScannerStateIx input) (rest : List Char),
    ScannerSurfCorrIx s ⟨(L4YAML.Emit.emit.emitPairList pairs).toList ++ rest, s.cursor.pos.col⟩ →
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

/-- Empty pair list is trivially scanned (0-step chain). Indexed twin of
    legacy `emitPairList_scans_empty` (lines 7651–7655). -/
theorem emitPairList_scans_emptyIx : EmitPairListScansInFlowIx (input := input) [] := by
  intro s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
  have h_eq : (L4YAML.Emit.emit.emitPairList ([] : List (YamlValue × YamlValue))).toList ++ rest
      = rest := by
    simp only [L4YAML.Emit.emit.emitPairList]; rfl
  rw [h_eq] at hcorr
  exact ⟨0, s, .zero, hcorr, rfl, rfl, rfl, rfl, h_col, h_flow, h_indent, rfl,
         h_atol, h_endline, rfl, .zero (Nat.le_refl _)⟩

/-- Non-empty pair list scanning via induction on the pair list. Each pair
    contributes key + `:` + value steps; the multi-pair tail additionally
    contributes a `,` separator and a recursive scan. Indexed twin of legacy
    `emitPairList_scans_nonempty` (lines 7663–8011). Unlike legacy, the
    `scanValueValidate` precondition for the `:` step is derived internally
    (see §2b), so no `h_sv` plumbing is needed. -/
theorem emitPairList_scans_nonemptyIx (pairs : List (YamlValue × YamlValue))
    (h_ne : pairs ≠ [])
    (h_all_k : ∀ p ∈ pairs, EmitScansInFlowIx (input := input) p.1)
    (h_all_v : ∀ p ∈ pairs, EmitScansInFlowIx (input := input) p.2) :
    EmitPairListScansInFlowIx (input := input) pairs := by
  induction pairs with
  | nil => contradiction
  | cons p tail ih =>
    intro s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
    match tail, ih with
    | [], _ =>
      -- ══ Singleton [(k,v)]: emitPairList [(k,v)] = emit k ++ ": " ++ emit v ══
      have h_eq : (L4YAML.Emit.emit.emitPairList [p]).toList ++ rest_chars =
          (L4YAML.Emit.emit p.1).toList ++
            ([':', ' '] ++ (L4YAML.Emit.emit p.2).toList ++ rest_chars) := by
        simp [L4YAML.Emit.emit.emitPairList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: scan key via EmitScansInFlowIx
      have h_ek_key : EmitScansInFlowIx (input := input) p.1 := h_all_k p (.head _)
      obtain ⟨n₁, s₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁,
              h_flow₁, h_indent₁, _h_line₁, _ska₁, _h_last₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁⟩ :=
        h_ek_key s ([':', ' '] ++ (L4YAML.Emit.emit p.2).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
      -- Step 2: scan ':' via scanNextToken_flow_valueIx (validate derived internally)
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂⟩ :=
        scanNextToken_flow_valueIx s₁ ((L4YAML.Emit.emit p.2).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
      -- Step 3: handle the leading space before the value via the preprocess-eq twin
      obtain ⟨c_v, rest_v, h_first_v, h_nws_v, h_nlb_v, h_nc_v⟩ := emit_first_char p.2
      have h_corr₂_ws : ScannerSurfCorrIx s₂
          ⟨' ' :: c_v :: (rest_v ++ rest_chars), s₂.cursor.pos.col⟩ := by
        have h_eq_chars : ' ' :: ((L4YAML.Emit.emit p.2).toList ++ rest_chars) =
            ' ' :: c_v :: (rest_v ++ rest_chars) := by
          congr 1; rw [h_first_v]; simp only [List.cons_append]
        exact h_eq_chars ▸ h_corr₂
      have h_s2_flow : s₂.inFlow = true := by
        unfold ScannerStateIx.inFlow
        exact decide_eq_true (by rw [h_fl₂, h_fl₁]; exact h_fl)
      have h_s2_indent : s₂.currentIndent < 0 := by
        unfold ScannerStateIx.currentIndent; rw [h_ids₂]; exact h_indent₁
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃,
              _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃⟩ :=
        scanNextTokenIx_preprocess_flow_ws1 s₂ c_v (rest_v ++ rest_chars) h_corr₂_ws
          h_s2_flow h_nws_v h_nlb_v h_nc_v h_s2_indent
      have h_corr₃' : ScannerSurfCorrIx s₃
          ⟨(L4YAML.Emit.emit p.2).toList ++ rest_chars, s₃.cursor.pos.col⟩ := by
        have : c_v :: (rest_v ++ rest_chars) =
            (L4YAML.Emit.emit p.2).toList ++ rest_chars := by
          rw [h_first_v]; simp only [List.cons_append]
        rwa [this] at h_corr₃
      -- Step 4: scan value via EmitScansInFlowIx
      have h_ev : EmitScansInFlowIx (input := input) p.2 := h_all_v p (.head _)
      obtain ⟨n₃, s_end, h_chain₃, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, _, _, h_atol_end,
              h_endline_end, h_stack_end, h_fmc₃⟩ :=
        h_ev s₃ rest_chars h_corr₃'
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_s2_indent)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃, h_ek₂])
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
      -- Step 5: lift chain for s₂ via the preprocessing equality
      have h_snt_eq : scanNextTokenIx s₂ = scanNextTokenIx s₃ :=
        scanNextTokenIx_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_n₃_pos : n₃ ≥ 1 := by
        match n₃, h_chain₃ with
        | 0, .zero =>
          exfalso
          have h_chars_eq :=
            CouplingBridge.CharsFromOffset_unique h_corr₃'.chars_from h_corr_end.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (L4YAML.Emit.emit p.2).toList = [] := by
            match h_list : (L4YAML.Emit.emit p.2).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.2
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      obtain ⟨n₃', rfl⟩ : ∃ k, n₃ = k + 1 := ⟨n₃ - 1, by omega⟩
      have h_filt_le :
          (s₂.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≤
          (s₃.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws : ScanChainGrewIx (fun t => t.token != .placeholder)
            s₂ (n₃' + 1) s_end :=
        ScanChainGrewIx_of_scanNextTokenIx_eq h_snt_eq h_filt_le h_chain₃
      -- Per-step witness for the colon step (s₁ → s₂): the next char is ':'.
      have h_grew₂ :
          (s₂.tokens.tokens.filter (fun t => t.token != .placeholder)).size >
          (s₁.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorrIx s₁
            ⟨':' :: (' ' :: (L4YAML.Emit.emit p.2).toList ++ rest_chars), s₁.cursor.pos.col⟩ := by
          have : [':', ' '] ++ (L4YAML.Emit.emit p.2).toList ++ rest_chars =
              ':' :: (' ' :: (L4YAML.Emit.emit p.2).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextTokenIx_filtered_grows_in_flow s₁ s₂ ':'
          (' ' :: (L4YAML.Emit.emit p.2).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      -- FlowMonoChainIx: lift value chain through preprocessing, compose with key + colon
      have h_fmc₃' : FlowMonoChainIx s.flowLevel s₃ (n₃' + 1) s_end :=
        (show s.flowLevel = s₃.flowLevel from by rw [h_fl₃, h_fl₂, h_fl₁]) ▸ h_fmc₃
      have h_fmc_ws : FlowMonoChainIx s.flowLevel s₂ (n₃' + 1) s_end :=
        FlowMonoChainIx_of_scanNextTokenIx_eq h_snt_eq (by omega) h_fmc₃'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChainIx.single h_snt₂ (by omega) (by omega)).trans h_fmc_ws)
      -- Compose strict chains: key (n₁) + colon (1) + space+value (n₃'+1)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrewIx.single h_snt₂ h_grew₂).trans h_chain_ws)
      have h_arith : n₁ + (1 + (n₃' + 1)) = n₁ + 1 + (n₃' + 1) := by omega
      refine ⟨n₁ + 1 + (n₃' + 1), s_end, h_arith ▸ h_chain_all,
        h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end, ?_,
        h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all⟩
      · rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek₃, h_ek₂]; exact h_ek.symm
      · rw [h_line_end, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp₃, h_stack_v₂, h_stack₁]
    | p' :: ps, ih =>
      -- ══ Multi-pair: emit k ++ ": " ++ emit v ++ ", " ++ emitPairList (p' :: ps) ══
      have h_eq : (L4YAML.Emit.emit.emitPairList (p :: p' :: ps)).toList ++ rest_chars =
          (L4YAML.Emit.emit p.1).toList ++ ([':', ' '] ++ (L4YAML.Emit.emit p.2).toList ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
        simp [L4YAML.Emit.emit.emitPairList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: scan key via EmitScansInFlowIx
      have h_ek_key : EmitScansInFlowIx (input := input) p.1 := h_all_k p (.head _)
      obtain ⟨n₁, s₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁,
              h_flow₁, h_indent₁, _h_line₁, _ska₁, _h_last₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁⟩ :=
        h_ek_key s ([':', ' '] ++ (L4YAML.Emit.emit p.2).toList ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
      -- Step 2: scan ':' via scanNextToken_flow_valueIx (validate derived internally)
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂⟩ :=
        scanNextToken_flow_valueIx s₁
          ((L4YAML.Emit.emit p.2).toList ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
      -- Step 3: handle the leading space before the value
      obtain ⟨c_v, rest_v, h_first_v, h_nws_v, h_nlb_v, h_nc_v⟩ := emit_first_char p.2
      have h_corr₂_ws : ScannerSurfCorrIx s₂
          ⟨' ' :: c_v :: (rest_v ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars),
            s₂.cursor.pos.col⟩ := by
        have h_eq_chars : ' ' :: ((L4YAML.Emit.emit p.2).toList ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars) =
            ' ' :: c_v :: (rest_v ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
          congr 1; rw [h_first_v]; simp only [List.cons_append, List.append_assoc]
        exact h_eq_chars ▸ h_corr₂
      have h_s2_flow : s₂.inFlow = true := by
        unfold ScannerStateIx.inFlow
        exact decide_eq_true (by rw [h_fl₂, h_fl₁]; exact h_fl)
      have h_s2_indent : s₂.currentIndent < 0 := by
        unfold ScannerStateIx.currentIndent; rw [h_ids₂]; exact h_indent₁
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃,
              _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃⟩ :=
        scanNextTokenIx_preprocess_flow_ws1 s₂ c_v
          (rest_v ++ [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₂_ws h_s2_flow h_nws_v h_nlb_v h_nc_v h_s2_indent
      have h_corr₃' : ScannerSurfCorrIx s₃
          ⟨(L4YAML.Emit.emit p.2).toList ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars,
            s₃.cursor.pos.col⟩ := by
        have : c_v :: (rest_v ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars) =
            (L4YAML.Emit.emit p.2).toList ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars := by
          rw [h_first_v]; simp only [List.cons_append, List.append_assoc]
        rwa [this] at h_corr₃
      -- Step 4: scan value via EmitScansInFlowIx
      have h_ev : EmitScansInFlowIx (input := input) p.2 := h_all_v p (.head _)
      have h_corr₃_assoc : ScannerSurfCorrIx s₃
          ⟨(L4YAML.Emit.emit p.2).toList ++ ([',', ' '] ++
            (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₃.cursor.pos.col⟩ := by
        simp only [List.append_assoc] at h_corr₃' ⊢; exact h_corr₃'
      obtain ⟨n_v, s_v, h_chain_v, h_corr_v, h_fl_v, h_dp_v, h_ids_v,
              h_ek_v, h_col_v, h_flow_v, h_indent_v, _h_line_v, _ska_v, h_last_v, h_atol_v,
              h_endline_v, h_stack_v, h_fmc_v⟩ :=
        h_ev s₃
          ([',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₃_assoc
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_s2_indent)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃, h_ek₂])
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
      -- Lift value chain through preprocessing equality
      have h_snt_eq_v : scanNextTokenIx s₂ = scanNextTokenIx s₃ :=
        scanNextTokenIx_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_n_v_pos : n_v ≥ 1 := by
        match n_v, h_chain_v with
        | 0, .zero =>
          exfalso
          have h_chars_eq :=
            CouplingBridge.CharsFromOffset_unique h_corr₃'.chars_from h_corr_v.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (L4YAML.Emit.emit p.2).toList = [] := by
            match h_list : (L4YAML.Emit.emit p.2).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.2
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      obtain ⟨n_v', rfl⟩ : ∃ k, n_v = k + 1 := ⟨n_v - 1, by omega⟩
      have h_filt_le_v :
          (s₂.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≤
          (s₃.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws_v : ScanChainGrewIx (fun t => t.token != .placeholder)
            s₂ (n_v' + 1) s_v :=
        ScanChainGrewIx_of_scanNextTokenIx_eq h_snt_eq_v h_filt_le_v h_chain_v
      -- Per-step witness for the colon step (s₁ → s₂): next char is ':'.
      have h_grew₂ :
          (s₂.tokens.tokens.filter (fun t => t.token != .placeholder)).size >
          (s₁.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorrIx s₁
            ⟨':' :: (' ' :: (L4YAML.Emit.emit p.2).toList ++ [',', ' '] ++
              (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars),
              s₁.cursor.pos.col⟩ := by
          have : [':', ' '] ++ (L4YAML.Emit.emit p.2).toList ++ [',', ' '] ++
              (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars =
              ':' :: (' ' :: (L4YAML.Emit.emit p.2).toList ++ [',', ' '] ++
              (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextTokenIx_filtered_grows_in_flow s₁ s₂ ':'
          (' ' :: (L4YAML.Emit.emit p.2).toList ++ [',', ' '] ++
              (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      -- Step 6: scan ',' via scanNextTokenIx_flow_comma
      obtain ⟨s_c, h_snt_c, h_corr_c, h_fl_c, h_dp_c, h_ids_c, h_ek_c, h_col_c, _h_line_c,
              h_atol_c, h_endline_c, h_stack_c⟩ :=
        scanNextTokenIx_flow_comma s_v
          (' ' :: (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v h_flow_v h_indent_v h_col_v h_last_v h_atol_v h_endline_v
      -- Step 7: handle the leading space before the next pair
      obtain ⟨c_p, rest_p, h_first_p, h_nws_p, h_nlb_p, h_nc_p⟩ :=
        emitPairList_first_charIx p' ps
      have h_corr_c_ws : ScannerSurfCorrIx s_c
          ⟨' ' :: c_p :: (rest_p ++ rest_chars), s_c.cursor.pos.col⟩ := by
        have : ' ' :: (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars =
            ' ' :: c_p :: (rest_p ++ rest_chars) := by
          rw [h_first_p]; simp only [List.cons_append]
        rwa [this] at h_corr_c
      have h_sc_flow : s_c.inFlow = true := by
        unfold ScannerStateIx.inFlow
        exact decide_eq_true (by rw [h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
      have h_sc_indent : s_c.currentIndent < 0 := by
        unfold ScannerStateIx.currentIndent; rw [h_ids_c]; exact h_indent_v
      obtain ⟨s_pp, h_corr_pp, h_flow_pp, h_fl_pp, h_indent_pp, h_col_pp, h_dp_pp, h_ids_pp,
              h_ek_pp, _h_line_pp, h_pp_eq_r, h_atol_transfer_pp, h_endline_transfer_pp,
              h_stack_pp, h_toks_pp⟩ :=
        scanNextTokenIx_preprocess_flow_ws1 s_c c_p (rest_p ++ rest_chars) h_corr_c_ws
          h_sc_flow h_nws_p h_nlb_p h_nc_p h_sc_indent
      have h_corr_pp' : ScannerSurfCorrIx s_pp
          ⟨(L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars, s_pp.cursor.pos.col⟩ := by
        have : c_p :: (rest_p ++ rest_chars) =
            (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars := by
          rw [h_first_p]; simp only [List.cons_append]
        rwa [this] at h_corr_pp
      -- Step 8: recursive scan of emitPairList (p' :: ps)
      have h_tail_all_k : ∀ q ∈ p' :: ps, EmitScansInFlowIx (input := input) q.1 :=
        fun q hq => h_all_k q (.tail _ hq)
      have h_tail_all_v : ∀ q ∈ p' :: ps, EmitScansInFlowIx (input := input) q.2 :=
        fun q hq => h_all_v q (.tail _ hq)
      have h_ih_list : EmitPairListScansInFlowIx (input := input) (p' :: ps) :=
        ih (by simp) h_tail_all_k h_tail_all_v
      obtain ⟨n_r, s_end, h_chain_r, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end,
              h_endline_end, h_stack_end, h_fmc_r⟩ :=
        h_ih_list s_pp rest_chars h_corr_pp'
          h_flow_pp
          (by rw [h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent_pp]; exact h_sc_indent)
          (by rw [h_col_pp]; omega)
          (by rw [h_ek_pp, h_ek_c, h_ek_v, h_ek₃, h_ek₂])
          (h_atol_transfer_pp h_atol_c)
          (h_endline_transfer_pp h_endline_c)
      -- Lift recursive chain through preprocessing equality
      have h_snt_eq_r : scanNextTokenIx s_c = scanNextTokenIx s_pp :=
        scanNextTokenIx_eq_of_preprocess s_c s_pp h_pp_eq_r
      have h_n_r_pos : n_r ≥ 1 := by
        match n_r, h_chain_r with
        | 0, .zero =>
          exfalso
          have h_chars_eq :=
            CouplingBridge.CharsFromOffset_unique h_corr_pp'.chars_from h_corr_end.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList = [] := by
            match h_list : (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emitPairList_first_charIx p' ps
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      obtain ⟨n_r', rfl⟩ : ∃ k, n_r = k + 1 := ⟨n_r - 1, by omega⟩
      have h_filt_le_r :
          (s_c.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≤
          (s_pp.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
        rw [h_toks_pp]; exact Nat.le_refl _
      have h_chain_ws_r : ScanChainGrewIx (fun t => t.token != .placeholder)
            s_c (n_r' + 1) s_end :=
        ScanChainGrewIx_of_scanNextTokenIx_eq h_snt_eq_r h_filt_le_r h_chain_r
      -- Per-step witness for the comma step (s_v → s_c): next char is ','.
      have h_grew_c :
          (s_c.tokens.tokens.filter (fun t => t.token != .placeholder)).size >
          (s_v.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
        have h_corr_v_cons : ScannerSurfCorrIx s_v
            ⟨',' :: (' ' :: (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars),
              s_v.cursor.pos.col⟩ := by
          have : [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars =
              ',' :: (' ' :: (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr_v
        exact scanNextTokenIx_filtered_grows_in_flow s_v s_c ','
          (' ' :: (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v_cons h_flow_v h_indent_v h_col_v
          (by decide) (by decide) (by decide) h_snt_c
      -- FlowMonoChainIx: compose all sub-chains
      have h_fmc_v' : FlowMonoChainIx s.flowLevel s₃ (n_v' + 1) s_v :=
        (show s.flowLevel = s₃.flowLevel from by rw [h_fl₃, h_fl₂, h_fl₁]) ▸ h_fmc_v
      have h_fmc_ws_v : FlowMonoChainIx s.flowLevel s₂ (n_v' + 1) s_v :=
        FlowMonoChainIx_of_scanNextTokenIx_eq h_snt_eq_v (by omega) h_fmc_v'
      have h_fmc_r' : FlowMonoChainIx s.flowLevel s_pp (n_r' + 1) s_end :=
        (show s.flowLevel = s_pp.flowLevel from by
          rw [h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁]) ▸ h_fmc_r
      have h_fmc_ws_r : FlowMonoChainIx s.flowLevel s_c (n_r' + 1) s_end :=
        FlowMonoChainIx_of_scanNextTokenIx_eq h_snt_eq_r (by omega) h_fmc_r'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChainIx.single h_snt₂ (by omega) (by omega)).trans
          (h_fmc_ws_v.trans
            ((FlowMonoChainIx.single h_snt_c (by omega) (by omega)).trans h_fmc_ws_r)))
      -- Step 9: compose strict chains
      -- key(n₁) + colon(1) + space+value(n_v'+1) + comma(1) + space+recurse(n_r'+1)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrewIx.single h_snt₂ h_grew₂).trans
          (h_chain_ws_v.trans
            ((ScanChainGrewIx.single h_snt_c h_grew_c).trans h_chain_ws_r)))
      have h_arith : n₁ + (1 + ((n_v' + 1) + (1 + (n_r' + 1)))) =
          n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1) := by omega
      refine ⟨n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1), s_end,
        h_arith ▸ h_chain_all,
        h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end, ?_,
        h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all⟩
      · rw [h_fl_end, h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp_pp, h_dp_c, h_dp_v, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids_pp, h_ids_c, h_ids_v, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek_pp, h_ek_c, h_ek_v, h_ek₃, h_ek₂]; exact h_ek.symm
      · rw [h_line_end, _h_line_pp, _h_line_c, _h_line_v, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp, h_stack_c, h_stack_v, h_stack_pp₃, h_stack_v₂, h_stack₁]

end L4YAML.Proofs.Indexed.EmitterScannability.EmitScans
