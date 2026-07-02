/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Maintenance.FlowDispatch
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Maintenance.Pipeline

/-! # `FlowMonoChain.Sync.Detail` — Phase 3 Step 6f.3b3.flowmono.sync.detail

**Sub-session 1 of `.flowmono.sync`** (legacy
`Proofs/Output/EmitterScannability.lean` lines 3793–3843, 4423–4461,
4711–4745, 4910–4914, 5022–5055, 5085–5117; ~400 LOC contribution
before substrate elimination).

Per-scanner `_detail` lemmas combining `ScannerSurfCorrIx`
propagation with field preservation through
`scanFlow{Sequence,Mapping}{Start,End}Ix` and `scanFlowEntryIx`, plus
end-scanner `_lastRealTokenValIx` / `_peek` helpers needed by the
`.sync.scenarios` chain theorems.

## Indexed simplification

Legacy `_detail` lemmas need `ScannerSurfCorr_transfer` to peel the
`end_eq` invariant before calling `advance_non_newline_corr`, since
`ScannerSurfCorr` carries `s.inputEnd = s.input.utf8ByteSize` as an
explicit field. Indexed `ScannerSurfCorrIx` has **no** `end_eq` field:
the byte-bound is a type-level invariant of `IxCursor.posBound`, so
the bridge from the per-scanner state to the post-advance cursor is
direct. Each `_detail` lemma becomes a one-`unfold` step combining
the cursor-level `advance_non_newline_corrIx` (Basic.lean §3.1) with
the field-preservation `@[simp]` lemmas already shipped in
`.maintenance.flowdispatch`.

## Scope

  - **§1** — State-level `ScannerSurfCorrIx` advance helpers:
    `peek_of_chars_consIx_state`, `advance_non_newline_corrIx_state`,
    `advance_line_of_peekIx_state`. Lift the cursor-level helpers
    (`Basic.lean` §3.0–3.1) to `ScannerSurfCorrIx` by projecting
    through `.cursor`.
  - **§2** — `scanFlowSequenceStartIx_detail`.
  - **§3** — `scanFlowMappingStartIx_detail`.
  - **§4** — `scanFlowSequenceEndIx_detail` + `_lastRealTokenValIx`
    + `_peek`.
  - **§5** — `scanFlowMappingEndIx_detail` + `_lastRealTokenValIx`
    + `_peek`.
  - **§6** — `scanFlowEntryIx_detail`.

## Legacy mapping

  | Section | Legacy lines | Indexed counterpart                |
  | ------- | ------------ | ---------------------------------- |
  | §1      | n/a (factored from `peek_of_chars_cons` + `advance_non_newline_corr`) | `peek_of_chars_consIx_state`, `advance_non_newline_corrIx_state`, `advance_line_of_peekIx_state` |
  | §2      | 3817–3842    | `scanFlowSequenceStartIx_detail`   |
  | §3      | 5032–5055    | `scanFlowMappingStartIx_detail`    |
  | §4      | 4711–4745, 4910–4914 | `scanFlowSequenceEndIx_detail` + `_lastRealTokenValIx` + `_peek` |
  | §5      | 5085–5117    | `scanFlowMappingEndIx_detail` + `_lastRealTokenValIx` + `_peek` |
  | §6      | 4423–4461    | `scanFlowEntryIx_detail`           |

## Deferred to `.sync.scenarios`

The seven `scanNextTokenIx_flow_*` scenario chain theorems
(`scanNextTokenIx_flow_comma`, `_close_seq_{nested,outermost}`,
`_close_mapping_{nested,outermost}`, `_open_mapping_nested`,
`_open_mapping_init`) consume the `_detail` lemmas here and ship in
sibling `Scenarios.lean`.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.EmitterScannability.Basic
open L4YAML.Proofs.Indexed.EmitterScannability.ScanChain
open L4YAML.Surface

variable {input : String}

/-! ## §1  State-level `ScannerSurfCorrIx` advance helpers

These wrappers project `ScannerSurfCorrIx` (which has the four-field
shape `chars_from`, `col_eq`, `input_prefix`, `indent_cols_nonneg`)
to the cursor-level `CursorSurfCorrIx` (three-field) and lift the
results back. The `indent_cols_nonneg` invariant transfers
unchanged through any update that preserves `s.indents`. -/

/-- `ScannerSurfCorrIx`-form of `peek_of_chars_consIx` (cursor-level
    twin in `Basic.lean:477`). When the surface position has a head
    character, the state's `peek?` matches and the cursor is in
    bounds. -/
theorem peek_of_chars_consIx_state (s : ScannerStateIx input) (c : Char)
    (rest : List Char) (col : Nat)
    (hcorr : ScannerSurfCorrIx s ⟨c :: rest, col⟩) :
    s.peek? = some c ∧ s.cursor.pos.offset < input.utf8ByteSize := by
  exact peek_of_chars_consIx s.cursor c rest col
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.input_prefix⟩

/-- `ScannerSurfCorrIx`-form of `advance_non_newline_corrIx`
    (cursor-level twin in `Basic.lean:509`). When the state's
    cursor advances past a non-newline character, the new state
    (assumed to share the same cursor as `s.cursor.advance` and the
    same indents) keeps surface correspondence. -/
theorem advance_non_newline_corrIx_state (s s' : ScannerStateIx input)
    (ch : Char) (rest : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨ch :: rest, s.cursor.pos.col⟩)
    (h_cur : s'.cursor = s.cursor.advance)
    (h_indents : s'.indents = s.indents)
    (hmore : s.cursor.pos.offset < input.utf8ByteSize)
    (hnl : ch ≠ '\n') (hcr : ch ≠ '\r') :
    ScannerSurfCorrIx s' ⟨rest, s.cursor.pos.col + 1⟩ := by
  have h_adv := advance_non_newline_corrIx s.cursor ch rest
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.input_prefix⟩ hmore hnl hcr
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_cur]; exact h_adv.chars_from
  · rw [h_cur]; exact h_adv.col_eq
  · rw [h_cur]; exact h_adv.input_prefix
  · intro i hi h0
    have hi' : i < s.indents.size := h_indents ▸ hi
    have heq : s'.indents[i]'hi = s.indents[i]'hi' := by congr 1
    rw [heq]; exact hcorr.indent_cols_nonneg i hi' h0

/-- `ScannerSurfCorrIx`-form of `advance_line_of_peekIx` (cursor-level
    twin in `Basic.lean:634`). When `peek?` matches a known non-newline
    char, advance preserves line. -/
theorem advance_line_of_peekIx_state (s : ScannerStateIx input) (ch : Char)
    (h_lt : s.cursor.pos.offset < input.utf8ByteSize)
    (h_peek : s.peek? = some ch)
    (hnl : ch ≠ '\n') (hcr : ch ≠ '\r') :
    s.advance.cursor.pos.line = s.cursor.pos.line := by
  show s.cursor.advance.pos.line = s.cursor.pos.line
  exact advance_line_of_peekIx s.cursor ch h_lt h_peek hnl hcr

/-! ## §2  `scanFlowSequenceStartIx_detail`

Combines surface-correspondence advance past `'['` with field
preservation simp lemmas from `.maintenance.flowdispatch` §1. -/

/-- `scanFlowSequenceStartIx` advances past `[`, giving specific
    `ScannerSurfCorrIx` at the rest and bundled field preservation.
    Indexed twin of `scanFlowSequenceStart_detail` (legacy 3817). -/
theorem scanFlowSequenceStartIx_detail (s : ScannerStateIx input)
    (rest : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨'[' :: rest, s.cursor.pos.col⟩) :
    ScannerSurfCorrIx (scanFlowSequenceStartIx s) ⟨rest, s.cursor.pos.col + 1⟩
    ∧ (scanFlowSequenceStartIx s).flowLevel = s.flowLevel + 1
    ∧ (scanFlowSequenceStartIx s).directivesPresent = s.directivesPresent
    ∧ (scanFlowSequenceStartIx s).indents = s.indents
    ∧ (scanFlowSequenceStartIx s).cursor.pos.col = s.cursor.pos.col + 1 := by
  have ⟨_, h_lt⟩ := peek_of_chars_consIx_state s '[' rest _ hcorr
  have h_cur_eq : (scanFlowSequenceStartIx s).cursor = s.cursor.advance := by
    unfold scanFlowSequenceStartIx
    show (((s.emit YamlToken.flowSequenceStart).advance).cursor) = _
    rw [advance_cursor, emit_cursor]
  have h_ind_eq : (scanFlowSequenceStartIx s).indents = s.indents :=
    scanFlowSequenceStartIx_indents s
  have h_corr_final := advance_non_newline_corrIx_state s (scanFlowSequenceStartIx s)
    '[' rest hcorr h_cur_eq h_ind_eq h_lt (by decide) (by decide)
  exact ⟨h_corr_final,
         scanFlowSequenceStartIx_flowLevel_eq s,
         scanFlowSequenceStartIx_directivesPresent s,
         h_ind_eq,
         h_corr_final.col_eq.symm⟩

/-! ## §3  `scanFlowMappingStartIx_detail` -/

/-- `scanFlowMappingStartIx` advances past `{`, mirror of §2.
    Indexed twin of `scanFlowMappingStart_detail` (legacy 5032). -/
theorem scanFlowMappingStartIx_detail (s : ScannerStateIx input)
    (rest : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨'{' :: rest, s.cursor.pos.col⟩) :
    ScannerSurfCorrIx (scanFlowMappingStartIx s) ⟨rest, s.cursor.pos.col + 1⟩
    ∧ (scanFlowMappingStartIx s).flowLevel = s.flowLevel + 1
    ∧ (scanFlowMappingStartIx s).directivesPresent = s.directivesPresent
    ∧ (scanFlowMappingStartIx s).indents = s.indents
    ∧ (scanFlowMappingStartIx s).cursor.pos.col = s.cursor.pos.col + 1 := by
  have ⟨_, h_lt⟩ := peek_of_chars_consIx_state s '{' rest _ hcorr
  have h_cur_eq : (scanFlowMappingStartIx s).cursor = s.cursor.advance := by
    unfold scanFlowMappingStartIx
    show (((s.emit YamlToken.flowMappingStart).advance).cursor) = _
    rw [advance_cursor, emit_cursor]
  have h_ind_eq : (scanFlowMappingStartIx s).indents = s.indents :=
    scanFlowMappingStartIx_indents s
  have h_corr_final := advance_non_newline_corrIx_state s (scanFlowMappingStartIx s)
    '{' rest hcorr h_cur_eq h_ind_eq h_lt (by decide) (by decide)
  exact ⟨h_corr_final,
         scanFlowMappingStartIx_flowLevel_eq s,
         scanFlowMappingStartIx_directivesPresent s,
         h_ind_eq,
         h_corr_final.col_eq.symm⟩

/-! ## §4  `scanFlowSequenceEndIx_detail` + `_lastRealTokenValIx` + `_peek` -/

/-- `scanFlowSequenceEndIx` advances past `]`, decrementing
    `flowLevel`. Indexed twin of `scanFlowSequenceEnd_detail`
    (legacy 4711). -/
theorem scanFlowSequenceEndIx_detail (s : ScannerStateIx input)
    (rest : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨']' :: rest, s.cursor.pos.col⟩) :
    ScannerSurfCorrIx (scanFlowSequenceEndIx s) ⟨rest, s.cursor.pos.col + 1⟩
    ∧ (scanFlowSequenceEndIx s).flowLevel = s.flowLevel - 1
    ∧ (scanFlowSequenceEndIx s).directivesPresent = s.directivesPresent
    ∧ (scanFlowSequenceEndIx s).indents = s.indents
    ∧ (scanFlowSequenceEndIx s).cursor.pos.col = s.cursor.pos.col + 1 := by
  have ⟨_, h_lt⟩ := peek_of_chars_consIx_state s ']' rest _ hcorr
  have h_cur_eq : (scanFlowSequenceEndIx s).cursor = s.cursor.advance := by
    unfold scanFlowSequenceEndIx
    show (((s.emit YamlToken.flowSequenceEnd).advance).cursor) = _
    rw [advance_cursor, emit_cursor]
  have h_ind_eq : (scanFlowSequenceEndIx s).indents = s.indents :=
    scanFlowSequenceEndIx_indents s
  have h_corr_final := advance_non_newline_corrIx_state s (scanFlowSequenceEndIx s)
    ']' rest hcorr h_cur_eq h_ind_eq h_lt (by decide) (by decide)
  exact ⟨h_corr_final,
         scanFlowSequenceEndIx_flowLevel_eq s,
         scanFlowSequenceEndIx_directivesPresent s,
         h_ind_eq,
         h_corr_final.col_eq.symm⟩

/-- Token property: `scanFlowSequenceEndIx` ends with `.flowSequenceEnd`
    as last real token. Indexed twin of `scanFlowSequenceEnd_
    lastRealTokenVal` (legacy 4736). -/
theorem scanFlowSequenceEndIx_lastRealTokenValIx (s : ScannerStateIx input) :
    lastRealTokenValIx? (scanFlowSequenceEndIx s).tokens = some YamlToken.flowSequenceEnd := by
  unfold scanFlowSequenceEndIx
  show lastRealTokenValIx? ((s.emit YamlToken.flowSequenceEnd).advance).tokens = _
  rw [advance_tokens]
  show lastRealTokenValIx? (s.tokens.push _) = _
  exact lastRealTokenValIx_push_non_ph s.tokens _ nofun

/-- `scanFlowSequenceEndIx` preserves `peek?` from the underlying
    advance. Indexed twin of `scanFlowSequenceEnd_peek` (legacy 4912). -/
theorem scanFlowSequenceEndIx_peek (s : ScannerStateIx input) :
    (scanFlowSequenceEndIx s).peek? = (s.emit YamlToken.flowSequenceEnd).advance.peek? := by
  unfold scanFlowSequenceEndIx
  rfl

/-! ## §5  `scanFlowMappingEndIx_detail` + `_lastRealTokenValIx` + `_peek` -/

/-- `scanFlowMappingEndIx` advances past `}`, decrementing `flowLevel`.
    Indexed twin of `scanFlowMappingEnd_detail` (legacy 5085). -/
theorem scanFlowMappingEndIx_detail (s : ScannerStateIx input)
    (rest : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨'}' :: rest, s.cursor.pos.col⟩) :
    ScannerSurfCorrIx (scanFlowMappingEndIx s) ⟨rest, s.cursor.pos.col + 1⟩
    ∧ (scanFlowMappingEndIx s).flowLevel = s.flowLevel - 1
    ∧ (scanFlowMappingEndIx s).directivesPresent = s.directivesPresent
    ∧ (scanFlowMappingEndIx s).indents = s.indents
    ∧ (scanFlowMappingEndIx s).cursor.pos.col = s.cursor.pos.col + 1 := by
  have ⟨_, h_lt⟩ := peek_of_chars_consIx_state s '}' rest _ hcorr
  have h_cur_eq : (scanFlowMappingEndIx s).cursor = s.cursor.advance := by
    unfold scanFlowMappingEndIx
    show (((s.emit YamlToken.flowMappingEnd).advance).cursor) = _
    rw [advance_cursor, emit_cursor]
  have h_ind_eq : (scanFlowMappingEndIx s).indents = s.indents :=
    scanFlowMappingEndIx_indents s
  have h_corr_final := advance_non_newline_corrIx_state s (scanFlowMappingEndIx s)
    '}' rest hcorr h_cur_eq h_ind_eq h_lt (by decide) (by decide)
  exact ⟨h_corr_final,
         scanFlowMappingEndIx_flowLevel_eq s,
         scanFlowMappingEndIx_directivesPresent s,
         h_ind_eq,
         h_corr_final.col_eq.symm⟩

/-- Token property: `scanFlowMappingEndIx` ends with `.flowMappingEnd`
    as last real token. Indexed twin of `scanFlowMappingEnd_
    lastRealTokenVal` (legacy 5107). -/
theorem scanFlowMappingEndIx_lastRealTokenValIx (s : ScannerStateIx input) :
    lastRealTokenValIx? (scanFlowMappingEndIx s).tokens = some YamlToken.flowMappingEnd := by
  unfold scanFlowMappingEndIx
  show lastRealTokenValIx? ((s.emit YamlToken.flowMappingEnd).advance).tokens = _
  rw [advance_tokens]
  show lastRealTokenValIx? (s.tokens.push _) = _
  exact lastRealTokenValIx_push_non_ph s.tokens _ nofun

/-- `scanFlowMappingEndIx` preserves `peek?` from the underlying
    advance. Indexed twin of `scanFlowMappingEnd_peek` (legacy 5115). -/
theorem scanFlowMappingEndIx_peek (s : ScannerStateIx input) :
    (scanFlowMappingEndIx s).peek? = (s.emit YamlToken.flowMappingEnd).advance.peek? := by
  unfold scanFlowMappingEndIx
  rfl

/-! ## §6  `scanFlowEntryIx_detail`

Composes `scanFlowEntryIx_ok` (precondition: no trailing flow
delimiter — already in `.maintenance.pipeline` §5) with surface
correspondence advance past `,`. -/

/-- Field preservation + ScannerSurfCorrIx through `scanFlowEntryIx`.
    Indexed twin of `scanFlowEntry_detail` (legacy 4424). -/
theorem scanFlowEntryIx_detail (s : ScannerStateIx input) (rest : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨',' :: rest, s.cursor.pos.col⟩)
    (h_last : ∀ t, lastRealTokenValIx? s.tokens = some t →
      t ≠ YamlToken.flowSequenceStart ∧ t ≠ YamlToken.flowMappingStart
      ∧ t ≠ YamlToken.flowEntry) :
    scanFlowEntryIx s =
      .ok { (s.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }
    ∧ ScannerSurfCorrIx
        { (s.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }
        ⟨rest, s.cursor.pos.col + 1⟩
    ∧ ({ (s.emit YamlToken.flowEntry).advance with
            simpleKeyAllowed := true } : ScannerStateIx input).flowLevel = s.flowLevel
    ∧ ({ (s.emit YamlToken.flowEntry).advance with
            simpleKeyAllowed := true } : ScannerStateIx input).directivesPresent
          = s.directivesPresent
    ∧ ({ (s.emit YamlToken.flowEntry).advance with
            simpleKeyAllowed := true } : ScannerStateIx input).indents = s.indents
    ∧ ({ (s.emit YamlToken.flowEntry).advance with
            simpleKeyAllowed := true } : ScannerStateIx input).cursor.pos.col
          = s.cursor.pos.col + 1 := by
  have h_ok := scanFlowEntryIx_ok s h_last
  have ⟨_, h_lt⟩ := peek_of_chars_consIx_state s ',' rest _ hcorr
  -- Field equalities for the witness state
  have h_cur_eq : ({ (s.emit YamlToken.flowEntry).advance with
        simpleKeyAllowed := true } : ScannerStateIx input).cursor = s.cursor.advance := by
    show (s.emit YamlToken.flowEntry).advance.cursor = s.cursor.advance
    rw [advance_cursor, emit_cursor]
  have h_ind_eq : ({ (s.emit YamlToken.flowEntry).advance with
        simpleKeyAllowed := true } : ScannerStateIx input).indents = s.indents := by
    show (s.emit YamlToken.flowEntry).advance.indents = s.indents
    rfl
  have h_corr_final := advance_non_newline_corrIx_state s
    { (s.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }
    ',' rest hcorr h_cur_eq h_ind_eq h_lt (by decide) (by decide)
  refine ⟨h_ok, h_corr_final, ?_, ?_, h_ind_eq, ?_⟩
  · show (s.emit YamlToken.flowEntry).advance.flowLevel = s.flowLevel
    rw [advance_flowLevel, emit_flowLevel]
  · show (s.emit YamlToken.flowEntry).advance.directivesPresent = s.directivesPresent
    rfl
  · exact h_corr_final.col_eq.symm

end L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
