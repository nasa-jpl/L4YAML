/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.Basic
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness
import L4YAML.Proofs.Coupling.CouplingBridge
import L4YAML.Output.Emitter

/-! # `IndexedEmitterScannability.ScanChain` — Phase 3 Step 6f.3b3 staging

**Status**: staging file, partially populated. §1 below ports the legacy
§3 prelude *utility lemmas* (lines 842–1184 of
`Proofs/Output/EmitterScannability.lean`) to the indexed substrate.
The `ScanChainIx` inductive + helpers (legacy lines 1185–1306) lands in
a follow-up `.internals.chain` slice.

## Scope of §1 (this slice)

  - **§1.0** — EOF behaviour of skip-whitespace / skip-to-content
    (`skipToContentS_atEnd`).
  - **§1.1** — `scanNextTokenIx_eof`: `scanNextTokenIx` returns
    `.ok none` when the cursor is past end-of-input.
  - **§1.2** — `scanLoopIx` compositionality:
    `scanLoopIx_step[_eq]`, `scanLoopIx_fuel_mono`,
    `scanLoopIx_two_iter[_eq]`, `scanLoopIx_eof[_eq]`.
  - **§1.3** — `ScannerSurfCorrIx`: scanner-state ↔ surface-position
    correspondence (indexed twin of legacy
    `Proofs/Coupling/CouplingBridge.lean`'s `ScannerSurfCorr`),
    plus `peek_none_of_empty_surfIx` and `ScannerSurfCorrIx_transfer`.
  - **§1.4** — `dispatchContentIx_quote`: the dispatch chain for `'"'`
    falls through to `dispatchContent` (mirrors legacy
    `dispatchContent_quote`).
  - **§1.5** — `emitScalar_toList` / `emitScalar_utf8ByteSize_ge`:
    value-level facts about `Output.Emitter.emitScalar` reused by
    the scanner-acceptance proofs.

## Phase 3 Step 6f cutover

See `Basic.lean` for the directory-wide cutover plan.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.ScanChain

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Surface
open L4YAML.Proofs.CouplingBridge

variable {input : String}

/-! ## §1.0  EOF behaviour of `skipToContentS`

Cursor-level `skipToContent_atEnd` already lives at
`Proofs/Scanner/IndexedIndent.lean:193`. The state-level variant
needed for `scanNextTokenIx_eof` (and for the `scanLoopIx` chain
lemmas) is proved by combining `skipToContent_atEnd` with the
`skipToContentS` definitional unfold. -/

/-- When the cursor is at end-of-input, `skipToContentS` is the
    identity on the state. The cursor-level no-op
    (`L4YAML.Scanner.Indexed.skipToContent_atEnd`) implies the
    line counter does not advance, so `skipToContentS`'s
    "if-line-changed" branch never fires. -/
theorem skipToContentS_atEnd (s : ScannerStateIx input)
    (h : s.peek? = none) : s.skipToContentS = s := by
  unfold ScannerStateIx.skipToContentS
  have h_cur : L4YAML.Scanner.Indexed.skipToContent s.cursor = s.cursor :=
    L4YAML.Scanner.Indexed.skipToContent_atEnd s.cursor h
  rw [h_cur]
  simp

/-! ## §1.1  `scanNextTokenIx_eof`

`scanNextTokenIx` returns `.ok none` at end-of-input. The preprocess
step's `skipToContentS` is a no-op (§1.0); the subsequent
`!s.hasMore` test short-circuits to `.ok none`. -/

/-- The preprocess step returns `.ok none` at end-of-input. -/
theorem scanNextTokenIx_preprocess_eof (s : ScannerStateIx input)
    (h : s.peek? = none) :
    scanNextTokenIx_preprocess s = .ok none := by
  unfold scanNextTokenIx_preprocess
  rw [skipToContentS_atEnd s h]
  have h_not : ¬ s.cursor.pos.offset < input.utf8ByteSize := by
    have h_le : input.utf8ByteSize ≤ s.cursor.pos.offset :=
      (IxCursor.peek?_eq_none_iff s.cursor).mp h
    exact Nat.not_lt.mpr h_le
  have h_hm : s.hasMore = false := by
    show s.cursor.hasMore = false
    unfold IxCursor.hasMore
    simp [h_not]
  simp [h_hm]

/-- `scanNextTokenIx` returns `.ok none` at end-of-input. -/
theorem scanNextTokenIx_eof (s : ScannerStateIx input)
    (h : s.peek? = none) : scanNextTokenIx s = .ok none := by
  unfold scanNextTokenIx
  rw [scanNextTokenIx_preprocess_eof s h]
  rfl

/-! ## §1.2  `scanLoopIx` compositionality

Forward step (single + existential), fuel monotonicity, two-iteration
(`some` then `none`), and terminal (EOF) characterisations. The
indexed `scanLoopIx`'s EOF branch differs from legacy `scanLoop`:
`flowLevel > 0` is a hard error, and so is
`directivesPresent && !documentEverStarted`. The terminal lemmas
take the two preconditions explicitly. -/

/-- **Forward step (equality)**: If `scanNextTokenIx` produces a new
    state `s₁`, and `scanLoopIx s₁ fuel` succeeds with `ts`, then
    `scanLoopIx s₀ (fuel + 1)` succeeds with the same `ts`. -/
theorem scanLoopIx_step_eq {s₀ s₁ : ScannerStateIx input} {fuel : Nat}
    {ts : Indexed.TokenStream input}
    (h_snt : scanNextTokenIx s₀ = .ok (some s₁))
    (h_loop : scanLoopIx s₁ fuel = .ok ts) :
    scanLoopIx s₀ (fuel + 1) = .ok ts := by
  unfold scanLoopIx
  rw [h_snt]
  exact h_loop

/-- **Forward step (existential)**: existential variant of
    `scanLoopIx_step_eq`. -/
theorem scanLoopIx_step {s₀ s₁ : ScannerStateIx input} {fuel : Nat}
    (h_snt : scanNextTokenIx s₀ = .ok (some s₁))
    (h_loop : ∃ ts, scanLoopIx s₁ fuel = .ok ts) :
    ∃ ts, scanLoopIx s₀ (fuel + 1) = .ok ts := by
  obtain ⟨ts, h⟩ := h_loop
  exact ⟨ts, scanLoopIx_step_eq h_snt h⟩

/-- **Fuel monotonicity**: `scanLoopIx` success with `fuel₁` lifts to
    any larger fuel `fuel₂ ≥ fuel₁`. Mirrors legacy
    `scanLoop_fuel_mono`. -/
theorem scanLoopIx_fuel_mono {s : ScannerStateIx input} {fuel₁ fuel₂ : Nat}
    {ts : Indexed.TokenStream input}
    (h : scanLoopIx s fuel₁ = .ok ts) (h_le : fuel₁ ≤ fuel₂) :
    scanLoopIx s fuel₂ = .ok ts := by
  induction fuel₁ generalizing s fuel₂ ts with
  | zero =>
    unfold scanLoopIx at h
    cases h
  | succ m IH =>
    obtain ⟨n, rfl⟩ : ∃ n, fuel₂ = n + 1 := ⟨fuel₂ - 1, by omega⟩
    unfold scanLoopIx at h ⊢
    cases hSc : scanNextTokenIx s with
    | error e => rw [hSc] at h; cases h
    | ok res =>
      rw [hSc] at h
      cases res with
      | none => exact h
      | some s' => exact IH h (by omega)

/-- **Two-iteration (existential)**: a `some` step followed by an
    `none` step (with the trailing state satisfying the EOF
    preconditions) gives `scanLoopIx s₀ fuel = .ok _` for any `fuel ≥ 2`. -/
theorem scanLoopIx_two_iter {s₀ s₁ : ScannerStateIx input} {fuel : Nat}
    (h_fuel : fuel ≥ 2)
    (h_snt0 : scanNextTokenIx s₀ = .ok (some s₁))
    (h_snt1 : scanNextTokenIx s₁ = .ok none)
    (h_flow : s₁.flowLevel = 0)
    (h_dp : s₁.directivesPresent = false) :
    ∃ ts, scanLoopIx s₀ fuel = .ok ts := by
  obtain ⟨f, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  -- One step: scanLoopIx s₀ (f+2) = scanLoopIx s₁ (f+1).
  have h1 : scanLoopIx s₀ (f + 2) = scanLoopIx s₁ (f + 1) := by
    simp only [scanLoopIx, h_snt0]
  -- Terminal step: scanLoopIx s₁ (f+1) succeeds.
  have h2 : ∃ ts, scanLoopIx s₁ (f + 1) = .ok ts := by
    unfold scanLoopIx
    rw [h_snt1]
    have h_flow_not : ¬ s₁.flowLevel > 0 := by omega
    rw [if_neg h_flow_not]
    have h_dp_check : ¬ (s₁.directivesPresent && !s₁.documentEverStarted) = true := by
      simp [h_dp]
    rw [if_neg h_dp_check]
    exact ⟨_, rfl⟩
  rw [h1]; exact h2

/-- **Two-iteration (equality)**: computational variant of
    `scanLoopIx_two_iter`. -/
theorem scanLoopIx_two_iter_eq {s₀ s₁ : ScannerStateIx input} {fuel : Nat}
    (h_fuel : fuel ≥ 2)
    (h_snt0 : scanNextTokenIx s₀ = .ok (some s₁))
    (h_snt1 : scanNextTokenIx s₁ = .ok none)
    (h_flow : s₁.flowLevel = 0)
    (h_dp : s₁.directivesPresent = false) :
    scanLoopIx s₀ fuel = .ok ((unwindIndentsIx s₁ (-1)).emit YamlToken.streamEnd).tokens := by
  obtain ⟨f, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  have h_step : scanLoopIx s₀ (f + 2) = scanLoopIx s₁ (f + 1) := by
    simp only [scanLoopIx, h_snt0]
  rw [h_step]
  unfold scanLoopIx
  rw [h_snt1]
  have h_flow_not : ¬ s₁.flowLevel > 0 := by omega
  rw [if_neg h_flow_not]
  have h_dp_check : ¬ (s₁.directivesPresent && !s₁.documentEverStarted) = true := by
    simp [h_dp]
  rw [if_neg h_dp_check]

/-- **Terminal step (existential)**: at EOF (and with the no-error
    preconditions on `flowLevel` and `directivesPresent`),
    `scanLoopIx s 1` succeeds. -/
theorem scanLoopIx_eof {s : ScannerStateIx input}
    (h_snt : scanNextTokenIx s = .ok none)
    (h_fl : s.flowLevel = 0)
    (h_dp : s.directivesPresent = false) :
    ∃ ts, scanLoopIx s 1 = .ok ts := by
  unfold scanLoopIx
  rw [h_snt]
  have h_flow_not : ¬ s.flowLevel > 0 := by omega
  rw [if_neg h_flow_not]
  have h_dp_check : ¬ (s.directivesPresent && !s.documentEverStarted) = true := by
    simp [h_dp]
  rw [if_neg h_dp_check]
  exact ⟨_, rfl⟩

/-- **Terminal step (equality)**: at EOF, `scanLoopIx` produces
    exactly the unwound + `streamEnd` token stream. -/
theorem scanLoopIx_eof_eq {s : ScannerStateIx input} {fuel : Nat}
    (h_fuel : fuel ≥ 1)
    (h_snt : scanNextTokenIx s = .ok none)
    (h_fl : s.flowLevel = 0)
    (h_dp : s.directivesPresent = false) :
    scanLoopIx s fuel = .ok ((unwindIndentsIx s (-1)).emit YamlToken.streamEnd).tokens := by
  obtain ⟨f, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  unfold scanLoopIx
  rw [h_snt]
  have h_flow_not : ¬ s.flowLevel > 0 := by omega
  rw [if_neg h_flow_not]
  have h_dp_check : ¬ (s.directivesPresent && !s.documentEverStarted) = true := by
    simp [h_dp]
  rw [if_neg h_dp_check]

/-! ## §1.3  Surface correspondence (`ScannerSurfCorrIx`)

Indexed twin of legacy `Proofs/Coupling/CouplingBridge.lean`'s
`ScannerSurfCorr`. Whereas the legacy version carries an `end_eq`
field (`sc.inputEnd = sc.input.utf8ByteSize`), the indexed version
folds that obligation into the `IxCursor`'s `posBound` invariant —
the type-level `input` parameter is the canonical input string, so
no field is needed to identify it. -/

/-- Scanner state and surface position correspond when the remaining
    characters match, columns agree, and the offset is at a valid
    UTF-8 boundary (witnessed by `input_prefix`). Indexed twin of
    `ScannerSurfCorr` (`Proofs/Coupling/CouplingBridge.lean:212`). -/
structure ScannerSurfCorrIx {input : String} (sc : ScannerStateIx input)
    (sp : SurfPos) : Prop where
  chars_from : CharsFromOffset input sc.cursor.pos.offset sp.chars
  col_eq : sp.col = sc.cursor.pos.col
  input_prefix : ∃ pre, input.toList = pre ++ sp.chars ∧ listByteSize pre = sc.cursor.pos.offset
  indent_cols_nonneg :
    ∀ (i : Nat) (hi : i < sc.indents.size), i > 0 → sc.indents[i].column ≥ 0

/-- If the surface position has empty remaining chars, then `peek? = none`. -/
theorem peek_none_of_empty_surfIx (sc : ScannerStateIx input) (col : Nat)
    (hcorr : ScannerSurfCorrIx sc ⟨[], col⟩) :
    sc.peek? = none := by
  have h_ge : input.utf8ByteSize ≤ sc.cursor.pos.offset :=
    match hcorr.chars_from with | .at_end _ h => h
  show sc.cursor.peek? = none
  exact (IxCursor.peek?_eq_none_iff sc.cursor).mpr h_ge

/-- Transfer `ScannerSurfCorrIx` when only non-position fields change
    (tokens, simple key, flags, etc.). Mirrors legacy
    `ScannerSurfCorr_transfer`; the `input` parameter is type-level
    so no `input` field needs to match. -/
theorem ScannerSurfCorrIx_transfer {sc sc' : ScannerStateIx input} {sp : SurfPos}
    (hcorr : ScannerSurfCorrIx sc sp)
    (h_offset : sc'.cursor.pos.offset = sc.cursor.pos.offset)
    (h_col : sc'.cursor.pos.col = sc.cursor.pos.col)
    (h_indents : sc'.indents = sc.indents) :
    ScannerSurfCorrIx sc' sp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_offset]; exact hcorr.chars_from
  · rw [h_col]; exact hcorr.col_eq
  · obtain ⟨pre, hpre, hsize⟩ := hcorr.input_prefix
    exact ⟨pre, hpre, by rw [h_offset]; exact hsize⟩
  · intro i hi h0
    have hi' : i < sc.indents.size := h_indents ▸ hi
    have heq : sc'.indents[i]'hi = sc.indents[i]'hi' := by congr 1
    rw [heq]; exact hcorr.indent_cols_nonneg i hi' h0

/-! ## §1.4  `dispatchContentIx_quote`

The dispatch chain on `'"'` (at the stream-level prefix: not in flow,
indent = -1, not at a document marker) returns `none` from every
upstream dispatcher, so control falls through to
`dispatchContent`. Mirrors legacy `dispatchContent_quote`. -/

/-- For `'"'` at the stream prefix (no flow, no indent, no document
    marker), each of the four upstream dispatchers returns the no-op
    result, so `scanNextTokenIx` ultimately reaches
    `dispatchContent`. -/
theorem dispatchContentIx_quote (s : ScannerStateIx input) (c : Char) (hc : c = '"')
    (h_notFlow : s.flowLevel = 0)
    (h_indent : s.currentIndent = -1)
    (h_noDocStart : atDocumentStartIx s.cursor = false)
    (h_noDocEnd : atDocumentEndIx s.cursor = false) :
    scanNextTokenIx_dispatchStructural s c = .ok none
    ∧ scanNextTokenIx_checkBlockFlowIndent s c = .ok ()
    ∧ scanNextTokenIx_dispatchFlowIndicators s c = .ok none
    ∧ scanNextTokenIx_dispatchBlockIndicators s c = .ok none := by
  subst hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- dispatchStructural: '"' doesn't match %, ---, ...
    unfold scanNextTokenIx_dispatchStructural
    simp [ScannerStateIx.inFlow, h_notFlow, h_noDocStart, h_noDocEnd,
          bind, Except.bind, pure, Except.pure]
  · -- checkBlockFlowIndent: currentIndent = -1 < 0, condition false
    unfold scanNextTokenIx_checkBlockFlowIndent
    simp [ScannerStateIx.inFlow, h_notFlow, h_indent]
  · -- dispatchFlowIndicators: '"' doesn't match [, ], {, }, ,
    unfold scanNextTokenIx_dispatchFlowIndicators
    simp [bind, Except.bind, pure, Except.pure]
  · -- dispatchBlockIndicators: '"' doesn't match -, ?, :
    unfold scanNextTokenIx_dispatchBlockIndicators
    simp [bind, Except.bind, pure, Except.pure]

/-! ## §1.5  `emitScalar` value-level lemmas

Pure facts about `Output.Emitter.emitScalar` — no scanner involvement.
Ported verbatim from legacy `emitScalar_toList` /
`emitScalar_utf8ByteSize_ge` (lines 1058–1070). -/

/-- `emitScalar content` decomposes as `'"' :: escapeString content :: '"'`. -/
theorem emitScalar_toList (content : String) :
    (L4YAML.Emit.emitScalar content).toList
      = ['"'] ++ (L4YAML.Emit.escapeString content).toList ++ ['"'] := by
  have h1 : ("\"" : String).toList = ['"'] := by native_decide
  show (("\"" ++ L4YAML.Emit.escapeString content) ++ "\"").toList = _
  simp only [String.toList_append, h1]

/-- `emitScalar content` has at least 2 bytes (the two `'"'` delimiters). -/
theorem emitScalar_utf8ByteSize_ge (content : String) :
    (L4YAML.Emit.emitScalar content).utf8ByteSize ≥ 2 := by
  simp only [utf8ByteSize_eq_listByteSize, emitScalar_toList,
             listByteSize_append, listByteSize]
  have : Char.utf8Size '"' = 1 := by native_decide
  omega

end L4YAML.Proofs.Indexed.EmitterScannability.ScanChain
