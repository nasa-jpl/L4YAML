/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.Basic
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness
import L4YAML.Proofs.Scanner.IndexedScannerProgress
import L4YAML.Proofs.Coupling.CouplingBridge
import L4YAML.Output.Emitter

/-! # `IndexedEmitterScannability.ScanChain` — Phase 3 Step 6f.3b3 staging

**Status**: staging file, fully populated through §3. §1 ports the
legacy §3 prelude *utility lemmas* (lines 842–1184 of
`Proofs/Output/EmitterScannability.lean`); §2 ports the `ScanChain`
inductive + helpers (legacy lines 1185–1232 + 1261–1280). §3 lifts
the strict-progress capstone (`scanNextTokenIx_progress` from
`Proofs/Scanner/IndexedScannerProgress.lean` §7) into the
`ScanChainIx.bound_invariant` strict form and `ScanChainIx.fuel_bound`
(legacy lines 1281–1303).

## Scope of §1 (utility slice, landed 2026-05-24)

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

## Scope of §2 (chain slice, this session)

  - **§2.0** — `ScanChainIx` inductive: `n` consecutive successful
    `scanNextTokenIx` steps from `s` to `s'`. Twin of legacy
    `ScanChain` (line 1185).
  - **§2.1** — Combinators: `.trans` / `.single`.
  - **§2.2** — `scanLoopIx` connection: `.to_scanLoopIx` /
    `.to_scanLoopIx_exists`.
  - **§2.3** — Weak offset/bound invariants. The indexed substrate's
    `IxCursor.posBound` field subsumes legacy `inputEnd`/`input`/
    `IsValid` bookkeeping; `scanNextTokenIx_offset_monotonic`
    (`IndexedDispatch.lean:1608`) is the only "preservation"
    needed. The legacy `scanNextToken_preserves_bound` (line 1251)
    becomes vacuous — no theorem needed, replaced by direct
    `posBound` projection. `.offset_monotonic_weak` gives the
    `s_final.offset ≥ s₀.offset` form (no strict-progress needed).

## Scope of §3 (strict-progress + fuel bound, this session)

  - **§3.0** — `ScanChainIx.bound_invariant` strict form: combine
    `ScanChainIx.offset_bounded` (§2.3) with the strict-progress
    capstone (`Proofs/Scanner/IndexedScannerProgress.lean` §7) to
    derive `s_final.offset ≥ s₀.offset + n`.
  - **§3.1** — `ScanChainIx.fuel_bound`: chain the strict bound
    with the cursor's `posBound` to derive
    `n + 1 ≤ (input.utf8ByteSize + 1) * 4`. The indexed version
    drops the legacy `h_le`/`h_ie`/`h_iv` preconditions: all four
    legacy invariants (`offset ≤ inputEnd`, `inputEnd = utf8ByteSize`,
    `IsValid s.input ⟨offset⟩`, `s_final.input = s₀.input`) are
    either structural in the indexed substrate or carried by
    `IxCursor.posBound`.

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
lemma skipToContentS_atEnd (s : ScannerStateIx input)
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
lemma scanNextTokenIx_preprocess_eof (s : ScannerStateIx input)
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
lemma scanNextTokenIx_eof (s : ScannerStateIx input)
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
lemma scanLoopIx_step_eq {s₀ s₁ : ScannerStateIx input} {fuel : Nat}
    {ts : Indexed.TokenStream input}
    (h_snt : scanNextTokenIx s₀ = .ok (some s₁))
    (h_loop : scanLoopIx s₁ fuel = .ok ts) :
    scanLoopIx s₀ (fuel + 1) = .ok ts := by
  unfold scanLoopIx
  rw [h_snt]
  exact h_loop

/-- **Forward step (existential)**: existential variant of
    `scanLoopIx_step_eq`. -/
lemma scanLoopIx_step {s₀ s₁ : ScannerStateIx input} {fuel : Nat}
    (h_snt : scanNextTokenIx s₀ = .ok (some s₁))
    (h_loop : ∃ ts, scanLoopIx s₁ fuel = .ok ts) :
    ∃ ts, scanLoopIx s₀ (fuel + 1) = .ok ts := by
  obtain ⟨ts, h⟩ := h_loop
  exact ⟨ts, scanLoopIx_step_eq h_snt h⟩

/-- **Fuel monotonicity**: `scanLoopIx` success with `fuel₁` lifts to
    any larger fuel `fuel₂ ≥ fuel₁`. Mirrors legacy
    `scanLoop_fuel_mono`. -/
lemma scanLoopIx_fuel_mono {s : ScannerStateIx input} {fuel₁ fuel₂ : Nat}
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
lemma scanLoopIx_two_iter {s₀ s₁ : ScannerStateIx input} {fuel : Nat}
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
    have h_dp_check : ¬ s₁.directivesPresent = true := by
      simp [h_dp]
    rw [if_neg h_dp_check]
    exact ⟨_, rfl⟩
  rw [h1]; exact h2

/-- **Two-iteration (equality)**: computational variant of
    `scanLoopIx_two_iter`. -/
lemma scanLoopIx_two_iter_eq {s₀ s₁ : ScannerStateIx input} {fuel : Nat}
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
  have h_dp_check : ¬ s₁.directivesPresent = true := by
    simp [h_dp]
  rw [if_neg h_dp_check]

/-- **Terminal step (existential)**: at EOF (and with the no-error
    preconditions on `flowLevel` and `directivesPresent`),
    `scanLoopIx s 1` succeeds. -/
lemma scanLoopIx_eof {s : ScannerStateIx input}
    (h_snt : scanNextTokenIx s = .ok none)
    (h_fl : s.flowLevel = 0)
    (h_dp : s.directivesPresent = false) :
    ∃ ts, scanLoopIx s 1 = .ok ts := by
  unfold scanLoopIx
  rw [h_snt]
  have h_flow_not : ¬ s.flowLevel > 0 := by omega
  rw [if_neg h_flow_not]
  have h_dp_check : ¬ s.directivesPresent = true := by
    simp [h_dp]
  rw [if_neg h_dp_check]
  exact ⟨_, rfl⟩

/-- **Terminal step (equality)**: at EOF, `scanLoopIx` produces
    exactly the unwound + `streamEnd` token stream. -/
lemma scanLoopIx_eof_eq {s : ScannerStateIx input} {fuel : Nat}
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
  have h_dp_check : ¬ s.directivesPresent = true := by
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
lemma peek_none_of_empty_surfIx (sc : ScannerStateIx input) (col : Nat)
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
lemma ScannerSurfCorrIx_transfer {sc sc' : ScannerStateIx input} {sp : SurfPos}
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
lemma dispatchContentIx_quote (s : ScannerStateIx input) (c : Char) (hc : c = '"')
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
    simp [ScannerStateIx.inFlow, h_notFlow, h_noDocStart, h_noDocEnd, pure, Except.pure]
  · -- checkBlockFlowIndent: currentIndent = -1 < 0, condition false
    unfold scanNextTokenIx_checkBlockFlowIndent
    simp [ScannerStateIx.inFlow, h_notFlow, h_indent]
  · -- dispatchFlowIndicators: '"' doesn't match [, ], {, }, ,
    unfold scanNextTokenIx_dispatchFlowIndicators
    simp [pure, Except.pure]
  · -- dispatchBlockIndicators: '"' doesn't match -, ?, :
    unfold scanNextTokenIx_dispatchBlockIndicators
    simp [pure, Except.pure]

/-! ## §1.5  `emitScalar` value-level lemmas

Pure facts about `Output.Emitter.emitScalar` — no scanner involvement.
Ported verbatim from legacy `emitScalar_toList` /
`emitScalar_utf8ByteSize_ge` (lines 1058–1070). -/

/-- `emitScalar content` decomposes as `'"' :: escapeString content :: '"'`. -/
lemma emitScalar_toList (content : String) :
    (L4YAML.Emit.emitScalar content).toList
      = ['"'] ++ (L4YAML.Emit.escapeString content).toList ++ ['"'] := by
  have h1 : ("\"" : String).toList = ['"'] := by native_decide
  show (("\"" ++ L4YAML.Emit.escapeString content) ++ "\"").toList = _
  simp only [String.toList_append, h1]

/-- `emitScalar content` has at least 2 bytes (the two `'"'` delimiters). -/
lemma emitScalar_utf8ByteSize_ge (content : String) :
    (L4YAML.Emit.emitScalar content).utf8ByteSize ≥ 2 := by
  simp only [utf8ByteSize_eq_listByteSize, emitScalar_toList,
             listByteSize_append, listByteSize]
  have : Char.utf8Size '"' = 1 := by native_decide
  omega

/-! ## §2  `ScanChainIx` — n-step scan chains

Indexed twin of legacy `ScanChain` (lines 1185–1232 + 1261–1280 of
`Proofs/Output/EmitterScannability.lean`). Captures the fact that
`n` successive `scanNextTokenIx` calls each return `.ok (some ...)`,
threading an intermediate state through to the final state `s'`.

**Differences from legacy `ScanChain`**:

  - The `input : String` parameter is type-level (lifted into
    `ScannerStateIx input`), so both endpoints share the same input
    by construction. Legacy needs `s.input = s'.input` as a
    derivable conclusion; here it is structural.
  - The cursor's `posBound` field guarantees
    `pos.offset ≤ input.utf8ByteSize` for free, so legacy's
    `scanNextToken_preserves_bound` is vacuous — no indexed twin
    needed.
  - `.fuel_bound` requires *strict* progress (`offset < offset`),
    not yet ported (see `.internals.progress` slice). The weak
    `.offset_monotonic_weak` (using
    `scanNextTokenIx_offset_monotonic`) is what we can land here. -/

/-- `ScanChainIx s n s'` means `n` successive `scanNextTokenIx` calls
    starting from `s` each return `.ok (some ...)`, with the final
    state being `s'`. Indexed twin of `ScanChain`. -/
inductive ScanChainIx {input : String} :
    ScannerStateIx input → Nat → ScannerStateIx input → Prop where
  | zero {s : ScannerStateIx input} : ScanChainIx s 0 s
  | step {s s_mid s' : ScannerStateIx input} {n : Nat} :
         scanNextTokenIx s = .ok (some s_mid) →
         ScanChainIx s_mid n s' →
         ScanChainIx s (n + 1) s'

/-! ### §2.1  Combinators (`.trans`, `.single`) -/

/-- Transitivity: concatenate two scan chains. Mirrors legacy
    `ScanChain.trans` (line 1193). -/
lemma ScanChainIx.trans {s₁ s₂ s₃ : ScannerStateIx input} {n₁ n₂ : Nat}
    (h1 : ScanChainIx s₁ n₁ s₂) (h2 : ScanChainIx s₂ n₂ s₃) :
    ScanChainIx s₁ (n₁ + n₂) s₃ := by
  induction h1 with
  | zero => simpa using h2
  | @step s s_mid s₂ k h_snt _h_rest ih =>
    have h_ih := ih h2
    have : k + 1 + n₂ = (k + n₂) + 1 := by omega
    rw [this]
    exact .step h_snt h_ih

/-- A single `scanNextTokenIx` step as a `ScanChainIx`. Mirrors
    legacy `ScanChain.single` (line 1205). -/
lemma ScanChainIx.single {s s' : ScannerStateIx input}
    (h : scanNextTokenIx s = .ok (some s')) :
    ScanChainIx s 1 s' :=
  .step h .zero

/-! ### §2.2  Connection to `scanLoopIx` -/

/-- If `n` steps succeed reaching `s'`, and `scanLoopIx s' fuel`
    succeeds, then `scanLoopIx s (fuel + n)` succeeds with the same
    result. Mirrors legacy `ScanChain.to_scanLoop` (line 1213). -/
lemma ScanChainIx.to_scanLoopIx {s s' : ScannerStateIx input}
    {n fuel : Nat} {ts : Indexed.TokenStream input}
    (h_chain : ScanChainIx s n s')
    (h_loop : scanLoopIx s' fuel = .ok ts) :
    scanLoopIx s (fuel + n) = .ok ts := by
  induction h_chain with
  | zero => exact h_loop
  | @step s s_mid s' k h_snt _h_rest ih =>
    have h_ih := ih h_loop
    have : fuel + (k + 1) = (fuel + k) + 1 := by omega
    rw [this]
    exact scanLoopIx_step_eq h_snt h_ih

/-- Existential variant of `.to_scanLoopIx`. Mirrors legacy
    `ScanChain.to_scanLoop_exists` (line 1227). -/
lemma ScanChainIx.to_scanLoopIx_exists {s s' : ScannerStateIx input}
    {n : Nat}
    (h_chain : ScanChainIx s n s')
    (h_loop : ∃ fuel ts, scanLoopIx s' fuel = .ok ts) :
    ∃ fuel ts, scanLoopIx s fuel = .ok ts := by
  obtain ⟨fuel, ts, h⟩ := h_loop
  exact ⟨fuel + n, ts, h_chain.to_scanLoopIx h⟩

/-! ### §2.3  Weak offset/bound invariants

Legacy's `scanNextToken_preserves_bound` (line 1251) tracks
`offset ≤ inputEnd`, `inputEnd = input.utf8ByteSize`,
`input = input`, and `IsValid`. In the indexed substrate:
  - `inputEnd` does not exist (replaced by `input.utf8ByteSize`).
  - `input` is type-level (same for both endpoints by construction).
  - `pos.offset ≤ input.utf8ByteSize` is `IxCursor.posBound`.
  - `IsValid` is folded into the cursor's bound bookkeeping.

So the only non-trivial preservation needed is the offset
monotonicity already proved as
`scanNextTokenIx_offset_monotonic` in
`IndexedDispatch.lean:1608`. We lift it through the chain
inductively. -/

/-- A `ScanChainIx` weakly preserves offset monotonicity:
    `s_final.cursor.pos.offset ≥ s₀.cursor.pos.offset`.

    *Weak* form (no strict progress): the legacy
    `bound_invariant` (line 1261) would give
    `offset ≥ offset + n`, but that requires the strict-progress
    capstone `scanNextTokenIx_progress` which is not yet ported.
    See `.internals.progress` slice. -/
lemma ScanChainIx.offset_monotonic_weak {s₀ s_final : ScannerStateIx input}
    {n : Nat} (h_chain : ScanChainIx s₀ n s_final) :
    s_final.cursor.pos.offset ≥ s₀.cursor.pos.offset := by
  induction h_chain with
  | zero => exact Nat.le_refl _
  | @step s s_mid s' k h_snt _h_rest ih =>
    have h_step := scanNextTokenIx_offset_monotonic h_snt
    exact Nat.le_trans h_step ih

/-- A `ScanChainIx`'s final cursor offset is bounded by the input
    size. This is the indexed twin of legacy `bound_invariant`'s
    second conjunct (`offset ≤ inputEnd`); in the indexed substrate
    it is a direct projection of the cursor's `posBound` field. -/
lemma ScanChainIx.offset_bounded {s₀ s_final : ScannerStateIx input}
    {n : Nat} (_h_chain : ScanChainIx s₀ n s_final) :
    s_final.cursor.pos.offset ≤ input.utf8ByteSize :=
  s_final.cursor.posBound

/-! ## §3  Strict-progress bound invariant + fuel bound

Lifts `scanNextTokenIx_progress` (strict form, from
`Proofs/Scanner/IndexedScannerProgress.lean` §7) inductively along a
`ScanChainIx`, then derives `n + 1 ≤ (input.utf8ByteSize + 1) * 4`
which is the fuel `scanIx` provides to `scanLoopIx`. -/

/-- **Strict bound invariant**: an n-step `ScanChainIx` advances the
    cursor by at least `n` bytes. Indexed twin of legacy
    `ScanChain.bound_invariant`'s first conjunct
    (`Proofs/Output/EmitterScannability.lean:1261`). The legacy
    second/third conjuncts (`offset ≤ inputEnd`,
    `inputEnd = s₀.inputEnd`) are split off as
    `ScanChainIx.offset_bounded` (§2.3): in the indexed substrate the
    `inputEnd` field doesn't exist and `posBound` is structural. -/
lemma ScanChainIx.bound_invariant {s₀ s_final : ScannerStateIx input}
    {n : Nat} (h_chain : ScanChainIx s₀ n s_final) :
    s_final.cursor.pos.offset ≥ s₀.cursor.pos.offset + n := by
  induction h_chain with
  | zero => exact Nat.le_refl _
  | @step s s_mid s_final k h_snt _h_rest ih =>
    have h_prog := L4YAML.Proofs.Indexed.ScannerProgress.scanNextTokenIx_progress h_snt
    -- ih: s_final.cursor.pos.offset ≥ s_mid.cursor.pos.offset + k
    -- h_prog: s.cursor.pos.offset < s_mid.cursor.pos.offset
    omega

/-- **Fuel bound**: an n-step `ScanChainIx` from the initial state
    `s₀ = ScannerStateIx.mk' input |>.emit streamStart` followed by
    EOF satisfies `n + 1 ≤ (input.utf8ByteSize + 1) * 4`. This is the
    termination argument for `scanIx`'s fuel choice
    (`Scanner/IndexedDispatch.lean:1109`,
    `fuel := input.utf8ByteSize + 1; scanLoopIx s (fuel * 4)`).

    Indexed twin of legacy `ScanChain.fuel_bound`
    (`Proofs/Output/EmitterScannability.lean:1281`). The legacy version
    needs `h_le` / `h_ie` / `h_iv` preconditions that are all
    structural in the indexed substrate; only the `s₀ = mk'.emit ...`
    starting-shape and the chain itself are needed. -/
lemma ScanChainIx.fuel_bound (s₀ s_final : ScannerStateIx input)
    (n : Nat) (h_s0 : s₀ = (ScannerStateIx.mk' input).emit YamlToken.streamStart)
    (h_chain : ScanChainIx s₀ n s_final)
    (_h_eof : scanNextTokenIx s_final = .ok none) :
    n + 1 ≤ (input.utf8ByteSize + 1) * 4 := by
  have h_s0_off : s₀.cursor.pos.offset = 0 := by subst h_s0; rfl
  have h_ge : s_final.cursor.pos.offset ≥ s₀.cursor.pos.offset + n :=
    h_chain.bound_invariant
  have h_le : s_final.cursor.pos.offset ≤ input.utf8ByteSize :=
    h_chain.offset_bounded
  rw [h_s0_off] at h_ge
  -- h_ge : s_final.cursor.pos.offset ≥ n
  -- h_le : s_final.cursor.pos.offset ≤ input.utf8ByteSize
  -- ⟹  n ≤ input.utf8ByteSize ⟹  n + 1 ≤ (input.utf8ByteSize + 1) * 4
  omega

end L4YAML.Proofs.Indexed.EmitterScannability.ScanChain
