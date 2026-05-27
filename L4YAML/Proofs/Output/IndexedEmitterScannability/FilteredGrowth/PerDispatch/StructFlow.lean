/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FilteredGrowth.Infra
import L4YAML.Proofs.Production.IndexedScannerPlainScalarValid

/-! # `FilteredGrowth.PerDispatch.StructFlow` — Phase 3 Step
`6f.3b3.filteredgrowth.perdispatch.structflow`

**Sub-session 1 of `.perdispatch`** (legacy
`Proofs/Output/EmitterScannability.lean` lines 6071–6362, ~292 LOC).

Per-dispatch-layer filtered growth lemmas for the **structural**
(document markers + directives) and **flow-indicator** dispatchers.
The companion sub-session `.blockcontent` will ship the block-
indicator + content dispatcher lemmas (legacy 6364–6757).

Ships:

  * **§0  Shape helpers** — small private `_tokens_eq` lemmas
    extracting each scanner's post-state `tokens` field as a single-
    push extension of its key predecessor. The simple ones are
    `rfl`; `scanDocumentEndIx`'s requires a case split on the
    trailing `do`-block probe (each successful arm collapses by
    `rfl` after `subst`).
  * **§1 `scanDocumentStart_filtered_growsIx`** — `≥ +1` for
    document-start (legacy 6075).
  * **§2 `scanDocumentEnd_filtered_growsIx`** — `≥ +1` for document-
    end (legacy 6092).
  * **§3 `scanYamlDirective_new_token_eqIx`** — YAML directive emits
    a non-`.placeholder` at the first new slot (legacy 6137).
  * **§4 `scanTagDirective_new_token_eqIx`** — TAG directive emits
    a non-`.placeholder` at the first new slot (legacy 6184).
  * **§5 `scanDirective_filtered_growsIx`** — `≥ +1` under
    `h_grew` (legacy 6232).
  * **§6 `dispatchStructural_filtered_monoIx`** — filter-monotone
    across all three sub-cases (legacy 6293).
  * **§7 `dispatchFlowIndicators_filtered_growsIx`** — `≥ +1` for
    each of `[`/`]`/`{`/`}`/`,` (legacy 6307).

## Indexed simplification

The `_ok_some_cases` helpers in `Proofs/Scanner/IndexedDispatch.lean`
exhaustively enumerate the post-state per branch — one `rcases`
replaces the legacy `repeat (any_goals split at h)` cascade. The
per-scanner `_preserves_prefix` lemmas discharge the existing-tokens
hypothesis. The §0 shape helpers collapse the record-update +
`advanceN` chain by Lean's definitional equality, so the new-token
claim reduces to `Array.getElem_push_eq` + `decide`.

The `TokenStream` ↔ `Array (IxToken)` defeq (Reflection 133) keeps
the bridge invisible — but `omega` doesn't reduce by defeq, so the
proofs explicitly `change` between `.tokens.size` (TokenStream-
level) and `.tokens.tokens.size` (Array-level) at the boundary.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.ScannerCorrectness
-- Selective open of the `_preserves_prefix` lemma family living in
-- `L4YAML.Proofs.Indexed.ScannerPlainScalarValid` (a full `open` would
-- shadow `Scanner.Indexed.emitAt_tokens_size` with an ambiguous copy).
open L4YAML.Proofs.Indexed.ScannerPlainScalarValid (
  scanDocumentStartIx_preserves_prefix
  scanDocumentEndIx_preserves_prefix
  scanDirectiveIx_preserves_prefix
  scanFlowSequenceStartIx_preserves_prefix
  scanFlowSequenceEndIx_preserves_prefix
  scanFlowMappingStartIx_preserves_prefix
  scanFlowMappingEndIx_preserves_prefix
  scanFlowEntryIx_preserves_prefix)

variable {input : String}

/-! ## §0  Shape helpers — extracting the pushed token's value -/

/-- `scanDocumentStartIx`'s `tokens` field equals
    `(unwindIndentsIx s (-1)).emit YamlToken.documentStart`'s tokens. -/
theorem scanDocumentStartIx_tokens_eq (s : ScannerStateIx input) :
    (scanDocumentStartIx s).tokens =
      ((unwindIndentsIx s (-1)).emit YamlToken.documentStart).tokens := rfl

/-- `scanDocumentEndIx`'s `tokens` field equals
    `(unwindIndentsIx s (-1)).emit YamlToken.documentEnd`'s tokens
    on every successful branch. -/
theorem scanDocumentEndIx_tokens_eq {s s' : ScannerStateIx input}
    (h : scanDocumentEndIx s = .ok s') :
    s'.tokens = ((unwindIndentsIx s (-1)).emit YamlToken.documentEnd).tokens := by
  unfold scanDocumentEndIx at h
  by_cases hd : (s.directivesPresent && !s.documentEverStarted) = true
  · rw [if_pos hd] at h; simp [Bind.bind, Except.bind] at h
  · rw [if_neg hd] at h
    simp only [pure_bind] at h
    split at h
    all_goals first
      | (simp only [Except.ok.injEq] at h; subst h; rfl)
      | (split at h
         all_goals first
           | (simp only [Except.ok.injEq] at h; subst h; rfl)
           | (simp [Bind.bind, Except.bind] at h))

/-- `scanFlowEntryIx`'s `tokens` field equals
    `(s.emit YamlToken.flowEntry)`'s tokens on every successful branch. -/
theorem scanFlowEntryIx_tokens_eq {s s' : ScannerStateIx input}
    (h : scanFlowEntryIx s = .ok s') :
    s'.tokens = (s.emit YamlToken.flowEntry).tokens := by
  unfold scanFlowEntryIx at h
  simp only [bind, Except.bind] at h
  split at h
  · split at h
    · simp at h
    · injection h with h; subst h; rfl
  · injection h with h; subst h; rfl

/-! ## §1  `scanDocumentStart_filtered_growsIx`

`scanDocumentStartIx` grows the filtered token count by `≥ 1`: it
unwinds indents (`unwindIndentsIx_tokens_size_le`), then emits
`.documentStart` (non-placeholder). Indexed twin of legacy
`scanDocumentStart_filtered_grows` (line 6075). -/

theorem scanDocumentStart_filtered_growsIx (s : ScannerStateIx input) :
    let p := fun (t : IxToken input) => t.token != .placeholder
    ((scanDocumentStartIx s).tokens.tokens.filter p).size ≥
      (s.tokens.tokens.filter p).size + 1 := by
  have h_unwind_sz : s.tokens.tokens.size ≤ (unwindIndentsIx s (-1)).tokens.tokens.size :=
    unwindIndentsIx_tokens_size_le s (-1)
  have h_eq := scanDocumentStartIx_tokens_eq s
  have h_arr : (scanDocumentStartIx s).tokens.tokens =
      ((unwindIndentsIx s (-1)).emit YamlToken.documentStart).tokens.tokens :=
    congrArg Indexed.TokenStream.tokens h_eq
  rw [emit_tokens_pushIx] at h_arr
  -- Use j = unwind.tokens.size (the first new slot, where the `.documentStart` lives).
  refine filtered_grows_of_any_newIx s.tokens.tokens
    (scanDocumentStartIx s).tokens.tokens (fun t => t.token != .placeholder)
    ?h_sz ?h_pres ((unwindIndentsIx s (-1)).tokens.tokens.size) ?h_lb ?h_ub ?h_new
  case h_sz => rw [h_arr, Array.size_push]; omega
  case h_pres => intro i hi; exact scanDocumentStartIx_preserves_prefix s i hi
  case h_lb => exact h_unwind_sz
  case h_ub => rw [h_arr, Array.size_push]; omega
  case h_new =>
    -- Goal: ((scanDocumentStartIx s).tokens.tokens[unwind.size]).token != .placeholder
    simp only [h_arr, Array.getElem_push_eq, IxToken.mk']
    rfl

/-! ## §2  `scanDocumentEnd_filtered_growsIx`

`scanDocumentEndIx` grows the filtered token count by `≥ 1` when it
succeeds: same structure as `scanDocumentStartIx`, with the
trailing `do`-block probe (excluded by `h`). Indexed twin of legacy
`scanDocumentEnd_filtered_grows` (line 6092). -/

theorem scanDocumentEnd_filtered_growsIx {s s' : ScannerStateIx input}
    (h : scanDocumentEndIx s = .ok s') :
    let p := fun (t : IxToken input) => t.token != .placeholder
    (s'.tokens.tokens.filter p).size ≥ (s.tokens.tokens.filter p).size + 1 := by
  have h_unwind_sz : s.tokens.tokens.size ≤ (unwindIndentsIx s (-1)).tokens.tokens.size :=
    unwindIndentsIx_tokens_size_le s (-1)
  have h_eq := scanDocumentEndIx_tokens_eq h
  have h_arr : s'.tokens.tokens =
      ((unwindIndentsIx s (-1)).emit YamlToken.documentEnd).tokens.tokens :=
    congrArg Indexed.TokenStream.tokens h_eq
  rw [emit_tokens_pushIx] at h_arr
  refine filtered_grows_of_any_newIx s.tokens.tokens s'.tokens.tokens
    (fun t => t.token != .placeholder)
    ?h_sz ?h_pres ((unwindIndentsIx s (-1)).tokens.tokens.size) ?h_lb ?h_ub ?h_new
  case h_sz => rw [h_arr, Array.size_push]; omega
  case h_pres => intro i hi; exact scanDocumentEndIx_preserves_prefix s s' h i hi
  case h_lb => exact h_unwind_sz
  case h_ub => rw [h_arr, Array.size_push]; omega
  case h_new =>
    simp only [h_arr, Array.getElem_push_eq, IxToken.mk']
    rfl

/-! ## §3  `scanYamlDirective_new_token_eqIx`

`scanYamlDirectiveIx` (when successful) emits exactly one new
`.versionDirective` token via `emitAt` at the saved `startPos`.
Indexed analogue of legacy `scanYamlDirective_new_token_eq` (line 6137).

The legacy statement `∃ major minor, s'.tokens = s.tokens.push
  { pos := startPos, val := .versionDirective major minor }` is
flattened to the form consumed by §5: the post-state strictly grows
by 1 raw token, and the new token at index `s.tokens.size` is non-
`.placeholder`. -/

theorem scanYamlDirective_new_token_eqIx {s : ScannerStateIx input}
    {cAfterWS : IxCursor input} {startPos : YamlPos}
    {hStart : startPos.offset ≤ cAfterWS.pos.offset} {s' : ScannerStateIx input}
    (h : scanYamlDirectiveIx s cAfterWS startPos hStart = .ok s') :
    ∃ (h_lt : s.tokens.tokens.size < s'.tokens.tokens.size),
      (s'.tokens.tokens[s.tokens.tokens.size]'h_lt).token ≠ YamlToken.placeholder := by
  unfold scanYamlDirectiveIx at h
  by_cases hd : s.seenYamlDirective = true
  · rw [if_pos hd] at h; simp [Bind.bind, Except.bind] at h
  · rw [if_neg hd] at h
    simp only [pure_bind] at h
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      -- After subst, s' is `({{s with cursor:=...}.emitAt startPos (.versionDirective major minor) hBound}
      --   with seenYamlDirective := true, directivesPresent := true)`. The record-update preserves
      --   .tokens by Lean defeq; emitAt unfolds via `simp [ScannerStateIx.emitAt]`.
      refine ⟨?_, ?_⟩
      · -- Strict size
        show s.tokens.tokens.size < _
        simp only [ScannerStateIx.emitAt]
        show s.tokens.tokens.size < (s.tokens.push _).tokens.size
        rw [show ∀ (ts : Indexed.TokenStream input) (t : IxToken input),
                (ts.push t).tokens.size = ts.tokens.size + 1 from
              fun ts t => Array.size_push ..]
        change s.tokens.tokens.size < s.tokens.tokens.size + 1
        omega
      · -- Token at s.tokens.size is `.versionDirective`, non-placeholder
        intro h_pl
        simp only [ScannerStateIx.emitAt, IxToken.mk', Indexed.TokenStream.push,
                   Array.getElem_push_eq] at h_pl
        contradiction
    · simp at h

/-! ## §4  `scanTagDirective_new_token_eqIx`

`scanTagDirectiveIx` (when successful) emits exactly one new
`.tagDirective` token via `emitAt`. Indexed analogue of legacy
`scanTagDirective_new_token_eq` (line 6184). Same flattened form
as §3. -/

theorem scanTagDirective_new_token_eqIx {s : ScannerStateIx input}
    {cAfterWS : IxCursor input} {startPos : YamlPos}
    {hStart : startPos.offset ≤ cAfterWS.pos.offset} {s' : ScannerStateIx input}
    (h : scanTagDirectiveIx s cAfterWS startPos hStart = .ok s') :
    ∃ (h_lt : s.tokens.tokens.size < s'.tokens.tokens.size),
      (s'.tokens.tokens[s.tokens.tokens.size]'h_lt).token ≠ YamlToken.placeholder := by
  unfold scanTagDirectiveIx at h
  simp only [Except.ok.injEq] at h
  subst h
  refine ⟨?_, ?_⟩
  · -- Strict size
    show s.tokens.tokens.size < _
    simp only [ScannerStateIx.emitAt]
    show s.tokens.tokens.size < (s.tokens.push _).tokens.size
    rw [show ∀ (ts : Indexed.TokenStream input) (t : IxToken input),
            (ts.push t).tokens.size = ts.tokens.size + 1 from
          fun ts t => Array.size_push ..]
    change s.tokens.tokens.size < s.tokens.tokens.size + 1
    omega
  · -- Token at s.tokens.size is `.tagDirective`, non-placeholder
    intro h_pl
    simp only [ScannerStateIx.emitAt, IxToken.mk', Indexed.TokenStream.push,
               Array.getElem_push_eq] at h_pl
    contradiction

/-! ## §5  `scanDirective_filtered_growsIx`

`scanDirectiveIx` grows filtered token count by `≥ 1` *whenever it
grows the raw token count*. The reserved-directive branch (`%FOO`)
emits no token (tokens unchanged), so under `h_grew : s'.tokens.size
> s.tokens.size` the dispatch must have hit YAML or TAG — both of
which emit a non-`.placeholder` token by §3/§4. Indexed twin of legacy
`scanDirective_filtered_grows` (line 6232). -/

theorem scanDirective_filtered_growsIx {s s' : ScannerStateIx input}
    (h : scanDirectiveIx s = .ok s')
    (h_grew : s'.tokens.tokens.size > s.tokens.tokens.size) :
    (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≥
    (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size + 1 := by
  refine filtered_grows_of_any_newIx s.tokens.tokens
    s'.tokens.tokens (fun t => t.token != .placeholder)
    (by omega) ?_ s.tokens.tokens.size (Nat.le_refl _) (by omega) ?_
  · intro i hi
    exact scanDirectiveIx_preserves_prefix s s' h i hi
  · -- New token at s.tokens.size is non-placeholder.
    unfold scanDirectiveIx at h
    split at h
    · simp at h
    · simp only at h
      split at h
      · -- YAML branch: delegate to §3
        obtain ⟨_, h_ne⟩ := scanYamlDirective_new_token_eqIx h
        show (s'.tokens.tokens[s.tokens.tokens.size]'(by omega)).token != .placeholder
        simp only [bne_iff_ne]; exact h_ne
      · split at h
        · -- TAG branch: delegate to §4
          obtain ⟨_, h_ne⟩ := scanTagDirective_new_token_eqIx h
          show (s'.tokens.tokens[s.tokens.tokens.size]'(by omega)).token != .placeholder
          simp only [bne_iff_ne]; exact h_ne
        · -- Reserved branch: tokens unchanged, contradicts h_grew.
          exfalso
          simp only [Except.ok.injEq] at h
          subst h
          -- s' = {s.advance with cursor := skipWhitespace ...}. Record-update on cursor preserves
          --   .tokens (defeq); advance preserves .tokens (defeq). So h_grew becomes
          --   `s.tokens.tokens.size > s.tokens.tokens.size`, which is False.
          change s.tokens.tokens.size > s.tokens.tokens.size at h_grew
          omega

/-! ## §6  `dispatchStructural_filtered_monoIx`

`scanNextTokenIx_dispatchStructural` is *filter-monotone*
(`≥ +0`). The three sub-cases (document-start / document-end /
directive) each preserve filtered prefix. Indexed twin of legacy
`dispatchStructural_filtered_mono` (line 6293). -/

theorem dispatchStructural_filtered_monoIx {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchStructural s c = .ok (some s')) :
    (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≥
    (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
  have h_mono : s.tokens.tokens.size ≤ s'.tokens.tokens.size :=
    scanNextTokenIx_dispatchStructural_tokens_size_le h
  have h_pres : ∀ i (hi : i < s.tokens.tokens.size),
      s'.tokens.tokens[i]'(Nat.lt_of_lt_of_le hi h_mono) = s.tokens.tokens[i]'hi := by
    intro i hi
    rcases scanNextTokenIx_dispatchStructural_ok_some_cases h with heq | hOk | hOk
    · subst heq; exact scanDocumentStartIx_preserves_prefix s i hi
    · exact scanDocumentEndIx_preserves_prefix s _ hOk i hi
    · exact scanDirectiveIx_preserves_prefix s _ hOk i hi
  obtain ⟨suffix, h_eq⟩ :=
    Array_filter_prefix_of_raw_prefix s.tokens.tokens s'.tokens.tokens
      (fun t => t.token != .placeholder) h_mono h_pres
  show (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).toList.length ≥
       (s.tokens.tokens.filter (fun t => t.token != .placeholder)).toList.length
  rw [h_eq, List.length_append]; omega

/-! ## §7  `dispatchFlowIndicators_filtered_growsIx`

`scanNextTokenIx_dispatchFlowIndicators` strictly grows filtered
count (`≥ +1`). Each of the five sub-cases (`[`, `]`, `{`, `}`, `,`)
emits exactly one non-`.placeholder` token. Indexed twin of legacy
`dispatchFlowIndicators_filtered_grows` (line 6307). -/

/-- Shared body for the 5 flow-indicator dispatch cases: given the
post-state's `tokens` field equals `(s.emit tok).tokens` and `tok`
is non-`.placeholder`, derive `≥ +1` filtered growth. -/
theorem flowIndicator_filtered_grows_of_emit_eq
    (s s' : ScannerStateIx input) (tok : YamlToken)
    (h_eq : s'.tokens = (s.emit tok).tokens)
    (h_tok : tok ≠ YamlToken.placeholder)
    (h_pres : ∀ i (hi : i < s.tokens.tokens.size),
      s'.tokens.tokens[i]'(by
        have h_arr : s'.tokens.tokens = (s.emit tok).tokens.tokens :=
          congrArg Indexed.TokenStream.tokens h_eq
        rw [h_arr]; show i < (s.tokens.tokens.push _).size
        rw [Array.size_push]; omega) =
      s.tokens.tokens[i]'hi) :
    (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≥
    (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size + 1 := by
  have h_arr : s'.tokens.tokens = (s.emit tok).tokens.tokens :=
    congrArg Indexed.TokenStream.tokens h_eq
  rw [emit_tokens_pushIx] at h_arr
  refine filtered_grows_of_extended_prefixIx s.tokens.tokens s'.tokens.tokens
    (fun t => t.token != .placeholder) ?_ h_pres ?_
  · rw [h_arr, Array.size_push]; omega
  · -- Goal: ((s'.tokens.tokens[s.tokens.tokens.size]'h).token != .placeholder) = true.
    simp only [bne_iff_ne]
    intro h_pl
    simp only [h_arr, Array.getElem_push_eq, IxToken.mk'] at h_pl
    exact h_tok h_pl

theorem dispatchFlowIndicators_filtered_growsIx {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s')) :
    (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≥
    (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size + 1 := by
  rcases scanNextTokenIx_dispatchFlowIndicators_ok_some_cases h with
    heq | heq | heq | heq | hOk
  · -- `[`: scanFlowSequenceStartIx; body emits .flowSequenceStart then advances.
    subst heq
    refine flowIndicator_filtered_grows_of_emit_eq s _ YamlToken.flowSequenceStart
      rfl (by intro h_pl; cases h_pl) ?_
    intro i hi; exact scanFlowSequenceStartIx_preserves_prefix s i hi
  · -- `]`: scanFlowSequenceEndIx
    subst heq
    refine flowIndicator_filtered_grows_of_emit_eq s _ YamlToken.flowSequenceEnd
      rfl (by intro h_pl; cases h_pl) ?_
    intro i hi; exact scanFlowSequenceEndIx_preserves_prefix s i hi
  · -- `{`: scanFlowMappingStartIx
    subst heq
    refine flowIndicator_filtered_grows_of_emit_eq s _ YamlToken.flowMappingStart
      rfl (by intro h_pl; cases h_pl) ?_
    intro i hi; exact scanFlowMappingStartIx_preserves_prefix s i hi
  · -- `}`: scanFlowMappingEndIx
    subst heq
    refine flowIndicator_filtered_grows_of_emit_eq s _ YamlToken.flowMappingEnd
      rfl (by intro h_pl; cases h_pl) ?_
    intro i hi; exact scanFlowMappingEndIx_preserves_prefix s i hi
  · -- `,`: scanFlowEntryIx
    refine flowIndicator_filtered_grows_of_emit_eq s s' YamlToken.flowEntry
      (scanFlowEntryIx_tokens_eq hOk) (by intro h_pl; cases h_pl) ?_
    intro i hi; exact scanFlowEntryIx_preserves_prefix s s' hOk i hi

end L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth
