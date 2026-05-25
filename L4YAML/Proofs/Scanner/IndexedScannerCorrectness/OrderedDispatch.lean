/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness.OrderedPrims

/-! # `IndexedScannerCorrectness.OrderedDispatch` — §8.7–§8.8

Per-helper `_preserves_ScanInvIx` / `_preserves_AllKeysValidIx`
bricks for every leaf scanner helper (`scanFlow*Ix`, `scanBlockEntryIx`,
`scanKeyIx`, `scanValueClearKeyIx`, `scanValuePrepareIx`,
`scanValueIx`, `scanDocument*Ix`, `scanDirectiveIx`,
`scanAnchorOrAliasIx`, `scanTagIx`), then per-dispatcher composition
(`preprocess`, `dispatchStructural`, `dispatchFlow`, `dispatchBlock`,
`dispatchContent`).

Split out of `IndexedScannerCorrectness.lean` (Reflection 112). -/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.ScannerCorrectness

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.WellBehaved
open L4YAML.Proofs.Indexed.ScannerPlainScalarValid

variable {input : String}

/-! ### §8.7  Per-helper `_preserves_ScanInvIx` / `_preserves_AllKeysValidIx`
bricks for the scanNextTokenIx dispatchers.

Each helper composes the §8.3 primitives directly (no mono needed for
emit-chain helpers) or, for helpers that wrap cursor-only subroutines
(directives, anchor, tag, scalars), uses `ScanInvIx_of_offset_ge`. -/

/-! #### §8.7.1  flowStartIx / flowEndIx AllKeysValidIx helpers. -/

/-- A flow-start operation (clears simpleKey, pushes old simpleKey to
    stack, appends tokens preserving prefix) preserves `AllKeysValidIx`. -/
theorem flowStartIx_preserves_AllKeysValidIx {input : String}
    (s s' : ScannerStateIx input)
    (h_akv : AllKeysValidIx s)
    (h_cleared : s'.simpleKey.possible = false)
    (h_pushed : s'.simpleKeyStack = s.simpleKeyStack.push s.simpleKey)
    (h_mono : s.tokens.size ≤ s'.tokens.size)
    (h_pref : ∀ i (hi : i < s.tokens.size),
      s'.tokens[i]'(by omega) = s.tokens[i]'hi) :
    AllKeysValidIx s' := by
  -- Bridges: TokenStream.size ↔ underlying Array.size are `rfl`; cast h_mono and h_pref
  -- to the Array form used by `SimpleKeyStackValidIx`.
  have h_mono_arr : s.tokens.tokens.size ≤ s'.tokens.tokens.size := h_mono
  have h_pref_arr : ∀ i (hi : i < s.tokens.tokens.size),
      s'.tokens.tokens[i]'(Nat.lt_of_lt_of_le hi h_mono_arr) =
      s.tokens.tokens[i]'hi := fun i hi => h_pref i hi
  refine ⟨SimpleKeyValidIx_of_not_possible s' h_cleared, ?_⟩
  intro j hj h_poss
  have hj_sz : j < s.simpleKeyStack.size + 1 := by
    rw [h_pushed, Array.size_push] at hj; exact hj
  have h_get : s'.simpleKeyStack[j]'hj =
      (s.simpleKeyStack.push s.simpleKey)[j]'(by rw [Array.size_push]; exact hj_sz) := by
    simp [h_pushed]
  rw [h_get] at h_poss ⊢
  by_cases hlt : j < s.simpleKeyStack.size
  · rw [Array.getElem_push_lt hlt] at h_poss ⊢
    have ⟨hb1, hb2, hp1, hp2⟩ := h_akv.2 j hlt h_poss
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro _h1; rw [h_pref_arr _ hb1]; exact hp1 hb1
    · intro _h2; rw [h_pref_arr _ hb2]; exact hp2 hb2
  · have hj_eq : j = s.simpleKeyStack.size := by omega
    subst hj_eq
    rw [Array.getElem_push_eq] at h_poss ⊢
    have ⟨hb1, hb2, hp1, hp2⟩ := h_akv.1 h_poss
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro _h1; rw [h_pref_arr _ hb1]; exact hp1 hb1
    · intro _h2; rw [h_pref_arr _ hb2]; exact hp2 hb2

/-- A flow-end operation (restores simpleKey from stack top, pops stack,
    appends tokens preserving prefix) preserves `AllKeysValidIx`. -/
theorem flowEndIx_preserves_AllKeysValidIx {input : String}
    (s s' : ScannerStateIx input)
    (h_akv : AllKeysValidIx s)
    (h_restored : s'.simpleKey = s.simpleKeyStack.back?.getD { cursor := IxCursor.start input })
    (h_popped : s'.simpleKeyStack = s.simpleKeyStack.pop)
    (h_mono : s.tokens.size ≤ s'.tokens.size)
    (h_pref : ∀ i (hi : i < s.tokens.size),
      s'.tokens[i]'(by omega) = s.tokens[i]'hi) :
    AllKeysValidIx s' := by
  have h_mono_arr : s.tokens.tokens.size ≤ s'.tokens.tokens.size := h_mono
  have h_pref_arr : ∀ i (hi : i < s.tokens.tokens.size),
      s'.tokens.tokens[i]'(Nat.lt_of_lt_of_le hi h_mono_arr) =
      s.tokens.tokens[i]'hi := fun i hi => h_pref i hi
  refine ⟨?_, ?_⟩
  · intro h_poss
    rw [h_restored] at h_poss ⊢
    by_cases h_size : s.simpleKeyStack.size > 0
    · have h_bound : s.simpleKeyStack.size - 1 < s.simpleKeyStack.size := by omega
      have h_get : s.simpleKeyStack.back?.getD { cursor := IxCursor.start input } =
          s.simpleKeyStack[s.simpleKeyStack.size - 1]'h_bound := by
        simp [Array.back?, h_bound]
      rw [h_get] at h_poss ⊢
      have ⟨hb1, hb2, hp1, hp2⟩ := h_akv.2 (s.simpleKeyStack.size - 1) h_bound h_poss
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro _h1; rw [h_pref_arr _ hb1]; exact hp1 hb1
      · intro _h2; rw [h_pref_arr _ hb2]; exact hp2 hb2
    · have h_empty : s.simpleKeyStack.size = 0 := by omega
      simp [Array.back?, h_empty] at h_poss
  · intro j hj h_poss
    have hj' : j < s.simpleKeyStack.size := by
      simp [h_popped, Array.size_pop] at hj; omega
    have h_get : s'.simpleKeyStack[j]'hj = s.simpleKeyStack[j]'hj' := by
      simp [h_popped, Array.getElem_pop]
    rw [h_get] at h_poss ⊢
    have ⟨hb1, hb2, hp1, hp2⟩ := h_akv.2 j hj' h_poss
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro _h1; rw [h_pref_arr _ hb1]; exact hp1 hb1
    · intro _h2; rw [h_pref_arr _ hb2]; exact hp2 hb2

/-! #### §8.7.2  Flow indicator preservation. -/

theorem scanFlowSequenceStartIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (h : ScanInvIx s) :
    ScanInvIx (scanFlowSequenceStartIx s) := by
  have h1 := emit_preserves_ScanInvIx s YamlToken.flowSequenceStart h
  have h2 := advance_preserves_ScanInvIx _ h1
  exact ScanInvIx_of_field_update _ _ h2 rfl rfl

theorem scanFlowSequenceEndIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (h : ScanInvIx s) :
    ScanInvIx (scanFlowSequenceEndIx s) := by
  have h1 := emit_preserves_ScanInvIx s YamlToken.flowSequenceEnd h
  have h2 := advance_preserves_ScanInvIx _ h1
  exact ScanInvIx_of_field_update _ _ h2 rfl rfl

theorem scanFlowMappingStartIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (h : ScanInvIx s) :
    ScanInvIx (scanFlowMappingStartIx s) := by
  have h1 := emit_preserves_ScanInvIx s YamlToken.flowMappingStart h
  have h2 := advance_preserves_ScanInvIx _ h1
  exact ScanInvIx_of_field_update _ _ h2 rfl rfl

theorem scanFlowMappingEndIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (h : ScanInvIx s) :
    ScanInvIx (scanFlowMappingEndIx s) := by
  have h1 := emit_preserves_ScanInvIx s YamlToken.flowMappingEnd h
  have h2 := advance_preserves_ScanInvIx _ h1
  exact ScanInvIx_of_field_update _ _ h2 rfl rfl

theorem scanFlowEntryIx_preserves_ScanInvIx {input : String}
    (s s' : ScannerStateIx input) (h : ScanInvIx s)
    (h_ok : scanFlowEntryIx s = .ok s') : ScanInvIx s' := by
  unfold scanFlowEntryIx at h_ok
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_ok
  have h1 := emit_preserves_ScanInvIx s YamlToken.flowEntry h
  have h2 := advance_preserves_ScanInvIx _ h1
  split at h_ok
  · split at h_ok
    · simp at h_ok
    · simp only [Except.ok.injEq] at h_ok; subst h_ok
      exact ScanInvIx_of_field_update _ _ h2 rfl rfl
  · simp only [Except.ok.injEq] at h_ok; subst h_ok
    exact ScanInvIx_of_field_update _ _ h2 rfl rfl

theorem scanFlowSequenceStartIx_preserves_AllKeysValidIx {input : String}
    (s : ScannerStateIx input) (h_akv : AllKeysValidIx s) :
    AllKeysValidIx (scanFlowSequenceStartIx s) := by
  apply flowStartIx_preserves_AllKeysValidIx s _ h_akv
    (scanFlowSequenceStartIx_simpleKey_cleared s)
    (scanFlowSequenceStartIx_stack_pushed s)
    (scanFlowSequenceStartIx_tokens_size_le s)
    (fun i hi => scanFlowSequenceStartIx_preserves_prefix s i hi)

theorem scanFlowSequenceEndIx_preserves_AllKeysValidIx {input : String}
    (s : ScannerStateIx input) (h_akv : AllKeysValidIx s) :
    AllKeysValidIx (scanFlowSequenceEndIx s) := by
  apply flowEndIx_preserves_AllKeysValidIx s _ h_akv
    (scanFlowSequenceEndIx_simpleKey_restored s)
    (scanFlowSequenceEndIx_stack_popped s)
    (scanFlowSequenceEndIx_tokens_size_le s)
    (fun i hi => scanFlowSequenceEndIx_preserves_prefix s i hi)

theorem scanFlowMappingStartIx_preserves_AllKeysValidIx {input : String}
    (s : ScannerStateIx input) (h_akv : AllKeysValidIx s) :
    AllKeysValidIx (scanFlowMappingStartIx s) := by
  apply flowStartIx_preserves_AllKeysValidIx s _ h_akv
    (scanFlowMappingStartIx_simpleKey_cleared s)
    (scanFlowMappingStartIx_stack_pushed s)
    (scanFlowMappingStartIx_tokens_size_le s)
    (fun i hi => scanFlowMappingStartIx_preserves_prefix s i hi)

theorem scanFlowMappingEndIx_preserves_AllKeysValidIx {input : String}
    (s : ScannerStateIx input) (h_akv : AllKeysValidIx s) :
    AllKeysValidIx (scanFlowMappingEndIx s) := by
  apply flowEndIx_preserves_AllKeysValidIx s _ h_akv
    (scanFlowMappingEndIx_simpleKey_restored s)
    (scanFlowMappingEndIx_stack_popped s)
    (scanFlowMappingEndIx_tokens_size_le s)
    (fun i hi => scanFlowMappingEndIx_preserves_prefix s i hi)

theorem scanFlowEntryIx_preserves_AllKeysValidIx {input : String}
    (s s' : ScannerStateIx input) (h_akv : AllKeysValidIx s)
    (h_ok : scanFlowEntryIx s = .ok s') : AllKeysValidIx s' := by
  apply AllKeysValidIx_mono s s' h_akv
    (scanFlowEntryIx_preserves_simpleKey s s' h_ok)
    (scanFlowEntryIx_preserves_simpleKeyStack s s' h_ok)
    (scanFlowEntryIx_tokens_size_le h_ok)
    (fun i hi => scanFlowEntryIx_preserves_prefix s s' h_ok i hi)

/-! #### §8.7.3  Block entry / key preservation. -/

theorem scanBlockEntryIx_preserves_ScanInvIx {input : String}
    (s s' : ScannerStateIx input) (h : ScanInvIx s)
    (h_ok : scanBlockEntryIx s = .ok s') : ScanInvIx s' := by
  unfold scanBlockEntryIx at h_ok
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_ok
  split at h_ok
  · -- !s.inFlow = true: tab check active
    split at h_ok
    · simp at h_ok
    · simp only [Except.ok.injEq] at h_ok; subst h_ok
      have h1 := pushSequenceIndentIx_preserves_ScanInvIx s s.cursor.pos.col h
      have h2 := emit_preserves_ScanInvIx _ YamlToken.blockEntry h1
      have h3 := advance_preserves_ScanInvIx _ h2
      exact ScanInvIx_of_field_update _ _ h3 rfl rfl
  · -- !s.inFlow = false: skip push
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    have h2 := emit_preserves_ScanInvIx s YamlToken.blockEntry h
    have h3 := advance_preserves_ScanInvIx _ h2
    exact ScanInvIx_of_field_update _ _ h3 rfl rfl

theorem scanBlockEntryIx_preserves_AllKeysValidIx {input : String}
    (s s' : ScannerStateIx input) (h_akv : AllKeysValidIx s)
    (h_ok : scanBlockEntryIx s = .ok s') : AllKeysValidIx s' := by
  apply AllKeysValidIx_mono s s' h_akv
    (scanBlockEntryIx_preserves_simpleKey s s' h_ok)
    (scanBlockEntryIx_preserves_simpleKeyStack s s' h_ok)
    (scanBlockEntryIx_tokens_size_le h_ok)
    (fun i hi => scanBlockEntryIx_preserves_prefix s s' h_ok i hi)

theorem scanKeyIx_preserves_ScanInvIx {input : String}
    (s s' : ScannerStateIx input) (h : ScanInvIx s)
    (h_ok : scanKeyIx s = .ok s') : ScanInvIx s' := by
  unfold scanKeyIx at h_ok
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_ok
  split at h_ok
  · split at h_ok
    · split at h_ok
      · simp at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok
        have h1 := pushMappingIndentIx_preserves_ScanInvIx s s.cursor.pos.col h
        have h2 := emit_preserves_ScanInvIx _ YamlToken.key h1
        have h3 := advance_preserves_ScanInvIx _ h2
        exact ScanInvIx_of_field_update _ _ h3 rfl rfl
    · simp only [Except.ok.injEq] at h_ok; subst h_ok
      have h1 := pushMappingIndentIx_preserves_ScanInvIx s s.cursor.pos.col h
      have h2 := emit_preserves_ScanInvIx _ YamlToken.key h1
      have h3 := advance_preserves_ScanInvIx _ h2
      exact ScanInvIx_of_field_update _ _ h3 rfl rfl
  · split at h_ok
    · split at h_ok
      · simp at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok
        have h2 := emit_preserves_ScanInvIx s YamlToken.key h
        have h3 := advance_preserves_ScanInvIx _ h2
        exact ScanInvIx_of_field_update _ _ h3 rfl rfl
    · simp only [Except.ok.injEq] at h_ok; subst h_ok
      have h2 := emit_preserves_ScanInvIx s YamlToken.key h
      have h3 := advance_preserves_ScanInvIx _ h2
      exact ScanInvIx_of_field_update _ _ h3 rfl rfl

theorem scanKeyIx_preserves_AllKeysValidIx {input : String}
    (s s' : ScannerStateIx input) (h_akv : AllKeysValidIx s)
    (h_ok : scanKeyIx s = .ok s') : AllKeysValidIx s' := by
  refine AllKeysValidIx_of_cleared s' (scanKeyIx_clears_simpleKey s s' h_ok) ?_
  exact SimpleKeyStackValidIx_mono s s' h_akv.2
    (scanKeyIx_preserves_simpleKeyStack s s' h_ok)
    (scanKeyIx_tokens_size_le h_ok)
    (fun i hi => scanKeyIx_preserves_prefix s s' h_ok i hi)

/-! #### §8.7.4  Value pipeline preservation.

`scanValueIx` chains: `scanValueClearKeyIx` (pure field update; SimpleKeyValidIx
either preserved or vacuous via cleared) → `scanValuePrepareIx`
(overwriteAtCursor when simpleKey.possible; uses SimpleKeyValidIx to
discharge the slot-offset match) → emit value → advance → field update. -/

theorem scanValueClearKeyIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (h : ScanInvIx s) :
    ScanInvIx (scanValueClearKeyIx s) := by
  unfold scanValueClearKeyIx
  split
  · split
    · exact ScanInvIx_of_field_update _ _ h rfl rfl
    · split
      · exact ScanInvIx_of_field_update _ _ h rfl rfl
      · exact h
  · exact h

theorem scanValueClearKeyIx_preserves_SimpleKeyValidIx {input : String}
    (s : ScannerStateIx input) (h_skv : SimpleKeyValidIx s) :
    SimpleKeyValidIx (scanValueClearKeyIx s) := by
  unfold scanValueClearKeyIx
  split
  · split
    · -- simpleKey cleared to default (possible = false)
      apply SimpleKeyValidIx_of_not_possible
      rfl
    · split
      · apply SimpleKeyValidIx_of_not_possible
        rfl
      · exact h_skv
  · exact h_skv

theorem scanValueClearKeyIx_preserves_AllKeysValidIx {input : String}
    (s : ScannerStateIx input) (h_akv : AllKeysValidIx s) :
    AllKeysValidIx (scanValueClearKeyIx s) := by
  refine ⟨scanValueClearKeyIx_preserves_SimpleKeyValidIx s h_akv.1, ?_⟩
  exact SimpleKeyStackValidIx_mono s _ h_akv.2
    (scanValueClearKeyIx_preserves_simpleKeyStack s)
    (scanValueClearKeyIx_tokens_size_le s)
    (fun i hi => scanValueClearKeyIx_preserves_prefix s i hi)

/-! #### §8.7.5  Document marker AllKeysValidIx preservation.

The `_preserves_AllKeysValidIx` direction goes via
`AllKeysValidIx_of_cleared` because both `scanDocumentStartIx` and
`scanDocumentEndIx` reset `simpleKey` to default (`possible = false`),
while preserving the simpleKeyStack and (only growing) tokens. -/

theorem scanDocumentStartIx_preserves_AllKeysValidIx {input : String}
    (s : ScannerStateIx input) (h_akv : AllKeysValidIx s) :
    AllKeysValidIx (scanDocumentStartIx s) := by
  refine AllKeysValidIx_of_cleared _ (scanDocumentStartIx_clears_simpleKey s) ?_
  exact SimpleKeyStackValidIx_mono s _ h_akv.2
    (scanDocumentStartIx_preserves_simpleKeyStack s)
    (scanDocumentStartIx_tokens_size_le s)
    (fun i hi => scanDocumentStartIx_preserves_prefix s i hi)

theorem scanDocumentEndIx_preserves_AllKeysValidIx {input : String}
    (s s' : ScannerStateIx input) (h_akv : AllKeysValidIx s)
    (h_ok : scanDocumentEndIx s = .ok s') : AllKeysValidIx s' := by
  refine AllKeysValidIx_of_cleared _ (scanDocumentEndIx_clears_simpleKey s s' h_ok) ?_
  exact SimpleKeyStackValidIx_mono s _ h_akv.2
    (scanDocumentEndIx_preserves_simpleKeyStack s s' h_ok)
    (scanDocumentEndIx_tokens_size_le h_ok)
    (fun i hi => scanDocumentEndIx_preserves_prefix s s' h_ok i hi)

/-! #### §8.7.5'  Document marker ScanInvIx preservation.

Each marker chains `unwindIndentsIx` → field update (clear simpleKey)
→ `emit documentStart/End` → `advanceN 3` → final structure update.
Built as an explicit `have`-chain to bypass the `apply`-elaboration
failure on `@[inline] advanceN` (Reflection 111). -/

theorem scanDocumentStartIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (h : ScanInvIx s) :
    ScanInvIx (scanDocumentStartIx s) := by
  unfold scanDocumentStartIx
  have h_unwind := unwindIndentsIx_preserves_ScanInvIx s (-1 : Int) h
  have h_clear : ScanInvIx { unwindIndentsIx s (-1) with
      simpleKey := { cursor := IxCursor.start input } } :=
    ScanInvIx_of_field_update _ _ h_unwind rfl rfl
  have h_emit := emit_preserves_ScanInvIx _ YamlToken.documentStart h_clear
  have h_adv := advanceN_preserves_ScanInvIx _ 3 h_emit
  exact ScanInvIx_of_field_update _ _ h_adv rfl rfl

theorem scanDocumentEndIx_preserves_ScanInvIx {input : String}
    (s s' : ScannerStateIx input) (h : ScanInvIx s)
    (h_ok : scanDocumentEndIx s = .ok s') : ScanInvIx s' := by
  -- Reusable witness for every success branch: ScanInvIx of the
  -- structure-update applied to `(... unwind → clear sk → emit → advanceN 3 ...)`.
  have h_unwind := unwindIndentsIx_preserves_ScanInvIx s (-1 : Int) h
  have h_clear : ScanInvIx { unwindIndentsIx s (-1) with
      simpleKey := { cursor := IxCursor.start input } } :=
    ScanInvIx_of_field_update _ _ h_unwind rfl rfl
  have h_emit := emit_preserves_ScanInvIx _ YamlToken.documentEnd h_clear
  have h_adv := advanceN_preserves_ScanInvIx _ 3 h_emit
  have h_fld := ScanInvIx_of_field_update _
    { ((({ unwindIndentsIx s (-1) with
        simpleKey := { cursor := IxCursor.start input } }
      : ScannerStateIx input).emit YamlToken.documentEnd).advanceN 3) with
        simpleKeyAllowed := true, allowDirectives := true,
        directivesPresent := false, definedAnchors := #[] } h_adv rfl rfl
  unfold scanDocumentEndIx at h_ok
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_ok
  repeat (any_goals (split at h_ok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h_ok; subst h_ok)
  all_goals exact h_fld

/-! #### §8.7.6  `scanValuePrepareIx_preserves_ScanInvIx`.

This is the only helper that performs `overwriteAtCursor` (and the
two-overwrite branch is the only chain). The `h_match` precondition
for each call is discharged via `SimpleKeyValidIx`: the saved
`tokenIndex` / `tokenIndex+1` slots carry `.start = simpleKey.pos`.

For the second overwrite (in the `col > currentIndent` branch), the
first overwrite at `idx` does NOT disturb the slot at `idx+1` — this
is precisely `overwriteAtCursor_preserves_other_start`. -/

theorem scanValuePrepareIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (h : ScanInvIx s) (h_skv : SimpleKeyValidIx s) :
    ScanInvIx (scanValuePrepareIx s) := by
  unfold scanValuePrepareIx
  split
  · rename_i h_poss
    obtain ⟨hb1, hb2, hp1, hp2⟩ := h_skv h_poss
    -- `sk.pos = simpleKey.cursor.pos = simpleKey.pos` by `@[inline] def`.
    have h_match_idx : ∀ (h_i : s.simpleKey.tokenIndex < s.tokens.tokens.size),
        s.simpleKey.cursor.pos.offset =
          (s.tokens.tokens[s.simpleKey.tokenIndex]'h_i).start.offset := by
      intro h_i; rw [hp1 h_i]; rfl
    have h_match_idx1 : ∀ (h_i : s.simpleKey.tokenIndex + 1 < s.tokens.tokens.size),
        s.simpleKey.cursor.pos.offset =
          (s.tokens.tokens[s.simpleKey.tokenIndex + 1]'h_i).start.offset := by
      intro h_i; rw [hp2 h_i]; rfl
    split
    · split
      · -- !inFlow ∧ col > currentIndent: two overwrites + structure update.
        have h1 : ScanInvIx (s.overwriteAtCursor s.simpleKey.tokenIndex
            s.simpleKey.cursor YamlToken.blockMappingStart) :=
          overwriteAtCursor_preserves_ScanInvIx s s.simpleKey.tokenIndex
            s.simpleKey.cursor YamlToken.blockMappingStart h h_match_idx
        have h2 : ScanInvIx ((s.overwriteAtCursor s.simpleKey.tokenIndex
            s.simpleKey.cursor YamlToken.blockMappingStart).overwriteAtCursor
              (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor YamlToken.key) := by
          apply overwriteAtCursor_preserves_ScanInvIx _ _ _ _ h1
          intro h_i
          -- The first overwrite did not change idx+1's `.start`.
          have h_other : ((s.overwriteAtCursor s.simpleKey.tokenIndex
              s.simpleKey.cursor YamlToken.blockMappingStart).tokens.tokens[
                s.simpleKey.tokenIndex + 1]'h_i).start =
              (s.tokens.tokens[s.simpleKey.tokenIndex + 1]'hb2).start :=
            overwriteAtCursor_preserves_other_start s
              s.simpleKey.tokenIndex (s.simpleKey.tokenIndex + 1)
              s.simpleKey.cursor YamlToken.blockMappingStart (by omega) hb2
          exact (h_match_idx1 hb2).trans (congrArg YamlPos.offset h_other.symm)
        exact ScanInvIx_of_field_update _ _ h2 rfl rfl
      · -- !inFlow ∧ col ≤ currentIndent: one overwrite + structure update.
        have h1 : ScanInvIx (s.overwriteAtCursor (s.simpleKey.tokenIndex + 1)
            s.simpleKey.cursor YamlToken.key) :=
          overwriteAtCursor_preserves_ScanInvIx s _ _ _ h h_match_idx1
        exact ScanInvIx_of_field_update _ _ h1 rfl rfl
    · -- inFlow: one overwrite + structure update.
      have h1 : ScanInvIx (s.overwriteAtCursor (s.simpleKey.tokenIndex + 1)
          s.simpleKey.cursor YamlToken.key) :=
        overwriteAtCursor_preserves_ScanInvIx s _ _ _ h h_match_idx1
      exact ScanInvIx_of_field_update _ _ h1 rfl rfl
  · split
    · -- ¬simpleKey.possible ∧ explicitKeyLine.isSome: pure record update.
      exact ScanInvIx_of_field_update _ _ h rfl rfl
    · split
      · -- ¬simpleKey.possible ∧ !inFlow: pushMappingIndentIx.
        exact pushMappingIndentIx_preserves_ScanInvIx s s.cursor.pos.col h
      · -- ¬simpleKey.possible ∧ inFlow: identity.
        exact h

/-! #### §8.7.7  `scanValuePrepareIx_preserves_AllKeysValidIx`.

`scanValuePrepareIx_clears_simpleKey` is unconditional — so we use
`AllKeysValidIx_of_cleared` for the `SimpleKeyValidIx` side, and
`SimpleKeyStackValidIx_mono_pos` for the stack side. The
`.start`-preservation hypothesis for `_mono_pos` is discharged
slot-by-slot: in the overwrite branches via
`overwriteAtCursor_preserves_start_if_match` (using
`SimpleKeyValidIx s` to assert that the original `idx` / `idx+1`
slots already carry `.start = sk.pos`); in the
`pushMappingIndentIx` branch via the existing
`pushMappingIndentIx_preserves_prefix`. -/

private theorem scanValuePrepareIx_preserves_start {input : String}
    (s : ScannerStateIx input) (h_skv : SimpleKeyValidIx s)
    (k : Nat) (hk : k < s.tokens.tokens.size) :
    ((scanValuePrepareIx s).tokens.tokens[k]'(by
        have h_sz := scanValuePrepareIx_tokens_size_le s
        show k < (scanValuePrepareIx s).tokens.size
        exact Nat.lt_of_lt_of_le hk h_sz)).start =
      (s.tokens.tokens[k]'hk).start := by
  unfold scanValuePrepareIx
  split
  · rename_i h_poss
    obtain ⟨hb1, hb2, hp1, hp2⟩ := h_skv h_poss
    have h_match_idx : ∀ (h_i : s.simpleKey.tokenIndex < s.tokens.tokens.size),
        (s.tokens.tokens[s.simpleKey.tokenIndex]'h_i).start = s.simpleKey.cursor.pos := by
      intro h_i; rw [hp1 h_i]; rfl
    have h_match_idx1 : ∀ (h_i : s.simpleKey.tokenIndex + 1 < s.tokens.tokens.size),
        (s.tokens.tokens[s.simpleKey.tokenIndex + 1]'h_i).start = s.simpleKey.cursor.pos := by
      intro h_i; rw [hp2 h_i]; rfl
    split
    · split
      · -- !inFlow ∧ col > currentIndent: two overwrites + structure update.
        -- The structure update touches `indents` and `simpleKey`; `.tokens` is invariant.
        show (((s.overwriteAtCursor s.simpleKey.tokenIndex
              s.simpleKey.cursor YamlToken.blockMappingStart).overwriteAtCursor
                (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor
                YamlToken.key).tokens.tokens[k]'_).start = _
        -- Apply outer overwrite preservation.
        have h_match_outer : ∀ (h_i : s.simpleKey.tokenIndex + 1 <
              (s.overwriteAtCursor s.simpleKey.tokenIndex s.simpleKey.cursor
                YamlToken.blockMappingStart).tokens.tokens.size),
            ((s.overwriteAtCursor s.simpleKey.tokenIndex s.simpleKey.cursor
                YamlToken.blockMappingStart).tokens.tokens[
                  s.simpleKey.tokenIndex + 1]'h_i).start = s.simpleKey.cursor.pos := by
          intro _h_i
          rw [overwriteAtCursor_preserves_other_start s _ _ _ _ (by omega) hb2]
          exact h_match_idx1 hb2
        have h_outer := overwriteAtCursor_preserves_start_if_match
          (s.overwriteAtCursor s.simpleKey.tokenIndex s.simpleKey.cursor
            YamlToken.blockMappingStart)
          (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor YamlToken.key
          h_match_outer k (by
            show k < (s.overwriteAtCursor s.simpleKey.tokenIndex s.simpleKey.cursor
                YamlToken.blockMappingStart).tokens.tokens.size
            rw [show (s.overwriteAtCursor s.simpleKey.tokenIndex s.simpleKey.cursor
                YamlToken.blockMappingStart).tokens.tokens.size = s.tokens.tokens.size
              from Scanner.Indexed.overwriteAtCursor_tokens_size s _ _ _]
            exact hk)
        rw [h_outer]
        exact overwriteAtCursor_preserves_start_if_match s _ _ _ h_match_idx k hk
      · -- !inFlow ∧ col ≤ currentIndent: one overwrite at idx+1 + structure update.
        show ((s.overwriteAtCursor (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor
              YamlToken.key).tokens.tokens[k]'_).start = _
        exact overwriteAtCursor_preserves_start_if_match s _ _ _ h_match_idx1 k hk
    · -- inFlow: one overwrite at idx+1 + structure update.
      show ((s.overwriteAtCursor (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor
            YamlToken.key).tokens.tokens[k]'_).start = _
      exact overwriteAtCursor_preserves_start_if_match s _ _ _ h_match_idx1 k hk
  · split
    · -- ¬possible ∧ explicitKeyLine.isSome: pure record update, tokens unchanged.
      rfl
    · split
      · -- ¬possible ∧ !inFlow: pushMappingIndentIx, prefix preserved fully.
        exact congrArg IxToken.start (pushMappingIndentIx_preserves_prefix s s.cursor.pos.col k hk)
      · -- ¬possible ∧ inFlow: identity.
        rfl

theorem scanValuePrepareIx_preserves_AllKeysValidIx {input : String}
    (s : ScannerStateIx input) (h_akv : AllKeysValidIx s) :
    AllKeysValidIx (scanValuePrepareIx s) := by
  refine AllKeysValidIx_of_cleared _ (scanValuePrepareIx_clears_simpleKey s) ?_
  apply SimpleKeyStackValidIx_mono_pos s _ h_akv.2
    (scanValuePrepareIx_preserves_simpleKeyStack s)
    (scanValuePrepareIx_tokens_size_le s)
  intro i hi
  exact scanValuePrepareIx_preserves_start s h_akv.1 i hi

/-! #### §8.7.8  `scanValueIx_preserves_ScanInvIx` / `_preserves_AllKeysValidIx`.

The four-stage chain: `scanValueClearKeyIx` → validate (Unit) →
`scanValuePrepareIx` → emit `.value` → advance → tab-check (Unit) →
field update. The `SimpleKeyValidIx` precondition for
`scanValuePrepareIx` is supplied by
`scanValueClearKeyIx_preserves_SimpleKeyValidIx`. -/

theorem scanValueIx_preserves_ScanInvIx {input : String}
    (s s' : ScannerStateIx input) (h : ScanInvIx s) (h_skv : SimpleKeyValidIx s)
    (h_ok : scanValueIx s = .ok s') : ScanInvIx s' := by
  unfold scanValueIx at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok <;> try contradiction
  split at h_ok <;> try contradiction
  simp only [Except.ok.injEq] at h_ok; subst h_ok
  -- Compose preservation along the chain.
  have h_kc := scanValueClearKeyIx_preserves_ScanInvIx s h
  have h_skv_kc := scanValueClearKeyIx_preserves_SimpleKeyValidIx s h_skv
  have h_prep := scanValuePrepareIx_preserves_ScanInvIx _ h_kc h_skv_kc
  have h_emit := emit_preserves_ScanInvIx _ YamlToken.value h_prep
  have h_adv := advance_preserves_ScanInvIx _ h_emit
  exact ScanInvIx_of_field_update _ _ h_adv rfl rfl

theorem scanValueIx_preserves_AllKeysValidIx {input : String}
    (s s' : ScannerStateIx input) (h_akv : AllKeysValidIx s)
    (h_ok : scanValueIx s = .ok s') : AllKeysValidIx s' := by
  unfold scanValueIx at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok <;> try contradiction
  split at h_ok <;> try contradiction
  simp only [Except.ok.injEq] at h_ok; subst h_ok
  have h_kc := scanValueClearKeyIx_preserves_AllKeysValidIx s h_akv
  have h_prep := scanValuePrepareIx_preserves_AllKeysValidIx _ h_kc
  have h_emit := emit_preserves_AllKeysValidIx _ YamlToken.value h_prep
  have h_adv := advance_preserves_AllKeysValidIx _ h_emit
  -- Final field update: simpleKeyAllowed := true, explicitKeyLine := none.
  refine AllKeysValidIx_of_cleared _ ?_ ?_
  · -- simpleKey was already cleared by scanValuePrepareIx (preserved by emit/advance).
    show ((scanValuePrepareIx (scanValueClearKeyIx s)).emit YamlToken.value).advance.simpleKey.possible = false
    rw [advance_preserves_simpleKey, emit_preserves_simpleKey]
    exact scanValuePrepareIx_clears_simpleKey _
  · exact h_adv.2

/-! #### §8.7.10  `scanAnchorOrAliasIx` / `scanTagIx` / `scanDirectiveIx`
preservation.

Each emits one token (via `emitAt`) or is cursor-only (directives).
ScanInvIx uses `emitAt_preserves_ScanInvIx` with the `h_ge` precondition
discharged from the input `ScanInvIx`'s bound; AllKeysValidIx uses
`AllKeysValidIx_mono` with the existing
`_preserves_simpleKey` / `_preserves_simpleKeyStack` /
`_tokens_size_le` / `_preserves_prefix` bricks. -/

theorem scanAnchorOrAliasIx_preserves_AllKeysValidIx {input : String}
    (s s' : ScannerStateIx input) (isAnchor : Bool) (h_akv : AllKeysValidIx s)
    (h_ok : scanAnchorOrAliasIx s isAnchor = .ok s') : AllKeysValidIx s' := by
  apply AllKeysValidIx_mono s s' h_akv
    (scanAnchorOrAliasIx_preserves_simpleKey s isAnchor s' h_ok)
    (scanAnchorOrAliasIx_preserves_simpleKeyStack s isAnchor s' h_ok)
    (scanAnchorOrAliasIx_tokens_size_le h_ok)
    (fun i hi => scanAnchorOrAliasIx_preserves_prefix s isAnchor s' h_ok i hi)

theorem scanTagIx_preserves_AllKeysValidIx {input : String}
    (s s' : ScannerStateIx input) (h_akv : AllKeysValidIx s)
    (h_ok : scanTagIx s = .ok s') : AllKeysValidIx s' := by
  apply AllKeysValidIx_mono s s' h_akv
    (scanTagIx_preserves_simpleKey s s' h_ok)
    (scanTagIx_preserves_simpleKeyStack s s' h_ok)
    (scanTagIx_tokens_size_le h_ok)
    (fun i hi => scanTagIx_preserves_prefix s s' h_ok i hi)

theorem scanDirectiveIx_preserves_AllKeysValidIx {input : String}
    (s s' : ScannerStateIx input) (h_akv : AllKeysValidIx s)
    (h_ok : scanDirectiveIx s = .ok s') : AllKeysValidIx s' := by
  apply AllKeysValidIx_mono s s' h_akv
    (scanDirectiveIx_preserves_simpleKey s s' h_ok)
    (scanDirectiveIx_preserves_simpleKeyStack s s' h_ok)
    (scanDirectiveIx_tokens_size_le h_ok)
    (fun i hi => scanDirectiveIx_preserves_prefix s s' h_ok i hi)

/-! ### §8.7.10'  Status note — ScanInvIx for emit-at-prior-cursor helpers
deferred to `OrderedLoop.lean`.

`scanAnchorOrAliasIx_preserves_ScanInvIx`,
`scanTagIx_preserves_ScanInvIx`, and
`scanDirectiveIx_preserves_ScanInvIx` use `emitAt startPos` where
`startPos = s.cursor.pos` (the *original* cursor, before the loop scans
the name). The `h_ge` precondition of `emitAt_preserves_ScanInvIx`
requires `∀ i, s_intermediate.tokens.tokens[i].start.offset ≤
startPos.offset`, where `s_intermediate` is a cursor-updated form
`{ s.advance with cursor := cAfterLoop }`. The structure update folds
to a `let __src := s.advance; { cursor := cAfterLoop, ... }` form
internally, which trips up `rw` (the Fin-indexed `getElem` form in the
goal differs from the Nat-indexed `getElem'` form produced by helpers).

The fix requires either (a) per-helper `_new_token_start_eq_cursor`
bricks plus a generic `ScanInvIx_of_one_emit_at_cursor` helper, or
(b) the legacy `let __src` zeta workaround. Deferred to the
`6f.3b3.primitives.ordered.compose.value.tail` next-session sub-step
(see Reflection 112). -/

end L4YAML.Proofs.Indexed.ScannerCorrectness
