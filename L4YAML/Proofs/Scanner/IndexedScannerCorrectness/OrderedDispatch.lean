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

theorem scanValuePrepareIx_preserves_start {input : String}
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

/-! #### §8.7.10'  `_new_token_start` bricks per emit-at-prior-cursor helper.

For each helper that emits one token via `emitAt startPos` where
`startPos = s.cursor.pos` (anchor/alias, tag, YAML directive, TAG
directive), we prove that the pushed slot at `s.tokens.size` carries
`.start = startPos`. Each brick follows the legacy
`scanAnchorOrAliasIx_new_token_not_plain`
(`Proofs/Production/IndexedScannerPlainScalarValid:1359`) template:
unfold the helper, kill error branches, then `show` the goal in
`(arr.push (IxToken.mk' startPos ...))[arr.size]'_` form and close
with `Array.getElem_push_eq` + `rfl`. The `.start` field of `IxToken.mk'`
is the first argument by definitional unfolding. -/

theorem scanAnchorOrAliasIx_new_token_start {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (h_ok : scanAnchorOrAliasIx s isAnchor = .ok s')
    (hj : s.tokens.size < s'.tokens.size) :
    (s'.tokens[s.tokens.size]'hj).start = s.cursor.pos := by
  unfold scanAnchorOrAliasIx at h_ok
  dsimp only [] at h_ok
  split at h_ok
  · simp at h_ok
  · simp only [Except.ok.injEq] at h_ok
    subst h_ok
    show ((s.tokens.tokens.push (IxToken.mk' s.cursor.pos
        (if isAnchor then YamlToken.anchor (collectAnchorNameLoopIx
            s.advance.cursor "" (input.utf8ByteSize - s.advance.cursor.pos.offset)).fst
         else YamlToken.alias (collectAnchorNameLoopIx s.advance.cursor ""
            (input.utf8ByteSize - s.advance.cursor.pos.offset)).fst)
        _ _ _))[s.tokens.tokens.size]'_).start = s.cursor.pos
    simp only [Array.getElem_push_eq, IxToken.mk']

theorem scanTagIx_new_token_start {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanTagIx s = .ok s')
    (hj : s.tokens.size < s'.tokens.size) :
    (s'.tokens[s.tokens.size]'hj).start = s.cursor.pos := by
  unfold scanTagIx at h_ok
  dsimp only [] at h_ok
  split at h_ok
  · -- '<' verbatim tag branch: nested guards on foundClose / uri.isEmpty
    split at h_ok
    · simp at h_ok
    · split at h_ok
      · simp at h_ok
      · simp only [Except.ok.injEq] at h_ok
        subst h_ok
        show ((s.tokens.tokens.push (IxToken.mk' s.cursor.pos _
            _ _ _))[s.tokens.tokens.size]'_).start = s.cursor.pos
        simp only [Array.getElem_push_eq, IxToken.mk']
  · -- '!' secondary tag branch
    simp only [Except.ok.injEq] at h_ok
    subst h_ok
    show ((s.tokens.tokens.push (IxToken.mk' s.cursor.pos _
        _ _ _))[s.tokens.tokens.size]'_).start = s.cursor.pos
    simp only [Array.getElem_push_eq, IxToken.mk']
  · -- default branch (named tag / primary handle)
    simp only [Except.ok.injEq] at h_ok
    subst h_ok
    show ((s.tokens.tokens.push (IxToken.mk' s.cursor.pos _
        _ _ _))[s.tokens.tokens.size]'_).start = s.cursor.pos
    simp only [Array.getElem_push_eq, IxToken.mk']

theorem scanYamlDirectiveIx_new_token_start {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset)
    (s' : ScannerStateIx input)
    (h_ok : scanYamlDirectiveIx s cAfterWS startPos hStart = .ok s')
    (hj : s.tokens.size < s'.tokens.size) :
    (s'.tokens[s.tokens.size]'hj).start = startPos := by
  unfold scanYamlDirectiveIx at h_ok
  by_cases hd : s.seenYamlDirective = true
  · rw [if_pos hd] at h_ok; simp [Bind.bind, Except.bind] at h_ok
  · rw [if_neg hd] at h_ok
    simp only [pure_bind] at h_ok
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok
      subst h_ok
      show ((s.tokens.tokens.push (IxToken.mk' startPos _
          _ _ _))[s.tokens.tokens.size]'_).start = startPos
      simp only [Array.getElem_push_eq, IxToken.mk']
    · simp at h_ok

theorem scanTagDirectiveIx_new_token_start {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset)
    (s' : ScannerStateIx input)
    (h_ok : scanTagDirectiveIx s cAfterWS startPos hStart = .ok s')
    (hj : s.tokens.size < s'.tokens.size) :
    (s'.tokens[s.tokens.size]'hj).start = startPos := by
  unfold scanTagDirectiveIx at h_ok
  simp only [Except.ok.injEq] at h_ok
  subst h_ok
  show ((s.tokens.tokens.push (IxToken.mk' startPos _
      _ _ _))[s.tokens.tokens.size]'_).start = startPos
  simp only [Array.getElem_push_eq, IxToken.mk']

/-! #### §8.7.10''  ScanInvIx for emit-at-prior-cursor helpers.

The closer is `ScanInvIx_of_one_emit_at_pre_cursor` (OrderedPrims §8.6'').
For `scanAnchorOrAliasIx` / `scanTagIx`, exactly one token is added at
`s.tokens.size` with `.start = s.cursor.pos` (per the bricks above).
For `scanDirectiveIx`, the YAML and TAG branches each add one token
with the same `startPos = s.cursor.pos`; the reserved-directive
default branch adds *no* token (tokens preserved by field update),
so the `h_new` precondition is satisfied vacuously. -/

theorem scanAnchorOrAliasIx_preserves_ScanInvIx {input : String}
    (s s' : ScannerStateIx input) (isAnchor : Bool) (h : ScanInvIx s)
    (h_ok : scanAnchorOrAliasIx s isAnchor = .ok s') : ScanInvIx s' := by
  apply ScanInvIx_of_one_emit_at_pre_cursor s s' h
    (scanAnchorOrAliasIx_offset_monotonic h_ok)
    (scanAnchorOrAliasIx_tokens_size_le h_ok)
  · intro i hi
    -- The lemma gives s'.tokens[i] = s.tokens[i] (TokenStream form, def-eq to .tokens.tokens).
    have h_eq : s'.tokens.tokens[i]'(Nat.lt_of_lt_of_le hi (scanAnchorOrAliasIx_tokens_size_le h_ok)) =
        s.tokens.tokens[i]'hi :=
      scanAnchorOrAliasIx_preserves_prefix s isAnchor s' h_ok i hi
    exact congrArg (fun t => t.start.offset) h_eq
  · intro k h_lo h_hi
    have h_size := scanAnchorOrAliasIx_adds_one_token s isAnchor s' h_ok
    -- h_size : s'.tokens.size = s.tokens.size + 1.  h_lo / h_hi are in tokens.tokens.size form.
    have h_lo' : s.tokens.size ≤ k := h_lo
    have h_hi' : k < s.tokens.size + 1 := h_size ▸ h_hi
    have h_keq : k = s.tokens.size := by omega
    subst h_keq
    have h_hj : s.tokens.size < s'.tokens.size := h_hi
    have h_brick := scanAnchorOrAliasIx_new_token_start s isAnchor s' h_ok h_hj
    exact congrArg YamlPos.offset h_brick

theorem scanTagIx_preserves_ScanInvIx {input : String}
    (s s' : ScannerStateIx input) (h : ScanInvIx s)
    (h_ok : scanTagIx s = .ok s') : ScanInvIx s' := by
  apply ScanInvIx_of_one_emit_at_pre_cursor s s' h
    (scanTagIx_offset_monotonic h_ok)
    (scanTagIx_tokens_size_le h_ok)
  · intro i hi
    have h_eq : s'.tokens.tokens[i]'(Nat.lt_of_lt_of_le hi (scanTagIx_tokens_size_le h_ok)) =
        s.tokens.tokens[i]'hi :=
      scanTagIx_preserves_prefix s s' h_ok i hi
    exact congrArg (fun t => t.start.offset) h_eq
  · intro k h_lo h_hi
    have h_size := scanTagIx_adds_one_token s s' h_ok
    have h_lo' : s.tokens.size ≤ k := h_lo
    have h_hi' : k < s.tokens.size + 1 := h_size ▸ h_hi
    have h_keq : k = s.tokens.size := by omega
    subst h_keq
    have h_hj : s.tokens.size < s'.tokens.size := h_hi
    have h_brick := scanTagIx_new_token_start s s' h_ok h_hj
    exact congrArg YamlPos.offset h_brick

/-- Upper bound: `scanYamlDirectiveIx` adds at most one token. -/
theorem scanYamlDirectiveIx_tokens_size_le_succ {input : String}
    {s s' : ScannerStateIx input} {cAfterWS : IxCursor input} {startPos : YamlPos}
    {hStart : startPos.offset ≤ cAfterWS.pos.offset}
    (h : scanYamlDirectiveIx s cAfterWS startPos hStart = .ok s') :
    s'.tokens.size ≤ s.tokens.size + 1 := by
  unfold scanYamlDirectiveIx at h
  by_cases hd : s.seenYamlDirective = true
  · rw [if_pos hd] at h; simp [Bind.bind, Except.bind] at h
  · rw [if_neg hd] at h
    simp only [pure_bind] at h
    split at h
    · simp only [Except.ok.injEq] at h; subst h; simp
    · simp at h

/-- Upper bound: `scanTagDirectiveIx` adds at most one token. -/
theorem scanTagDirectiveIx_tokens_size_le_succ {input : String}
    {s s' : ScannerStateIx input} {cAfterWS : IxCursor input} {startPos : YamlPos}
    {hStart : startPos.offset ≤ cAfterWS.pos.offset}
    (h : scanTagDirectiveIx s cAfterWS startPos hStart = .ok s') :
    s'.tokens.size ≤ s.tokens.size + 1 := by
  unfold scanTagDirectiveIx at h
  simp only [Except.ok.injEq] at h; subst h; simp

/-- Upper bound: `scanDirectiveIx` adds at most one token across all
    three branches (YAML, TAG, reserved). -/
theorem scanDirectiveIx_tokens_size_le_succ {input : String}
    {s s' : ScannerStateIx input} (h_ok : scanDirectiveIx s = .ok s') :
    s'.tokens.size ≤ s.tokens.size + 1 := by
  unfold scanDirectiveIx at h_ok
  split at h_ok
  · simp at h_ok
  · simp only at h_ok
    split at h_ok
    · -- YAML branch delegate.
      have := scanYamlDirectiveIx_tokens_size_le_succ h_ok
      show s'.tokens.size ≤ s.tokens.size + 1
      exact this
    · split at h_ok
      · -- TAG branch delegate.
        have := scanTagDirectiveIx_tokens_size_le_succ h_ok
        show s'.tokens.size ≤ s.tokens.size + 1
        exact this
      · -- Reserved: no token added.
        simp only [Except.ok.injEq] at h_ok; subst h_ok
        show s.tokens.size ≤ s.tokens.size + 1; omega

/-- New-token start for the composite `scanDirectiveIx`. Composes the
    `scanYamlDirectiveIx_new_token_start` / `scanTagDirectiveIx_new_token_start`
    bricks per branch; the reserved-directive default branch adds no
    token, making the `hj` precondition impossible. -/
theorem scanDirectiveIx_new_token_start {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanDirectiveIx s = .ok s')
    (hj : s.tokens.size < s'.tokens.size) :
    (s'.tokens[s.tokens.size]'hj).start = s.cursor.pos := by
  unfold scanDirectiveIx at h_ok
  split at h_ok
  · simp at h_ok
  · simp only at h_ok
    split at h_ok
    · -- YAML branch: the inner state's tokens.size = s.tokens.size def-eq, so
      -- the brick's conclusion matches.
      exact scanYamlDirectiveIx_new_token_start _ _ s.cursor.pos _ s' h_ok hj
    · split at h_ok
      · -- TAG branch
        exact scanTagDirectiveIx_new_token_start _ _ s.cursor.pos _ s' h_ok hj
      · -- Reserved-directive default: tokens unchanged → `hj` is impossible.
        simp only [Except.ok.injEq] at h_ok
        subst h_ok
        exact absurd hj (Nat.lt_irrefl _)

theorem scanDirectiveIx_preserves_ScanInvIx {input : String}
    (s s' : ScannerStateIx input) (h : ScanInvIx s)
    (h_ok : scanDirectiveIx s = .ok s') : ScanInvIx s' := by
  apply ScanInvIx_of_one_emit_at_pre_cursor s s' h
    (scanDirectiveIx_offset_monotonic h_ok)
    (scanDirectiveIx_tokens_size_le h_ok)
  · intro i hi
    have h_eq : s'.tokens.tokens[i]'(Nat.lt_of_lt_of_le hi (scanDirectiveIx_tokens_size_le h_ok)) =
        s.tokens.tokens[i]'hi :=
      scanDirectiveIx_preserves_prefix s s' h_ok i hi
    exact congrArg (fun t => t.start.offset) h_eq
  · intro k h_lo h_hi
    -- Establish k = s.tokens.size when there *is* a new token, else hit the
    -- vacuous reserved branch via scanDirectiveIx_new_token_start.
    -- Strategy: bound s'.tokens.size by s.tokens.size + 1 (true for all three
    -- branches), then close via `omega` + the brick.
    -- We do not have a tight `_adds_at_most_one_token` lemma; instead we
    -- delegate per-branch from inside the brick (which already discharges the
    -- contradiction in the no-new-token case).
    -- For the closer's `h_new` we need exactly k = s.tokens.size, which we
    -- prove by ruling out k > s.tokens.size:
    by_cases h_eq : k = s.tokens.size
    · subst h_eq
      have h_hj : s.tokens.size < s'.tokens.size := h_hi
      have h_brick := scanDirectiveIx_new_token_start s s' h_ok h_hj
      exact congrArg YamlPos.offset h_brick
    · -- k ≠ s.tokens.size, but s.tokens.size ≤ k. So k > s.tokens.size.
      -- Use `scanDirectiveIx_tokens_size_le_succ` to bound s'.tokens.size,
      -- giving k < s.tokens.size + 1 ⇒ k = s.tokens.size, contradicting h_eq.
      exfalso
      have h_at_most_one := scanDirectiveIx_tokens_size_le_succ h_ok
      have h_lo' : s.tokens.size ≤ k := h_lo
      have h_hi_ts : k < s'.tokens.size := h_hi
      omega

/-! ### §8.8  Per-dispatcher preservation: preprocess + four dispatchers.

Each sub-dispatcher of `scanNextTokenIx` composes the §8.7 per-helper
bricks. The `_ok_some_cases` / `_ok_monotonic` enumeration lemmas
from `Proofs/Scanner/IndexedDispatch.lean` reduce each dispatcher to a
finite case-split on its productions, after which we just apply the
matching per-helper preservation lemma.

`dispatchBlockIndicators` is the only dispatcher requiring
`SimpleKeyValidIx` (for the `scanValueIx` production); it is supplied
via `h_akv.1` from the paired invariant.

`dispatchContent` has four inline-scalar branches (block scalar,
double-quoted, single-quoted, plain) that compute the result via
`{ sAfter.emitAt s.cursor.pos token hBound with simpleKeyAllowed := false }`.
These do *not* have packaged per-helper bricks; we discharge them via
a private `_scalar_emitAt_preserves_*` helper that captures the
shared pattern using `ScanInvIx_of_one_emit_at_pre_cursor` /
`AllKeysValidIx_mono`. -/

/-! #### §8.8.0  Inline-scalar helper (shared by dispatchContent's four
scalar branches).

Each scalar branch produces `{ sAfter.emitAt s.cursor.pos tok hBound
with simpleKeyAllowed := false }` where `sAfter := { s with cursor :=
cAfter }`. The `simpleKey`, `simpleKeyStack`, `flowStack`, etc. fields
are inherited from `sAfter` (= those of `s`), so monotonicity-based
preservation closes both invariants. -/

/-- The fully-folded resulting state has `.tokens` = `s.tokens.push (new token)`,
    `.cursor = cAfter`, `.simpleKey = s.simpleKey`, etc. This lemma packages
    those projections by structural rfl (the `let __src := emitAt; { src with
    simpleKeyAllowed := false }` form unfolds projection-by-projection
    definitionally). -/
theorem _scalar_emitAt_tokens_size_eq {input : String}
    (s : ScannerStateIx input) (cAfter : IxCursor input) (tok : YamlToken)
    (hBound : s.cursor.pos.offset ≤ cAfter.pos.offset) :
    (({ ({ s with cursor := cAfter } : ScannerStateIx input).emitAt
        s.cursor.pos tok hBound with simpleKeyAllowed := false }
        : ScannerStateIx input)).tokens.tokens.size = s.tokens.tokens.size + 1 := by
  show (s.tokens.tokens.push _).size = _
  exact Array.size_push ..

theorem _scalar_emitAt_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (cAfter : IxCursor input) (tok : YamlToken)
    (hBound : s.cursor.pos.offset ≤ cAfter.pos.offset) (h : ScanInvIx s) :
    ScanInvIx ({ ({ s with cursor := cAfter } : ScannerStateIx input).emitAt
        s.cursor.pos tok hBound with simpleKeyAllowed := false }
        : ScannerStateIx input) := by
  have h_size_eq := _scalar_emitAt_tokens_size_eq s cAfter tok hBound
  refine ScanInvIx_of_one_emit_at_pre_cursor s _ h ?_ ?_ ?_ ?_
  · -- h_off: cursor.pos.offset folds to cAfter.pos.offset
    exact hBound
  · -- h_size
    rw [h_size_eq]; omega
  · -- h_pref
    intro i hi
    have h_eq :
        ({ ({ s with cursor := cAfter } : ScannerStateIx input).emitAt
            s.cursor.pos tok hBound with simpleKeyAllowed := false }
            : ScannerStateIx input).tokens.tokens[i]'(by
          rw [h_size_eq]; omega) =
        s.tokens.tokens[i]'hi := by
      show (s.tokens.tokens.push _)[i]'_ = _
      exact Array.getElem_push_lt hi
    exact congrArg (fun t => t.start.offset) h_eq
  · -- h_new
    intro k h_lo h_hi
    have h_hi' : k < s.tokens.tokens.size + 1 := h_size_eq ▸ h_hi
    have h_keq : k = s.tokens.tokens.size := by omega
    subst h_keq
    have h_get : ({ ({ s with cursor := cAfter } : ScannerStateIx input).emitAt
        s.cursor.pos tok hBound with simpleKeyAllowed := false }
        : ScannerStateIx input).tokens.tokens[s.tokens.tokens.size]'h_hi =
        IxToken.mk' s.cursor.pos tok cAfter.pos hBound cAfter.posBound := by
      show (s.tokens.tokens.push _)[s.tokens.tokens.size]'h_hi = _
      exact Array.getElem_push_eq ..
    rw [h_get]; rfl

theorem _scalar_emitAt_preserves_AllKeysValidIx {input : String}
    (s : ScannerStateIx input) (cAfter : IxCursor input) (tok : YamlToken)
    (hBound : s.cursor.pos.offset ≤ cAfter.pos.offset) (h_akv : AllKeysValidIx s) :
    AllKeysValidIx ({ ({ s with cursor := cAfter } : ScannerStateIx input).emitAt
        s.cursor.pos tok hBound with simpleKeyAllowed := false }
        : ScannerStateIx input) := by
  have h_size_eq := _scalar_emitAt_tokens_size_eq s cAfter tok hBound
  refine AllKeysValidIx_mono s _ h_akv ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rw [h_size_eq]; omega
  · intro i hi
    show (s.tokens.tokens.push _)[i]'_ = s.tokens.tokens[i]'hi
    exact Array.getElem_push_lt hi

/-! #### §8.8.1  `scanNextTokenIx_preprocess` preservation.

`preprocess` chains: `skipToContentS` (cursor-only) → optional
`unwindIndentsIx` (emits blockEnd tokens) → optional field update on
`needIndentCheck` → `saveSimpleKeyIx` (may emit two placeholders) →
peek. We follow the same scaffold as `_preprocess_preserves_prefix`
(StreamStart.lean §7.7') but for the §8 invariants. -/

theorem scanNextTokenIx_preprocess_preserves_ScanInvIx {input : String}
    {s s' : ScannerStateIx input} {c : Char} (h : ScanInvIx s)
    (h_pre : scanNextTokenIx_preprocess s = .ok (some (s', c))) : ScanInvIx s' := by
  have h_skip := skipToContentS_preserves_ScanInvIx s h
  unfold scanNextTokenIx_preprocess at h_pre
  simp only at h_pre
  split at h_pre
  · simp at h_pre
  · split at h_pre
    · -- with indent check
      split at h_pre
      · simp at h_pre
      · split at h_pre
        · simp at h_pre
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_pre
          obtain ⟨hs, _⟩ := h_pre
          subst hs
          have h_unwind := unwindIndentsIx_preserves_ScanInvIx s.skipToContentS
            (s.skipToContentS.cursor.pos.col : Int) h_skip
          have h_fld : ScanInvIx ({ unwindIndentsIx s.skipToContentS
              (s.skipToContentS.cursor.pos.col : Int) with needIndentCheck := false }
              : ScannerStateIx input) :=
            ScanInvIx_of_field_update _ _ h_unwind rfl rfl
          exact saveSimpleKeyIx_preserves_ScanInvIx _ h_fld
    · -- without indent check
      split at h_pre
      · simp at h_pre
      · split at h_pre
        · simp at h_pre
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_pre
          obtain ⟨hs, _⟩ := h_pre
          subst hs
          exact saveSimpleKeyIx_preserves_ScanInvIx _ h_skip

theorem scanNextTokenIx_preprocess_preserves_AllKeysValidIx {input : String}
    {s s' : ScannerStateIx input} {c : Char} (h_akv : AllKeysValidIx s)
    (h_pre : scanNextTokenIx_preprocess s = .ok (some (s', c))) : AllKeysValidIx s' := by
  have h_skip := skipToContentS_preserves_AllKeysValidIx s h_akv
  unfold scanNextTokenIx_preprocess at h_pre
  simp only at h_pre
  split at h_pre
  · simp at h_pre
  · split at h_pre
    · -- with indent check
      split at h_pre
      · simp at h_pre
      · split at h_pre
        · simp at h_pre
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_pre
          obtain ⟨hs, _⟩ := h_pre
          subst hs
          have h_unwind := unwindIndentsIx_preserves_AllKeysValidIx s.skipToContentS
            (s.skipToContentS.cursor.pos.col : Int) h_skip
          have h_fld : AllKeysValidIx ({ unwindIndentsIx s.skipToContentS
              (s.skipToContentS.cursor.pos.col : Int) with needIndentCheck := false }
              : ScannerStateIx input) := by
            refine AllKeysValidIx_mono _ _ h_unwind rfl rfl ?_ ?_
            · exact Nat.le_refl _
            · intro i hi; rfl
          exact saveSimpleKeyIx_preserves_AllKeysValidIx _ h_fld
    · -- without indent check
      split at h_pre
      · simp at h_pre
      · split at h_pre
        · simp at h_pre
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_pre
          obtain ⟨hs, _⟩ := h_pre
          subst hs
          exact saveSimpleKeyIx_preserves_AllKeysValidIx _ h_skip

/-! #### §8.8.2  `scanNextTokenIx_dispatchStructural` preservation. -/

theorem scanNextTokenIx_dispatchStructural_preserves_ScanInvIx {input : String}
    {s s' : ScannerStateIx input} {c : Char} (h : ScanInvIx s)
    (h_ok : scanNextTokenIx_dispatchStructural s c = .ok (some s')) : ScanInvIx s' := by
  rcases scanNextTokenIx_dispatchStructural_ok_some_cases h_ok with heq | hOk | hOk
  · subst heq; exact scanDocumentStartIx_preserves_ScanInvIx s h
  · exact scanDocumentEndIx_preserves_ScanInvIx s s' h hOk
  · exact scanDirectiveIx_preserves_ScanInvIx s s' h hOk

theorem scanNextTokenIx_dispatchStructural_preserves_AllKeysValidIx {input : String}
    {s s' : ScannerStateIx input} {c : Char} (h_akv : AllKeysValidIx s)
    (h_ok : scanNextTokenIx_dispatchStructural s c = .ok (some s')) : AllKeysValidIx s' := by
  rcases scanNextTokenIx_dispatchStructural_ok_some_cases h_ok with heq | hOk | hOk
  · subst heq; exact scanDocumentStartIx_preserves_AllKeysValidIx s h_akv
  · exact scanDocumentEndIx_preserves_AllKeysValidIx s s' h_akv hOk
  · exact scanDirectiveIx_preserves_AllKeysValidIx s s' h_akv hOk

/-! #### §8.8.3  `scanNextTokenIx_dispatchFlowIndicators` preservation. -/

theorem scanNextTokenIx_dispatchFlowIndicators_preserves_ScanInvIx {input : String}
    {s s' : ScannerStateIx input} {c : Char} (h : ScanInvIx s)
    (h_ok : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s')) : ScanInvIx s' := by
  rcases scanNextTokenIx_dispatchFlowIndicators_ok_some_cases h_ok with
    heq | heq | heq | heq | hOk
  · subst heq; exact scanFlowSequenceStartIx_preserves_ScanInvIx s h
  · subst heq; exact scanFlowSequenceEndIx_preserves_ScanInvIx s h
  · subst heq; exact scanFlowMappingStartIx_preserves_ScanInvIx s h
  · subst heq; exact scanFlowMappingEndIx_preserves_ScanInvIx s h
  · exact scanFlowEntryIx_preserves_ScanInvIx s s' h hOk

theorem scanNextTokenIx_dispatchFlowIndicators_preserves_AllKeysValidIx {input : String}
    {s s' : ScannerStateIx input} {c : Char} (h_akv : AllKeysValidIx s)
    (h_ok : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s')) : AllKeysValidIx s' := by
  rcases scanNextTokenIx_dispatchFlowIndicators_ok_some_cases h_ok with
    heq | heq | heq | heq | hOk
  · subst heq; exact scanFlowSequenceStartIx_preserves_AllKeysValidIx s h_akv
  · subst heq; exact scanFlowSequenceEndIx_preserves_AllKeysValidIx s h_akv
  · subst heq; exact scanFlowMappingStartIx_preserves_AllKeysValidIx s h_akv
  · subst heq; exact scanFlowMappingEndIx_preserves_AllKeysValidIx s h_akv
  · exact scanFlowEntryIx_preserves_AllKeysValidIx s s' h_akv hOk

/-! #### §8.8.4  `scanNextTokenIx_dispatchBlockIndicators` preservation.

Note: the `scanValueIx` production requires `SimpleKeyValidIx`, so
the ScanInvIx-side proof needs the paired `AllKeysValidIx` to
extract `h_akv.1`. -/

theorem scanNextTokenIx_dispatchBlockIndicators_preserves_ScanInvIx {input : String}
    {s s' : ScannerStateIx input} {c : Char} (h : ScanInvIx s) (h_akv : AllKeysValidIx s)
    (h_ok : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s')) : ScanInvIx s' := by
  rcases scanNextTokenIx_dispatchBlockIndicators_ok_some_cases h_ok with hOk | hOk | hOk
  · exact scanBlockEntryIx_preserves_ScanInvIx s s' h hOk
  · exact scanKeyIx_preserves_ScanInvIx s s' h hOk
  · exact scanValueIx_preserves_ScanInvIx s s' h h_akv.1 hOk

theorem scanNextTokenIx_dispatchBlockIndicators_preserves_AllKeysValidIx {input : String}
    {s s' : ScannerStateIx input} {c : Char} (h_akv : AllKeysValidIx s)
    (h_ok : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s')) : AllKeysValidIx s' := by
  rcases scanNextTokenIx_dispatchBlockIndicators_ok_some_cases h_ok with hOk | hOk | hOk
  · exact scanBlockEntryIx_preserves_AllKeysValidIx s s' h_akv hOk
  · exact scanKeyIx_preserves_AllKeysValidIx s s' h_akv hOk
  · exact scanValueIx_preserves_AllKeysValidIx s s' h_akv hOk

/-! #### §8.8.5  `scanNextTokenIx_dispatchContent` preservation.

Six productions: anchor/alias (`&`/`*`), tag (`!`), block scalar
(`|`/`>`), double-quoted (`"`), single-quoted (`'`), plain scalar.
The four scalar productions use the `_scalar_emitAt_preserves_*`
helper above. -/

theorem scanNextTokenIx_dispatchContent_preserves_ScanInvIx {input : String}
    {s s' : ScannerStateIx input} {c : Char} (h : ScanInvIx s)
    (h_ok : scanNextTokenIx_dispatchContent s c = .ok s') : ScanInvIx s' := by
  -- Peel the 7-way content dispatch one `if` at a time with `by_cases`/`rw` (a single `split`
  -- over the whole dispatch exceeds `split`'s internal simp step budget under Lean 4.31.0);
  -- the inner `split` on a scalar production's `Except` match stays cheap.
  unfold scanNextTokenIx_dispatchContent at h_ok
  by_cases hg1 : (c == '&') = true
  · -- '&' anchor
    rw [if_pos hg1] at h_ok
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
    cases hA : scanAnchorOrAliasIx s true with
    | error e => rw [hA] at h_ok; cases h_ok
    | ok v =>
      rw [hA] at h_ok
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      exact scanAnchorOrAliasIx_preserves_ScanInvIx s v true h hA
  · rw [if_neg hg1] at h_ok
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
    by_cases hg2 : (c == '*') = true
    · -- '*' alias
      rw [if_pos hg2] at h_ok
      cases hA : scanAnchorOrAliasIx s false with
      | error e => rw [hA] at h_ok; cases h_ok
      | ok v =>
        rw [hA] at h_ok
        simp only [Except.ok.injEq] at h_ok; subst h_ok
        exact scanAnchorOrAliasIx_preserves_ScanInvIx s v false h hA
    · rw [if_neg hg2] at h_ok
      by_cases hg3 : (c == '!') = true
      · -- '!' tag
        rw [if_pos hg3] at h_ok
        cases hT : scanTagIx s with
        | error e => rw [hT] at h_ok; cases h_ok
        | ok v =>
          rw [hT] at h_ok
          simp only [Except.ok.injEq] at h_ok; subst h_ok
          exact scanTagIx_preserves_ScanInvIx s v h hT
      · rw [if_neg hg3] at h_ok
        by_cases hg4 : (c == '|' || c == '>') = true
        · -- block scalar
          rw [if_pos hg4] at h_ok
          split at h_ok
          · rename_i r hBS
            simp only [Except.ok.injEq] at h_ok; subst h_ok
            exact _scalar_emitAt_preserves_ScanInvIx s _ _
              (scanBlockScalarIx_offset_monotonic s.cursor _ hBS) h
          · cases h_ok
        · rw [if_neg hg4] at h_ok
          by_cases hg5 : (c == '"') = true
          · -- double-quoted
            rw [if_pos hg5] at h_ok
            split at h_ok
            · rename_i r hDQ
              simp only [Except.ok.injEq] at h_ok; subst h_ok
              exact _scalar_emitAt_preserves_ScanInvIx s _ _
                (Nat.le_of_lt (scanDoubleQuotedIx_offset_lt s.cursor hDQ)) h
            · cases h_ok
          · rw [if_neg hg5] at h_ok
            by_cases hg6 : (c == '\'') = true
            · -- single-quoted
              rw [if_pos hg6] at h_ok
              split at h_ok
              · rename_i r hSQ
                simp only [Except.ok.injEq] at h_ok; subst h_ok
                exact _scalar_emitAt_preserves_ScanInvIx s _ _
                  (Nat.le_of_lt (scanSingleQuotedIx_offset_lt s.cursor hSQ)) h
              · cases h_ok
            · rw [if_neg hg6] at h_ok
              -- plain scalar (success) vs error: one small inner `if`
              split at h_ok
              · simp only [Except.ok.injEq] at h_ok; subst h_ok
                exact _scalar_emitAt_preserves_ScanInvIx s _ _
                  (scanPlainScalarIx_offset_monotonic s.cursor _ _) h
              · cases h_ok

theorem scanNextTokenIx_dispatchContent_preserves_AllKeysValidIx {input : String}
    {s s' : ScannerStateIx input} {c : Char} (h_akv : AllKeysValidIx s)
    (h_ok : scanNextTokenIx_dispatchContent s c = .ok s') : AllKeysValidIx s' := by
  -- Peel the 7-way content dispatch one `if` at a time with `by_cases`/`rw` (a single `split`
  -- over the whole dispatch exceeds `split`'s internal simp step budget under Lean 4.31.0);
  -- the inner `split` on a scalar production's `Except` match stays cheap.
  unfold scanNextTokenIx_dispatchContent at h_ok
  by_cases hg1 : (c == '&') = true
  · -- '&' anchor
    rw [if_pos hg1] at h_ok
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
    cases hA : scanAnchorOrAliasIx s true with
    | error e => rw [hA] at h_ok; cases h_ok
    | ok v =>
      rw [hA] at h_ok
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      exact scanAnchorOrAliasIx_preserves_AllKeysValidIx s v true h_akv hA
  · rw [if_neg hg1] at h_ok
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
    by_cases hg2 : (c == '*') = true
    · -- '*' alias
      rw [if_pos hg2] at h_ok
      cases hA : scanAnchorOrAliasIx s false with
      | error e => rw [hA] at h_ok; cases h_ok
      | ok v =>
        rw [hA] at h_ok
        simp only [Except.ok.injEq] at h_ok; subst h_ok
        exact scanAnchorOrAliasIx_preserves_AllKeysValidIx s v false h_akv hA
    · rw [if_neg hg2] at h_ok
      by_cases hg3 : (c == '!') = true
      · -- '!' tag
        rw [if_pos hg3] at h_ok
        cases hT : scanTagIx s with
        | error e => rw [hT] at h_ok; cases h_ok
        | ok v =>
          rw [hT] at h_ok
          simp only [Except.ok.injEq] at h_ok; subst h_ok
          exact scanTagIx_preserves_AllKeysValidIx s v h_akv hT
      · rw [if_neg hg3] at h_ok
        by_cases hg4 : (c == '|' || c == '>') = true
        · -- block scalar
          rw [if_pos hg4] at h_ok
          split at h_ok
          · rename_i r hBS
            simp only [Except.ok.injEq] at h_ok; subst h_ok
            exact _scalar_emitAt_preserves_AllKeysValidIx s _ _
              (scanBlockScalarIx_offset_monotonic s.cursor _ hBS) h_akv
          · cases h_ok
        · rw [if_neg hg4] at h_ok
          by_cases hg5 : (c == '"') = true
          · -- double-quoted
            rw [if_pos hg5] at h_ok
            split at h_ok
            · rename_i r hDQ
              simp only [Except.ok.injEq] at h_ok; subst h_ok
              exact _scalar_emitAt_preserves_AllKeysValidIx s _ _
                (Nat.le_of_lt (scanDoubleQuotedIx_offset_lt s.cursor hDQ)) h_akv
            · cases h_ok
          · rw [if_neg hg5] at h_ok
            by_cases hg6 : (c == '\'') = true
            · -- single-quoted
              rw [if_pos hg6] at h_ok
              split at h_ok
              · rename_i r hSQ
                simp only [Except.ok.injEq] at h_ok; subst h_ok
                exact _scalar_emitAt_preserves_AllKeysValidIx s _ _
                  (Nat.le_of_lt (scanSingleQuotedIx_offset_lt s.cursor hSQ)) h_akv
              · cases h_ok
            · rw [if_neg hg6] at h_ok
              -- plain scalar (success) vs error: one small inner `if`
              split at h_ok
              · simp only [Except.ok.injEq] at h_ok; subst h_ok
                exact _scalar_emitAt_preserves_AllKeysValidIx s _ _
                  (scanPlainScalarIx_offset_monotonic s.cursor _ _) h_akv
              · cases h_ok

end L4YAML.Proofs.Indexed.ScannerCorrectness
