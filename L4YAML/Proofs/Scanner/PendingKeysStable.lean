/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import L4YAML.Proofs.Coupling.ScalarCoupling
public import L4YAML.Proofs.Output.EmitterScannability.ScanSteps
public import L4YAML.Proofs.Scanner.BlockScalarFlowGuard
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey
public import L4YAML.Proofs.Scanner.FlowIndentStable
public import L4YAML.Proofs.Scanner.IndentStackBase
public import L4YAML.Proofs.Scanner.PreprocessIndentStable
public import L4YAML.Proofs.Scanner.ScannerContracts
public import L4YAML.Proofs.Scanner.ScannerDispatch
public import L4YAML.Proofs.Scanner.ScannerDocument
public import L4YAML.Proofs.Scanner.ScannerIndentStack
public import L4YAML.Proofs.Scanner.ScannerLinePreservation
public import L4YAML.Proofs.Scanner.ScannerLoopInvariant
public import L4YAML.Proofs.Scanner.ScannerScalar
public import L4YAML.Proofs.Scanner.ScannerWhitespace
public import L4YAML.Scanner.Scanner
@[expose] public section Blanket

/-! # `pendingKeys` is stable through every non-writer scanner step (DOCS item 338)

`ScannerState.pendingKeys` is in lockstep with `indents` (item 335): the only
writers are the four stack writers (`unwindIndentsLoop`, `pushSequenceIndent`,
`pushMappingIndent`, `scanValuePrepare`), the two register writers that mark
and settle a level (`scanKey`, `scanValue`) and the stale-key hook.  Every other
step leaves it alone, and this file says so lemma by lemma — each one the
`pendingKeys` twin of an existing `_preserves_pendingKeys` lemma, so that
`PendingKeySound` (the token-level carrier) can be transported through them. -/

namespace L4YAML.Proofs.PendingKeysStable

open L4YAML.Scanner
open L4YAML.Proofs.CloseStaleExplicitKey
open L4YAML.Proofs.FlowIndentStable
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.ScalarCoupling (terminates_state_eq)
open L4YAML.Proofs.ScannerContracts
open L4YAML.Proofs.ScannerDocument
open L4YAML.Proofs.ScannerIndentStack
open L4YAML.Proofs.ScannerLoopInvariant
open L4YAML.Proofs.ScannerScalar
open L4YAML.Proofs.ScannerWhitespace
open L4YAML.Proofs.FlowIndentStable L4YAML.Proofs.IndentStackBase L4YAML.Proofs.PreprocessIndentStable

/-! ## §0 Primitives — `pendingKeys` twins of the `EmitterScannability` `_preserves_indents` lemmas -/

-- from L4YAML/Proofs/Scanner/FlowIndentStable.lean:116
-- from L4YAML/Proofs/Scanner/FlowIndentStable.lean:148
-- from L4YAML/Proofs/Scanner/FlowIndentStable.lean:164
-- from L4YAML/Proofs/Scanner/FlowIndentStable.lean:181
-- from L4YAML/Proofs/Scanner/FlowIndentStable.lean:198
-- from L4YAML/Proofs/Scanner/FlowIndentStable.lean:262
-- from L4YAML/Proofs/Scanner/FlowIndentStable.lean:317
-- from L4YAML/Proofs/Scanner/FlowIndentStable.lean:382
-- from L4YAML/Proofs/Scanner/FlowIndentStable.lean:393
-- from L4YAML/Proofs/Scanner/FlowIndentStable.lean:413
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:149
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:157
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:161
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:173
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:177
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:188
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:200
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:211
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:222
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:233
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:247
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:256
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:268
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:296
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:308
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:321
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:332
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:344
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:357
-- from L4YAML/Proofs/Scanner/IndentStackBase.lean:547
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:62
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:73
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:77
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:90
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:94
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:108
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:127
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:155
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:187
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:402
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:656
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:669
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:683
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:696
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:710
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:722
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:736
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:743
-- from L4YAML/Proofs/Scanner/PreprocessIndentStable.lean:754
-- from L4YAML/Proofs/Scanner/ScannerDispatch.lean:130
-- from L4YAML/Proofs/Scanner/ScannerDispatch.lean:147
-- from L4YAML/Proofs/Scanner/ScannerWhitespace.lean:77

lemma emit_pendingKeys (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).pendingKeys = s.pendingKeys := by
  rfl

lemma advance_preserves_pendingKeys (s : ScannerState) :
    s.advance.pendingKeys = s.pendingKeys := by
  unfold ScannerState.advance
  split
  · simp only []
    split
    · rfl
    · split <;> rfl
  · rfl

lemma collectHexDigitsLoop_preserves_pendingKeys (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.pendingKeys = s.pendingKeys := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ _ ih =>
    unfold collectHexDigitsLoop
    split
    · split
      · rw [ih, advance_preserves_pendingKeys]
      · rfl
    · rfl

lemma parseHexEscape_preserves_pendingKeys (s : ScannerState) (digits : Nat)
    (result : Char × ScannerState) (h : parseHexEscape s digits = .ok result) :
    result.snd.pendingKeys = s.pendingKeys := by
  unfold parseHexEscape at h
  simp only [] at h
  split at h
  · contradiction
  · split at h
    · injection h with h_eq; subst h_eq
      exact collectHexDigitsLoop_preserves_pendingKeys s "" digits
    · contradiction

lemma processEscape_preserves_pendingKeys (s : ScannerState) (result : Char × ScannerState)
    (h : processEscape s = .ok result) :
    result.snd.pendingKeys = s.pendingKeys := by
  unfold processEscape at h
  split at h <;> try contradiction
  split at h
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · injection h with h_eq; subst h_eq; exact advance_preserves_pendingKeys s
  · simp only [] at h; exact parseHexEscape_preserves_pendingKeys _ _ _ h |>.trans (advance_preserves_pendingKeys s)
  · simp only [] at h; exact parseHexEscape_preserves_pendingKeys _ _ _ h |>.trans (advance_preserves_pendingKeys s)
  · simp only [] at h; exact parseHexEscape_preserves_pendingKeys _ _ _ h |>.trans (advance_preserves_pendingKeys s)
  · contradiction

lemma advance_pendingKeys (s : ScannerState) :
    s.advance.pendingKeys = s.pendingKeys := advance_preserves_pendingKeys s

lemma scanFlowSequenceStart_preserves_pendingKeys (s : ScannerState) :
    (scanFlowSequenceStart s).pendingKeys = s.pendingKeys := by
  unfold scanFlowSequenceStart; simp only [advance_preserves_pendingKeys, ScannerState.emit, ScannerState.emitAt]

lemma scanFlowMappingStart_preserves_pendingKeys (s : ScannerState) :
    (scanFlowMappingStart s).pendingKeys = s.pendingKeys := by
  unfold scanFlowMappingStart; simp only [advance_preserves_pendingKeys, ScannerState.emit, ScannerState.emitAt]

lemma scanValueClearKey_pendingKeys (s : ScannerState) :
    (scanValueClearKey s).pendingKeys = s.pendingKeys := by
  unfold scanValueClearKey
  rcases hek : s.explicitKeyLine with _ | ekLine
  · rfl
  · dsimp only
    split <;> (try split) <;> rfl

/-- `scanValuePrepare`'s `[187]` push is `!inFlow`-guarded. -/
lemma scanValuePrepare_pendingKeys_of_inFlow {s : ScannerState} (h_flow : s.inFlow = true) :
    (scanValuePrepare s).pendingKeys = s.pendingKeys := by
  unfold scanValuePrepare
  simp only [h_flow, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  split <;> (try split) <;> rfl

/-- In flow the `:` settles `pendingKeys` to the advanced state's own, which is `s`'s. -/
lemma scanValue_pendingKeys_of_inFlow {s s' : ScannerState}
    (h_flow : s.inFlow = true) (hok : scanValue s = .ok s') :
    s'.pendingKeys = s.pendingKeys := by
  have key : (((scanValuePrepare (scanValueClearKey s)).emit YamlToken.value).advance).pendingKeys
      = s.pendingKeys := by
    rw [advance_preserves_pendingKeys, emit_pendingKeys,
        scanValuePrepare_pendingKeys_of_inFlow
          (by rw [(scanValueClearKey_fields s).2.2.1]; exact h_flow)]
    exact scanValueClearKey_pendingKeys s
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  repeat' split at hok
  all_goals first
    | contradiction
    | (simp only [Except.ok.injEq] at hok; subst hok; simp only [h_flow, Bool.true_or, ite_true]; exact key)

/-- `scanKey`'s `[187]` push and its mark are both `!inFlow`-guarded. -/
lemma scanKey_pendingKeys_of_inFlow {s s' : ScannerState}
    (h_flow : s.inFlow = true) (hok : scanKey s = .ok s') :
    s'.pendingKeys = s.pendingKeys := by
  unfold scanKey at hok
  simp only [bind, Except.bind, h_flow, Bool.not_true, ite_eq_right Bool.false_ne_true] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok)
  all_goals simp [advance_preserves_pendingKeys, emit_pendingKeys, h_flow]


lemma skipWhitespaceLoop_preserves_pendingKeys (s : ScannerState) (fuel : Nat) :
    (skipWhitespaceLoop s fuel).pendingKeys = s.pendingKeys := by
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ fuel' ih =>
    unfold skipWhitespaceLoop
    split
    · split
      · rw [ih, advance_pendingKeys]
      · rfl
    · rfl

lemma skipWhitespace_preserves_pendingKeys (s : ScannerState) :
    (skipWhitespace s).pendingKeys = s.pendingKeys := skipWhitespaceLoop_preserves_pendingKeys s _

lemma consumeNewline_preserves_pendingKeys (s : ScannerState) :
    (consumeNewline s).pendingKeys = s.pendingKeys := by
  unfold consumeNewline
  split
  · -- some '\n' => { s.advance with needIndentCheck := true }
    exact advance_pendingKeys s
  · -- some '\r' => let s' := s.advance; match s'.peek? with ...
    dsimp only []
    split
    · -- s.advance.peek? = some '\n' (CRLF: raw offset skip preserves indents)
      exact advance_pendingKeys s
    · -- _ => { s.advance with needIndentCheck := true }
      exact advance_pendingKeys s
  · -- _ => s
    rfl

lemma foldQuotedNewlinesLoop_preserves_pendingKeys (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s emptyCount with
  | zero => unfold foldQuotedNewlinesLoop; rfl
  | succ _ ih =>
    unfold foldQuotedNewlinesLoop
    simp only []
    split
    · split
      · split
        · rfl
        · rw [ih, consumeNewline_preserves_pendingKeys, skipWhitespace_preserves_pendingKeys]
      · rfl
    · rfl

lemma skipSpacesLoop_preserves_pendingKeys (s : ScannerState) (fuel : Nat) :
    (skipSpacesLoop s fuel).pendingKeys = s.pendingKeys := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ fuel' ih =>
    unfold skipSpacesLoop
    split
    · rw [ih, advance_pendingKeys]
    · rfl

lemma skipSpaces_preserves_pendingKeys (s : ScannerState) :
    (skipSpaces s).pendingKeys = s.pendingKeys := skipSpacesLoop_preserves_pendingKeys s _

lemma foldQuotedNewlines_preserves_pendingKeys (s : ScannerState) (result : String × ScannerState)
    (h : foldQuotedNewlines s = .ok result) :
    result.snd.pendingKeys = s.pendingKeys := by
  unfold foldQuotedNewlines at h
  simp only [] at h
  split at h
  · split at h <;> try contradiction
    split at h
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_pendingKeys, skipSpaces_preserves_pendingKeys,
            foldQuotedNewlinesLoop_preserves_pendingKeys, consumeNewline_preserves_pendingKeys]
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_pendingKeys, skipSpaces_preserves_pendingKeys,
            foldQuotedNewlinesLoop_preserves_pendingKeys, consumeNewline_preserves_pendingKeys]
  · split at h
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_pendingKeys, skipSpaces_preserves_pendingKeys,
            foldQuotedNewlinesLoop_preserves_pendingKeys, consumeNewline_preserves_pendingKeys]
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_pendingKeys, skipSpaces_preserves_pendingKeys,
            foldQuotedNewlinesLoop_preserves_pendingKeys, consumeNewline_preserves_pendingKeys]

lemma collectDoubleQuotedLoop_preserves_pendingKeys (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    (result : String × ScannerState)
    (h : collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result) :
    result.snd.pendingKeys = s.pendingKeys := by
  -- protectedLen (default 0) generalised so the IH covers the fold shift (B2).
  suffices H : ∀ (p : Nat) (s : ScannerState) (content : String),
      collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd p = .ok result →
      result.snd.pendingKeys = s.pendingKeys by
    exact H 0 s content h
  clear h
  intro p s content h
  induction fuel generalizing s content p with
  | zero => unfold collectDoubleQuotedLoop at h; contradiction
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at h
    split at h <;> try contradiction
    · -- closing quote
      injection h with h_eq; subst h_eq
      exact advance_preserves_pendingKeys s
    · -- escape
      simp only [] at h
      split at h <;> try contradiction
      · split at h
        · -- escaped line break — the landing is a fold (item 87)
          simp only [bind, Except.bind] at h
          split at h <;> try contradiction
          rename_i fold_result heq_fold
          repeat' split at h
          all_goals first
            | contradiction
            | exact (ih _ _ _ h).trans (foldQuotedNewlines_preserves_pendingKeys _ _ heq_fold)
                |>.trans (advance_preserves_pendingKeys s)
        · simp only [bind, Except.bind] at h
          split at h <;> try contradiction
          rename_i escape_result heq_escape
          cases escape_result
          exact (ih _ _ _ h).trans (processEscape_preserves_pendingKeys _ _ heq_escape)
                |>.trans (advance_preserves_pendingKeys s)
    · -- regular character
      split at h
      · simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq_fold
        split at h <;> try contradiction
        split at h <;> try contradiction
        -- 4.32.0: `== " "` guard splits into recursive branches; close each via IH
        split at h <;> (first | (exact (ih _ _ _ h).trans (foldQuotedNewlines_preserves_pendingKeys _ _ heq_fold)) | contradiction)
      · split at h <;> try contradiction
        exact (ih _ _ _ h).trans (advance_preserves_pendingKeys s)

lemma scanDoubleQuoted_preserves_pendingKeys (s s' : ScannerState)
    (h_ok : scanDoubleQuoted s = .ok s') :
    s'.pendingKeys = s.pendingKeys := by
  unfold scanDoubleQuoted at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok <;> try contradiction
  rename_i result heq
  have h_ids_collect := collectDoubleQuotedLoop_preserves_pendingKeys _ _ _ _ _ _ _ _ heq
  split at h_ok
  · split at h_ok <;> try contradiction
    injection h_ok with h_eq; subst h_eq
    unfold ScannerState.emitAt
    exact h_ids_collect.trans (advance_preserves_pendingKeys s)
  · injection h_ok with h_eq; subst h_eq
    unfold ScannerState.emitAt
    exact h_ids_collect.trans (advance_preserves_pendingKeys s)

lemma scanFlowSequenceEnd_preserves_pendingKeys (s : ScannerState) :
    (scanFlowSequenceEnd s).pendingKeys = s.pendingKeys := by
  unfold scanFlowSequenceEnd; dsimp only []; simp only [advance_preserves_pendingKeys, ScannerState.emit]

lemma scanFlowMappingEnd_preserves_pendingKeys (s : ScannerState) :
    (scanFlowMappingEnd s).pendingKeys = s.pendingKeys := by
  unfold scanFlowMappingEnd; dsimp only []; simp only [advance_preserves_pendingKeys, ScannerState.emit]

lemma collectAnchorNameLoop_preserves_pendingKeys (s : ScannerState) (name : String) (fuel : Nat) :
    (collectAnchorNameLoop s name fuel).2.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s name with
  | zero => unfold collectAnchorNameLoop; rfl
  | succ fuel' ih =>
    unfold collectAnchorNameLoop
    split
    · split
      · rw [ih, advance_pendingKeys]
      · rfl
    · rfl

lemma scanAnchorOrAlias_preserves_pendingKeys {s s' : ScannerState} {isAnchor : Bool}
    (hok : scanAnchorOrAlias s isAnchor = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanAnchorOrAlias at hok
  simp only [] at hok
  split at hok
  · simp at hok
  · simp only [Except.ok.injEq] at hok
    subst hok
    simp only [ScannerState.emitAt]
    rw [collectAnchorNameLoop_preserves_pendingKeys, advance_pendingKeys]

lemma collectVerbatimTagLoop_preserves_pendingKeys (s : ScannerState) (uri : String) (fuel : Nat) :
    (collectVerbatimTagLoop s uri fuel).2.2.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s uri with
  | zero => unfold collectVerbatimTagLoop; rfl
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop
    split
    · exact advance_pendingKeys s
    · split
      · rw [ih, advance_pendingKeys]
      · rfl
    · rfl

lemma scanVerbatimTag_preserves_pendingKeys {s s' : ScannerState} {p : YamlPos}
    (hok : scanVerbatimTag s p = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanVerbatimTag at hok
  simp only [] at hok
  split at hok
  · simp at hok
  · split at hok
    · simp at hok
    · simp only [Except.ok.injEq] at hok
      subst hok
      simp only [ScannerState.emitAt]
      rw [collectVerbatimTagLoop_preserves_pendingKeys, advance_pendingKeys]

lemma collectTagSuffixLoop_preserves_pendingKeys (s : ScannerState) (suffix : String) (fuel : Nat) :
    (collectTagSuffixLoop s suffix fuel).2.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s suffix with
  | zero => unfold collectTagSuffixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagSuffixLoop
    split
    · split
      · rw [ih, advance_pendingKeys]
      · rfl
    · rfl

lemma scanSecondaryTag_preserves_pendingKeys (s : ScannerState) (p : YamlPos) :
    (scanSecondaryTag s p).pendingKeys = s.pendingKeys := by
  unfold scanSecondaryTag
  simp only [ScannerState.emitAt]
  rw [collectTagSuffixLoop_preserves_pendingKeys, advance_pendingKeys]

lemma collectTagHandleLoop_preserves_pendingKeys (s : ScannerState) (chars : String) (fuel : Nat) :
    (collectTagHandleLoop s chars fuel).2.2.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s chars with
  | zero => unfold collectTagHandleLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleLoop
    split
    · exact advance_pendingKeys s
    · split
      · rw [ih, advance_pendingKeys]
      · rfl
    · rfl

lemma scanNamedTag_preserves_pendingKeys (s : ScannerState) (p : YamlPos) (inputEnd : Nat) :
    (scanNamedTag s p inputEnd).pendingKeys = s.pendingKeys := by
  unfold scanNamedTag
  simp only []
  split
  · simp only [ScannerState.emitAt]
    rw [collectTagSuffixLoop_preserves_pendingKeys, collectTagHandleLoop_preserves_pendingKeys]
  · simp only [ScannerState.emitAt]
    rw [collectTagSuffixLoop_preserves_pendingKeys, collectTagHandleLoop_preserves_pendingKeys]

lemma scanTag_preserves_pendingKeys {s s' : ScannerState}
    (hok : scanTag s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanTag at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · split at hok
    · simp at hok
    · rename_i s_inner h_inner
      simp only [Except.ok.injEq] at hok
      subst hok
      show s_inner.pendingKeys = _
      rw [scanVerbatimTag_preserves_pendingKeys h_inner, advance_pendingKeys]
  · simp only [Except.ok.injEq] at hok
    subst hok
    show (scanSecondaryTag s.advance s.currentPos).pendingKeys = _
    rw [scanSecondaryTag_preserves_pendingKeys, advance_pendingKeys]
  · simp only [Except.ok.injEq] at hok
    subst hok
    show (scanNamedTag s.advance s.currentPos s.inputEnd).pendingKeys = _
    rw [scanNamedTag_preserves_pendingKeys, advance_pendingKeys]

lemma dispatchContent_props_pendingKeys {s s' : ScannerState} {c : Char}
    (hc : c = '&' ∨ c = '!') (hok : scanNextToken_dispatchContent s c = .ok s') :
    s'.pendingKeys = s.pendingKeys := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  cases hc with
  | inl h =>
    subst h
    simp only [beq_self_eq_true, ite_true] at hok
    split at hok
    · simp at hok
    · split at hok
      · simp at hok
      · rename_i s_a ha
        simp only [Except.ok.injEq] at hok
        subst hok
        show s_a.pendingKeys = s.pendingKeys
        exact scanAnchorOrAlias_preserves_pendingKeys ha
  | inr h =>
    subst h
    have h1 : (('!' : Char) == '&' : Bool) = false := by decide
    have h2 : (('!' : Char) == '*' : Bool) = false := by decide
    simp only [h1, h2, ite_eq_right Bool.false_ne_true, beq_self_eq_true, ite_true] at hok
    split at hok
    · simp at hok
    · exact scanTag_preserves_pendingKeys hok

lemma emitAt_pendingKeys (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).pendingKeys = s.pendingKeys := by
  unfold ScannerState.emitAt; rfl

/-! ## §1 The twins of the `*IndentStable` / `IndentStackBase` lemmas -/

lemma collectSingleQuotedLoop_preserves_pendingKeys (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int)
    (inputEnd : Nat) (result : String × ScannerState)
    (h : collectSingleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd
         = .ok result) : result.2.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s content with
  | zero => unfold collectSingleQuotedLoop at h; contradiction
  | succ f ih =>
    unfold collectSingleQuotedLoop at h
    split at h
    · contradiction
    · simp only [] at h
      split at h
      · rw [ih _ _ h,
            advance_preserves_pendingKeys s.advance,
            advance_preserves_pendingKeys s]
      · injection h with h_eq; cases h_eq
        exact advance_preserves_pendingKeys s
    · split at h
      · simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_pendingKeys
            s (folded, s_fold) heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih s_fold _ h, h_fold])
      · split at h <;> try contradiction
        rw [ih s.advance _ h, advance_preserves_pendingKeys s]

lemma scanSingleQuoted_preserves_pendingKeys {s s' : ScannerState}
    (h : scanSingleQuoted s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanSingleQuoted at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · rename_i result heq
    have hres := collectSingleQuotedLoop_preserves_pendingKeys s.advance "" _ _ _ _ _ result heq
    split at h
    · split at h <;> try contradiction
      injection h with h_eq; subst h_eq
      simpa [emitAt_pendingKeys] using hres.trans (advance_preserves_pendingKeys s)
    · injection h with h_eq; subst h_eq
      simpa [emitAt_pendingKeys] using hres.trans (advance_preserves_pendingKeys s)

lemma skipBlankLinesLoop_preserves_pendingKeys (s : ScannerState) (cnt fuel inputEnd : Nat) :
    (skipBlankLinesLoop s cnt fuel inputEnd).2.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s cnt with
  | zero => rfl
  | succ f ih =>
    unfold skipBlankLinesLoop; dsimp only []
    split
    · split
      · -- item 100: the gate's arm keeps the stack
        split
        · rfl
        · rw [ih, consumeNewline_preserves_pendingKeys,
              skipWhitespace_preserves_pendingKeys]
      · rfl
    · rfl

lemma handleBlockLineBreak_preserves_pendingKeys {s s' : ScannerState}
    {content content' : String} {contentIndent inputEnd : Nat}
    (h : collectPlainScalar_handleBlockLineBreak s content contentIndent inputEnd
         = some (content', s')) : s'.pendingKeys = s.pendingKeys := by
  unfold collectPlainScalar_handleBlockLineBreak at h
  dsimp only [] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rw [skipWhitespace_preserves_pendingKeys, skipSpaces_preserves_pendingKeys,
          skipBlankLinesLoop_preserves_pendingKeys,
          consumeNewline_preserves_pendingKeys]

lemma collectPlainScalarLoop_preserves_pendingKeys (s : ScannerState)
    (content spaces : String) (fuel : Nat) (inFlow : Bool)
    (contentIndent inputEnd : Nat) (result : PlainScalarResult)
    (h : collectPlainScalarLoop s content spaces fuel inFlow contentIndent inputEnd
         = .ok result) : result.state.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s content spaces with
  | zero => simp only [collectPlainScalarLoop, Except.ok.injEq] at h; subst h; rfl
  | succ f ih =>
    unfold collectPlainScalarLoop at h
    split at h
    · simp only [Except.ok.injEq] at h; subst h; rfl
    · split at h
      · rename_i r_term h_term
        simp only [Except.ok.injEq] at h; subst h
        rw [terminates_state_eq _ s content spaces inFlow r_term h_term]
      · split at h
        · split at h
          · -- flow break
            simp only [bind, Except.bind] at h
            split at h
            · exact absurd h (by simp)
            · rename_i fold_result hfold
              have hf := foldQuotedNewlines_preserves_pendingKeys
                s fold_result hfold
              split at h
              · simp only [Except.ok.injEq] at h; subst h; rfl
              · split at h
                · exact absurd h (by simp)
                · generalize h_loop : collectPlainScalarLoop fold_result.2
                      (content ++ fold_result.1) "" f inFlow contentIndent inputEnd = cont at h
                  cases cont with
                  | error e => simp at h
                  | ok inner =>
                    dsimp only [] at h
                    split at h
                    · simp only [Except.ok.injEq] at h; subst h; rfl
                    · simp only [Except.ok.injEq] at h; subst h
                      exact (ih _ _ _ h_loop).trans hf
          · -- block break
            split at h
            · simp only [Except.ok.injEq] at h; subst h; rfl
            · rename_i content' s_b hblk
              have hb := handleBlockLineBreak_preserves_pendingKeys hblk
              split at h
              · simp only [Except.ok.injEq] at h; subst h; rfl
              · generalize h_loop : collectPlainScalarLoop s_b content' "" f inFlow
                  contentIndent inputEnd = cont at h
                cases cont with
                | error e => simp at h
                | ok inner =>
                  dsimp only [] at h
                  split at h
                  · simp only [Except.ok.injEq] at h; subst h; rfl
                  · simp only [Except.ok.injEq] at h; subst h
                    exact (ih _ _ _ h_loop).trans hb
        · split at h
          · exact (ih _ _ _ h).trans
              (advance_preserves_pendingKeys s)
          · split at h
            · simp only [Except.ok.injEq] at h; subst h; rfl
            · exact (ih _ _ _ h).trans
                (advance_preserves_pendingKeys s)

lemma scanPlainScalar_preserves_pendingKeys {s s' : ScannerState}
    (h : scanPlainScalar s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · rename_i result hloop
    simp only [Except.ok.injEq] at h
    subst h
    simpa [emitAt_pendingKeys] using collectPlainScalarLoop_preserves_pendingKeys s _ _ _ _ _ _ result hloop

lemma dispatchContent_preserves_pendingKeys {s s' : ScannerState} {c : Char}
    (h_flow : s.inFlow = true)
    (h : scanNextToken_dispatchContent s c = .ok s') : s'.pendingKeys = s.pendingKeys := by
  obtain ⟨hnotPipe, hnotGt⟩ :=
    Proofs.BlockScalarFlowGuard.dispatchContent_not_blockScalar_of_inFlow h_flow h
  by_cases hc_amp : c = '&'
  · exact dispatchContent_props_pendingKeys (Or.inl hc_amp) h
  · by_cases hc_bang : c = '!'
    · exact dispatchContent_props_pendingKeys (Or.inr hc_bang) h
    · unfold scanNextToken_dispatchContent at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      rw [ite_eq_right (by simpa using hc_amp)] at h
      by_cases hc_star : c = '*'
      · subst hc_star
        rw [ite_eq_left (by simp)] at h
        split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          replace h := aliasArm_scan_ok h
          generalize h_fn : scanAnchorOrAlias s false = res at h
          cases res with
          | error e => simp at h
          | ok s_a =>
            try dsimp only [] at h
            simp only [Except.ok.injEq] at h; subst h
            exact scanAnchorOrAlias_preserves_pendingKeys h_fn

      · rw [ite_eq_right (by simpa using hc_star), ite_eq_right (by simpa using hc_bang),
            ite_eq_right (by simp [hnotPipe, hnotGt])] at h
        by_cases hc_dq : c = '"'
        · subst hc_dq
          rw [ite_eq_left (by simp)] at h
          generalize h_fn : scanDoubleQuoted s = res at h
          cases res with
          | error e => simp at h
          | ok s_q =>
            have hq := scanDoubleQuoted_preserves_pendingKeys
              s s_q h_fn
            dsimp only [] at h
            split at h <;>
              · simp only [Except.ok.injEq] at h; subst h; simpa using hq
        · rw [ite_eq_right (by simpa using hc_dq)] at h
          by_cases hc_sq : c = '\''
          · subst hc_sq
            rw [ite_eq_left (by simp)] at h
            generalize h_fn : scanSingleQuoted s = res at h
            cases res with
            | error e => simp at h
            | ok s_q =>
              have hq := scanSingleQuoted_preserves_pendingKeys h_fn
              dsimp only [] at h
              split at h <;>
                · simp only [Except.ok.injEq] at h; subst h; simpa using hq
          · rw [ite_eq_right (by simpa using hc_sq)] at h
            split at h
            · generalize h_fn : scanPlainScalar s = res at h
              cases res with
              | error e => simp at h
              | ok s_p =>
                simp only [Except.ok.injEq] at h; subst h
                exact scanPlainScalar_preserves_pendingKeys h_fn
            · exact absurd h (by simp)

lemma scanFlowEntry_preserves_pendingKeys {s s' : ScannerState}
    (hok : scanFlowEntry s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanFlowEntry at hok
  simp only [bind, Except.bind] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok)
  all_goals simp [advance_preserves_pendingKeys, emit_pendingKeys]

lemma dispatchFlowIndicators_preserves_pendingKeys {s s' : ScannerState} {c : Char}
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) :
    s'.pendingKeys = s.pendingKeys := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (try (simp only [Except.ok.injEq, Option.some.injEq] at h; subst h))
  all_goals first
    | rfl
    | exact scanFlowSequenceStart_preserves_pendingKeys s
    | exact scanFlowSequenceEnd_preserves_pendingKeys s
    | exact scanFlowMappingStart_preserves_pendingKeys s
    | exact scanFlowMappingEnd_preserves_pendingKeys s
    | exact scanFlowEntry_preserves_pendingKeys (by assumption)
    | simp_all

lemma dispatchBlockIndicators_preserves_pendingKeys {s s' : ScannerState} {c : Char}
    (h_flow : s.inFlow = true)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    s'.pendingKeys = s.pendingKeys := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (simp only [Except.ok.injEq, Option.some.injEq] at h
       subst h
       first
         | exact scanKey_pendingKeys_of_inFlow h_flow (by assumption)
         | exact scanValue_pendingKeys_of_inFlow h_flow (by assumption))
    | simp_all

lemma advanceNLoop_preserves_pendingKeys (s : ScannerState) (n : Nat) :
    (s.advanceNLoop n).pendingKeys = s.pendingKeys := by
  induction n generalizing s with
  | zero => unfold ScannerState.advanceNLoop; rfl
  | succ _ ih =>
    unfold ScannerState.advanceNLoop
    exact (ih s.advance).trans (advance_pendingKeys s)

lemma advanceN_preserves_pendingKeys (s : ScannerState) (n : Nat) :
    (s.advanceN n).pendingKeys = s.pendingKeys := by
  unfold ScannerState.advanceN; exact advanceNLoop_preserves_pendingKeys s n

lemma skipToEndOfLineLoop_preserves_pendingKeys (s : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop s fuel).pendingKeys = s.pendingKeys := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ _ ih =>
    unfold skipToEndOfLineLoop
    split
    · split
      · rfl
      · rw [ih]; exact advance_pendingKeys s
    · rfl

lemma skipToEndOfLine_preserves_pendingKeys (s : ScannerState) :
    (skipToEndOfLine s).pendingKeys = s.pendingKeys := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_preserves_pendingKeys s _

lemma collectDirectiveNameLoop_preserves_pendingKeys (s : ScannerState) (name : String)
    (fuel : Nat) : (collectDirectiveNameLoop s name fuel).snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s name with
  | zero => unfold collectDirectiveNameLoop; rfl
  | succ _ ih =>
    unfold collectDirectiveNameLoop; split
    · split
      · rw [ih]; exact advance_pendingKeys s
      · rfl
    · rfl

lemma collectVersionMajorLoop_preserves_pendingKeys (s : ScannerState) (major : String)
    (fuel : Nat) : (collectVersionMajorLoop s major fuel).snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s major with
  | zero => unfold collectVersionMajorLoop; rfl
  | succ _ ih =>
    unfold collectVersionMajorLoop; split
    · exact advance_pendingKeys s
    · split
      · rw [ih]; exact advance_pendingKeys s
      · rfl
    · rfl

lemma collectVersionMinorLoop_preserves_pendingKeys (s : ScannerState) (minor : String)
    (fuel : Nat) : (collectVersionMinorLoop s minor fuel).snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s minor with
  | zero => unfold collectVersionMinorLoop; rfl
  | succ _ ih =>
    unfold collectVersionMinorLoop; split
    · split
      · rw [ih]; exact advance_pendingKeys s
      · rfl
    · rfl

lemma collectTagHandleDirectiveLoop_preserves_pendingKeys (s : ScannerState) (handle : String)
    (fuel : Nat) : (collectTagHandleDirectiveLoop s handle fuel).snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s handle with
  | zero => unfold collectTagHandleDirectiveLoop; rfl
  | succ _ ih =>
    unfold collectTagHandleDirectiveLoop; split
    · split
      · rw [ih]; exact advance_pendingKeys s
      · rfl
    · rfl

lemma collectTagPrefixLoop_preserves_pendingKeys (s : ScannerState) (pfx : String)
    (fuel : Nat) : (collectTagPrefixLoop s pfx fuel).snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s pfx with
  | zero => unfold collectTagPrefixLoop; rfl
  | succ _ ih =>
    unfold collectTagPrefixLoop; split
    · split
      · rw [ih]; exact advance_pendingKeys s
      · rfl
    · rfl

lemma parseBlockHeaderLoop_preserves_pendingKeys (s : ScannerState) (chomp : ChompStyle)
    (offset : Option Nat) (fuel : Nat) :
    (parseBlockHeaderLoop s chomp offset fuel).snd.snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s chomp offset with
  | zero => unfold parseBlockHeaderLoop; rfl
  | succ _ ih =>
    unfold parseBlockHeaderLoop; split
    · rw [ih]; exact advance_pendingKeys s
    · rw [ih]; exact advance_pendingKeys s
    · split
      · rw [ih]; exact advance_pendingKeys s
      · rfl
    · rfl

lemma consumeExactSpaces_preserves_pendingKeys (s : ScannerState) (count : Nat) :
    (consumeExactSpaces s count).snd.pendingKeys = s.pendingKeys := by
  induction count generalizing s with
  | zero => unfold consumeExactSpaces; rfl
  | succ _ ih =>
    unfold consumeExactSpaces; split
    · simp only []; rw [ih]; exact advance_pendingKeys s
    · rfl

lemma collectLineContentLoop_preserves_pendingKeys (s : ScannerState) (content : String)
    (fuel : Nat) : (collectLineContentLoop s content fuel).snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s content with
  | zero => unfold collectLineContentLoop; rfl
  | succ _ ih =>
    unfold collectLineContentLoop
    split
    · split
      · rfl
      · rw [ih]; exact advance_pendingKeys s
    · rfl

lemma collectBlockScalarLoop_preserves_pendingKeys (s : ScannerState) (rawContent : String)
    (fuel : Nat) (contentIndent : Nat) (inputEnd : Nat) :
    (collectBlockScalarLoop s rawContent fuel contentIndent inputEnd).snd.pendingKeys
      = s.pendingKeys := by
  induction fuel generalizing s rawContent with
  | zero => unfold collectBlockScalarLoop; rfl
  | succ _ ih =>
    unfold collectBlockScalarLoop
    split
    · rfl
    · simp only []
      split
      · exact consumeExactSpaces_preserves_pendingKeys s contentIndent
      · split
        · rw [ih, consumeNewline_preserves_pendingKeys, consumeExactSpaces_preserves_pendingKeys]
        · split
          · rfl
          · split
            · split
              · rw [ih, consumeNewline_preserves_pendingKeys,
                    collectLineContentLoop_preserves_pendingKeys,
                    consumeExactSpaces_preserves_pendingKeys]
              · split
                · rfl
                · rw [collectLineContentLoop_preserves_pendingKeys,
                    consumeExactSpaces_preserves_pendingKeys]
            · rw [collectLineContentLoop_preserves_pendingKeys,
                  consumeExactSpaces_preserves_pendingKeys]

lemma skipDocEndWhitespace_preserves_pendingKeys (s : ScannerState) (fuel : Nat) :
    (skipDocEndWhitespace s fuel).pendingKeys = s.pendingKeys := by
  induction fuel generalizing s with
  | zero => unfold skipDocEndWhitespace; rfl
  | succ _ ih =>
    unfold skipDocEndWhitespace
    split
    · split
      · rw [ih]; exact advance_pendingKeys s
      · rfl
    · rfl

lemma collectCommentTextLoop_preserves_pendingKeys (s : ScannerState) (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' ih =>
    unfold collectCommentTextLoop
    split
    · split
      · rfl
      · rw [ih, advance_pendingKeys]
    · rfl

lemma scanBlockScalarSkipComment_preserves_pendingKeys (s : ScannerState) :
    (scanBlockScalarSkipComment s).pendingKeys = s.pendingKeys := by
  unfold scanBlockScalarSkipComment
  split
  · split
    · dsimp only []
      split
      · simp only []
        rw [collectCommentTextLoop_preserves_pendingKeys, advance_pendingKeys]
      · rfl
    · rfl
  · rfl

lemma scanBlockScalarConsumeNewline_preserves_pendingKeys {s s' : ScannerState}
    (h : scanBlockScalarConsumeNewline s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanBlockScalarConsumeNewline at h
  split at h
  · split at h
    · injection h with h_eq; subst h_eq; exact consumeNewline_preserves_pendingKeys s
    · split at h
      · injection h with h_eq; subst h_eq; rfl
      · contradiction
  · injection h with h_eq; subst h_eq; rfl

lemma scanBlockScalarBody_preserves_pendingKeys {s_orig s_nl s' : ScannerState}
    {chomp : ChompStyle} {expl : Option Nat} {isLit : Bool} {startPos : YamlPos}
    (h_ids : s_nl.pendingKeys = s_orig.pendingKeys)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.pendingKeys = s_orig.pendingKeys := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; dsimp only [])
  all_goals rw [emitAt_pendingKeys, collectBlockScalarLoop_preserves_pendingKeys, h_ids]

lemma scanBlockScalar_preserves_pendingKeys {s s' : ScannerState}
    (h : scanBlockScalar s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanBlockScalar at h
  simp only [] at h
  split at h
  · contradiction
  · exact scanBlockScalarBody_preserves_pendingKeys
      (by rw [scanBlockScalarConsumeNewline_preserves_pendingKeys (by assumption),
              scanBlockScalarSkipComment_preserves_pendingKeys,
              skipWhitespace_preserves_pendingKeys,
              parseBlockHeaderLoop_preserves_pendingKeys,
              advance_pendingKeys]) h

lemma scanDirective_preserves_pendingKeys {s s' : ScannerState}
    (h : scanDirective s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanDirective at h
  split at h
  · contradiction
  · simp only [] at h
    split at h
    · split at h
      · rename_i s_inner h_inner
        have h_eq := Except.ok.inj h; subst h_eq
        rw [skipToEndOfLine_preserves_pendingKeys]
        unfold scanYamlDirective at h_inner
        simp only [bind, Except.bind] at h_inner
        split at h_inner <;> try contradiction
        repeat (any_goals (split at h_inner))
        all_goals (try contradiction)
        all_goals (simp only [Except.ok.injEq] at h_inner; subst h_inner)
        all_goals (try simp [emitAt_pendingKeys, skipWhitespace_preserves_pendingKeys,
              collectVersionMinorLoop_preserves_pendingKeys,
              collectVersionMajorLoop_preserves_pendingKeys])
        all_goals (rw [collectDirectiveNameLoop_preserves_pendingKeys,
                       advance_pendingKeys])
      · contradiction
    · split at h
      · split at h
        · rename_i s_inner h_inner
          have h_eq := Except.ok.inj h; subst h_eq
          rw [skipToEndOfLine_preserves_pendingKeys]
          unfold scanTagDirective at h_inner
          dsimp only [] at h_inner
          simp only [bind, Except.bind] at h_inner
          split at h_inner
          · contradiction  -- [89]: a malformed `%TAG` handle is refused
          split at h_inner <;> try (split at h_inner <;> try contradiction)
          all_goals (try contradiction)
          all_goals (simp only [Except.ok.injEq] at h_inner; subst h_inner)
          all_goals simp [emitAt_pendingKeys, collectTagPrefixLoop_preserves_pendingKeys,
                skipWhitespace_preserves_pendingKeys,
                collectTagHandleDirectiveLoop_preserves_pendingKeys,
                collectDirectiveNameLoop_preserves_pendingKeys,
                advance_pendingKeys]
        · contradiction
      · simp only [Except.ok.injEq] at h; subst h
        simp [skipToEndOfLine_preserves_pendingKeys, skipWhitespace_preserves_pendingKeys,
              collectDirectiveNameLoop_preserves_pendingKeys,
              advance_pendingKeys]

lemma skipToContentComment_preserves_pendingKeys (s : ScannerState) :
    (skipToContentComment s).pendingKeys = s.pendingKeys := by
  unfold skipToContentComment
  split
  · simp only []
    split
    · split
      · simp only []
        rw [collectCommentTextLoop_preserves_pendingKeys, advance_pendingKeys]
      · rfl
    · split
      · simp only []
        rw [collectCommentTextLoop_preserves_pendingKeys, advance_pendingKeys]
      · rfl
  · rfl

lemma skipToContentWs_preserves_pendingKeys (s s' : ScannerState)
    (h : skipToContentWs s = .ok s') :
    s'.pendingKeys = s.pendingKeys := by
  unfold skipToContentWs at h
  split at h
  · simp only [] at h
    split at h
    · split at h
      · split at h
        · simp at h
          rw [← h, skipWhitespace_preserves_pendingKeys, skipSpaces_preserves_pendingKeys]
        · split at h
          · simp at h
            rw [← h, skipWhitespace_preserves_pendingKeys, skipSpaces_preserves_pendingKeys]
          · split at h
            · simp at h
              rw [← h, skipWhitespace_preserves_pendingKeys, skipSpaces_preserves_pendingKeys]
            · simp at h
        · simp at h
          rw [← h, skipWhitespace_preserves_pendingKeys, skipSpaces_preserves_pendingKeys]
      · simp at h
        rw [← h, skipSpaces_preserves_pendingKeys]
    · simp at h
      rw [← h, skipWhitespace_preserves_pendingKeys, skipSpaces_preserves_pendingKeys]
  · simp at h
    rw [← h, skipWhitespace_preserves_pendingKeys]

lemma skipToContentLoop_preserves_pendingKeys (s s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') :
    s'.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s with
  | zero =>
    unfold skipToContentLoop at h
    simp at h; rw [← h]
  | succ fuel' ih =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      simp only [] at h
      split at h
      · split at h
        · split at h
          · rw [ih _ h, consumeNewline_preserves_pendingKeys,
                skipToContentComment_preserves_pendingKeys]
            exact skipToContentWs_preserves_pendingKeys s s1 hws
          · rw [ih _ h, consumeNewline_preserves_pendingKeys,
                skipToContentComment_preserves_pendingKeys]
            exact skipToContentWs_preserves_pendingKeys s s1 hws
        · simp at h
          rw [← h, skipToContentComment_preserves_pendingKeys]
          exact skipToContentWs_preserves_pendingKeys s s1 hws
      · simp at h
        rw [← h, skipToContentComment_preserves_pendingKeys]
        exact skipToContentWs_preserves_pendingKeys s s1 hws

lemma skipToContent_preserves_pendingKeys (s s' : ScannerState)
    (h : skipToContent s = .ok s') :
    s'.pendingKeys = s.pendingKeys := by
  unfold skipToContent at h
  exact skipToContentLoop_preserves_pendingKeys s s' _ h

lemma saveSimpleKey_preserves_pendingKeys (s : ScannerState) :
    (saveSimpleKey s).pendingKeys = s.pendingKeys := by
  unfold saveSimpleKey
  split
  · rfl
  · split <;> rfl

end L4YAML.Proofs.PendingKeysStable

end Blanket
