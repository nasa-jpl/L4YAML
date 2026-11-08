/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.DocStartLiveInv

@[expose] public section Blanket

/-! # Every `.tag` the scanner emits has a shaped handle, and it emits no `.comment` (capstone 7.7, stream S3, obligation (a) and the `.comment` residue)

    `ParseCheckFrom.TagUsesShaped ts` — every `.tag h _` in `ts` has `h ∈ {"", "!", "!!"}` or
    `isNamedHandle h` — is the one scanner-shape premise of `parseStream_ok_checkFrom` that
    `ScannerShape` still took from outside.  This module discharges it for real scanner output.

    The carrier is a per-token invariant, `TagInv s := ∀ t ∈ vals s, emitOk t`, with
    `emitOk (.tag h _) := h == "" || isTagHandleShaped h` (the scanner's own directive-side handle
    predicate, `Scanner/Document.lean`; `ScannerShape.tagOk_shaped` bridges it to the parser's
    `BuiltinTagHandle ∨ isNamedHandle`, resting on `isWordCharBool c → c.isAlphanum ∨ c = '-'`).
    Each `scanNextToken` arm is shown to be a `TagExt s s' := ∀ t ∈ vals s', t ∈ vals s ∨ emitOk t`
    — every token it writes (appended or, for `scanValuePrepare`'s retroactive slots, `set`) is
    either old or shaped — so `TagInv` is carried without any side invariant.  The only arm that
    builds a `.tag` is `scanTag`: `scanVerbatimTag` emits `""`, `scanSecondaryTag` `"!!"`, and
    `scanNamedTag` either `"!"` or `"!" ++ w ++ "!"` with `w` the word chars
    `collectTagHandleLoop` collected (`collectTagHandleLoop_chars`), which is shaped
    (`shaped_named`; `w = ""` gives `"!!"`).

    The same carrier excludes `.comment` tokens (`emitOk (.comment _) = false`): no arm builds one,
    so `DeadResidue`'s `.comment` disjunct (item 449) is closed by `ScannerShape.LoopDead_scanFiltered`.

    Rule 2 first: `Tests/AdversarialInstantiation.lean`, Priority 95 (tags) and 96 (comments). -/

namespace L4YAML.Proofs.TagShape

open L4YAML L4YAML.Scanner L4YAML.CharPredicates
open L4YAML.Proofs.DirectiveRuns
open L4YAML.Proofs.DocStartLiveInv
open L4YAML.Proofs.ScannerCorrectness L4YAML.Proofs.ScannerCorrectness.ScanHelpers
open L4YAML.Proofs.FlowAdjacency L4YAML.Proofs.CloseStaleExplicitKey

/-! ## The predicate, the extension relation, the invariant -/

/-- A token the scanner may emit, as far as tags and comments go: a `.tag` whose handle is `""`
(verbatim) or passes the scanner's `isTagHandleShaped` (`"!"`, `"!!"`, `"!word!"`); never a
`.comment` (comments go to `skipToContent`'s side channel, not `tokens`); anything else. -/
def emitOk : YamlToken → Bool
  | .tag h _ => h == "" || isTagHandleShaped h
  | .comment _ => false
  | _ => true

/-- Every token of `s'` is a token of `s` or is tag-shaped. -/
def TagExt (s s' : ScannerState) : Prop := ∀ t ∈ vals s', t ∈ vals s ∨ emitOk t = true

/-- Every token of `s` is tag-shaped. -/
def TagInv (s : ScannerState) : Prop := ∀ t ∈ vals s, emitOk t = true

lemma TagInv.of {s s' : ScannerState} (hI : TagInv s) (hE : TagExt s s') : TagInv s' :=
  fun t ht => (hE t ht).elim (hI t) id

lemma TagExt.refl (s : ScannerState) : TagExt s s := fun _ ht => Or.inl ht

lemma TagExt.ofVals {s s' : ScannerState} (hv : vals s' = vals s) : TagExt s s' := by
  intro t ht; rw [hv] at ht; exact Or.inl ht

lemma TagExt.ofTokens {s s' : ScannerState} (h : s'.tokens = s.tokens) : TagExt s s' :=
  TagExt.ofVals (by simp [vals, h])

lemma TagExt.trans {a b c : ScannerState} (h1 : TagExt a b) (h2 : TagExt b c) : TagExt a c :=
  fun t ht => (h2 t ht).elim (fun hb => h1 t hb) Or.inr

lemma TagExt.append {s s' : ScannerState} (M : List YamlToken) (hv : vals s' = vals s ++ M)
    (hM : ∀ t ∈ M, emitOk t = true) : TagExt s s' := by
  intro t ht; rw [hv] at ht
  rcases List.mem_append.1 ht with h | h
  · exact Or.inl h
  · exact Or.inr (hM t h)

lemma TagExt.snoc {s s' : ScannerState} {u : YamlToken} (hv : vals s' = vals s ++ [u])
    (hu : emitOk u = true) : TagExt s s' :=
  TagExt.append [u] hv (fun t ht => by simp at ht; subst ht; exact hu)

lemma TagExt.set {s s' : ScannerState} {i : Nat} {u : YamlToken} (hv : vals s' = (vals s).set i u)
    (hu : emitOk u = true) : TagExt s s' := by
  intro t ht; rw [hv] at ht
  rcases List.mem_or_eq_of_mem_set ht with h | rfl
  · exact Or.inl h
  · exact Or.inr hu

/-! ## Handles: word chars, the named shape, what `collectTagHandleLoop` collects -/

/-- `ns-word-char` is alphanumeric-or-dash — the parser's `isNamedHandle` character test. -/
lemma wordChar_alnum (c : Char) (h : isWordCharBool c = true) : (c.isAlphanum || c == '-') = true := by
  simp only [isWordCharBool, decide_eq_true_eq] at h
  unfold isWordCharProp isAsciiLetterProp at h
  rcases h with ⟨h1, h2⟩ | (⟨h1, h2⟩ | ⟨h1, h2⟩) | h
  all_goals simp_all [Char.isAlphanum, Char.isAlpha, Char.isDigit, Char.isUpper, Char.isLower]

/-- `"!" ++ w ++ "!"` is shaped when `w` is all word chars (`w = ""` gives `"!!"`). -/
lemma shaped_named (w : String) (hw : w.toList.all isWordCharBool = true) :
    isTagHandleShaped ("!" ++ w ++ "!") = true := by
  cases hw' : w.toList with
  | nil =>
    have hw0 : w = "" := by cases w; simp at hw'; simp [hw']
    subst hw0; decide
  | cons c cs =>
    unfold isTagHandleShaped
    rw [Bool.or_eq_true]; right
    have hl : ("!" ++ w ++ "!").toList = '!' :: (w.toList ++ ['!']) := by simp
    rw [hl, hw']
    rw [hw'] at hw
    show (decide ((c :: cs ++ ['!']).length ≥ 2) && (c :: cs ++ ['!']).getLast? == some '!' &&
      (c :: cs ++ ['!']).dropLast.all isWordCharBool) = true
    rw [List.getLast?_concat, List.dropLast_concat]
    simp [hw]

/-- `collectTagHandleLoop` only appends word chars to its accumulator. -/
lemma collectTagHandleLoop_chars : ∀ (fuel : Nat) (s : ScannerState) (acc : String),
    ∃ L, (collectTagHandleLoop s acc fuel).1.toList = acc.toList ++ L ∧ L.all isWordCharBool = true := by
  intro fuel
  induction fuel with
  | zero => intro s acc; exact ⟨[], by simp [collectTagHandleLoop], rfl⟩
  | succ n ih =>
    intro s acc
    unfold collectTagHandleLoop
    split
    · exact ⟨[], by simp, rfl⟩
    · split
      · rename_i c _ _ hc
        obtain ⟨L, hL, hall⟩ := ih s.advance (acc.push c)
        refine ⟨c :: L, ?_, ?_⟩
        · rw [hL, String.toList_push, List.append_assoc]; rfl
        · simp [hall, hc]
      · exact ⟨[], by simp, rfl⟩
    · exact ⟨[], by simp, rfl⟩

/-! ## Content scanners push one shaped token -/

/-- `s'` is `s` plus exactly one tag-shaped token. -/
def PushTag (s s' : ScannerState) : Prop :=
  ∃ t, vals s' = vals s ++ [t] ∧ emitOk t = true

lemma PushTag.emitAt (s s0 : ScannerState) (p : YamlPos) (t : YamlToken)
    (h0 : s0.tokens = s.tokens) (ht : emitOk t = true) : PushTag s (s0.emitAt p t) :=
  ⟨t, by rw [vals_emitAt]; simp [vals, h0], ht⟩

lemma PushTag.ofEq {s s1 s' : ScannerState} (h : PushTag s1 s') (h1 : s1.tokens = s.tokens) :
    PushTag s s' := by
  obtain ⟨t, hv, ht⟩ := h
  exact ⟨t, by rw [hv]; simp [vals, h1], ht⟩

lemma PushTag.congr {s s' s'' : ScannerState} (h : PushTag s s') (h2 : s''.tokens = s'.tokens) :
    PushTag s s'' := by
  obtain ⟨t, hv, ht⟩ := h
  exact ⟨t, by rw [← hv]; simp [vals, h2], ht⟩

lemma TagExt.ofPush {s s' : ScannerState} (h : PushTag s s') : TagExt s s' := by
  obtain ⟨t, hv, ht⟩ := h
  exact TagExt.snoc hv ht

lemma scanAnchorOrAlias_pushTag (s : ScannerState) (isAnchor : Bool) (s' : ScannerState)
    (hok : scanAnchorOrAlias s isAnchor = .ok s') : PushTag s s' := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; try dsimp only []
    have h_collect :=
      collectAnchorNameLoop_preserves_tokens s.advance "" (s.inputEnd - s.advance.offset)
    have h_adv := advance_preserves_tokens s
    apply PushTag.emitAt _ _ _ _ (h_collect.trans h_adv)
    first | rfl | (cases isAnchor <;> rfl)

lemma scanVerbatimTag_pushTag (s : ScannerState) (pos : YamlPos) (s' : ScannerState)
    (hok : scanVerbatimTag s pos = .ok s') : PushTag s s' := by
  unfold scanVerbatimTag at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      exact PushTag.emitAt _ _ _ _
        (by simp only [collectVerbatimTagLoop_preserves_tokens, advance_preserves_tokens])
        (by simp [emitOk])

lemma scanSecondaryTag_pushTag (s : ScannerState) (pos : YamlPos) :
    PushTag s (scanSecondaryTag s pos) := by
  unfold scanSecondaryTag
  exact PushTag.emitAt _ _ _ _
    (by simp only [collectTagSuffixLoop_preserves_tokens, advance_preserves_tokens])
    (by simp [emitOk, isTagHandleShaped])

lemma scanNamedTag_pushTag (s : ScannerState) (pos : YamlPos) (inputEnd : Nat) :
    PushTag s (scanNamedTag s pos inputEnd) := by
  unfold scanNamedTag; simp only []
  have h_handle := collectTagHandleLoop_preserves_tokens s "" (inputEnd - s.offset)
  obtain ⟨L, hL, hall⟩ := collectTagHandleLoop_chars (inputEnd - s.offset) s ""
  split
  · refine PushTag.emitAt _ _ _ _ (by rw [collectTagSuffixLoop_preserves_tokens, h_handle]) ?_
    simp only [emitOk, Bool.or_eq_true]
    right
    apply shaped_named
    simp only [String.toList_empty, List.nil_append] at hL
    rw [hL]; exact hall
  · exact PushTag.emitAt _ _ _ _ (by rw [collectTagSuffixLoop_preserves_tokens, h_handle])
      (by simp [emitOk, isTagHandleShaped])

lemma scanTag_pushTag (s s' : ScannerState) (hok : scanTag s = .ok s') : PushTag s s' := by
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok
      have h := Except.ok.inj hok; subst h; try dsimp only []
      exact (scanVerbatimTag_pushTag _ _ _ hv).ofEq (advance_preserves_tokens s)
  · have h := Except.ok.inj hok; subst h; try dsimp only []
    exact (scanSecondaryTag_pushTag _ _).ofEq (advance_preserves_tokens s)
  · have h := Except.ok.inj hok; subst h; try dsimp only []
    exact (scanNamedTag_pushTag _ _ _).ofEq (advance_preserves_tokens s)

lemma scanBlockScalarBody_pushTag (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos)
    (s' : ScannerState) (h_tok : s_nl.tokens = s_orig.tokens)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    PushTag s_orig s' := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; try dsimp only [])
  all_goals exact (PushTag.emitAt _ _ _ _
    (by rw [collectBlockScalarLoop_preserves_tokens, h_tok]) rfl).congr rfl

lemma scanBlockScalar_pushTag (s s' : ScannerState) (h : scanBlockScalar s = .ok s') :
    PushTag s s' := by
  unfold scanBlockScalar at h
  simp only [] at h
  split at h
  · contradiction
  · exact scanBlockScalarBody_pushTag s _ _ _ _ _ s'
      (by rw [scanBlockScalarConsumeNewline_preserves_tokens _ _ (by assumption),
              scanBlockScalarSkipComment_preserves_tokens,
              skipWhitespace_preserves_tokens,
              parseBlockHeaderLoop_preserves_tokens,
              advance_preserves_tokens]) h

lemma scanPlainScalar_pushTag (s s' : ScannerState) (h : scanPlainScalar s = .ok s') :
    PushTag s s' := by
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i heq
  have h_collect := collectPlainScalarLoop_preserves_tokens s "" "" _ _ _ _ _ heq
  injection h with h_eq; subst h_eq
  exact PushTag.emitAt _ _ _ _ h_collect rfl

lemma scanDoubleQuoted_pushTag (s s' : ScannerState) (h : scanDoubleQuoted s = .ok s') :
    PushTag s s' := by
  unfold scanDoubleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i heq
  have h_collect := collectDoubleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
  have h_adv := advance_preserves_tokens s
  split at h
  · split at h <;> try contradiction
    injection h with h_eq; subst h_eq
    exact PushTag.emitAt _ _ _ _ (h_collect.trans h_adv) rfl
  · injection h with h_eq; subst h_eq
    exact PushTag.emitAt _ _ _ _ (h_collect.trans h_adv) rfl

lemma scanSingleQuoted_pushTag (s s' : ScannerState) (h : scanSingleQuoted s = .ok s') :
    PushTag s s' := by
  unfold scanSingleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i heq
  have h_collect := collectSingleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
  have h_adv := advance_preserves_tokens s
  split at h
  · split at h <;> try contradiction
    injection h with h_eq; subst h_eq
    exact PushTag.emitAt _ _ _ _ (h_collect.trans h_adv) rfl
  · injection h with h_eq; subst h_eq
    exact PushTag.emitAt _ _ _ _ (h_collect.trans h_adv) rfl

lemma TagExt_dispatchContent (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s') : TagExt s s' := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · split at h
    · simp at h
    generalize h_fn : scanAnchorOrAlias s true = result at h
    cases result with
    | error e => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h
      exact TagExt.ofPush (scanAnchorOrAlias_pushTag s true s_a h_fn)
  · split at h
    · split at h
      · simp at h
      split at h
      · simp at h
      · exact TagExt.ofPush (scanAnchorOrAlias_pushTag s false _ (aliasArm_scan_ok h))
    · split at h
      · split at h
        · simp at h
        generalize h_fn : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact TagExt.ofPush (scanTag_pushTag s s_t h_fn)
      · repeat (any_goals (split at h))
        any_goals contradiction
        all_goals (try simp only [Except.ok.injEq] at *)
        all_goals (try contradiction)
        all_goals (try subst_vars)
        all_goals first
          | exact TagExt.ofPush (scanBlockScalar_pushTag _ _ (by assumption))
          | exact TagExt.ofPush (scanPlainScalar_pushTag _ _ (by assumption))
          | exact TagExt.ofPush (scanDoubleQuoted_pushTag _ _ (by assumption))
          | exact TagExt.ofPush (scanSingleQuoted_pushTag _ _ (by assumption))
          | exact TagExt.ofPush ((scanDoubleQuoted_pushTag _ _ (by assumption)).congr (by rfl))
          | exact TagExt.ofPush ((scanSingleQuoted_pushTag _ _ (by assumption)).congr (by rfl))
          | (simp_all; done)

/-! ## Preprocessing and the structural arms -/

lemma TagExt_unwindIndents (s : ScannerState) (col : Int) : TagExt s (unwindIndents s col) := by
  obtain ⟨M, hv, hM⟩ := unwindIndents_vals s col
  exact TagExt.append M hv (fun t ht => by rw [hM t ht]; rfl)

lemma TagExt_saveSimpleKey (s : ScannerState) : TagExt s (saveSimpleKey s) := by
  unfold saveSimpleKey
  split
  · exact TagExt.refl s
  · split
    · exact TagExt.append [.placeholder, .placeholder] (by simp [vals, toks]) (by simp [emitOk])
    · exact TagExt.refl s

lemma TagExt_preprocess (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) : TagExt s s1 := by
  unfold scanNextToken_preprocess at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have hE1 : TagExt s s_skip := TagExt.ofTokens (skipToContent_preserves_tokens s s_skip h_skip)
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            have h2 : TagExt (unwindIndents s_skip s_skip.col)
                { unwindIndents s_skip s_skip.col with needIndentCheck := false } := TagExt.ofTokens rfl
            have h3 := TagExt_saveSimpleKey { unwindIndents s_skip s_skip.col with needIndentCheck := false }
            have h4 : TagExt (saveSimpleKey { unwindIndents s_skip s_skip.col with needIndentCheck := false })
                (closeStaleExplicitKey (saveSimpleKey { unwindIndents s_skip s_skip.col with needIndentCheck := false })) :=
              TagExt.ofTokens (closeStaleExplicitKey_tokens _)
            exact hE1.trans ((TagExt_unwindIndents s_skip s_skip.col).trans (h2.trans (h3.trans h4)))
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            have h3 := TagExt_saveSimpleKey s_skip
            have h4 : TagExt (saveSimpleKey s_skip) (closeStaleExplicitKey (saveSimpleKey s_skip)) :=
              TagExt.ofTokens (closeStaleExplicitKey_tokens _)
            exact hE1.trans (h3.trans h4)

lemma TagExt_scanDocumentStart (s : ScannerState) : TagExt s (scanDocumentStart s) :=
  (TagExt_unwindIndents s (-1)).trans (TagExt.snoc (scanDocumentStart_fields s).1 rfl)

lemma TagExt_scanDocumentEnd (s s' : ScannerState) (h : scanDocumentEnd s = .ok s') : TagExt s s' :=
  (TagExt_unwindIndents s (-1)).trans (TagExt.snoc (scanDocumentEnd_fields s s' h).1 rfl)

lemma TagExt_scanDirective (s s' : ScannerState) (h : scanDirective s = .ok s') : TagExt s s' := by
  rcases (scanDirective_fields s s' h).1 with hv | ⟨d, hv, hd⟩
  · exact TagExt.ofVals hv
  · refine TagExt.snoc hv ?_
    cases d <;> simp [isDirTok] at hd <;> rfl

lemma TagExt_dispatchStructural (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s')) : TagExt s s' := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact TagExt_scanDocumentStart s
    | exact TagExt_scanDocumentEnd _ _ (by assumption)
    | exact TagExt_scanDirective _ _ (by assumption)

/-! ## Flow and block indicators -/

lemma TagExt_dispatchFlow (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) : TagExt s s' := by
  unfold scanNextToken_dispatchFlowIndicators at h
  replace h := peel_flowAdj h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact TagExt.snoc (scanFlowSequenceStart_vals s) rfl
  · split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
            exact TagExt.snoc (scanFlowSequenceEnd_vals s) rfl
    · split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact TagExt.snoc (scanFlowMappingStart_vals s) rfl
      · split at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                exact TagExt.snoc (scanFlowMappingEnd_vals s) rfl
        · split at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · rename_i _ _ _ h_entry
                simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                exact TagExt.snoc (scanFlowEntry_vals s _ h_entry) rfl
          · simp at h

lemma TagExt_pushSequenceIndent (s : ScannerState) (col : Int) :
    TagExt s (pushSequenceIndent s col) := by
  rcases pushSequenceIndent_vals s col with hp | hp
  · rw [hp]; exact TagExt.refl s
  · exact TagExt.snoc hp rfl

lemma TagExt_pushMappingIndent (s : ScannerState) (col : Int) :
    TagExt s (pushMappingIndent s col) := by
  rcases pushMappingIndent_vals s col with ⟨hp, _⟩ | hp
  · rw [hp]; exact TagExt.refl s
  · exact TagExt.snoc hp rfl

lemma TagExt_scanBlockEntry (s s' : ScannerState) (h : scanBlockEntry s = .ok s') : TagExt s s' := by
  have hv0 : vals s' = vals (if !s.inFlow then pushSequenceIndent s s.col else s) ++ [.blockEntry] := by
    rw [← vals_emit]; show toks s'.tokens = toks _; rw [scanBlockEntry_tokens s s' h]
  refine TagExt.trans ?_ (TagExt.snoc hv0 rfl)
  split
  · exact TagExt_pushSequenceIndent s s.col
  · exact TagExt.refl s

lemma TagExt_scanKey (s s' : ScannerState) (h : scanKey s = .ok s') : TagExt s s' := by
  have hv0 : vals s' = vals (if !s.inFlow then pushMappingIndent s s.col else s) ++ [.key] := by
    rw [← vals_emit]; show toks s'.tokens = toks _; rw [scanKey_tokens s s' h]
  refine TagExt.trans ?_ (TagExt.snoc hv0 rfl)
  split
  · exact TagExt_pushMappingIndent s s.col
  · exact TagExt.refl s

lemma TagExt_scanValuePrepare (s : ScannerState) : TagExt s (scanValuePrepare s) := by
  unfold scanValuePrepare
  split
  · split
    · split
      · intro t ht
        simp only [vals, DirectiveRuns.toks_setIfInBounds] at ht
        rcases List.mem_or_eq_of_mem_set ht with h | rfl
        · rcases List.mem_or_eq_of_mem_set h with h | rfl
          · exact Or.inl h
          · exact Or.inr rfl
        · exact Or.inr rfl
      · exact TagExt.set (i := s.simpleKey.tokenIndex + 1) (u := YamlToken.key)
          (by simp only [vals, DirectiveRuns.toks_setIfInBounds]) rfl
    · exact TagExt.set (i := s.simpleKey.tokenIndex + 1) (u := YamlToken.key)
          (by simp only [vals, DirectiveRuns.toks_setIfInBounds]) rfl
  · split
    · exact TagExt.refl s
    · split
      · exact TagExt_pushMappingIndent s s.col
      · exact TagExt.refl s

lemma TagExt_scanValue (s s' : ScannerState) (h : scanValue s = .ok s') : TagExt s s' := by
  obtain ⟨_, hv, _⟩ := scanValue_unfold s s' h
  exact (TagExt.ofTokens (scanValueClearKey_preserves_tokens s)).trans
    ((TagExt_scanValuePrepare _).trans (TagExt.snoc hv rfl))

lemma TagExt_dispatchBlock (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) : TagExt s s' := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact TagExt_scanBlockEntry s _ (by assumption)
    | exact TagExt_scanKey s _ (by assumption)
    | exact TagExt_scanValue s _ (by assumption)

/-! ## One step, the loop, the initial state -/

lemma TagExt_scanNextToken (s s' : ScannerState) (h : scanNextToken s = .ok (some s')) :
    TagExt s s' := by
  unfold scanNextToken at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  rename_i s2 c h_pre
  have hE2 := TagExt_preprocess s s2 c h_pre
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact hE2.trans (TagExt_dispatchStructural s2 c _ (by assumption))
  · split at h <;> (try (simp at h; done))
    split at h <;> (try (simp at h; done))
    have hE3 : TagExt s2 (if s2.allowDirectives = true then
        { s2 with allowDirectives := false, documentEverStarted := true } else s2) :=
      TagExt.ofTokens (allowDir_ite_tokens s2)
    split at h <;> (try (simp at h; done))
    split at h
    · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
      exact hE2.trans (hE3.trans (TagExt_dispatchFlow _ c _ (by assumption)))
    · split at h <;> (try (simp at h; done))
      split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact hE2.trans (hE3.trans (TagExt_dispatchBlock _ c _ (by assumption)))
      · split at h <;> (try (simp at h; done))
        split at h <;> (try (simp at h; done))
        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact hE2.trans (hE3.trans (TagExt_dispatchContent _ c _ (by assumption)))

lemma TagInv_scanLoop : ∀ (fuel : Nat) (s : ScannerState) (ts : Array (Positioned YamlToken)),
    TagInv s → scanLoop s fuel = .ok ts → ∀ t ∈ toks ts, emitOk t = true := by
  intro fuel
  induction fuel with
  | zero => intro s ts _ h; simp [scanLoop] at h
  | succ n ih =>
    intro s ts hI h
    unfold scanLoop at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · split at h
          · contradiction
          · split at h
            · contradiction
            · simp only [Except.ok.injEq] at h; subst h
              show TagInv ((unwindIndents s (-1)).emit .streamEnd)
              exact hI.of ((TagExt_unwindIndents s (-1)).trans (TagExt.snoc (vals_emit _ _) rfl))
    · rename_i s' hs'
      exact ih s' ts (hI.of (TagExt_scanNextToken s s' hs')) h

lemma TagInv_init (input : String) : TagInv ((ScannerState.mk' input).emit .streamStart) := by
  intro t ht
  simp [vals, toks, ScannerState.mk', ScannerState.emit] at ht
  subst ht; rfl

/-- Raw scanner output: every token is tag-shaped. -/
lemma scan_emitOk (input : String) (ts : Array (Positioned YamlToken)) (h : scan input = .ok ts) :
    ∀ t ∈ toks ts, emitOk t = true := by
  unfold scan at h
  have hI0 := TagInv_init input
  dsimp only at h
  split at h
  · exact TagInv_scanLoop _ _ ts (hI0.of (TagExt.ofTokens (consumeBOM_preserves_tokens _))) h
  · exact TagInv_scanLoop _ _ ts hI0 h

/-- Filtered scanner output: every token is tag-shaped. -/
lemma scanFiltered_emitOk (input : String) (ts : Array (Positioned YamlToken))
    (h : scanFiltered input = .ok ts) : ∀ t ∈ toks ts, emitOk t = true := by
  unfold scanFiltered at h
  split at h
  · rename_i raw hraw
    simp only [Except.ok.injEq] at h; subst h
    intro t ht
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
    have hp' : p ∈ raw := (Array.mem_filter.1 (Array.mem_toList_iff.1 hp)).1
    exact scan_emitOk input raw hraw _ (List.mem_map.2 ⟨p, Array.mem_toList_iff.2 hp', rfl⟩)
  · contradiction

end L4YAML.Proofs.TagShape

end Blanket
