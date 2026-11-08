/-
Copyright (c) 2025 NASA Jet Propulsion Laboratory. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Proofs.Serialization.TraceOf.Document
public import L4YAML.Proofs.Serialization.TokenEvents
public import L4YAML.Proofs.Production.StructureProduction
public import L4YAML.Proofs.Scanner.ScannerCorrectness
public import L4YAML.Proofs.Output.EmitterScannability.FilteredGrowth
public import L4YAML.Proofs.Scanner.TagShape
public import L4YAML.Proofs.Serialization.TraceOf.LeafBridge

/-!
# S3 slice (2): the document-marker bridge (capstone 7.7, item 462)

The scanner's `scanDocumentStart` / `scanDocumentEnd` / `scanDirective` arms land on the
surface relations `TraceOf/Document.lean` annotates (`SCDirectivesEnd`, `SCDocumentEnd`,
`ScannedDirective` — `SLDirective` once the line tail is read), and the tokens each arm
pushes read, through `TokenEvents.goOut`, as exactly the event list the annotation
carries: `---` is `beginDocument` followed by the pending `%TAG` handles as `declareTag`
in directive order; `...` is `endDocument`; a directive emits nothing and leaves
`declaredHandle` of its span pending — `TLDirective`'s payload, from the scanner's handle.
-/

namespace L4YAML.Proofs.Serialization.TraceOf.DocBridge

public section

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.StructureProduction L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScalarProduction L4YAML.Proofs.TagShape
open L4YAML.Proofs.ScannerCorrectness (advanceN_preserves_tokens skipWhitespace_preserves_tokens
  skipToEndOfLine_preserves_tokens)
open L4YAML.Proofs.EmitterScannability (scanYamlDirective_new_token_eq scanTagDirective_new_token_eq)

/-- `unwindIndentsLoop` appends `blockEnd`s and nothing else. -/
lemma unwindIndentsLoop_tokens_append (col : Int) : ∀ (fuel : Nat) (s : ScannerState),
    ∃ ends : List (Positioned YamlToken),
      (unwindIndentsLoop s col fuel).tokens.toList = s.tokens.toList ++ ends ∧
      ∀ t ∈ ends, t.val = .blockEnd := by
  intro fuel
  induction fuel with
  | zero => intro s; exact ⟨[], by simp [unwindIndentsLoop], by simp⟩
  | succ f ih =>
    intro s
    unfold unwindIndentsLoop
    split
    · obtain ⟨ends, hM, hall⟩ := ih _
      refine ⟨{ pos := s.currentPos, val := .blockEnd } :: ends, ?_, ?_⟩
      · rw [hM]; simp [ScannerState.emit]
      · intro t ht; simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · rfl
        · exact hall t ht
    · exact ⟨[], by simp, by simp⟩

lemma unwindIndents_tokens_append (s : ScannerState) (col : Int) :
    ∃ ends : List (Positioned YamlToken),
      (unwindIndents s col).tokens.toList = s.tokens.toList ++ ends ∧
      ∀ t ∈ ends, t.val = .blockEnd :=
  unwindIndentsLoop_tokens_append col _ s

/-- The tokens `scanDocumentStart` pushes: the unwound `blockEnd`s, then `documentStart`. -/
lemma scanDocumentStart_tokens (sc : ScannerState) :
    ∃ (ends : List (Positioned YamlToken)) (ds : Positioned YamlToken),
      (scanDocumentStart sc).tokens.toList = sc.tokens.toList ++ ends ++ [ds] ∧
      (∀ t ∈ ends, t.val = .blockEnd) ∧ ds.val = .documentStart := by
  obtain ⟨ends, hends, hall⟩ := unwindIndents_tokens_append sc (-1)
  refine ⟨ends, { pos := (unwindIndents sc (-1)).currentPos, val := .documentStart }, ?_, hall, rfl⟩
  simp only [scanDocumentStart, advanceN_preserves_tokens, ScannerState.emit]
  (simp [hends] <;> rfl)

/-- The tokens `scanDocumentEnd` pushes when it accepts: the unwound `blockEnd`s, then
`documentEnd`. -/
lemma scanDocumentEnd_tokens (sc s' : ScannerState) (hok : scanDocumentEnd sc = .ok s') :
    ∃ (ends : List (Positioned YamlToken)) (de : Positioned YamlToken),
      s'.tokens.toList = sc.tokens.toList ++ ends ++ [de] ∧
      (∀ t ∈ ends, t.val = .blockEnd) ∧ de.val = .documentEnd := by
  obtain ⟨ends, hends, hall⟩ := unwindIndents_tokens_append sc (-1)
  refine ⟨ends, { pos := (unwindIndents sc (-1)).currentPos, val := .documentEnd }, ?_, hall, rfl⟩
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · exact absurd hok (by simp)
  · have hres : ∀ r, (.ok r : Except ScanError ScannerState) = .ok s' → r = s' :=
      fun r h => Except.ok.inj h
    split at hok
    · have := hres _ hok; subst this
      simp only [advanceN_preserves_tokens, ScannerState.emit]; (simp [hends] <;> rfl)
    · have := hres _ hok; subst this
      simp only [advanceN_preserves_tokens, ScannerState.emit]; (simp [hends] <;> rfl)
    · split at hok
      · have := hres _ hok; subst this
        simp only [advanceN_preserves_tokens, ScannerState.emit]; (simp [hends] <;> rfl)
      · exact absurd hok (by simp)

/-- What the marker's tokens say to `goOut`: `---` is `beginDocument` then the pending
handles, in directive order, and clears them. -/
lemma goOut_marker_start (ends : List (Positioned YamlToken)) (ds : Positioned YamlToken)
    (hends : ∀ t ∈ ends, t.val = .blockEnd) (hds : ds.val = .documentStart) (p : List String) :
    goOut (ends ++ [ds]) p = (.beginDocument :: p.reverse.map .declareTag, []) := by
  rw [goOut_blockEnds ends hends, goOut_documentStart ds hds]; simp

/-- `...` is `endDocument`; the pending handles are untouched. -/
lemma goOut_marker_end (ends : List (Positioned YamlToken)) (de : Positioned YamlToken)
    (hends : ∀ t ∈ ends, t.val = .blockEnd) (hde : de.val = .documentEnd) (p : List String) :
    goOut (ends ++ [de]) p = ([.endDocument], p) := by
  rw [goOut_blockEnds ends hends, goOut_documentEnd de hde]; simp

/-- **`---`**: the scanner's document start is `[203] c-directives-end` on its span, and the
tokens it pushes read `beginDocument :: declareTag*` of the pending handles. -/
lemma scanDocumentStart_trace (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (rest : List Char) (hchars : sp.chars = '-' :: '-' :: '-' :: rest)
    (hcol : sp.col = 0) :
    ∃ (sp' : SurfPos) (ends : List (Positioned YamlToken)) (ds : Positioned YamlToken),
      SCDirectivesEnd sp sp' ∧ ScannerSurfCorr (scanDocumentStart sc) sp' ∧
      (scanDocumentStart sc).tokens.toList = sc.tokens.toList ++ ends ++ [ds] ∧
      (∀ t ∈ ends, t.val = .blockEnd) ∧ ds.val = .documentStart ∧
      ∀ p, goOut (ends ++ [ds]) p = (.beginDocument :: p.reverse.map .declareTag, []) := by
  obtain ⟨sp', hprod, hcorr'⟩ := scanDocumentStart_prod sc sp hcorr rest hchars hcol
  obtain ⟨ends, ds, htoks, hends, hds⟩ := scanDocumentStart_tokens sc
  exact ⟨sp', ends, ds, hprod, hcorr', htoks, hends, hds, goOut_marker_start ends ds hends hds⟩

/-- **`...`**: the scanner's document end is `[204] c-document-end` on its span, and the
tokens it pushes read `[endDocument]`, the pending handles untouched. -/
lemma scanDocumentEnd_trace (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (rest : List Char) (hchars : sp.chars = '.' :: '.' :: '.' :: rest)
    (hcol : sp.col = 0)
    (s' : ScannerState) (hok : scanDocumentEnd sc = .ok s') :
    ∃ (sp' : SurfPos) (ends : List (Positioned YamlToken)) (de : Positioned YamlToken),
      SCDocumentEnd sp sp' ∧ ScannerSurfCorr s' sp' ∧
      s'.tokens.toList = sc.tokens.toList ++ ends ++ [de] ∧
      (∀ t ∈ ends, t.val = .blockEnd) ∧ de.val = .documentEnd ∧
      ∀ p, goOut (ends ++ [de]) p = ([.endDocument], p) := by
  obtain ⟨sp', hprod, hcorr'⟩ := scanDocumentEnd_prod sc sp hcorr rest hchars hcol s' hok
  obtain ⟨ends, de, htoks, hends, hde⟩ := scanDocumentEnd_tokens sc s' hok
  exact ⟨sp', ends, de, hprod, hcorr', htoks, hends, hde, goOut_marker_end ends de hends hde⟩

/-! ## The `%TAG` handle: scanner run vs the lexer's `declaredHandle` -/

open L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SourceEvents
open L4YAML.Proofs.Serialization.EventsOf (declaredHandle)

/-- `isNamedHandle`'s character test is `[38] ns-word-char`. -/
lemma isAlphanum_or_dash_eq_isWordCharBool (c : Char) :
    (c.isAlphanum || c = '-') = isWordCharBool c := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro h
    rw [isWordCharBool, decide_eq_true_eq]
    unfold isWordCharProp isAsciiLetterProp
    simp only [Char.isAlphanum, Char.isAlpha, Char.isDigit, Char.isUpper, Char.isLower,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | h
    · exact Or.inr (Or.inl (Or.inl ⟨h1, h2⟩))
    · exact Or.inr (Or.inl (Or.inr ⟨h1, h2⟩))
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inr h)
  · intro h
    have := L4YAML.Proofs.TagShape.wordChar_alnum c h
    simpa using this

/-- The three shapes `isTagHandleShaped` accepts. -/
lemma shaped_cases (hd : String) (h : isTagHandleShaped hd = true) :
    hd.toList = ['!'] ∨ hd.toList = ['!', '!'] ∨
      ∃ w : List Char, w ≠ [] ∧ w.all isWordCharBool = true ∧ hd.toList = '!' :: (w ++ ['!']) := by
  unfold isTagHandleShaped at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (rfl | rfl) | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · right; right
    split at h
    · rename_i rest heq
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨⟨hlen, hlast⟩, hall⟩ := h
      have hne : rest ≠ [] := by intro h0; subst h0; simp at hlen
      have hsplit := List.dropLast_concat_getLast hne
      have hlast' : rest.getLast hne = '!' := by
        have := List.getLast?_eq_some_getLast (l := rest) hne
        rw [this] at hlast; exact Option.some.inj hlast
      refine ⟨rest.dropLast, ?_, hall, ?_⟩
      · intro h0
        have := List.length_dropLast (xs := rest)
        rw [h0] at this; simp at this; omega
      · rw [heq, ← hsplit, hlast']; simp
    · exact absurd h (by simp)

lemma isNamedHandle_of_named (hd : String) (w : List Char) (hw : w ≠ [])
    (hall : w.all isWordCharBool = true) (hh : hd.toList = '!' :: (w ++ ['!'])) :
    isNamedHandle hd = true := by
  simp only [isNamedHandle, hh]
  rw [List.getLast?_concat, List.dropLast_concat]
  cases w with
  | nil => exact absurd rfl hw
  | cons c cs =>
    simp only [List.length_append, List.length_cons, beq_self_eq_true,
      Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by omega, ?_⟩
    rw [List.all_eq_true]
    intro x hx
    rw [isAlphanum_or_dash_eq_isWordCharBool]
    exact List.all_eq_true.mp hall x hx

lemma isNamedHandle_of_toList_bang (hd : String) (hh : hd.toList = ['!']) :
    isNamedHandle hd = false := by
  simp [isNamedHandle, hh]

lemma isNamedHandle_of_toList_bangbang (hd : String) (hh : hd.toList = ['!', '!']) :
    isNamedHandle hd = false := by
  simp [isNamedHandle, hh]

lemma white_cases (c : Char) (hc : isWhiteSpaceBool c = true) : c = ' ' ∨ c = '\t' := by
  by_cases h1 : c = ' '
  · exact Or.inl h1
  · by_cases h2 : c = '\t'
    · exact Or.inr h2
    · exfalso; simp [isWhiteSpaceBool, isSpaceBool, isTabBool, h1, h2] at hc

/-- `dropHSpace` skips exactly a white prefix when what follows is not white. -/
lemma dropHSpace_append (ws L : List Char) (hws : ∀ c ∈ ws, isWhiteSpaceBool c = true)
    (hL : ∀ c, L.head? = some c → isWhiteSpaceBool c = false) :
    dropHSpace (ws ++ L) = L := by
  induction ws with
  | nil =>
    cases L with
    | nil => rfl
    | cons c cs =>
      have hc := hL c rfl
      have h1 : c ≠ ' ' := by intro h; subst h; exact absurd hc (by decide)
      have h2 : c ≠ '\t' := by intro h; subst h; exact absurd hc (by decide)
      simp [dropHSpace, h1, h2]
  | cons c cs ih =>
    have ih' := ih (fun x hx => hws x (by simp [hx]))
    rcases white_cases c (hws c (by simp)) with rfl | rfl <;> simp [dropHSpace, ih']

/-- A `%TAG` declaration the lexer accepts starts `%TAG` + one white. -/
lemma namedTagDeclarationAt_some_shape (L : List Char) (e : Event) (tl : List Char)
    (h : namedTagDeclarationAt L = some (e, tl)) :
    ∃ c cs, L = '%' :: 'T' :: 'A' :: 'G' :: c :: cs ∧ (c = ' ' ∨ c = '\t') := by
  unfold namedTagDeclarationAt at h
  split at h
  · exact ⟨' ', _, rfl, Or.inl rfl⟩
  · exact ⟨'\t', _, rfl, Or.inr rfl⟩
  · exact absurd h (by simp)

lemma declaredHandle_some_shape (L : List Char) (hd : String) (h : declaredHandle L = some hd) :
    ∃ c cs, L = '%' :: 'T' :: 'A' :: 'G' :: c :: cs ∧ (c = ' ' ∨ c = '\t') := by
  unfold declaredHandle at h
  cases hN : namedTagDeclarationAt L with
  | none => simp [hN] at h
  | some pr =>
    obtain ⟨e, tl⟩ := pr
    exact namedTagDeclarationAt_some_shape L e tl hN

lemma not_white_of_wordOrBang (c : Char) (h : (isWordCharBool c || c == '!') = true) :
    isWhiteSpaceBool c = false := by
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | rfl
  · simp only [isWordCharBool, decide_eq_true_eq] at h
    unfold isWordCharProp isAsciiLetterProp at h
    by_cases h1 : c = ' '
    · subst h1; simp at h
    · by_cases h2 : c = '\t'
      · subst h2; simp at h
      · simp [isWhiteSpaceBool, isSpaceBool, isTabBool, h1, h2]
  · decide

/-- **The lexer on a scanner-accepted `%TAG` line.**  With `c` the separating white, `ws`
further whites, `run` the handle the scanner collected (maximal: `tail` does not start with a
word char or `!`) and `hd` shaped, `declaredHandle` names `hd` iff it is named. -/
lemma declaredHandle_TAG_line (c : Char) (hc : c = ' ' ∨ c = '\t')
    (ws run tail : List Char)
    (hws : ∀ x ∈ ws, isWhiteSpaceBool x = true)
    (hrun : run.all (fun x => isWordCharBool x || x == '!') = true)
    (htail : ∀ x, tail.head? = some x → (isWordCharBool x || x == '!') = false)
    (hd : String) (hhd : hd.toList = run) (hshaped : isTagHandleShaped hd = true) :
    declaredHandle ('%' :: 'T' :: 'A' :: 'G' :: c :: (ws ++ run ++ tail)) =
      (if isNamedHandle hd then some hd else none) := by
  have hbang : isWordCharBool '!' = false := by decide
  have hstep : namedTagDeclarationAt ('%' :: 'T' :: 'A' :: 'G' :: c :: (ws ++ run ++ tail)) =
      namedTagDeclarationAfterSep (ws ++ run ++ tail) := by
    rcases hc with rfl | rfl <;> rfl
  unfold declaredHandle
  rw [hstep]
  rcases shaped_cases hd hshaped with h1 | h2 | ⟨w, hwne, hwall, hw⟩
  · -- `!`
    rw [h1] at hhd; subst hhd
    rw [isNamedHandle_of_toList_bang hd h1]
    have hdrop : dropHSpace (ws ++ '!' :: tail) = '!' :: tail :=
      dropHSpace_append ws ('!' :: tail) hws (fun x hx => by
        simp only [List.head?_cons, Option.some.injEq] at hx; subst hx; decide)
    have hspan : spanWhile isWordCharBool tail = ([], tail) := by
      cases tail with
      | nil => rfl
      | cons t ts =>
        have := htail t rfl
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at this
        simp [spanWhile, this.1]
    have hL : ws ++ ['!'] ++ tail = ws ++ '!' :: tail := by simp
    have h1 : namedTagDeclarationAfterSep (ws ++ '!' :: tail) = namedTagDeclarationTail tail := by
      unfold namedTagDeclarationAfterSep; rw [hdrop]; rfl
    rw [hL, h1]; unfold namedTagDeclarationTail; rw [hspan]; simp
  · -- `!!`
    rw [h2] at hhd; subst hhd
    rw [isNamedHandle_of_toList_bangbang hd h2]
    have hdrop : dropHSpace (ws ++ '!' :: '!' :: tail) = '!' :: '!' :: tail :=
      dropHSpace_append ws ('!' :: '!' :: tail) hws (fun x hx => by
        simp only [List.head?_cons, Option.some.injEq] at hx; subst hx; decide)
    have hspan : spanWhile isWordCharBool ('!' :: tail) = ([], '!' :: tail) := by
      simp [spanWhile, hbang]
    have hL : ws ++ ['!', '!'] ++ tail = ws ++ '!' :: '!' :: tail := by simp
    have h1 : namedTagDeclarationAfterSep (ws ++ '!' :: '!' :: tail) =
        namedTagDeclarationTail ('!' :: tail) := by
      unfold namedTagDeclarationAfterSep; rw [hdrop]; rfl
    rw [hL, h1]; unfold namedTagDeclarationTail; rw [hspan]; simp
  · -- `!w!`
    rw [hw] at hhd; subst hhd
    rw [isNamedHandle_of_named hd w hwne hwall hw]
    have hdrop : dropHSpace (ws ++ '!' :: (w ++ '!' :: tail)) = '!' :: (w ++ '!' :: tail) :=
      dropHSpace_append ws ('!' :: (w ++ '!' :: tail)) hws (fun x hx => by
        simp only [List.head?_cons, Option.some.injEq] at hx; subst hx; decide)
    have hspan : spanWhile isWordCharBool (w ++ '!' :: tail) = (w, '!' :: tail) :=
      L4YAML.Proofs.Serialization.TraceOf.LeafBridge.spanWhile_prefix isWordCharBool w ('!' :: tail)
        hwall (fun x hx => by simp only [List.head?_cons, Option.some.injEq] at hx; subst hx; exact hbang)
    have hd_eq : hd = "!" ++ String.ofList w ++ "!" := by
      apply String.ext
      simp [hw]
    have hL : ws ++ '!' :: (w ++ ['!']) ++ tail = ws ++ '!' :: (w ++ '!' :: tail) := by simp
    cases w with
    | nil => exact absurd rfl hwne
    | cons a as =>
      have h1 : namedTagDeclarationAfterSep (ws ++ '!' :: (a :: as ++ '!' :: tail)) =
          namedTagDeclarationTail (a :: as ++ '!' :: tail) := by
        unfold namedTagDeclarationAfterSep; rw [hdrop]; rfl
      rw [hL, h1]; unfold namedTagDeclarationTail; rw [hspan]
      simp [hd_eq]

/-- `collectTagHandleDirectiveLoop` stores exactly the span it consumes: a run of word chars
and `!`s, maximal — the next char, if any, is neither. -/
lemma collectTagHandleDirectiveLoop_chars (fuel : Nat) :
    ∀ (sc : ScannerState) (sp : SurfPos) (acc : String),
    ScannerSurfCorr sc sp → sc.inputEnd - sc.offset ≤ fuel →
    ∃ (run : List Char) (sp' : SurfPos),
      sp.chars = run ++ sp'.chars ∧
      (collectTagHandleDirectiveLoop sc acc fuel).1.toList = acc.toList ++ run ∧
      run.all (fun c => isWordCharBool c || c == '!') = true ∧
      (∀ c, sp'.chars.head? = some c → (isWordCharBool c || c == '!') = false) ∧
      GStar (GChar (fun c => isWordCharProp c ∨ c = '!')) sp sp' ∧
      GNot (GChar (fun c => isWordCharProp c ∨ c = '!')) sp' ∧
      ScannerSurfCorr (collectTagHandleDirectiveLoop sc acc fuel).2 sp' := by
  induction fuel with
  | zero =>
    intro sc sp acc hcorr hfuel
    have hpeek := peek_none_of_fuel_zero hfuel
    have hnil := peek_none_chars_nil hcorr hpeek
    refine ⟨[], sp, by simp, by simp [collectTagHandleDirectiveLoop], rfl, ?_, GStar.nil _,
      gnot_gchar_of_peek_none hcorr hpeek,
      by simpa [collectTagHandleDirectiveLoop] using hcorr⟩
    intro c hc; rw [hnil] at hc; simp at hc
  | succ fuel' ih =>
    intro sc sp acc hcorr hfuel
    unfold collectTagHandleDirectiveLoop; split
    · rename_i c hpeek; split
      · rename_i hcond
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have hmore := peek_some_has_more hpeek
        have hnlb := isWordCharOrBang_not_isLineBreak c hcond
        have hne_nl : c ≠ '\n' := by intro heq; subst heq; exact hnlb (by decide)
        have hne_cr : c ≠ '\r' := by intro heq; subst heq; exact hnlb (by decide)
        have hcorr_adv := advance_non_newline_corr sc c rest hcorr hmore hne_nl hne_cr
        have hfuel' : sc.advance.inputEnd - sc.advance.offset ≤ fuel' := by
          have h1 := ScannerProgress.advance_offset_lt sc hmore
          have h2 : sc.advance.inputEnd = sc.inputEnd := advance_inputEnd sc
          omega
        obtain ⟨run, sp', hchars, hacc, hall, hstop, hg, hn, hcorr'⟩ :=
          ih sc.advance ⟨rest, sc.col + 1⟩ (acc.push c) hcorr_adv hfuel'
        have hcP : isWordCharProp c ∨ c = '!' := by
          simp only [Bool.or_eq_true, beq_iff_eq] at hcond
          rcases hcond with h | h
          · exact Or.inl ((isWordChar_iff c).mp h)
          · exact Or.inr h
        refine ⟨c :: run, sp', ?_, ?_, ?_, hstop, ?_, hn, hcorr'⟩
        · simp only at hchars; simp [hchars]
        · rw [hacc, String.toList_push]; simp
        · simp [hcond, hall]
        · exact GStar.cons _ _ _ (GChar.mk c rest sc.col hcP) hg
      · rename_i hcond
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have hcF : (isWordCharBool c || c == '!') = false := Bool.not_eq_true _ |>.mp hcond
        refine ⟨[], _, by simp, by simp, rfl, ?_, GStar.nil _, gnot_gchar_head ?_, hcorr⟩
        · intro c' hc'; simp only [List.head?_cons, Option.some.injEq] at hc'; subst hc'; exact hcF
        · intro hP
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hcF
          rcases hP with h | h
          · exact absurd ((isWordChar_iff c).mpr h) (by simp [hcF.1])
          · exact hcF.2 h
    · rename_i hpeek
      have hnil := peek_none_chars_nil hcorr hpeek
      refine ⟨[], sp, by simp, by simp, rfl, ?_, GStar.nil _, gnot_gchar_of_peek_none hcorr hpeek, hcorr⟩
      intro c hc; rw [hnil] at hc; simp at hc

/-! ## The directive arm -/

open L4YAML.Proofs.ScannerCorrectness (advance_preserves_tokens)
open L4YAML.Proofs.ScannerCoupling

lemma gstar_gchar_length {P : Char → Prop} {s s' : SurfPos} (h : GStar (GChar P) s s') :
    s'.chars.length ≤ s.chars.length := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons s₁ s₂ s₃ h1 _ ih =>
    cases h1 with
    | mk c rest col _ => simp only [List.length_cons] at ih ⊢; omega

lemma gstar_sswhite_chars {s s' : SurfPos} (h : GStar SSWhite s s') :
    ∃ ws : List Char, s.chars = ws ++ s'.chars ∧ ∀ c ∈ ws, isWhiteSpaceBool c = true := by
  induction h with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons s₁ s₂ s₃ h1 _ ih =>
    obtain ⟨ws, hw, hall⟩ := ih
    cases h1 with
    | space rest col =>
      refine ⟨' ' :: ws, by simp only at hw; simp [hw], ?_⟩
      intro c hc; simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · decide
      · exact hall c hc
    | tab rest col =>
      refine ⟨'\t' :: ws, by simp only at hw; simp [hw], ?_⟩
      intro c hc; simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · decide
      · exact hall c hc
open L4YAML.Proofs.ScannerCorrectness.ScanHelpers (collectDirectiveNameLoop_preserves_tokens
  collectTagHandleDirectiveLoop_preserves_tokens collectTagPrefixLoop_preserves_tokens)

lemma isNsChar_of_bool (c : Char)
    (h : (!isWhiteSpaceBool c && !isLineBreakBool c && isPrintableBool c && c != '\uFEFF') = true) :
    isNsChar c := (isNsChar_iff_bool c).mpr h

lemma not_isNsChar_of_white (c : Char) (hw : isWhiteSpaceBool c = true) : ¬ isNsChar c := by
  intro h; rw [isNsChar_iff_bool] at h; simp [hw] at h

lemma gnot_gchar_head_not {P : Char → Prop} {c : Char} {rest : List Char} {col : Nat}
    (h : GNot (GChar P) ⟨c :: rest, col⟩) : ¬ P c :=
  fun hp => h ⟨rest, col + 1⟩ (GChar.mk c rest col hp)

lemma gstar_sswhite_length {s s' : SurfPos} (h : GStar SSWhite s s') :
    s'.chars.length ≤ s.chars.length := by
  obtain ⟨ws, hw, _⟩ := gstar_sswhite_chars h
  rw [hw]; simp

/-- `declaredHandle` is `none` on every prefix of a line that does not start `%TAG` + white. -/
lemma declaredHandle_prefix_none (L : List Char)
    (hL : ∀ c cs, L = '%' :: 'T' :: 'A' :: 'G' :: c :: cs → (c = ' ' ∨ c = '\t') → False) (k : Nat) :
    declaredHandle (L.take k) = none := by
  cases h : declaredHandle (L.take k) with
  | none => rfl
  | some hd =>
    exfalso
    obtain ⟨c, cs, hshape, hc⟩ := declaredHandle_some_shape _ hd h
    have hLeq : L = '%' :: 'T' :: 'A' :: 'G' :: c :: (cs ++ L.drop k) := by
      have h2 : L = L.take k ++ L.drop k := (List.take_append_drop k L).symm
      rw [hshape] at h2; simpa using h2
    exact hL _ _ hLeq hc

lemma head?_take {α : Type} (l : List α) (m : Nat) (x : α) (h : (l.take m).head? = some x) :
    l.head? = some x := by
  cases m with
  | zero => simp at h
  | succ m => cases l with
    | nil => simp at h
    | cons a l => simpa using h

/-- `declaredHandle` of any span of a scanner-accepted `%TAG` line reaching past the handle. -/
lemma declaredHandle_span_TAG (sp sp'' : SurfPos) (c : Char) (hc : c = ' ' ∨ c = '\t')
    (ws run rest : List Char)
    (hsp : sp.chars = '%' :: 'T' :: 'A' :: 'G' :: c :: (ws ++ run ++ rest))
    (hws : ∀ x ∈ ws, isWhiteSpaceBool x = true)
    (hrun : run.all (fun x => isWordCharBool x || x == '!') = true)
    (hrest : ∀ x, rest.head? = some x → (isWordCharBool x || x == '!') = false)
    (hd : String) (hhd : hd.toList = run) (hshaped : isTagHandleShaped hd = true)
    (hlen : sp''.chars.length ≤ rest.length) :
    declaredHandle (span sp sp'') = (if isNamedHandle hd then some hd else none) := by
  have hsp' : sp.chars = ('%' :: 'T' :: 'A' :: 'G' :: c :: (ws ++ run)) ++ rest := by
    rw [hsp]; simp
  have hlen5 : sp.chars.length = ws.length + run.length + 5 + rest.length := by
    rw [hsp]; simp [List.length_append]; omega
  unfold span
  obtain ⟨i, hi⟩ : ∃ i, sp.chars.length - sp''.chars.length =
      ('%' :: 'T' :: 'A' :: 'G' :: c :: (ws ++ run)).length + i :=
    ⟨sp.chars.length - sp''.chars.length - ('%' :: 'T' :: 'A' :: 'G' :: c :: (ws ++ run)).length,
      by simp only [List.length_cons, List.length_append]; omega⟩
  rw [hi, hsp', List.take_append, List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  have h1 : ('%' :: 'T' :: 'A' :: 'G' :: c :: (ws ++ run)) ++ rest.take i
      = '%' :: 'T' :: 'A' :: 'G' :: c :: (ws ++ run ++ rest.take i) := by simp
  rw [h1]
  exact declaredHandle_TAG_line c hc ws run _ hws hrun
    (fun x hx => hrest x (head?_take _ _ _ hx)) hd hhd hshaped

/-- `scanTagDirective` read on the surface, with the handle it stored: the handle IS the
consumed run (`collectTagHandleDirectiveLoop_chars`), it is shaped (`[89]`), and the only
token pushed is `.tagDirective handle pfx` at `startPos`. -/
lemma scanTagDirective_trace
    (s_after_ws : ScannerState) (sp_ws : SurfPos) (hcorr_ws : ScannerSurfCorr s_after_ws sp_ws)
    (sc : ScannerState) (hend : s_after_ws.inputEnd = sc.inputEnd)
    (startPos : YamlPos) (s' : ScannerState)
    (hok : scanTagDirective sc s_after_ws startPos = .ok s') :
    ∃ (run : List Char) (s₂ s₃ s₄ sp_v : SurfPos) (handle pfx : String),
      sp_ws.chars = run ++ s₂.chars ∧ handle.toList = run ∧ isTagHandleShaped handle = true ∧
      run.all (fun c => isWordCharBool c || c == '!') = true ∧
      (∀ c, s₂.chars.head? = some c → (isWordCharBool c || c == '!') = false) ∧
      GStar (GChar (fun c => isWordCharProp c ∨ c = '!')) sp_ws s₂ ∧
      GNot (GChar (fun c => isWordCharProp c ∨ c = '!')) s₂ ∧
      GStar SSWhite s₂ s₃ ∧ GStar (GChar isUriCharProp) s₃ s₄ ∧
      GStar SSWhite s₄ sp_v ∧ DirectiveStop s₄ sp_v ∧ ScannerSurfCorr s' sp_v ∧
      s'.tokens = s_after_ws.tokens.push { pos := startPos, val := .tagDirective handle pfx } := by
  unfold scanTagDirective at hok
  simp only [bind, Except.bind] at hok
  obtain ⟨run, sp_hdl, hchars, hacc, hall, hstop, hg, hn, hcorr_hdl⟩ :=
    collectTagHandleDirectiveLoop_chars (sc.inputEnd - s_after_ws.offset) s_after_ws sp_ws "" hcorr_ws
      (by rw [hend]; exact Nat.le_refl _)
  obtain ⟨sp_ws2, h_ws, hcorr_ws2⟩ := skipWhitespace_corr _ sp_hdl hcorr_hdl
  obtain ⟨sp_pfx, h_pfx, hcorr_pfx⟩ := collectTagPrefixLoop_prod _ sp_ws2 hcorr_ws2 "" _
  obtain ⟨sp_val, h_ws_val, hcorr_val⟩ := skipWhitespace_corr _ sp_pfx hcorr_pfx
  have lift : ∀ (s_v : ScannerState) (sp_v : SurfPos), ScannerSurfCorr s_v sp_v →
      ∀ (startPos : YamlPos) (h t : String),
      ScannerSurfCorr { s_v.emitAt startPos (.tagDirective h t) with directivesPresent := true } sp_v :=
    fun _ _ hc _ _ _ => ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩
  have htoks : ∀ (s_v : ScannerState) (h t : String), s_v.tokens = s_after_ws.tokens →
      ({ s_v.emitAt startPos (.tagDirective h t) with directivesPresent := true } : ScannerState).tokens
        = s_after_ws.tokens.push { pos := startPos, val := .tagDirective h t } := by
    intro s_v h t hs; simp [ScannerState.emitAt, hs]
  have hval_toks : (skipWhitespace (collectTagPrefixLoop (skipWhitespace
      (collectTagHandleDirectiveLoop s_after_ws "" (sc.inputEnd - s_after_ws.offset)).2) ""
        (sc.inputEnd - (skipWhitespace (collectTagHandleDirectiveLoop s_after_ws ""
          (sc.inputEnd - s_after_ws.offset)).2).offset)).2).tokens = s_after_ws.tokens := by
    rw [skipWhitespace_preserves_tokens, collectTagPrefixLoop_preserves_tokens,
      skipWhitespace_preserves_tokens, collectTagHandleDirectiveLoop_preserves_tokens]
  have hacc' : (collectTagHandleDirectiveLoop s_after_ws "" (sc.inputEnd - s_after_ws.offset)).1.toList = run := by
    simpa using hacc
  have hshaped : isTagHandleShaped
      (collectTagHandleDirectiveLoop s_after_ws "" (sc.inputEnd - s_after_ws.offset)).1 = true := by
    cases hsh : isTagHandleShaped
        (collectTagHandleDirectiveLoop s_after_ws "" (sc.inputEnd - s_after_ws.offset)).1 with
    | true => simp
    | false =>
      exfalso
      simp only [hsh, Bool.not_false, ↓reduceIte] at hok
      simp [throw, throwThe, MonadExceptOf.throw] at hok
  simp only [hshaped, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
  split at hok
  · rename_i hpeek
    split at hok
    · exact absurd hok (by simp)
    · rename_i hcol
      have h := Except.ok.inj hok; subst h
      exact ⟨run, sp_hdl, sp_ws2, sp_pfx, sp_val, _, _, hchars, hacc', hshaped, hall, hstop, hg, hn,
        h_ws, h_pfx, h_ws_val,
        directiveStop_of_validated hcorr_pfx hcorr_val (Or.inr (Or.inr ⟨hpeek, hcol⟩)),
        lift _ _ hcorr_val _ _ _, htoks _ _ _ hval_toks⟩
  · rename_i c _ hpeek
    split at hok
    · exact absurd hok (by simp)
    · rename_i hlb
      have h := Except.ok.inj hok; subst h
      exact ⟨run, sp_hdl, sp_ws2, sp_pfx, sp_val, _, _, hchars, hacc', hshaped, hall, hstop, hg, hn,
        h_ws, h_pfx, h_ws_val,
        directiveStop_of_validated hcorr_pfx hcorr_val (Or.inr (Or.inl ⟨c, hpeek, by simpa using hlb⟩)),
        lift _ _ hcorr_val _ _ _, htoks _ _ _ hval_toks⟩
  · rename_i hpeek
    have h := Except.ok.inj hok; subst h
    exact ⟨run, sp_hdl, sp_ws2, sp_pfx, sp_val, _, _, hchars, hacc', hshaped, hall, hstop, hg, hn,
      h_ws, h_pfx, h_ws_val,
      directiveStop_of_validated hcorr_pfx hcorr_val (Or.inl hpeek),
      lift _ _ hcorr_val _ _ _, htoks _ _ _ hval_toks⟩

/-- **`%`**: the scanner's directive is `ScannedDirective` on its span, ending at a break or
EOF, and the tokens it pushes read through `goOut` as nothing emitted and exactly
`declaredHandle (span sp sp')` — `TLDirective`'s payload — added to the pending handles;
the payload is stable under any extension of the span (the `s-l-comments` tail). -/
lemma scanDirective_trace (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '%')
    (s' : ScannerState) (hok : scanDirective sc = .ok s') :
    ∃ sp', ScannedDirective sp sp' ∧ ScannerSurfCorr s' sp' ∧
      (sp'.chars = [] ∨ ∃ ch rest', sp'.chars = ch :: rest' ∧ isLineBreakBool ch = true) ∧
      ∃ new : List (Positioned YamlToken),
        s'.tokens.toList = sc.tokens.toList ++ new ∧
        (∀ p, goOut new p = ([], (declaredHandle (span sp sp')).toList ++ p)) ∧
        (∀ sp'' : SurfPos, sp''.chars.length ≤ sp'.chars.length →
          declaredHandle (span sp sp'') = declaredHandle (span sp sp')) := by
  obtain ⟨rest, rfl⟩ := peek_some_sp hcorr hpeek
  unfold scanDirective at hok
  split at hok
  · exact absurd hok (by simp)
  · dsimp only [] at hok
    have hmore := corr_nonempty_has_more hcorr
    have hcorr_pct := advance_non_newline_corr sc '%' rest
      ⟨hcorr.chars_from, rfl, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
      hmore (by decide) (by decide)
    obtain ⟨nm, sp_name, hchars, hcol, hall, hname, hnot, hcorr_name⟩ :=
      collectDirectiveNameLoop_prod sc.advance ⟨rest, sc.col + 1⟩ hcorr_pct ""
        (sc.inputEnd - sc.advance.offset) (Nat.le_of_eq (by rw [advance_inputEnd]))
    simp only [String.toList_empty, List.nil_append] at hname
    obtain ⟨sp_ws, h_ws, hcorr_ws⟩ := skipWhitespace_corr _ sp_name hcorr_name
    have hend_ws : (skipWhitespace (collectDirectiveNameLoop sc.advance "" (sc.inputEnd - sc.advance.offset)).snd).inputEnd
        = sc.inputEnd := by
      rw [skipWhitespace_inputEnd', collectDirectiveNameLoop_inputEnd, advance_inputEnd]
    have hws_toks : (skipWhitespace (collectDirectiveNameLoop sc.advance "" (sc.inputEnd - sc.advance.offset)).snd).tokens
        = sc.tokens := by
      rw [skipWhitespace_preserves_tokens, collectDirectiveNameLoop_preserves_tokens, advance_preserves_tokens]
    obtain ⟨tail, tcol⟩ := sp_name
    simp only at hchars hcol
    subst hchars
    split at hok
    · -- `%YAML`
      rename_i h_y
      have hnm : nm = ['Y', 'A', 'M', 'L'] := by
        have := congrArg String.toList (eq_of_beq h_y); rw [hname] at this; simpa using this
      subst hnm
      have hcol5 : tcol = sc.col + 5 := by simp at hcol; omega
      subst hcol5
      split at hok
      · rename_i s_yaml h_yaml_ok
        have h_eol := Except.ok.inj hok; subst h_eol
        obtain ⟨s₂, s₃, s₄, sp_v, hd1, hdot, hd2, h_wsv, hstop, hcorr_v⟩ :=
          scanYamlDirective_prod sc _ sp_ws hcorr_ws hend_ws _ s_yaml h_yaml_ok
        obtain ⟨sp', h_skip, hcorr'⟩ := skipToEndOfLine_corr _ sp_v hcorr_v
        obtain ⟨major, minor, htok⟩ := scanYamlDirective_new_token_eq sc _ _ s_yaml hws_toks h_yaml_ok
        have hnone : ∀ sp'' : SurfPos,
            declaredHandle (span ⟨'%' :: (['Y', 'A', 'M', 'L'] ++ tail), sc.col⟩ sp'') = none := by
          intro sp''
          unfold span
          apply declaredHandle_prefix_none
          intro c cs h _; simp at h
        refine ⟨sp', .yaml tail sc.col sp_ws s₂ s₃ s₄ sp' hnot h_ws hd1 hdot hd2 ⟨sp_v, h_wsv, hstop, h_skip⟩,
          hcorr', skipToEndOfLine_at_break_or_eof_chars _ sp' hcorr',
          [{ pos := sc.currentPos, val := .versionDirective major minor }], ?_, ?_, ?_⟩
        · rw [skipToEndOfLine_preserves_tokens, htok]; simp
        · intro p
          rw [goOut_silent _ rfl (by simp) (by intro h pfx; simp), goOut_nil, hnone]; rfl
        · intro sp'' _; rw [hnone, hnone]
      · simp at hok
    · rename_i h_y
      split at hok
      · -- `%TAG`
        rename_i h_t
        have hnm : nm = ['T', 'A', 'G'] := by
          have := congrArg String.toList (eq_of_beq h_t); rw [hname] at this; simpa using this
        subst hnm
        have hcol4 : tcol = sc.col + 4 := by simp at hcol; omega
        subst hcol4
        split at hok
        · rename_i s_tag h_tag_ok
          have h_eol := Except.ok.inj hok; subst h_eol
          obtain ⟨run, s₂, s₃, s₄, sp_v, handle, pfx, hchars_ws, hhd, hshaped, hrun, hstop2, h_hdl, h_hnot,
            h_ws2, h_pfx, h_wsv, hstop, hcorr_v, htok⟩ :=
            scanTagDirective_trace _ sp_ws hcorr_ws sc hend_ws _ s_tag h_tag_ok
          obtain ⟨sp', h_skip, hcorr'⟩ := skipToEndOfLine_corr _ sp_v hcorr_v
          obtain ⟨ws, htail, hws⟩ := gstar_sswhite_chars h_ws
          simp only at htail
          have hlen : sp'.chars.length ≤ s₂.chars.length :=
            Nat.le_trans (gstar_gchar_length h_skip) (Nat.le_trans (gstar_sswhite_length h_wsv)
              (Nat.le_trans (gstar_gchar_length h_pfx) (gstar_sswhite_length h_ws2)))
          -- the separation after `TAG` is non-empty: the handle starts with `!`, an ns-char
          have hrun_bang : ∃ r, run = '!' :: r := by
            rcases shaped_cases handle hshaped with h | h | ⟨w, _, _, h⟩ <;> rw [hhd] at h <;> exact ⟨_, h⟩
          obtain ⟨r, hr⟩ := hrun_bang
          cases ws with
          | nil =>
            exfalso
            have : tail = '!' :: (r ++ s₂.chars) := by rw [htail, hchars_ws, hr]; simp
            rw [this] at hnot
            exact gnot_gchar_head_not hnot (isNsChar_of_bool '!' (by decide))
          | cons c ws' =>
            have hc := white_cases c (hws c (by simp))
            have hsp : (⟨'%' :: (['T', 'A', 'G'] ++ tail), sc.col⟩ : SurfPos).chars =
                '%' :: 'T' :: 'A' :: 'G' :: c :: (ws' ++ run ++ s₂.chars) := by
              simp [htail, hchars_ws]
            have hws' : ∀ x ∈ ws', isWhiteSpaceBool x = true := fun x hx => hws x (by simp [hx])
            have hdecl : ∀ sp'' : SurfPos, sp''.chars.length ≤ s₂.chars.length →
                declaredHandle (span ⟨'%' :: (['T', 'A', 'G'] ++ tail), sc.col⟩ sp'') =
                  (if isNamedHandle handle then some handle else none) :=
              fun sp'' hl => declaredHandle_span_TAG _ sp'' c hc ws' run s₂.chars hsp hws' hrun hstop2
                handle hhd hshaped hl
            refine ⟨sp', .tag tail sc.col sp_ws s₂ s₃ s₄ sp' hnot h_ws h_hdl h_hnot h_ws2 h_pfx ⟨sp_v, h_wsv, hstop, h_skip⟩,
              hcorr', skipToEndOfLine_at_break_or_eof_chars _ sp' hcorr',
              [{ pos := sc.currentPos, val := .tagDirective handle pfx }], ?_, ?_, ?_⟩
            · rw [skipToEndOfLine_preserves_tokens, htok, hws_toks]; simp
            · intro p
              rw [goOut_tagDirective _ handle pfx rfl, goOut_nil, hdecl sp' hlen]
              split <;> simp
            · intro sp'' hl
              rw [hdecl sp'' (Nat.le_trans hl hlen), hdecl sp' hlen]
        · simp at hok
      · -- reserved
        rename_i h_t
        have h := Except.ok.inj hok; subst h
        obtain ⟨sp', h_skip, hcorr'⟩ := skipToEndOfLine_corr _ sp_ws hcorr_ws
        have hcol' : tcol = sc.col + 1 + nm.length := hcol
        subst hcol'
        have hnone : ∀ sp'' : SurfPos, declaredHandle (span ⟨'%' :: (nm ++ tail), sc.col⟩ sp'') = none := by
          intro sp''
          unfold span
          apply declaredHandle_prefix_none
          intro c cs h hw
          simp only [List.cons.injEq, true_and] at h
          have hcw : isWhiteSpaceBool c = true := by rcases hw with rfl | rfl <;> decide
          -- `nm` is the maximal ns-run after `%`: it must be exactly `TAG`, which the branch excluded
          have hTAG : nm = ['T', 'A', 'G'] := by
            rcases nm with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, nm'⟩⟩⟩⟩
            · exfalso
              simp only [List.nil_append] at h
              rw [h] at hnot
              exact gnot_gchar_head_not hnot (isNsChar_of_bool 'T' (by decide))
            · exfalso
              simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
              obtain ⟨rfl, h⟩ := h
              rw [h] at hnot
              exact gnot_gchar_head_not hnot (isNsChar_of_bool 'A' (by decide))
            · exfalso
              simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
              obtain ⟨rfl, rfl, h⟩ := h
              rw [h] at hnot
              exact gnot_gchar_head_not hnot (isNsChar_of_bool 'G' (by decide))
            · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
              obtain ⟨rfl, rfl, rfl, _⟩ := h
              rfl
            · exfalso
              simp only [List.cons_append, List.cons.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl, _⟩ := h
              exact not_isNsChar_of_white _ hcw (hall _ (by simp))
          apply h_t
          have : (collectDirectiveNameLoop sc.advance "" (sc.inputEnd - sc.advance.offset)).fst = "TAG" :=
            String.ext (by rw [hname, hTAG]; rfl)
          simp [this]
        refine ⟨sp', .reserved (nm ++ tail) sc.col ⟨tail, sc.col + 1 + nm.length⟩ sp'
          (gstar_gchar_of_all nm tail (sc.col + 1) hall) hnot ?_ ?_
          (GStar_trans (GStar_SSWhite_to_GStar_SCommentChar h_ws) h_skip),
          ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩,
          skipToEndOfLine_at_break_or_eof_chars _ sp' hcorr',
          [], ?_, ?_, ?_⟩
        · intro heq; apply h_y
          have hnm : nm = ['Y', 'A', 'M', 'L'] :=
            List.append_cancel_right (show nm ++ tail = ['Y', 'A', 'M', 'L'] ++ tail from heq)
          have : (collectDirectiveNameLoop sc.advance "" (sc.inputEnd - sc.advance.offset)).fst = "YAML" :=
            String.ext (by rw [hname, hnm]; rfl)
          simp [this]
        · intro heq; apply h_t
          have hnm : nm = ['T', 'A', 'G'] :=
            List.append_cancel_right (show nm ++ tail = ['T', 'A', 'G'] ++ tail from heq)
          have : (collectDirectiveNameLoop sc.advance "" (sc.inputEnd - sc.advance.offset)).fst = "TAG" :=
            String.ext (by rw [hname, hnm]; rfl)
          simp [this]
        · simp only [skipToEndOfLine_preserves_tokens, hws_toks, List.append_nil]
        · intro p; rw [goOut_nil, hnone]; rfl
        · intro sp'' _; rw [hnone, hnone]

end

end L4YAML.Proofs.Serialization.TraceOf.DocBridge
