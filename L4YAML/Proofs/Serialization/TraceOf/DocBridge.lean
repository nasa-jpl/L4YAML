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
        have := List.getLast?_eq_getLast (l := rest) hne
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
    simp only [List.length_append, List.length_cons, List.length_singleton, beq_self_eq_true,
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
      ScannerSurfCorr (collectTagHandleDirectiveLoop sc acc fuel).2 sp' := by
  induction fuel with
  | zero =>
    intro sc sp acc hcorr hfuel
    have hpeek := peek_none_of_fuel_zero hfuel
    have hnil := peek_none_chars_nil hcorr hpeek
    refine ⟨[], sp, by simp, by simp [collectTagHandleDirectiveLoop], rfl, ?_,
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
        obtain ⟨run, sp', hchars, hacc, hall, hstop, hcorr'⟩ :=
          ih sc.advance ⟨rest, sc.col + 1⟩ (acc.push c) hcorr_adv hfuel'
        refine ⟨c :: run, sp', ?_, ?_, ?_, hstop, hcorr'⟩
        · simp only at hchars; simp [hchars]
        · rw [hacc, String.toList_push]; simp
        · simp [hcond, hall]
      · rename_i hcond
        refine ⟨[], sp, by simp, by simp, rfl, ?_, hcorr⟩
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        intro c' hc'; simp only [List.head?_cons, Option.some.injEq] at hc'; subst hc'
        exact Bool.not_eq_true _ |>.mp hcond
    · rename_i hpeek
      have hnil := peek_none_chars_nil hcorr hpeek
      refine ⟨[], sp, by simp, by simp, rfl, ?_, hcorr⟩
      intro c hc; rw [hnil] at hc; simp at hc

end L4YAML.Proofs.Serialization.TraceOf.DocBridge
