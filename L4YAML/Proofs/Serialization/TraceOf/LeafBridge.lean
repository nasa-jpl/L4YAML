/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import L4YAML.Proofs.Serialization.TraceOf.Leaves
public import L4YAML.Proofs.Serialization.TokenEvents
public import L4YAML.Proofs.Production.NodeProduction
public import L4YAML.Proofs.Scanner.TagShape
public import L4YAML.Proofs.Production.Acceptance.Quoted
public meta import L4YAML.Proofs.Serialization.TraceOf.Leaves
public meta import L4YAML.Proofs.Production.StructureProduction
/-!
# S3 slice (1) — the leaf bridge (EVENTSOF §10, capstone 7.7 `parse_iff_grammar`)

The scanner's `.anchor name` / `.alias name` / `.tag handle suffix` tokens against the annotated leaf
relations of `TraceOf/Leaves.lean`: the lexeme the scanner consumed is a derivation of the leaf relation
whose trace is exactly `TokenEvents.tokenEvent` of the emitted token.  The surface derivation is the
`*_prod` lemmas' (`StructureProduction`/`NodeProduction`); what is new is the payload: the anchor name IS
the consumed span (`collectAnchorNameLoop_chars`), and a tag's handle IS `handleOf` of its span, arm by arm.
Rule 2 first: Priority 100 (`Tests/AdversarialInstantiation.lean`).
-/
namespace L4YAML.Proofs.Serialization.TraceOf.LeafBridge
@[expose] public section
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents (tokenEvent)
open L4YAML.Proofs.Serialization.SourceEvents (isAnchorCharBool)
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.StructureProduction L4YAML.Proofs.ScalarProduction L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.NodeProduction L4YAML.Proofs.TagShape L4YAML.Proofs.Acceptance

/-- `collectAnchorNameLoop`'s acceptance test is `isAnchorCharBool`. -/
lemma loopCond_eq_isAnchorCharBool (c : Char) :
    (!isFlowIndicatorBool c && !isWhiteSpaceBool c && !isLineBreakBool c && isPrintableBool c && c != '\uFEFF')
      = isAnchorCharBool c := by
  unfold isAnchorCharBool
  cases isFlowIndicatorBool c <;> cases isWhiteSpaceBool c <;> cases isLineBreakBool c <;>
    cases isPrintableBool c <;> cases (c != '\uFEFF') <;> rfl

/-- The name `collectAnchorNameLoop` returns is its accumulator followed by exactly the characters it
consumed, every one an `isAnchorCharBool`. -/
lemma collectAnchorNameLoop_chars (fuel : Nat) : ∀ (sc : ScannerState) (sp : SurfPos) (acc : String),
    ScannerSurfCorr sc sp → sc.inputEnd - sc.offset ≤ fuel →
    ∃ sp', ScannerSurfCorr (collectAnchorNameLoop sc acc fuel).2 sp' ∧
      (collectAnchorNameLoop sc acc fuel).1.toList = acc.toList ++ span sp sp' ∧
      (span sp sp').all isAnchorCharBool = true ∧ sp'.chars.length ≤ sp.chars.length := by
  induction fuel with
  | zero =>
    intro sc sp acc hcorr _
    exact ⟨sp, by simpa [collectAnchorNameLoop] using hcorr, by simp [collectAnchorNameLoop, span], by simp [span], Nat.le_refl _⟩
  | succ fuel' ih =>
    intro sc sp acc hcorr hfuel
    unfold collectAnchorNameLoop; split
    · rename_i c hpeek; split
      · rename_i hcond
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have hmore := peek_some_has_more hpeek
        have hlb : isLineBreakBool c = false :=
          bool_not_true_imp_false
            (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcond).1).1).2
        have hne_nl : c ≠ '\n' := by intro heq; rw [heq] at hlb; exact absurd hlb (by native_decide)
        have hne_cr : c ≠ '\r' := by intro heq; rw [heq] at hlb; exact absurd hlb (by native_decide)
        have hcorr_adv := advance_non_newline_corr sc c rest hcorr hmore hne_nl hne_cr
        have hfuel' : sc.advance.inputEnd - sc.advance.offset ≤ fuel' := by
          have h1 := ScannerProgress.advance_offset_lt sc hmore
          have h2 : sc.advance.inputEnd = sc.inputEnd := advance_inputEnd sc
          omega
        obtain ⟨sp', hcorr', hname, hall, hlen0⟩ := ih sc.advance ⟨rest, sc.col + 1⟩ (acc.push c) hcorr_adv hfuel'
        have hlen : sp'.chars.length ≤ rest.length := hlen0
        refine ⟨sp', hcorr', ?_, ?_, by simp only [List.length_cons]; omega⟩
        · rw [hname, String.toList_push]
          simp only [span, List.length_cons]
          rw [show (rest.length + 1 - sp'.chars.length) = (rest.length - sp'.chars.length) + 1 by omega]
          simp
        · have hc : isAnchorCharBool c = true := by rw [← loopCond_eq_isAnchorCharBool]; exact hcond
          simp only [span, List.length_cons] at hall ⊢
          rw [show (rest.length + 1 - sp'.chars.length) = (rest.length - sp'.chars.length) + 1 by omega]
          simp [hc, hall]
      · exact ⟨sp, hcorr, by simp [span], by simp [span], Nat.le_refl _⟩
    · exact ⟨sp, hcorr, by simp [span], by simp [span], Nat.le_refl _⟩

/-- A list all of whose members pass `p` is its own `takeWhile p`. -/
lemma takeWhile_all (p : Char → Bool) : ∀ (L : List Char), L.all p = true → L.takeWhile p = L
  | [], _ => rfl
  | c :: cs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [List.takeWhile_cons, h.1, takeWhile_all p cs h.2]

/-- `anchorEvents` on a `&`-led span whose tail is all anchor chars names exactly that tail. -/
lemma anchorEvents_span (L : List Char) (h : L.all isAnchorCharBool = true) :
    anchorEvents ('&' :: L) = [.defineAnchor (String.ofList L)] := by
  simp [anchorEvents, takeWhile_all _ L h]

lemma aliasEvents_span (L : List Char) (h : L.all isAnchorCharBool = true) :
    aliasEvents ('*' :: L) = [.useAlias (String.ofList L)] := by
  simp [aliasEvents, takeWhile_all _ L h]

/-- `collectAnchorNameLoop` emits nothing. -/
lemma collectAnchorNameLoop_tokens (fuel : Nat) : ∀ (sc : ScannerState) (acc : String),
    (collectAnchorNameLoop sc acc fuel).2.tokens = sc.tokens := by
  induction fuel with
  | zero => intro sc acc; rfl
  | succ n ih =>
    intro sc acc
    unfold collectAnchorNameLoop; split
    · split
      · rw [ih]; exact (keeps_advance sc).1
      · rfl
    · rfl

/-- `span` through a one-character step. -/
lemma span_cons (c : Char) (rest : List Char) (col col' : Nat) (sp' : SurfPos)
    (h : sp'.chars.length ≤ rest.length) :
    span ⟨c :: rest, col⟩ sp' = c :: span ⟨rest, col'⟩ sp' := by
  simp only [span, List.length_cons]
  rw [show rest.length + 1 - sp'.chars.length = (rest.length - sp'.chars.length) + 1 by omega]
  simp

/-- The anchor / alias leaf twin: a scanned `&name` / `*name` is the annotated leaf relation on its span,
with the trace `tokenEvent` gives the token. -/
lemma scanAnchorOrAlias_trace (sc : ScannerState) (sp : SurfPos) (isAnchor : Bool)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some (if isAnchor then '&' else '*'))
    (s' : ScannerState) (hok : scanAnchorOrAlias sc isAnchor = .ok s') :
    ∃ sp' name, s'.tokens = sc.tokens.push (Positioned.mk sc.currentPos (if isAnchor then .anchor name else .alias name) sc.currentPos) ∧
      ScannerSurfCorr s' sp' ∧
      (isAnchor = true → TCNsAnchorProperty sp sp' [.defineAnchor name]) ∧
      (isAnchor = false → TCNsAliasNode sp sp' [.useAlias name]) := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  have hcorr_adv := advance_non_newline_corr sc _ rest hcorr hmore
    (by cases isAnchor <;> decide) (by cases isAnchor <;> decide)
  obtain ⟨sp', hcorr', hname, hall, hlen⟩ :=
    collectAnchorNameLoop_chars (sc.inputEnd - sc.advance.offset) sc.advance ⟨rest, sc.col + 1⟩ ""
      hcorr_adv (by rw [advance_inputEnd sc]; exact Nat.le_refl _)
  obtain ⟨sp_mid, sp'', h_glit, h_gstar, h_ne, h_not, hcorr''⟩ :=
    scanAnchorOrAlias_prod sc _ hcorr isAnchor _ hpeek (by cases isAnchor <;> decide)
      (by cases isAnchor <;> decide) s' hok
  -- the token and the end state, by unfolding
  unfold scanAnchorOrAlias at hok
  dsimp only at hok
  split at hok
  · exact absurd hok (by simp)
  · rename_i hne
    have hs' := Except.ok.inj hok
    subst hs'
    have hlen' : sp'.chars.length ≤ rest.length := hlen
    have hname' : (collectAnchorNameLoop sc.advance "" (sc.inputEnd - sc.advance.offset)).1 =
        String.ofList (span ⟨rest, sc.col + 1⟩ sp') := by
      apply String.ext; simpa using hname
    have hcorr_s' : ScannerSurfCorr
        { (collectAnchorNameLoop sc.advance "" (sc.inputEnd - sc.advance.offset)).2.emitAt sc.currentPos
            (if isAnchor then .anchor (collectAnchorNameLoop sc.advance "" (sc.inputEnd - sc.advance.offset)).1
             else .alias (collectAnchorNameLoop sc.advance "" (sc.inputEnd - sc.advance.offset)).1)
          with simpleKeyAllowed := false } sp' :=
      ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩
    have hsp_eq : sp'' = sp' := ScannerSurfCorr_unique hcorr'' hcorr_s'
    rw [hsp_eq] at h_gstar h_ne h_not
    cases h_glit with
    | mk _ _ =>
      refine ⟨sp', (collectAnchorNameLoop sc.advance "" (sc.inputEnd - sc.advance.offset)).1,
        ?_, hcorr_s', ?_, ?_⟩
      · cases isAnchor <;> simp only [ScannerState.emitAt, collectAnchorNameLoop_tokens, (keeps_advance sc).1, ite_true, ite_false, Bool.false_eq_true]
      · intro hA; subst hA
        refine ⟨anchorProp_of_glit_gplus (GStar_to_GPlus h_gstar h_ne) h_not, ?_⟩
        simp only [ite_true]
        rw [hname', span_cons '&' rest sc.col (sc.col + 1) sp' hlen', anchorEvents_span _ hall]
      · intro hA; subst hA
        refine ⟨aliasNode_of_glit_gplus (GStar_to_GPlus h_gstar h_ne) h_not, ?_⟩
        simp only [Bool.false_eq_true, ite_false]
        rw [hname', span_cons '*' rest sc.col (sc.col + 1) sp' hlen', aliasEvents_span _ hall]

/-! ### The tag handle, arm by arm: `handleOf` of the lexeme's span is the handle the scanner emits -/

open L4YAML.Proofs.Serialization.SourceEvents in
/-- `spanWhile p` on a list whose prefix `w` passes `p` and whose next char fails it splits exactly there. -/
lemma spanWhile_prefix (p : Char → Bool) : ∀ (w rest : List Char), w.all p = true →
    (∀ c, rest.head? = some c → p c = false) → spanWhile p (w ++ rest) = (w, rest)
  | [], rest, _, hstop => by
    cases rest with
    | nil => rfl
    | cons c cs => simp [spanWhile, hstop c rfl]
  | c :: cs, rest, h, hstop => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [spanWhile, h.1, spanWhile_prefix p cs rest h.2 hstop]

lemma tagEvents_verbatim (cs : List Char) : tagEvents ('!' :: '<' :: cs) = [] := by
  simp [tagEvents]

lemma handleOf_secondary (cs : List Char) : EventsOf.handleOf ('!' :: '!' :: cs) = "!!" := by
  simp [EventsOf.handleOf, SourceEvents.namedTagUseAt, SourceEvents.namedTagUseTail, SourceEvents.spanWhile,
    show isWordCharBool '!' = false by decide]

lemma handleOf_named (w cs : List Char) (hw : w.all isWordCharBool = true) (hne : w ≠ []) :
    EventsOf.handleOf ('!' :: (w ++ '!' :: cs)) = "!" ++ String.ofList w ++ "!" := by
  have hsplit := spanWhile_prefix isWordCharBool w ('!' :: cs) hw
    (fun c hc => by simp at hc; subst hc; decide)
  have htail : SourceEvents.namedTagUseTail (w ++ '!' :: cs) =
      some (.useTag ("!" ++ String.ofList w ++ "!"), cs) := by
    unfold SourceEvents.namedTagUseTail
    rw [hsplit]
    cases w with
    | nil => exact absurd rfl hne
    | cons a as => rfl
  simp [EventsOf.handleOf, SourceEvents.namedTagUseAt, htail]

lemma handleOf_primary (w cs : List Char) (hw : w.all isWordCharBool = true)
    (hstop : ∀ c, cs.head? = some c → isWordCharBool c = false ∧ c ≠ '!') :
    EventsOf.handleOf ('!' :: (w ++ cs)) = "!" := by
  have hsplit := spanWhile_prefix isWordCharBool w cs hw (fun c hc => (hstop c hc).1)
  have hbang : isWordCharBool '!' = false := by decide
  have htail : SourceEvents.namedTagUseTail (w ++ cs) = none := by
    unfold SourceEvents.namedTagUseTail
    rw [hsplit]
    cases w with
    | nil => cases cs <;> rfl
    | cons a as =>
      cases cs with
      | nil => rfl
      | cons c cs' =>
        have hc := (hstop c rfl).2
        simp only
        split <;> simp_all
  simp only [EventsOf.handleOf, SourceEvents.namedTagUseAt, htail]
  cases w with
  | nil =>
    cases cs with
    | nil => rfl
    | cons c cs' =>
      have hc := (hstop c rfl).2
      simp only [List.nil_append]
      split <;> simp_all
  | cons a as =>
    simp only [List.all_cons, Bool.and_eq_true] at hw
    simp only [List.cons_append]
    split <;> simp_all

/-- The tag loops emit nothing. -/
lemma collectTagHandleLoop_tokens (fuel : Nat) : ∀ (sc : ScannerState) (acc : String),
    (collectTagHandleLoop sc acc fuel).2.2.tokens = sc.tokens := by
  induction fuel with
  | zero => intro sc acc; rfl
  | succ n ih =>
    intro sc acc
    unfold collectTagHandleLoop; split
    · exact (keeps_advance sc).1
    · split
      · rw [ih]; exact (keeps_advance sc).1
      · rfl
    · rfl

lemma collectTagSuffixLoop_tokens (fuel : Nat) : ∀ (sc : ScannerState) (acc : String),
    (collectTagSuffixLoop sc acc fuel).2.tokens = sc.tokens := by
  induction fuel with
  | zero => intro sc acc; rfl
  | succ n ih =>
    intro sc acc
    unfold collectTagSuffixLoop; split
    · split
      · rw [ih]; exact (keeps_advance sc).1
      · rfl
    · rfl

/-! ### Spans of the tag loops, in the form `sp.chars = consumed ++ sp'.chars` -/

/-- `span` read off a decomposition of the start's characters. -/
lemma span_of_eq (sp sp' : SurfPos) (L : List Char) (h : sp.chars = L ++ sp'.chars) :
    span sp sp' = L := by
  rw [span, h]; simp

lemma ne_newline_of_bool {p : Char → Bool} (c : Char) (hc : p c = true)
    (hn : p '\n' = false) (hr : p '\r' = false) : c ≠ '\n' ∧ c ≠ '\r' :=
  ⟨fun h => by subst h; rw [hc] at hn; exact Bool.noConfusion hn,
   fun h => by subst h; rw [hc] at hr; exact Bool.noConfusion hr⟩

/-- A one-character step of a loop that advances over a non-newline `c`. -/
lemma step_corr (sc : ScannerState) (c : Char) (rest : List Char)
    (hcorr : ScannerSurfCorr sc ⟨c :: rest, sc.col⟩) (hpeek : sc.peek? = some c)
    (hnl : c ≠ '\n') (hcr : c ≠ '\r') :
    ScannerSurfCorr sc.advance ⟨rest, sc.col + 1⟩ :=
  advance_non_newline_corr sc c rest hcorr (peek_some_has_more hpeek) hnl hcr

/-- `collectTagSuffixLoop` consumes a prefix of the surface (its content is irrelevant here). -/
lemma collectTagSuffixLoop_span (fuel : Nat) : ∀ (sc : ScannerState) (sp : SurfPos) (acc : String),
    ScannerSurfCorr sc sp →
    ∃ sp' L, ScannerSurfCorr (collectTagSuffixLoop sc acc fuel).2 sp' ∧ sp.chars = L ++ sp'.chars := by
  induction fuel with
  | zero => intro sc sp acc hcorr; exact ⟨sp, [], hcorr, rfl⟩
  | succ n ih =>
    intro sc sp acc hcorr
    unfold collectTagSuffixLoop; split
    · rename_i c hpeek; split
      · rename_i hc
        obtain ⟨rest, hsp⟩ := peek_some_sp hcorr hpeek
        subst hsp
        obtain ⟨hnl, hcr⟩ := ne_newline_of_bool c hc (by decide) (by decide)
        obtain ⟨sp', L, hcorr', hL⟩ := ih sc.advance ⟨rest, sc.col + 1⟩ (acc.push c)
          (step_corr sc c rest hcorr hpeek hnl hcr)
        have hL' : rest = L ++ sp'.chars := hL
        exact ⟨sp', c :: L, hcorr', by simp [hL']⟩
      · exact ⟨sp, [], hcorr, rfl⟩
    · exact ⟨sp, [], hcorr, rfl⟩

/-- `collectVerbatimTagLoop` consumes a prefix of the surface. -/
lemma collectVerbatimTagLoop_span (fuel : Nat) : ∀ (sc : ScannerState) (sp : SurfPos) (acc : String),
    ScannerSurfCorr sc sp →
    ∃ sp' L, ScannerSurfCorr (collectVerbatimTagLoop sc acc fuel).2.2 sp' ∧ sp.chars = L ++ sp'.chars := by
  induction fuel with
  | zero => intro sc sp acc hcorr; exact ⟨sp, [], hcorr, rfl⟩
  | succ n ih =>
    intro sc sp acc hcorr
    unfold collectVerbatimTagLoop; split
    · rename_i hpeek
      obtain ⟨rest, hsp⟩ := peek_some_sp hcorr hpeek
      subst hsp
      exact ⟨⟨rest, sc.col + 1⟩, ['>'], step_corr sc '>' rest hcorr hpeek (by decide) (by decide), rfl⟩
    · rename_i c hne hpeek; split
      · rename_i hc
        obtain ⟨rest, hsp⟩ := peek_some_sp hcorr hpeek
        subst hsp
        obtain ⟨hnl, hcr⟩ := ne_newline_of_bool c hc (by decide) (by decide)
        obtain ⟨sp', L, hcorr', hL⟩ := ih sc.advance ⟨rest, sc.col + 1⟩ (acc.push c)
          (step_corr sc c rest hcorr hpeek hnl hcr)
        have hL' : rest = L ++ sp'.chars := hL
        exact ⟨sp', c :: L, hcorr', by simp [hL']⟩
      · exact ⟨sp, [], hcorr, rfl⟩
    · exact ⟨sp, [], hcorr, rfl⟩

lemma collectVerbatimTagLoop_tokens (fuel : Nat) : ∀ (sc : ScannerState) (acc : String),
    (collectVerbatimTagLoop sc acc fuel).2.2.tokens = sc.tokens := by
  induction fuel with
  | zero => intro sc acc; rfl
  | succ n ih =>
    intro sc acc
    unfold collectVerbatimTagLoop; split
    · exact (keeps_advance sc).1
    · split
      · rw [ih]; exact (keeps_advance sc).1
      · rfl
    · rfl

/-- `collectTagHandleLoop` with enough fuel: the handle chars it returns are exactly the word chars it
consumed; with the bang it also consumed the `!`; without, the next character is neither a word char
nor `!`. -/
lemma collectTagHandleLoop_span (fuel : Nat) : ∀ (sc : ScannerState) (sp : SurfPos) (acc : String),
    ScannerSurfCorr sc sp → sc.inputEnd - sc.offset ≤ fuel →
    ∃ sp' w, ScannerSurfCorr (collectTagHandleLoop sc acc fuel).2.2 sp' ∧
      (collectTagHandleLoop sc acc fuel).1.toList = acc.toList ++ w ∧
      w.all isWordCharBool = true ∧
      (((collectTagHandleLoop sc acc fuel).2.1 = true ∧ sp.chars = (w ++ ['!']) ++ sp'.chars) ∨
       ((collectTagHandleLoop sc acc fuel).2.1 = false ∧ sp.chars = w ++ sp'.chars ∧
         ∀ c, sp'.chars.head? = some c → isWordCharBool c = false ∧ c ≠ '!')) := by
  induction fuel with
  | zero =>
    intro sc sp acc hcorr hfuel
    have hnone : sc.peek? = none := peek_none_of_fuel_zero (by omega)
    have hnil : sp.chars = [] := peek_none_chars_nil hcorr hnone
    exact ⟨sp, [], hcorr, by simp [collectTagHandleLoop], rfl,
      Or.inr ⟨rfl, by simp, fun c hc => by rw [hnil] at hc; cases hc⟩⟩
  | succ n ih =>
    intro sc sp acc hcorr hfuel
    unfold collectTagHandleLoop; split
    · rename_i hpeek
      obtain ⟨rest, hsp⟩ := peek_some_sp hcorr hpeek
      subst hsp
      exact ⟨⟨rest, sc.col + 1⟩, [], step_corr sc '!' rest hcorr hpeek (by decide) (by decide),
        by simp, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · rename_i c hne hpeek; split
      · rename_i hc
        obtain ⟨rest, hsp⟩ := peek_some_sp hcorr hpeek
        subst hsp
        obtain ⟨hnl, hcr⟩ := ne_newline_of_bool c hc (by decide) (by decide)
        have hmore := peek_some_has_more hpeek
        have hfuel' : sc.advance.inputEnd - sc.advance.offset ≤ n := by
          have h1 := ScannerProgress.advance_offset_lt sc hmore
          have h2 : sc.advance.inputEnd = sc.inputEnd := advance_inputEnd sc
          omega
        obtain ⟨sp', w, hcorr', hw, hall, hshape⟩ := ih sc.advance ⟨rest, sc.col + 1⟩ (acc.push c)
          (step_corr sc c rest hcorr hpeek hnl hcr) hfuel'
        refine ⟨sp', c :: w, hcorr', by rw [hw, String.toList_push]; simp, by simp [hc, hall], ?_⟩
        rcases hshape with ⟨hb, hL⟩ | ⟨hb, hL, hstop⟩
        · have hL' : rest = (w ++ ['!']) ++ sp'.chars := hL
          exact Or.inl ⟨hb, by simp [hL']⟩
        · have hL' : rest = w ++ sp'.chars := hL
          exact Or.inr ⟨hb, by simp [hL'], hstop⟩
      · rename_i hc
        obtain ⟨rest, hsp⟩ := peek_some_sp hcorr hpeek
        subst hsp
        refine ⟨⟨c :: rest, sc.col⟩, [], hcorr, by simp, rfl, Or.inr ⟨rfl, rfl, ?_⟩⟩
        intro c' hc'; simp at hc'; subst hc'
        exact ⟨by simpa using hc, hne⟩
    · rename_i hpeek
      have hnil : sp.chars = [] := peek_none_chars_nil hcorr hpeek
      exact ⟨sp, [], hcorr, by simp, rfl, Or.inr ⟨rfl, by simp, fun c hc => by rw [hnil] at hc; cases hc⟩⟩

end

end L4YAML.Proofs.Serialization.TraceOf.LeafBridge
