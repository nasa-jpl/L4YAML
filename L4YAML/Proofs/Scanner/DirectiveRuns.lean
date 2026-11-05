/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.ScannerDirectivesPresent
public import L4YAML.Proofs.Scanner.ScannerAllowDirectives
public import L4YAML.Proofs.Scanner.ContentAllowDirectives
public import L4YAML.Proofs.Scanner.PreprocessIndentStable
public import L4YAML.Proofs.Scanner.IndentStackBase

@[expose] public section Blanket

/-! # Directive runs in scanner output (capstone 7.7, stream S3, obligation (b))

    A `%YAML`/`%TAG` token is only ever followed, in the non-placeholder
    token stream, by another directive token or by `.documentStart`.  The
    scanner enforces it through `directiveWithoutDocument`: once a directive
    is scanned `directivesPresent` goes up, and only `scanDocumentStart`
    brings it down again — every other path that could emit a token first
    refuses on the raised flag.

    The proof carries a fold over the RAW token list (placeholders included,
    they are transparent) and reads the flag back out of it. -/

namespace L4YAML.Proofs.DirectiveRuns

open L4YAML L4YAML.Scanner
open L4YAML.Proofs.ScannerCorrectness L4YAML.Proofs.ScannerCorrectness.ScanHelpers
open L4YAML.Proofs.FlowAdjacency
open L4YAML.Proofs.ScannerDirectivesPresent L4YAML.Proofs.ScannerAllowDirectives
open L4YAML.Proofs.PreprocessIndentStable L4YAML.Proofs.IndentStackBase
open L4YAML.Proofs.CloseStaleExplicitKey

/-- The two directive token kinds, on an optional token (so it matches both
    `ts[i]?` reads and plain tokens through `some`). -/
def isDirTok : Option YamlToken → Bool
  | some (.versionDirective ..) | some (.tagDirective ..) => true
  | _ => false

/-- One token of the directive-run fold.  `none` is the dead state (a
    directive run was closed by something other than a directive or `---`);
    `some o` says whether a run is open. -/
def dirStep (acc : Option Bool) (t : YamlToken) : Option Bool :=
  match acc, t with
  | none, _ => none
  | some _, .versionDirective .. => some true
  | some _, .tagDirective .. => some true
  | some o, .placeholder => some o
  | some _, .documentStart => some false
  | some true, _ => none
  | some false, _ => some false

/-- Fold from openness `o`. -/
def dirRun (o : Bool) (L : List YamlToken) : Option Bool := L.foldl dirStep (some o)

/-- The target shape, on a token list: every directive is followed by a
    directive or `.documentStart`. -/
def ClosedList (F : List YamlToken) : Prop :=
  ∀ i, isDirTok F[i]? = true → isDirTok F[i + 1]? = true ∨ F[i + 1]? = some .documentStart

def nonPh (t : YamlToken) : Bool := !(t matches .placeholder)

@[simp] lemma dirRun_nil (o : Bool) : dirRun o [] = some o := rfl

lemma dirStep_none (t : YamlToken) : dirStep none t = none := by cases t <;> rfl

@[simp] lemma foldl_dirStep_none (L : List YamlToken) : L.foldl dirStep none = none := by
  induction L with
  | nil => rfl
  | cons t L ih => simp [List.foldl, dirStep_none, ih]

@[simp] lemma dirRun_cons (o : Bool) (t : YamlToken) (L : List YamlToken) :
    dirRun o (t :: L) = (dirStep (some o) t).bind fun o' => dirRun o' L := by
  unfold dirRun
  cases t <;> cases o <;> simp [List.foldl, dirStep]

lemma dirRun_append (o : Bool) (A B : List YamlToken) :
    dirRun o (A ++ B) = (dirRun o A).bind fun o' => dirRun o' B := by
  induction A generalizing o with
  | nil => simp
  | cons t A ih =>
    simp only [List.cons_append, dirRun_cons]
    cases dirStep (some o) t with
    | none => rfl
    | some o' => simp [ih]

lemma dirRun_none_bind (L : List YamlToken) :
    (none : Option Bool).bind (fun o' => dirRun o' L) = none := rfl

/-- The invariant is read on the raw list; this converts it to the shape on
    the placeholder-free list.  A closed fold (`some false`) gives a closed
    list, and starting open forces the filtered list to open with a
    directive or `---`. -/
lemma dirRun_false_closed (o : Bool) (L : List YamlToken)
    (h : dirRun o L = some false) :
    ClosedList (L.filter nonPh) ∧
      (o = true → ∃ h' R, L.filter nonPh = h' :: R ∧
        (isDirTok (some h') = true ∨ h' = .documentStart)) := by
  induction L generalizing o with
  | nil =>
    simp only [dirRun_nil, Option.some.injEq] at h
    subst h
    refine ⟨fun i hi => ?_, fun hc => by cases hc⟩
    simp [isDirTok] at hi
  | cons t L ih =>
    rw [dirRun_cons] at h
    cases t with
    | placeholder =>
      have h' : dirRun o L = some false := by
        cases o <;> simpa [dirStep] using h
      obtain ⟨hc, hh⟩ := ih o h'
      refine ⟨by simpa [List.filter, nonPh] using hc, fun ho => ?_⟩
      simpa [List.filter, nonPh] using hh ho
    | versionDirective a b =>
      have h' : dirRun true L = some false := by cases o <;> simpa [dirStep] using h
      obtain ⟨hc, hh⟩ := ih true h'
      obtain ⟨hd, R, hF, hhd⟩ := hh rfl
      refine ⟨fun i hi => ?_, fun _ => ⟨.versionDirective a b, L.filter nonPh,
        by simp [List.filter, nonPh], Or.inl (by simp [isDirTok])⟩⟩
      simp only [List.filter, nonPh] at hi ⊢
      simp only [Bool.not_false] at hi ⊢
      cases i with
      | zero => simp [hF]; rcases hhd with hd' | hd' <;> simp_all [isDirTok]
      | succ i => exact hc i hi
    | tagDirective a b =>
      have h' : dirRun true L = some false := by cases o <;> simpa [dirStep] using h
      obtain ⟨hc, hh⟩ := ih true h'
      obtain ⟨hd, R, hF, hhd⟩ := hh rfl
      refine ⟨fun i hi => ?_, fun _ => ⟨.tagDirective a b, L.filter nonPh,
        by simp [List.filter, nonPh], Or.inl (by simp [isDirTok])⟩⟩
      simp only [List.filter, nonPh] at hi ⊢
      simp only [Bool.not_false] at hi ⊢
      cases i with
      | zero => simp [hF]; rcases hhd with hd' | hd' <;> simp_all [isDirTok]
      | succ i => exact hc i hi
    | documentStart =>
      have h' : dirRun false L = some false := by cases o <;> simpa [dirStep] using h
      obtain ⟨hc, _⟩ := ih false h'
      refine ⟨fun i hi => ?_, fun _ => ⟨.documentStart, L.filter nonPh,
        by simp [List.filter, nonPh], Or.inr rfl⟩⟩
      simp only [List.filter, nonPh, Bool.not_false] at hi ⊢
      cases i with
      | zero => simp [isDirTok] at hi
      | succ i => exact hc i hi
    | _ =>
      cases o with
      | true => simp [dirStep] at h
      | false =>
        have h' : dirRun false L = some false := by simpa [dirStep] using h
        obtain ⟨hc, _⟩ := ih false h'
        refine ⟨fun i hi => ?_, fun hc => by cases hc⟩
        simp only [List.filter, nonPh, Bool.not_false] at hi ⊢
        cases i with
        | zero => simp [isDirTok] at hi
        | succ i => exact hc i hi

/-! ### Appends and in-place sets, on the raw list -/

lemma dirStep_false_nonDir (t : YamlToken) (ht : isDirTok (some t) = false) :
    dirStep (some false) t = some false := by
  cases t <;> simp_all [dirStep, isDirTok]

lemma dirStep_ph (o : Bool) : dirStep (some o) .placeholder = some o := by cases o <;> rfl

/-- A closed result from an open start is also reached from a closed start. -/
lemma dirRun_true_false (B : List YamlToken) (h : dirRun true B = some false) :
    dirRun false B = some false := by
  induction B with
  | nil => simp at h
  | cons t B ih =>
    rw [dirRun_cons] at h ⊢
    cases t <;> simp only [dirStep, Option.bind_some, Option.bind_none] at h ⊢ <;>
      first | exact h | exact ih h | cases h

lemma dirRun_append_nonDir (A M : List YamlToken) (hA : dirRun false A = some false)
    (hM : ∀ t ∈ M, isDirTok (some t) = false) :
    dirRun false (A ++ M) = some false := by
  rw [dirRun_append, hA, Option.bind_some]
  induction M with
  | nil => rfl
  | cons t M ih =>
    rw [dirRun_cons, dirStep_false_nonDir t (hM t (by simp)), Option.bind_some]
    exact ih fun u hu => hM u (by simp [hu])

lemma dirRun_ph_only (o : Bool) (M : List YamlToken) (hM : ∀ t ∈ M, t = .placeholder) :
    dirRun o M = some o := by
  induction M with
  | nil => rfl
  | cons t M ih =>
    rw [hM t (by simp), dirRun_cons, dirStep_ph, Option.bind_some]
    exact ih fun u hu => hM u (by simp [hu])

lemma dirRun_append_ph (o : Bool) (A M : List YamlToken) (hM : ∀ t ∈ M, t = .placeholder) :
    dirRun o (A ++ M) = dirRun o A := by
  rw [dirRun_append]
  cases dirRun o A with
  | none => rfl
  | some o' => simp [dirRun_ph_only o' M hM]

/-- Replacing position `j` by a non-directive token keeps every closed prefix
    closed, provided the prefix before `j` is itself closed. -/
lemma dirRun_set_closed : ∀ (L : List YamlToken) (j m : Nat) (y : YamlToken) (o : Bool),
    isDirTok (some y) = false →
    dirRun o (L.take j) = some false →
    dirRun o (L.take m) = some false →
    dirRun o ((L.set j y).take m) = some false := by
  intro L
  induction L with
  | nil => intro j m y o _ _ hm; simpa using hm
  | cons x L ih =>
    intro j m y o hy hj hm
    cases m with
    | zero => simpa using hm
    | succ m =>
      cases j with
      | zero =>
        simp only [List.take_zero, dirRun_nil, Option.some.injEq] at hj
        subst hj
        simp only [List.set_cons_zero, List.take_succ_cons, dirRun_cons] at hm ⊢
        rw [dirStep_false_nonDir y hy, Option.bind_some]
        cases x <;> simp only [dirStep, Option.bind_some] at hm <;>
          first | exact hm | exact dirRun_true_false _ hm | cases hm
      | succ j =>
        simp only [List.set_cons_succ, List.take_succ_cons, dirRun_cons] at hj hm ⊢
        cases hx : dirStep (some o) x with
        | none => rw [hx] at hj; cases hj
        | some o' =>
          rw [hx] at hj hm
          simp only [Option.bind_some] at hj hm ⊢
          exact ih j m y o' hy hj hm

lemma dirRun_take_length (o : Bool) (L : List YamlToken) :
    dirRun o (L.take L.length) = dirRun o L := by simp

lemma take_append_of_le {α : Type} (A M : List α) (k : Nat) (hk : k ≤ A.length) :
    (A ++ M).take k = A.take k := List.take_append_of_le_length hk

/-! ### Reading the fold off the scanner state -/

/-- Token values of a token array. -/
def toks (a : Array (Positioned YamlToken)) : List YamlToken := a.toList.map Positioned.val

/-- Token values of a scanner state. -/
def vals (s : ScannerState) : List YamlToken := toks s.tokens

@[simp] lemma toks_length (a : Array (Positioned YamlToken)) : (toks a).length = a.size := by
  simp [toks]

@[simp] lemma toks_push (a : Array (Positioned YamlToken)) (q : Positioned YamlToken) :
    toks (a.push q) = toks a ++ [q.val] := by simp [toks]

@[simp] lemma toks_setIfInBounds (a : Array (Positioned YamlToken)) (i : Nat)
    (q : Positioned YamlToken) : toks (a.setIfInBounds i q) = (toks a).set i q.val := by
  simp [toks, List.map_set]

lemma vals_emit (s : ScannerState) (t : YamlToken) : vals (s.emit t) = vals s ++ [t] := by
  simp [vals, ScannerState.emit]

lemma vals_emitAt (s : ScannerState) (p : YamlPos) (t : YamlToken) :
    vals (s.emitAt p t) = vals s ++ [t] := by
  simp [vals, ScannerState.emitAt]

/-- Nothing to unwind at any non-negative column: the indent stack is a lone
    sentinel, or its top is already at `-1`. -/
def Quiet (s : ScannerState) : Prop := s.indents.size ≤ 1 ∨ s.currentIndent ≤ -1

lemma Quiet_of_indents_eq {s t : ScannerState} (h : t.indents = s.indents) (hq : Quiet s) :
    Quiet t := by
  unfold Quiet ScannerState.currentIndent at hq ⊢
  rw [h]; exact hq

lemma unwindIndentsLoop_quiet_eq (s : ScannerState) (col : Int) (fuel : Nat)
    (hq : Quiet s) (hc : -1 ≤ col) : unwindIndentsLoop s col fuel = s := by
  cases fuel with
  | zero => simp only [unwindIndentsLoop]
  | succ f =>
    unfold unwindIndentsLoop
    have hcond : ¬ (s.currentIndent > col && s.indents.size > 1) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
      intro h1 h2
      rcases hq with hq | hq <;> omega
    simp [hcond]

lemma unwindIndents_quiet_eq (s : ScannerState) (col : Int) (hq : Quiet s) (hc : -1 ≤ col) :
    unwindIndents s col = s :=
  unwindIndentsLoop_quiet_eq s col _ hq hc

lemma unwindIndentsLoop_neg_one_quiet : ∀ (fuel : Nat) (s : ScannerState),
    s.indents.size ≤ fuel → Quiet (unwindIndentsLoop s (-1) fuel) := by
  intro fuel
  induction fuel with
  | zero => intro s hs; left; simp only [unwindIndentsLoop]; omega
  | succ f ih =>
    intro s hs
    unfold unwindIndentsLoop
    split
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      apply ih
      dsimp only
      simp only [ScannerState.emit, Array.size_pop]
      omega
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hcond
      unfold Quiet
      by_cases h1 : s.indents.size ≤ 1
      · exact Or.inl h1
      · right
        rcases Int.lt_or_le (-1) s.currentIndent with hgt | hle
        · exact absurd (by omega : s.indents.size > 1) (hcond hgt)
        · exact hle

lemma unwindIndents_neg_one_quiet (s : ScannerState) : Quiet (unwindIndents s (-1)) :=
  unwindIndentsLoop_neg_one_quiet _ _ (Nat.le_refl _)

lemma unwindIndentsLoop_vals : ∀ (fuel : Nat) (s : ScannerState) (col : Int),
    ∃ M, vals (unwindIndentsLoop s col fuel) = vals s ++ M ∧ ∀ t ∈ M, t = .blockEnd := by
  intro fuel
  induction fuel with
  | zero => intro s col; exact ⟨[], by simp [unwindIndentsLoop], by simp⟩
  | succ f ih =>
    intro s col
    unfold unwindIndentsLoop
    split
    · obtain ⟨M, hM, hall⟩ := ih _ col
      refine ⟨.blockEnd :: M, ?_, ?_⟩
      · rw [hM]; simp [vals, toks, ScannerState.emit]
      · intro t ht; simp at ht; rcases ht with rfl | ht; rfl; exact hall t ht
    · exact ⟨[], by simp, by simp⟩

lemma unwindIndents_vals (s : ScannerState) (col : Int) :
    ∃ M, vals (unwindIndents s col) = vals s ++ M ∧ ∀ t ∈ M, t = .blockEnd :=
  unwindIndentsLoop_vals _ s col

/-! ### The invariant -/

/-- Both prefixes a saved simple key can be rewritten at are closed. -/
def KeyOK (L : List YamlToken) (k : Nat) : Prop :=
  dirRun false (L.take k) = some false ∧ dirRun false (L.take (k + 1)) = some false

lemma KeyOK_append (L M : List YamlToken) (k : Nat) (hk : k + 1 ≤ L.length) (h : KeyOK L k) :
    KeyOK (L ++ M) k := by
  unfold KeyOK at h ⊢
  rw [take_append_of_le _ _ _ (by omega), take_append_of_le _ _ _ hk]
  exact h

lemma KeyOK_set (L : List YamlToken) (j : Nat) (y : YamlToken) (k : Nat)
    (hy : isDirTok (some y) = false) (hj : dirRun false (L.take j) = some false)
    (h : KeyOK L k) : KeyOK (L.set j y) k :=
  ⟨dirRun_set_closed L j k y false hy hj h.1, dirRun_set_closed L j (k + 1) y false hy hj h.2⟩

lemma KeyOK_of_closed (L : List YamlToken) (M : List YamlToken) (hM : ∀ t ∈ M, t = .placeholder)
    (h : dirRun false L = some false) : KeyOK (L ++ M) L.length := by
  unfold KeyOK
  constructor
  · rw [take_append_of_le L M L.length (Nat.le_refl _), List.take_length]; exact h
  · rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
    rw [dirRun_append_ph false L _ (fun t ht => hM t (List.mem_of_mem_take ht))]
    exact h

/-- The directive-run invariant on a scanner state. -/
structure DirInv (s : ScannerState) : Prop where
  ok : dirRun false (vals s) ≠ none
  flag : dirRun false (vals s) = some true → s.directivesPresent = true
  dpAD : s.directivesPresent = true → s.allowDirectives = true
  quiet : s.allowDirectives = true → Quiet s
  key : s.simpleKey.possible = true →
    KeyOK (vals s) s.simpleKey.tokenIndex ∨ s.directivesPresent = true
  stack : ∀ j (h : j < s.simpleKeyStack.size), s.simpleKeyStack[j].possible = true →
    KeyOK (vals s) s.simpleKeyStack[j].tokenIndex

lemma DirInv.closed {s : ScannerState} (hI : DirInv s) (hdp : s.directivesPresent = false) :
    dirRun false (vals s) = some false := by
  cases h : dirRun false (vals s) with
  | none => exact absurd h hI.ok
  | some b =>
    cases b with
    | true => exact absurd (hI.flag h) (by simp [hdp])
    | false => rfl

/-- The post-`directiveWithoutDocument`-check shape: the flag is down, so the
    fold is closed and only the key prefixes need re-establishing. -/
lemma DirInv.ofClosed (s2 : ScannerState)
    (hv : dirRun false (vals s2) = some false)
    (hdp : s2.directivesPresent = false) (had : s2.allowDirectives = false)
    (hkey : s2.simpleKey.possible = true → KeyOK (vals s2) s2.simpleKey.tokenIndex)
    (hstack : ∀ j (h : j < s2.simpleKeyStack.size), s2.simpleKeyStack[j].possible = true →
      KeyOK (vals s2) s2.simpleKeyStack[j].tokenIndex) : DirInv s2 where
  ok := by rw [hv]; simp
  flag := by rw [hv]; intro h; cases h
  dpAD := by rw [hdp]; intro h; cases h
  quiet := by rw [had]; intro h; cases h
  key := fun h => Or.inl (hkey h)
  stack := hstack

lemma vals_length (s : ScannerState) : (vals s).length = s.tokens.size := by simp [vals]

/-- Appending tokens that cannot open a run, with every field the invariant
    reads preserved except possibly a freshly saved key. -/
lemma DirInv.transport (s s2 : ScannerState) (M : List YamlToken)
    (hv : vals s2 = vals s ++ M)
    (hM : ∀ t ∈ M, isDirTok (some t) = false)
    (hopen : dirRun false (vals s) = some true → ∀ t ∈ M, t = .placeholder)
    (hdp : s2.directivesPresent = s.directivesPresent)
    (had : s2.allowDirectives = s.allowDirectives)
    (hind : s.allowDirectives = true → s2.indents = s.indents)
    (hstack : s2.simpleKeyStack = s.simpleKeyStack)
    (hkey : s2.simpleKey = s.simpleKey ∨ s2.simpleKey.possible = false ∨
      (s2.simpleKey.tokenIndex = s.tokens.size ∧ ∀ t ∈ M, t = .placeholder))
    (hA : AllKeysValid s) (hI : DirInv s) : DirInv s2 := by
  have hfold : dirRun false (vals s2) = dirRun false (vals s) ∨
      (dirRun false (vals s) = some false ∧ dirRun false (vals s2) = some false) := by
    cases h0 : dirRun false (vals s) with
    | none => exact absurd h0 hI.ok
    | some b =>
      cases b with
      | true => left; rw [hv, dirRun_append_ph false _ M (hopen h0), h0]
      | false => right; exact ⟨rfl, by rw [hv]; exact dirRun_append_nonDir _ _ h0 hM⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hfold with h | ⟨_, h⟩
    · rw [h]; exact hI.ok
    · rw [h]; simp
  · intro h
    rw [hdp]
    rcases hfold with h' | ⟨_, h'⟩
    · exact hI.flag (h' ▸ h)
    · rw [h'] at h; cases h
  · rw [hdp, had]; exact hI.dpAD
  · rw [had]; intro h; exact Quiet_of_indents_eq (hind h) (hI.quiet h)
  · intro hp
    rcases hkey with hk | hk | ⟨hk, hph⟩
    · rw [hk] at hp ⊢
      rcases hI.key hp with hK | hdp'
      · left; rw [hv]
        exact KeyOK_append _ _ _ (by have := (hA.1 hp).2.1; rw [vals_length]; omega) hK
      · right; rw [hdp]; exact hdp'
    · rw [hk] at hp; cases hp
    · rw [hk, hv]
      cases h0 : dirRun false (vals s) with
      | none => exact absurd h0 hI.ok
      | some b =>
        cases b with
        | true => right; rw [hdp]; exact hI.flag h0
        | false => left; rw [← vals_length]; exact KeyOK_of_closed _ _ hph h0
  · intro j hj hp
    have hj' : j < s.simpleKeyStack.size := hstack ▸ hj
    have he : s2.simpleKeyStack[j] = s.simpleKeyStack[j]'hj' := by simp [hstack]
    rw [he] at hp ⊢
    rw [hv]
    exact KeyOK_append _ _ _ (by have := (hA.2 j hj' hp).2.1; rw [vals_length]; omega)
      (hI.stack j hj' hp)

/-- Same tokens, same fields: the invariant transfers. -/
lemma DirInv.ofFields (s t : ScannerState) (ht : t.tokens = s.tokens)
    (hdp : t.directivesPresent = s.directivesPresent) (had : t.allowDirectives = s.allowDirectives)
    (hind : t.indents = s.indents) (hk : t.simpleKey = s.simpleKey ∨ t.simpleKey.possible = false)
    (hst : t.simpleKeyStack = s.simpleKeyStack) (hA : AllKeysValid s) (hI : DirInv s) : DirInv t :=
  DirInv.transport s t [] (by simp [vals, ht]) (by simp) (by simp) hdp had (fun _ => hind) hst
    (by rcases hk with hk | hk; exact Or.inl hk; exact Or.inr (Or.inl hk)) hA hI

/-! ### Preprocessing -/

lemma DirInv_skipToContent (s s1 : ScannerState) (h : skipToContent s = .ok s1)
    (hA : AllKeysValid s) (hI : DirInv s) : DirInv s1 :=
  DirInv.ofFields s s1 (skipToContent_preserves_tokens s s1 h)
    (skipToContent_preserves_directivesPresent s s1 h)
    (skipToContent_preserves_allowDirectives s s1 h)
    (skipToContent_preserves_indents s s1 h)
    (Or.inl (skipToContent_preserves_simpleKey s s1 h))
    (skipToContent_preserves_simpleKeyStack s s1 h) hA hI

/-- The preprocessing unwind at a non-negative column. -/
lemma DirInv_unwindIndents (s : ScannerState) (col : Int) (hc : -1 ≤ col)
    (hA : AllKeysValid s) (hI : DirInv s) : DirInv (unwindIndents s col) := by
  cases had : s.allowDirectives with
  | true => rw [unwindIndents_quiet_eq s col (hI.quiet had) hc]; exact hI
  | false =>
    obtain ⟨M, hM, hall⟩ := unwindIndents_vals s col
    have hdp : s.directivesPresent = false := by
      cases h : s.directivesPresent with
      | false => rfl
      | true => exact absurd (hI.dpAD h) (by simp [had])
    refine DirInv.transport s _ M hM (fun t ht => by rw [hall t ht]; rfl) ?_
      (unwindIndents_preserves_directivesPresent s col)
      (unwindIndents_preserves_allowDirectives s col) (fun h => by rw [had] at h; cases h)
      (unwindIndents_preserves_simpleKeyStack s col)
      (Or.inl (unwindIndents_preserves_simpleKey s col)) hA hI
    intro h; rw [hI.closed hdp] at h; cases h

lemma DirInv_needIndentCheck (s : ScannerState) (hA : AllKeysValid s) (hI : DirInv s) :
    DirInv { s with needIndentCheck := false } :=
  DirInv.ofFields s _ rfl rfl rfl rfl (Or.inl rfl) rfl hA hI

lemma DirInv_saveSimpleKey (s : ScannerState) (hA : AllKeysValid s) (hI : DirInv s) :
    DirInv (saveSimpleKey s) := by
  unfold saveSimpleKey
  split
  · exact hI
  · split
    · refine DirInv.transport s _ [.placeholder, .placeholder] ?_ ?_ ?_ rfl rfl (fun _ => rfl) rfl
        (Or.inr (Or.inr ⟨rfl, ?_⟩)) hA hI
      · simp [vals, toks]
      · intro t ht; simp at ht; rcases ht with rfl | rfl <;> rfl
      · intro _ t ht; simp at ht; rcases ht with rfl | rfl <;> rfl
      · intro t ht; simp at ht; rcases ht with rfl | rfl <;> rfl
    · exact hI

lemma DirInv_closeStaleExplicitKey (s : ScannerState) (hA : AllKeysValid s) (hI : DirInv s) :
    DirInv (closeStaleExplicitKey s) := by
  rcases closeStaleExplicitKey_cases s with h | ⟨c, _, h⟩
  · rw [h]; exact hI
  · rw [h]
    exact DirInv.ofFields s _ rfl rfl rfl rfl (Or.inl rfl) rfl hA hI

lemma skipToContent_preserves_AllKeysValid (s s' : ScannerState) (h : skipToContent s = .ok s')
    (hA : AllKeysValid s) : AllKeysValid s' :=
  ⟨skipToContent_preserves_SimpleKeyValid s s' h hA.1,
   skipToContent_preserves_SimpleKeyStackValid s s' h hA.2⟩

lemma unwindIndents_preserves_AllKeysValid (s : ScannerState) (col : Int)
    (hA : AllKeysValid s) : AllKeysValid (unwindIndents s col) :=
  ⟨unwindIndents_preserves_SimpleKeyValid s col hA.1,
   unwindIndents_preserves_SimpleKeyStackValid s col hA.2⟩

lemma saveSimpleKey_preserves_AllKeysValid (s : ScannerState) (hA : AllKeysValid s) :
    AllKeysValid (saveSimpleKey s) :=
  ⟨saveSimpleKey_preserves_SimpleKeyValid s hA.1, saveSimpleKey_preserves_SimpleKeyStackValid s hA.2⟩

lemma AllKeysValid_saveSimpleKey_closeStale (s : ScannerState) (hA : AllKeysValid s) :
    AllKeysValid (closeStaleExplicitKey (saveSimpleKey s)) :=
  ⟨closeStaleExplicitKey_preserves_SimpleKeyValid _ (saveSimpleKey_preserves_SimpleKeyValid _ hA.1),
   closeStaleExplicitKey_preserves_SimpleKeyStackValid _
     (saveSimpleKey_preserves_SimpleKeyStackValid _ hA.2)⟩

lemma DirInv_preprocess (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c)))
    (hA : AllKeysValid s) (hI : DirInv s) : DirInv s1 := by
  unfold scanNextToken_preprocess at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have hI1 := DirInv_skipToContent s s_skip h_skip hA hI
    have hA1 := skipToContent_preserves_AllKeysValid s s_skip h_skip hA
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            have hI2 := DirInv_needIndentCheck _
              (unwindIndents_preserves_AllKeysValid s_skip _ hA1)
              (DirInv_unwindIndents s_skip s_skip.col (by omega) hA1 hI1)
            have hA2 : AllKeysValid { unwindIndents s_skip s_skip.col with needIndentCheck := false } :=
              unwindIndents_preserves_AllKeysValid s_skip _ hA1
            exact DirInv_closeStaleExplicitKey _ (saveSimpleKey_preserves_AllKeysValid _ hA2)
              (DirInv_saveSimpleKey _ hA2 hI2)
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            exact DirInv_closeStaleExplicitKey _ (saveSimpleKey_preserves_AllKeysValid _ hA1)
              (DirInv_saveSimpleKey _ hA1 hI1)

/-! ### Directive-name loops leave `allowDirectives` alone -/

lemma collectDirectiveNameLoop_preserves_allowDirectives (s : ScannerState) (name : String)
    (fuel : Nat) : (collectDirectiveNameLoop s name fuel).snd.allowDirectives = s.allowDirectives := by
  induction fuel generalizing s name with
  | zero => unfold collectDirectiveNameLoop; rfl
  | succ fuel' ih =>
    unfold collectDirectiveNameLoop; split
    · split
      · rw [ih]; exact advance_preserves_allowDirectives s
      · rfl
    · rfl

lemma collectVersionMajorLoop_preserves_allowDirectives (s : ScannerState) (major : String)
    (fuel : Nat) : (collectVersionMajorLoop s major fuel).snd.allowDirectives = s.allowDirectives := by
  induction fuel generalizing s major with
  | zero => unfold collectVersionMajorLoop; rfl
  | succ fuel' ih =>
    unfold collectVersionMajorLoop; split
    · exact advance_preserves_allowDirectives s
    · split
      · rw [ih]; exact advance_preserves_allowDirectives s
      · rfl
    · rfl

lemma collectVersionMinorLoop_preserves_allowDirectives (s : ScannerState) (minor : String)
    (fuel : Nat) : (collectVersionMinorLoop s minor fuel).snd.allowDirectives = s.allowDirectives := by
  induction fuel generalizing s minor with
  | zero => unfold collectVersionMinorLoop; rfl
  | succ fuel' ih =>
    unfold collectVersionMinorLoop; split
    · split
      · rw [ih]; exact advance_preserves_allowDirectives s
      · rfl
    · rfl

lemma collectTagHandleDirectiveLoop_preserves_allowDirectives (s : ScannerState) (handle : String)
    (fuel : Nat) :
    (collectTagHandleDirectiveLoop s handle fuel).snd.allowDirectives = s.allowDirectives := by
  induction fuel generalizing s handle with
  | zero => unfold collectTagHandleDirectiveLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleDirectiveLoop; split
    · split
      · rw [ih]; exact advance_preserves_allowDirectives s
      · rfl
    · rfl

lemma collectTagPrefixLoop_preserves_allowDirectives (s : ScannerState) (pfx : String)
    (fuel : Nat) : (collectTagPrefixLoop s pfx fuel).snd.allowDirectives = s.allowDirectives := by
  induction fuel generalizing s pfx with
  | zero => unfold collectTagPrefixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagPrefixLoop; split
    · split
      · rw [ih]; exact advance_preserves_allowDirectives s
      · rfl
    · rfl

/-! ### Structural tokens -/

lemma dirStep_dir (o : Bool) (d : YamlToken) (hd : isDirTok (some d) = true) :
    dirStep (some o) d = some true := by
  cases d <;> simp_all [dirStep, isDirTok]

lemma dirRun_append_dir (A : List YamlToken) (d : YamlToken) (hd : isDirTok (some d) = true)
    (hA : dirRun false A ≠ none) : dirRun false (A ++ [d]) = some true := by
  rw [dirRun_append]
  cases h : dirRun false A with
  | none => exact absurd h hA
  | some o => simp [dirRun, dirStep_dir o d hd]

lemma dirRun_close (A M : List YamlToken) (hM : ∀ t ∈ M, t = .blockEnd)
    (h : dirRun false A = some false ∨ (dirRun false A = some true ∧ M = [])) :
    dirRun false (A ++ M ++ [.documentStart]) = some false := by
  rcases h with h | ⟨h, rfl⟩
  · have := dirRun_append_nonDir A M h (fun t ht => by rw [hM t ht]; rfl)
    rw [dirRun_append, this]; rfl
  · rw [List.append_nil, dirRun_append, h]; rfl

lemma scanDocumentStart_fields (s : ScannerState) :
    vals (scanDocumentStart s) = vals (unwindIndents s (-1)) ++ [.documentStart] ∧
    (scanDocumentStart s).directivesPresent = false ∧
    (scanDocumentStart s).allowDirectives = false ∧
    (scanDocumentStart s).simpleKey.possible = false ∧
    (scanDocumentStart s).simpleKeyStack = s.simpleKeyStack := by
  unfold scanDocumentStart
  refine ⟨?_, by simp, by simp, ?_, ?_⟩
  · simp [vals, toks, advanceN_preserves_tokens, ScannerState.emit]
  · simp [advanceN_preserves_simpleKey, ScannerState.emit]
  · simp [advanceN_preserves_simpleKeyStack, ScannerState.emit,
      unwindIndents_preserves_simpleKeyStack]

lemma DirInv_scanDocumentStart (s : ScannerState) (hA : AllKeysValid s) (hI : DirInv s) :
    DirInv (scanDocumentStart s) := by
  obtain ⟨hv, hdp, had, hk, hst⟩ := scanDocumentStart_fields s
  obtain ⟨M, hM, hall⟩ := unwindIndents_vals s (-1)
  have hv' : vals (scanDocumentStart s) = vals s ++ (M ++ [.documentStart]) := by
    rw [hv, hM, List.append_assoc]
  have hclosed : dirRun false (vals (scanDocumentStart s)) = some false := by
    rw [hv', ← List.append_assoc]
    apply dirRun_close _ _ hall
    cases h0 : dirRun false (vals s) with
    | none => exact absurd h0 hI.ok
    | some b =>
      cases b with
      | false => exact Or.inl rfl
      | true =>
        right
        refine ⟨rfl, ?_⟩
        have hq := hI.quiet (hI.dpAD (hI.flag h0))
        rw [unwindIndents_quiet_eq s (-1) hq (by omega)] at hM
        exact List.append_cancel_left (bs := M) (cs := []) (by rw [List.append_nil]; exact hM.symm)
  refine DirInv.ofClosed _ hclosed hdp had (fun h => by rw [hk] at h; cases h) ?_
  intro j hj hp
  have hj' : j < s.simpleKeyStack.size := hst ▸ hj
  have he : (scanDocumentStart s).simpleKeyStack[j] = s.simpleKeyStack[j]'hj' := by simp [hst]
  rw [he] at hp ⊢
  rw [hv']
  exact KeyOK_append _ _ _ (by have := (hA.2 j hj' hp).2.1; rw [vals_length]; omega)
    (hI.stack j hj' hp)

lemma scanDocumentEnd_ok_dp (s s' : ScannerState) (h : scanDocumentEnd s = .ok s') :
    s.directivesPresent = false := by
  unfold scanDocumentEnd at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i hn; simpa using hn

lemma scanDocumentEnd_fields (s s' : ScannerState) (h : scanDocumentEnd s = .ok s') :
    vals s' = vals (unwindIndents s (-1)) ++ [.documentEnd] ∧
    s'.directivesPresent = false ∧ s'.allowDirectives = true ∧
    s'.indents = (unwindIndents s (-1)).indents ∧
    s'.simpleKey.possible = false ∧ s'.simpleKeyStack = s.simpleKeyStack := by
  have hd := scanDocumentEnd_ok_dp s s' h
  unfold scanDocumentEnd at h
  simp only [hd, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [vals, toks, advanceN_preserves_tokens, ScannerState.emit,
    advanceN_preserves_indents, advanceN_preserves_simpleKeyStack, advanceN_preserves_simpleKey,
    unwindIndents_preserves_simpleKeyStack]

lemma DirInv_scanDocumentEnd (s s' : ScannerState) (h : scanDocumentEnd s = .ok s')
    (hA : AllKeysValid s) (hI : DirInv s) : DirInv s' := by
  have hd := scanDocumentEnd_ok_dp s s' h
  obtain ⟨hv, hdp, had, hind, hk, hst⟩ := scanDocumentEnd_fields s s' h
  obtain ⟨M, hM, hall⟩ := unwindIndents_vals s (-1)
  have hv' : vals s' = vals s ++ (M ++ [.documentEnd]) := by rw [hv, hM, List.append_assoc]
  have hclosed : dirRun false (vals s') = some false := by
    rw [hv']
    apply dirRun_append_nonDir _ _ (hI.closed hd)
    intro t ht
    simp at ht
    rcases ht with ht | rfl
    · rw [hall t ht]; rfl
    · rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hclosed]; simp
  · rw [hclosed]; intro h; cases h
  · intro _; exact had
  · intro _; exact Quiet_of_indents_eq hind (unwindIndents_neg_one_quiet s)
  · intro hp; rw [hk] at hp; cases hp
  · intro j hj hp
    have hj' : j < s.simpleKeyStack.size := hst ▸ hj
    have he : s'.simpleKeyStack[j] = s.simpleKeyStack[j]'hj' := by simp [hst]
    rw [he] at hp ⊢
    rw [hv']
    exact KeyOK_append _ _ _ (by have := (hA.2 j hj' hp).2.1; rw [vals_length]; omega)
      (hI.stack j hj' hp)

lemma scanDirective_fields (s s' : ScannerState) (h : scanDirective s = .ok s') :
    (vals s' = vals s ∨ ∃ d, vals s' = vals s ++ [d] ∧ isDirTok (some d) = true) ∧
    s'.directivesPresent = true ∧ s'.allowDirectives = s.allowDirectives := by
  unfold scanDirective at h
  split at h
  · contradiction
  · simp only [] at h
    split at h
    · split at h
      · rename_i s_inner h_inner
        have h_eq := Except.ok.inj h; subst h_eq
        simp only [vals, skipToEndOfLine_preserves_tokens, skipToEndOfLine_preserves_directivesPresent,
          skipToEndOfLine_preserves_allowDirectives]
        unfold scanYamlDirective at h_inner
        simp only [bind, Except.bind] at h_inner
        split at h_inner <;> try contradiction
        repeat (any_goals (split at h_inner))
        all_goals (try contradiction)
        all_goals (simp only [Except.ok.injEq] at h_inner; subst h_inner)
        all_goals refine ⟨?_, rfl, ?_⟩
        all_goals (try (simp [ScannerState.emitAt, skipWhitespace_preserves_allowDirectives,
          collectVersionMinorLoop_preserves_allowDirectives,
          collectVersionMajorLoop_preserves_allowDirectives,
          collectDirectiveNameLoop_preserves_allowDirectives,
          advance_preserves_allowDirectives]; done))
        all_goals (simp [toks, ScannerState.emitAt, skipWhitespace_preserves_tokens,
          collectVersionMinorLoop_preserves_tokens, collectVersionMajorLoop_preserves_tokens,
          collectDirectiveNameLoop_preserves_tokens, advance_preserves_tokens, isDirTok] <;>
          try exact Or.inr ⟨_, rfl, rfl⟩)
      · contradiction
    · split at h
      · split at h
        · rename_i s_inner h_inner
          have h_eq := Except.ok.inj h; subst h_eq
          simp only [vals, skipToEndOfLine_preserves_tokens,
            skipToEndOfLine_preserves_directivesPresent, skipToEndOfLine_preserves_allowDirectives]
          unfold scanTagDirective at h_inner
          dsimp only [] at h_inner
          simp only [bind, Except.bind] at h_inner
          split at h_inner
          · contradiction
          split at h_inner <;> try (split at h_inner <;> try contradiction)
          all_goals (try contradiction)
          all_goals (simp only [Except.ok.injEq] at h_inner; subst h_inner)
          all_goals refine ⟨?_, rfl, ?_⟩
          all_goals (try (simp [ScannerState.emitAt, collectTagPrefixLoop_preserves_allowDirectives,
            skipWhitespace_preserves_allowDirectives,
            collectTagHandleDirectiveLoop_preserves_allowDirectives,
            collectDirectiveNameLoop_preserves_allowDirectives,
            advance_preserves_allowDirectives]; done))
          all_goals (simp [toks, ScannerState.emitAt, collectTagPrefixLoop_preserves_tokens,
            skipWhitespace_preserves_tokens, collectTagHandleDirectiveLoop_preserves_tokens,
            collectDirectiveNameLoop_preserves_tokens, advance_preserves_tokens, isDirTok] <;>
            try exact Or.inr ⟨_, rfl, rfl⟩)
        · contradiction
      · simp only [Except.ok.injEq] at h; subst h
        refine ⟨Or.inl ?_, rfl, ?_⟩
        · simp [vals, skipToEndOfLine_preserves_tokens, skipWhitespace_preserves_tokens,
            collectDirectiveNameLoop_preserves_tokens, advance_preserves_tokens]
        · simp [skipToEndOfLine_preserves_allowDirectives, skipWhitespace_preserves_allowDirectives,
            collectDirectiveNameLoop_preserves_allowDirectives, advance_preserves_allowDirectives]

lemma DirInv_scanDirective (s s' : ScannerState) (h : scanDirective s = .ok s')
    (hA : AllKeysValid s) (hI : DirInv s) : DirInv s' := by
  obtain ⟨hv, hdp, had'⟩ := scanDirective_fields s s' h
  have had0 : s.allowDirectives = true := scanDirective_allowDirectives h
  have hq := hI.quiet had0
  have hind : s'.indents = s.indents := scanDirective_preserves_indents h
  have hst := scanDirective_preserves_simpleKeyStack s s' h
  have had : s'.allowDirectives = true := had'.trans had0
  refine ⟨?_, fun _ => hdp, fun _ => had, fun _ => Quiet_of_indents_eq hind hq,
    fun _ => Or.inr hdp, ?_⟩
  · rcases hv with hv | ⟨d, hv, hd⟩
    · rw [hv]; exact hI.ok
    · rw [hv, dirRun_append_dir _ _ hd hI.ok]; simp
  · intro j hj hp
    have hj' : j < s.simpleKeyStack.size := hst ▸ hj
    have he : s'.simpleKeyStack[j] = s.simpleKeyStack[j]'hj' := by simp [hst]
    rw [he] at hp ⊢
    rcases hv with hv | ⟨d, hv, _⟩
    · rw [hv]; exact hI.stack j hj' hp
    · rw [hv]
      exact KeyOK_append _ _ _ (by have := (hA.2 j hj' hp).2.1; rw [vals_length]; omega)
        (hI.stack j hj' hp)

lemma DirInv_dispatchStructural (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s'))
    (hA : AllKeysValid s) (hI : DirInv s) : DirInv s' := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact DirInv_scanDocumentStart s hA hI
    | exact DirInv_scanDocumentEnd _ _ (by assumption) hA hI
    | exact DirInv_scanDirective _ _ (by assumption) hA hI

/-! ### Content scanners push one non-directive token -/

/-- `s'` is `s` plus exactly one token, and that token is not a directive. -/
def PushNonDir (s s' : ScannerState) : Prop :=
  ∃ t, vals s' = vals s ++ [t] ∧ isDirTok (some t) = false

lemma PushNonDir.emitAt (s s0 : ScannerState) (p : YamlPos) (t : YamlToken)
    (h0 : s0.tokens = s.tokens) (ht : isDirTok (some t) = false) :
    PushNonDir s (s0.emitAt p t) :=
  ⟨t, by rw [vals_emitAt]; simp [vals, h0], ht⟩

lemma PushNonDir.ofEq {s s1 s' : ScannerState} (h : PushNonDir s1 s') (h1 : s1.tokens = s.tokens) :
    PushNonDir s s' := by
  obtain ⟨t, hv, ht⟩ := h
  exact ⟨t, by rw [hv]; simp [vals, h1], ht⟩

lemma PushNonDir.congr {s s' s'' : ScannerState} (h : PushNonDir s s') (h2 : s''.tokens = s'.tokens) :
    PushNonDir s s'' := by
  obtain ⟨t, hv, ht⟩ := h
  exact ⟨t, by rw [← hv]; simp [vals, h2], ht⟩

lemma scanAnchorOrAlias_pushNonDir (s : ScannerState) (isAnchor : Bool) (s' : ScannerState)
    (hok : scanAnchorOrAlias s isAnchor = .ok s') : PushNonDir s s' := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; try dsimp only []
    have h_collect :=
      collectAnchorNameLoop_preserves_tokens s.advance "" (s.inputEnd - s.advance.offset)
    have h_adv := advance_preserves_tokens s
    apply PushNonDir.emitAt _ _ _ _ (h_collect.trans h_adv)
    first | rfl | (cases isAnchor <;> rfl) | (cases isAnchor <;> simp [isDirTok])

lemma scanVerbatimTag_pushNonDir (s : ScannerState) (pos : YamlPos) (s' : ScannerState)
    (hok : scanVerbatimTag s pos = .ok s') : PushNonDir s s' := by
  unfold scanVerbatimTag at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      exact PushNonDir.emitAt _ _ _ _
        (by simp only [collectVerbatimTagLoop_preserves_tokens, advance_preserves_tokens]) rfl

lemma scanSecondaryTag_pushNonDir (s : ScannerState) (pos : YamlPos) :
    PushNonDir s (scanSecondaryTag s pos) := by
  unfold scanSecondaryTag
  exact PushNonDir.emitAt _ _ _ _
    (by simp only [collectTagSuffixLoop_preserves_tokens, advance_preserves_tokens]) rfl

lemma scanNamedTag_pushNonDir (s : ScannerState) (pos : YamlPos) (inputEnd : Nat) :
    PushNonDir s (scanNamedTag s pos inputEnd) := by
  unfold scanNamedTag; simp only []
  have h_handle := collectTagHandleLoop_preserves_tokens s "" (inputEnd - s.offset)
  split
  · exact PushNonDir.emitAt _ _ _ _ (by rw [collectTagSuffixLoop_preserves_tokens, h_handle]) rfl
  · exact PushNonDir.emitAt _ _ _ _ (by rw [collectTagSuffixLoop_preserves_tokens, h_handle]) rfl

lemma scanTag_pushNonDir (s s' : ScannerState) (hok : scanTag s = .ok s') : PushNonDir s s' := by
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok
      have h := Except.ok.inj hok; subst h; try dsimp only []
      exact (scanVerbatimTag_pushNonDir _ _ _ hv).ofEq (advance_preserves_tokens s)
  · have h := Except.ok.inj hok; subst h; try dsimp only []
    exact (scanSecondaryTag_pushNonDir _ _).ofEq (advance_preserves_tokens s)
  · have h := Except.ok.inj hok; subst h; try dsimp only []
    exact (scanNamedTag_pushNonDir _ _ _).ofEq (advance_preserves_tokens s)

lemma scanBlockScalarBody_pushNonDir (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos)
    (s' : ScannerState) (h_tok : s_nl.tokens = s_orig.tokens)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    PushNonDir s_orig s' := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; try dsimp only [])
  all_goals exact (PushNonDir.emitAt _ _ _ _
    (by rw [collectBlockScalarLoop_preserves_tokens, h_tok]) rfl).congr rfl

lemma scanBlockScalar_pushNonDir (s s' : ScannerState) (h : scanBlockScalar s = .ok s') :
    PushNonDir s s' := by
  unfold scanBlockScalar at h
  simp only [] at h
  split at h
  · contradiction
  · exact scanBlockScalarBody_pushNonDir s _ _ _ _ _ s'
      (by rw [scanBlockScalarConsumeNewline_preserves_tokens _ _ (by assumption),
              scanBlockScalarSkipComment_preserves_tokens,
              skipWhitespace_preserves_tokens,
              parseBlockHeaderLoop_preserves_tokens,
              advance_preserves_tokens]) h

lemma scanDoubleQuoted_pushNonDir (s s' : ScannerState) (h : scanDoubleQuoted s = .ok s') :
    PushNonDir s s' := by
  unfold scanDoubleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i heq
  have h_collect := collectDoubleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
  have h_adv := advance_preserves_tokens s
  split at h
  · split at h <;> try contradiction
    injection h with h_eq; subst h_eq
    exact PushNonDir.emitAt _ _ _ _ (h_collect.trans h_adv) rfl
  · injection h with h_eq; subst h_eq
    exact PushNonDir.emitAt _ _ _ _ (h_collect.trans h_adv) rfl

lemma scanSingleQuoted_pushNonDir (s s' : ScannerState) (h : scanSingleQuoted s = .ok s') :
    PushNonDir s s' := by
  unfold scanSingleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i heq
  have h_collect := collectSingleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
  have h_adv := advance_preserves_tokens s
  split at h
  · split at h <;> try contradiction
    injection h with h_eq; subst h_eq
    exact PushNonDir.emitAt _ _ _ _ (h_collect.trans h_adv) rfl
  · injection h with h_eq; subst h_eq
    exact PushNonDir.emitAt _ _ _ _ (h_collect.trans h_adv) rfl

lemma scanPlainScalar_pushNonDir (s s' : ScannerState) (h : scanPlainScalar s = .ok s') :
    PushNonDir s s' := by
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i heq
  have h_collect := collectPlainScalarLoop_preserves_tokens s "" "" _ _ _ _ _ heq
  injection h with h_eq; subst h_eq
  exact PushNonDir.emitAt _ _ _ _ h_collect rfl

/-! ### Post-check invariant: the directive run is already closed -/

/-- Token extension by non-directive tokens only. -/
def NonDirExt (a b : ScannerState) : Prop :=
  ∃ M, vals b = vals a ++ M ∧ ∀ t ∈ M, isDirTok (some t) = false

lemma NonDirExt.refl (a : ScannerState) : NonDirExt a a := ⟨[], by simp, by simp⟩

lemma NonDirExt.ofTokens {a b : ScannerState} (h : b.tokens = a.tokens) : NonDirExt a b :=
  ⟨[], by simp [vals, h], by simp⟩

lemma NonDirExt.congr {a b c : ScannerState} (h : NonDirExt a b) (h2 : c.tokens = b.tokens) :
    NonDirExt a c := by
  obtain ⟨M, hv, hM⟩ := h
  exact ⟨M, by rw [← hv]; simp [vals, h2], hM⟩

lemma NonDirExt.trans {a b c : ScannerState} (h1 : NonDirExt a b) (h2 : NonDirExt b c) :
    NonDirExt a c := by
  obtain ⟨M1, hv1, hM1⟩ := h1
  obtain ⟨M2, hv2, hM2⟩ := h2
  refine ⟨M1 ++ M2, by rw [hv2, hv1, List.append_assoc], ?_⟩
  intro t ht
  rcases List.mem_append.1 ht with ht | ht
  · exact hM1 t ht
  · exact hM2 t ht

lemma NonDirExt.emit (a : ScannerState) (t : YamlToken) (ht : isDirTok (some t) = false) :
    NonDirExt a (a.emit t) := ⟨[t], vals_emit a t, by simpa using ht⟩

lemma NonDirExt.ofPush {a b : ScannerState} (h : PushNonDir a b) : NonDirExt a b := by
  obtain ⟨t, hv, ht⟩ := h
  exact ⟨[t], hv, by simpa using ht⟩

/-- Every saved key on a stack has a closed prefix (both halves). -/
def StackOK (L : List YamlToken) (st : Array SimpleKeyState) : Prop :=
  ∀ j (h : j < st.size), st[j].possible = true → KeyOK L st[j].tokenIndex

structure PostInv (s : ScannerState) : Prop where
  closed : dirRun false (vals s) = some false
  key : s.simpleKey.possible = true → KeyOK (vals s) s.simpleKey.tokenIndex
  stack : StackOK (vals s) s.simpleKeyStack

lemma PostInv.ofDirInv (s : ScannerState) (hI : DirInv s) (hdp : s.directivesPresent = false) :
    PostInv s where
  closed := hI.closed hdp
  key := fun h => (hI.key h).resolve_right (by simp [hdp])
  stack := hI.stack

lemma DirInv.ofPost (s : ScannerState) (hP : PostInv s) (hdp : s.directivesPresent = false)
    (had : s.allowDirectives = false) : DirInv s where
  ok := by rw [hP.closed]; simp
  flag := by rw [hP.closed]; simp
  dpAD := by rw [hdp]; simp
  quiet := by rw [had]; simp
  key := fun h => Or.inl (hP.key h)
  stack := hP.stack

lemma stackLen_of_AllKeysValid (s : ScannerState) (hA : AllKeysValid s) :
    ∀ j (h : j < s.simpleKeyStack.size), s.simpleKeyStack[j].possible = true →
      s.simpleKeyStack[j].tokenIndex + 1 ≤ (vals s).length := by
  intro j hj hp
  have := (hA.2 j hj hp).2.1
  simp only [vals, toks_length]; omega

lemma keyLen_of_AllKeysValid (s : ScannerState) (hA : AllKeysValid s)
    (hp : s.simpleKey.possible = true) : s.simpleKey.tokenIndex + 1 ≤ (vals s).length := by
  have := (hA.1 hp).2.1
  simp only [vals, toks_length]; omega

/-- Every saved key on a stack sits strictly inside `L` (room for the key pair). -/
def StackLen (L : List YamlToken) (st : Array SimpleKeyState) : Prop :=
  ∀ j (h : j < st.size), st[j].possible = true → st[j].tokenIndex + 1 ≤ L.length

lemma StackLen.mono {L L' : List YamlToken} {st : Array SimpleKeyState} (h : StackLen L st)
    (hle : L.length ≤ L'.length) : StackLen L' st :=
  fun j hj hp => Nat.le_trans (h j hj hp) hle

lemma StackOK_append (L M : List YamlToken) (st : Array SimpleKeyState)
    (hlen : StackLen L st) (h : StackOK L st) : StackOK (L ++ M) st :=
  fun j hj hp => KeyOK_append L M _ (hlen j hj hp) (h j hj hp)

/-- The weakest key condition the transport needs. -/
def KeyTrans (s s2 : ScannerState) : Prop :=
  s2.simpleKey.possible = true →
    s.simpleKey.possible = true ∧ s2.simpleKey.tokenIndex = s.simpleKey.tokenIndex

lemma keyEq_ok {s s2 : ScannerState} (h : s2.simpleKey = s.simpleKey) : KeyTrans s s2 :=
  fun hp => by rw [h] at hp ⊢; exact ⟨hp, rfl⟩

lemma keyCleared_ok {s s2 : ScannerState} (h : s2.simpleKey.possible = false) : KeyTrans s s2 :=
  fun hp => by rw [h] at hp; cases hp

lemma KeyTrans_of {s s1 s2 : ScannerState} (h : s1.simpleKey = s.simpleKey)
    (hp : s2.simpleKey.possible = s1.simpleKey.possible)
    (hi : s2.simpleKey.tokenIndex = s1.simpleKey.tokenIndex) : KeyTrans s s2 := by
  intro hp2
  rw [← h, ← hp, ← hi]
  exact ⟨hp2, rfl⟩

lemma PostInv.transport (s s2 : ScannerState) (hE : NonDirExt s s2)
    (hstack : s2.simpleKeyStack = s.simpleKeyStack) (hkey : KeyTrans s s2)
    (hA : AllKeysValid s) (hP : PostInv s) : PostInv s2 := by
  obtain ⟨M, hv, hM⟩ := hE
  refine ⟨?_, ?_, ?_⟩
  · rw [hv]; exact dirRun_append_nonDir _ _ hP.closed hM
  · intro hp
    obtain ⟨hp0, hidx⟩ := hkey hp
    rw [hidx, hv]
    exact KeyOK_append _ _ _ (keyLen_of_AllKeysValid s hA hp0) (hP.key hp0)
  · rw [hstack, hv]
    exact StackOK_append _ _ _ (stackLen_of_AllKeysValid s hA) hP.stack

lemma PostInv.transportCleared (s s2 : ScannerState) (hE : NonDirExt s s2)
    (hstack : s2.simpleKeyStack = s.simpleKeyStack) (hk : s2.simpleKey.possible = false)
    (hlen : StackLen (vals s) s.simpleKeyStack) (hP : PostInv s) : PostInv s2 := by
  obtain ⟨M, hv, hM⟩ := hE
  refine ⟨?_, fun hp => (by rw [hk] at hp; cases hp), ?_⟩
  · rw [hv]; exact dirRun_append_nonDir _ _ hP.closed hM
  · rw [hstack, hv]; exact StackOK_append _ _ _ hlen hP.stack

lemma AllKeysValid_of_clear (s t : ScannerState) (ht : t.tokens = s.tokens)
    (hst : t.simpleKeyStack = s.simpleKeyStack) (hk : t.simpleKey.possible = false)
    (hA : AllKeysValid s) : AllKeysValid t := by
  refine ⟨fun hp => (by rw [hk] at hp; cases hp), ?_⟩
  unfold SimpleKeyStackValid
  simp only [hst, ht]
  exact hA.2

/-! ### Flow indicators -/

lemma PostInv_flowStart (s s' : ScannerState) (t : YamlToken) (ht : isDirTok (some t) = false)
    (hv : vals s' = vals s ++ [t]) (hk : s'.simpleKey.possible = false)
    (hst : s'.simpleKeyStack = s.simpleKeyStack.push s.simpleKey)
    (hA : AllKeysValid s) (hP : PostInv s) : PostInv s' := by
  refine ⟨?_, fun hp => (by rw [hk] at hp; cases hp), ?_⟩
  · rw [hv]; exact dirRun_append_nonDir _ _ hP.closed (by simpa using ht)
  · rw [hst, hv]
    intro j hj hp
    by_cases hlt : j < s.simpleKeyStack.size
    · simp only [Array.getElem_push, hlt, dite_true] at hp ⊢
      exact KeyOK_append _ _ _ (stackLen_of_AllKeysValid s hA j hlt hp) (hP.stack j hlt hp)
    · simp only [Array.getElem_push, hlt, dite_false] at hp ⊢
      exact KeyOK_append _ _ _ (keyLen_of_AllKeysValid s hA hp) (hP.key hp)

lemma PostInv_flowEnd (s s' : ScannerState) (t : YamlToken) (ht : isDirTok (some t) = false)
    (hv : vals s' = vals s ++ [t]) (hk : s'.simpleKey = s.simpleKeyStack.back?.getD {})
    (hst : s'.simpleKeyStack = s.simpleKeyStack.pop)
    (hA : AllKeysValid s) (hP : PostInv s) : PostInv s' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hv]; exact dirRun_append_nonDir _ _ hP.closed (by simpa using ht)
  · intro hp
    rw [hk] at hp ⊢
    cases hb : s.simpleKeyStack.back? with
    | none => rw [hb] at hp; simp at hp
    | some k =>
      rw [hb] at hp
      simp only [Option.getD_some] at hp ⊢
      simp only [Array.back?, Array.getElem?_eq_some_iff] at hb
      obtain ⟨hlt, hk'⟩ := hb
      rw [← hk'] at hp ⊢
      rw [hv]
      exact KeyOK_append _ _ _ (stackLen_of_AllKeysValid s hA _ hlt hp) (hP.stack _ hlt hp)
  · rw [hst, hv]
    intro j hj hp
    have hj' : j < s.simpleKeyStack.size := by simp at hj; omega
    simp only [Array.getElem_pop] at hp ⊢
    exact KeyOK_append _ _ _ (stackLen_of_AllKeysValid s hA j hj' hp) (hP.stack j hj' hp)

lemma scanFlowSequenceStart_vals (s : ScannerState) :
    vals (scanFlowSequenceStart s) = vals s ++ [.flowSequenceStart] := by
  simp [scanFlowSequenceStart, vals, toks, advance_preserves_tokens, ScannerState.emit]

lemma scanFlowMappingStart_vals (s : ScannerState) :
    vals (scanFlowMappingStart s) = vals s ++ [.flowMappingStart] := by
  simp [scanFlowMappingStart, vals, toks, advance_preserves_tokens, ScannerState.emit]

lemma scanFlowSequenceEnd_vals (s : ScannerState) :
    vals (scanFlowSequenceEnd s) = vals s ++ [.flowSequenceEnd] := by
  simp [scanFlowSequenceEnd, vals, toks, advance_preserves_tokens, ScannerState.emit]

lemma scanFlowMappingEnd_vals (s : ScannerState) :
    vals (scanFlowMappingEnd s) = vals s ++ [.flowMappingEnd] := by
  simp [scanFlowMappingEnd, vals, toks, advance_preserves_tokens, ScannerState.emit]

lemma scanFlowEntry_nonDirExt (s s' : ScannerState) (h : scanFlowEntry s = .ok s') :
    NonDirExt s s' := by
  unfold scanFlowEntry at h
  simp only [bind, Except.bind] at h
  repeat' (split at h)
  all_goals (first
    | contradiction
    | (injection h with h_eq; subst h_eq
       exact (NonDirExt.emit s .flowEntry rfl).congr (by simp [advance_preserves_tokens])))

lemma PostInv_dispatchFlow (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s'))
    (hA : AllKeysValid s) (hP : PostInv s) : PostInv s' := by
  unfold scanNextToken_dispatchFlowIndicators at h
  replace h := peel_flowAdj h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact PostInv_flowStart s _ _ rfl (scanFlowSequenceStart_vals s)
      (scanFlowSequenceStart_simpleKey_cleared s) (scanFlowSequenceStart_stack_pushed s) hA hP
  · split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
            exact PostInv_flowEnd s _ _ rfl (scanFlowSequenceEnd_vals s)
              (scanFlowSequenceEnd_simpleKey_restored s) (scanFlowSequenceEnd_stack_popped s) hA hP
    · split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact PostInv_flowStart s _ _ rfl (scanFlowMappingStart_vals s)
          (scanFlowMappingStart_simpleKey_cleared s) (scanFlowMappingStart_stack_pushed s) hA hP
      · split at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                exact PostInv_flowEnd s _ _ rfl (scanFlowMappingEnd_vals s)
                  (scanFlowMappingEnd_simpleKey_restored s) (scanFlowMappingEnd_stack_popped s)
                  hA hP
        · split at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · rename_i _ _ _ h_entry
                simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                exact PostInv.transport s _ (scanFlowEntry_nonDirExt s _ h_entry)
                  (scanFlowEntry_preserves_simpleKeyStack s _ h_entry)
                  (keyCleared_ok (scanFlowEntry_clears_simpleKey s _ h_entry)) hA hP
          · simp at h

/-! ### Block indicators -/

lemma pushSequenceIndent_nonDirExt (s : ScannerState) (col : Int) :
    NonDirExt s (pushSequenceIndent s col) := by
  unfold pushSequenceIndent
  split
  · exact (NonDirExt.emit s .blockSequenceStart rfl).congr rfl
  · exact NonDirExt.refl s

lemma pushMappingIndent_nonDirExt (s : ScannerState) (col : Int) :
    NonDirExt s (pushMappingIndent s col) := by
  unfold pushMappingIndent
  split
  · exact (NonDirExt.emit s .blockMappingStart rfl).congr rfl
  · exact NonDirExt.refl s

lemma pushSequenceIndent_ite_nonDirExt (s : ScannerState) (b : Bool) (col : Int) :
    NonDirExt s (if b then pushSequenceIndent s col else s) := by
  split
  · exact pushSequenceIndent_nonDirExt s col
  · exact NonDirExt.refl s

lemma pushMappingIndent_ite_nonDirExt (s : ScannerState) (b : Bool) (col : Int) :
    NonDirExt s (if b then pushMappingIndent s col else s) := by
  split
  · exact pushMappingIndent_nonDirExt s col
  · exact NonDirExt.refl s

lemma scanBlockEntry_tokens (s s' : ScannerState) (h : scanBlockEntry s = .ok s') :
    s'.tokens = ((if !s.inFlow then pushSequenceIndent s s.col else s).emit .blockEntry).tokens := by
  unfold scanBlockEntry at h
  simp only [bind, Except.bind] at h
  repeat' (split at h)
  all_goals (first
    | contradiction
    | (injection h with h_eq; subst h_eq
       simp_all [advance_preserves_tokens]))

lemma scanBlockEntry_nonDirExt (s s' : ScannerState) (h : scanBlockEntry s = .ok s') :
    NonDirExt s s' :=
  ((pushSequenceIndent_ite_nonDirExt s (!s.inFlow) s.col).trans
    (NonDirExt.emit _ .blockEntry rfl)).congr (scanBlockEntry_tokens s s' h)

lemma scanKey_tokens (s s' : ScannerState) (h : scanKey s = .ok s') :
    s'.tokens = ((if !s.inFlow then pushMappingIndent s s.col else s).emit .key).tokens := by
  unfold scanKey at h
  simp only [bind, Except.bind] at h
  repeat' (split at h)
  all_goals (first
    | contradiction
    | (injection h with h_eq; subst h_eq
       simp_all [advance_preserves_tokens]))

lemma scanKey_nonDirExt (s s' : ScannerState) (h : scanKey s = .ok s') :
    NonDirExt s s' :=
  ((pushMappingIndent_ite_nonDirExt s (!s.inFlow) s.col).trans
    (NonDirExt.emit _ .key rfl)).congr (scanKey_tokens s s' h)

lemma dirRun_set_full (L : List YamlToken) (j : Nat) (y : YamlToken)
    (hy : isDirTok (some y) = false) (hj : dirRun false (L.take j) = some false)
    (hL : dirRun false L = some false) : dirRun false (L.set j y) = some false := by
  have := dirRun_set_closed L j L.length y false hy hj (by simpa using hL)
  rwa [List.take_of_length_le (by simp)] at this

lemma KeyOK_set_one (L : List YamlToken) (idx : Nat) (y : YamlToken)
    (hy : isDirTok (some y) = false) (hk : KeyOK L idx) (hL : dirRun false L = some false) :
    dirRun false (L.set (idx + 1) y) = some false ∧
      ∀ k, KeyOK L k → KeyOK (L.set (idx + 1) y) k :=
  ⟨dirRun_set_full L (idx + 1) y hy hk.2 hL, fun k hkk => KeyOK_set L (idx + 1) y k hy hk.2 hkk⟩

lemma KeyOK_set_both (L : List YamlToken) (idx : Nat) (y1 y2 : YamlToken)
    (h1 : isDirTok (some y1) = false) (h2 : isDirTok (some y2) = false)
    (hk : KeyOK L idx) (hL : dirRun false L = some false) :
    dirRun false ((L.set idx y1).set (idx + 1) y2) = some false ∧
      ∀ k, KeyOK L k → KeyOK ((L.set idx y1).set (idx + 1) y2) k := by
  have hc1 := dirRun_set_full L idx y1 h1 hk.1 hL
  have hk1 : KeyOK (L.set idx y1) idx := KeyOK_set L idx y1 idx h1 hk.1 hk
  obtain ⟨hc2, hks⟩ := KeyOK_set_one (L.set idx y1) idx y2 h2 hk1 hc1
  exact ⟨hc2, fun k hkk => hks k (KeyOK_set L idx y1 k h1 hk.1 hkk)⟩

lemma PostInv_scanValuePrepare (s : ScannerState) (hA : AllKeysValid s) (hP : PostInv s) :
    PostInv (scanValuePrepare s) ∧ (scanValuePrepare s).simpleKey.possible = false ∧
      (scanValuePrepare s).simpleKeyStack = s.simpleKeyStack := by
  unfold scanValuePrepare
  split
  · rename_i hp
    have hk := hP.key hp
    split
    · split
      · obtain ⟨hc, hks⟩ := KeyOK_set_both (vals s) _ .blockMappingStart .key rfl rfl hk hP.closed
        refine ⟨⟨?_, by simp, ?_⟩, by simp, by simp⟩
        · show dirRun false (toks ((s.tokens.setIfInBounds _ _).setIfInBounds _ _)) = some false
          rw [toks_setIfInBounds, toks_setIfInBounds]; exact hc
        · show StackOK (toks ((s.tokens.setIfInBounds _ _).setIfInBounds _ _)) s.simpleKeyStack
          rw [toks_setIfInBounds, toks_setIfInBounds]
          exact fun j hj hp' => hks _ (hP.stack j hj hp')
      · obtain ⟨hc, hks⟩ := KeyOK_set_one (vals s) _ .key rfl hk hP.closed
        refine ⟨⟨?_, by simp, ?_⟩, by simp, by simp⟩
        · show dirRun false (toks (s.tokens.setIfInBounds _ _)) = some false
          rw [toks_setIfInBounds]; exact hc
        · show StackOK (toks (s.tokens.setIfInBounds _ _)) s.simpleKeyStack
          rw [toks_setIfInBounds]
          exact fun j hj hp' => hks _ (hP.stack j hj hp')
    · obtain ⟨hc, hks⟩ := KeyOK_set_one (vals s) _ .key rfl hk hP.closed
      refine ⟨⟨?_, by simp, ?_⟩, by simp, by simp⟩
      · show dirRun false (toks (s.tokens.setIfInBounds _ _)) = some false
        rw [toks_setIfInBounds]; exact hc
      · show StackOK (toks (s.tokens.setIfInBounds _ _)) s.simpleKeyStack
        rw [toks_setIfInBounds]
        exact fun j hj hp' => hks _ (hP.stack j hj hp')
  · rename_i hp
    split
    · exact ⟨PostInv.transport s _ (NonDirExt.ofTokens rfl) rfl (keyCleared_ok rfl) hA hP,
        rfl, rfl⟩
    · split
      · refine ⟨PostInv.transport s _ (pushMappingIndent_nonDirExt s s.col)
          (pushMappingIndent_preserves_simpleKeyStack s s.col)
          (keyEq_ok (pushMappingIndent_preserves_simpleKey s s.col)) hA hP, ?_,
          pushMappingIndent_preserves_simpleKeyStack s s.col⟩
        rw [pushMappingIndent_preserves_simpleKey]; simpa using hp
      · exact ⟨hP, by simpa using hp, rfl⟩

lemma scanValueClearKey_preserves_simpleKeyStack (s : ScannerState) :
    (scanValueClearKey s).simpleKeyStack = s.simpleKeyStack := by
  unfold scanValueClearKey
  repeat' split
  all_goals rfl

lemma scanValue_vals (s s' : ScannerState) (h : scanValue s = .ok s') :
    vals s' = vals (scanValuePrepare (scanValueClearKey s)) ++ [.value] := by
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  repeat' (split at h)
  all_goals (first
    | contradiction
    | (injection h with h_eq; subst h_eq
       simp [vals, toks, advance_preserves_tokens, ScannerState.emit]))

lemma PostInv_scanValue (s s' : ScannerState) (h : scanValue s = .ok s')
    (hA : AllKeysValid s) (hP : PostInv s) : PostInv s' := by
  have hkc := scanValueClearKey_identity_or_clear s
  have hA1 : AllKeysValid (scanValueClearKey s) := by
    rcases hkc with hkc | ⟨hk, ht⟩
    · rw [hkc]; exact hA
    · exact AllKeysValid_of_clear s _ ht (scanValueClearKey_preserves_simpleKeyStack s) hk hA
  have hP1 : PostInv (scanValueClearKey s) := by
    rcases hkc with hkc | ⟨hk, ht⟩
    · rw [hkc]; exact hP
    · exact PostInv.transport s _ (NonDirExt.ofTokens ht)
        (scanValueClearKey_preserves_simpleKeyStack s) (keyCleared_ok hk) hA hP
  obtain ⟨hP2, _, hst2⟩ := PostInv_scanValuePrepare _ hA1 hP1
  have hst1 := scanValueClearKey_preserves_simpleKeyStack s
  have hlen : StackLen (vals (scanValuePrepare (scanValueClearKey s)))
      (scanValuePrepare (scanValueClearKey s)).simpleKeyStack := by
    rw [hst2, hst1]
    refine StackLen.mono (L := vals s) (st := s.simpleKeyStack) (stackLen_of_AllKeysValid s hA) ?_
    simp only [vals, toks_length]
    have := scanValuePrepare_tokens_monotonic (scanValueClearKey s)
    rw [scanValueClearKey_preserves_tokens] at this
    omega
  refine PostInv.transportCleared _ s' ⟨[.value], scanValue_vals s s' h, by simp [isDirTok]⟩ ?_
    (scanValue_clears_simpleKey s s' h) hlen hP2
  rw [scanValue_preserves_simpleKeyStack s s' h, hst2, hst1]

lemma PostInv_dispatchBlock (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (hA : AllKeysValid s) (hP : PostInv s) : PostInv s' := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact PostInv.transport s _ (scanBlockEntry_nonDirExt s _ (by assumption))
        (scanBlockEntry_preserves_simpleKeyStack s _ (by assumption))
        (keyEq_ok (scanBlockEntry_preserves_simpleKey s _ (by assumption))) hA hP
    | exact PostInv.transport s _ (scanKey_nonDirExt s _ (by assumption))
        (scanKey_preserves_simpleKeyStack s _ (by assumption))
        (keyCleared_ok (scanKey_clears_simpleKey s _ (by assumption))) hA hP
    | exact PostInv_scanValue s _ (by assumption) hA hP

/-! ### Content -/

lemma dispatchContent_shape (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s') :
    NonDirExt s s' ∧ KeyTrans s s' := by
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
      exact ⟨(NonDirExt.ofPush (scanAnchorOrAlias_pushNonDir s true s_a h_fn)).congr rfl,
        keyEq_ok (scanAnchorOrAlias_preserves_simpleKey s true s_a h_fn)⟩
  · split at h
    · split at h
      · simp at h
      split at h
      · simp at h
      · exact ⟨NonDirExt.ofPush (scanAnchorOrAlias_pushNonDir s false _ (aliasArm_scan_ok h)),
          keyEq_ok (scanAnchorOrAlias_preserves_simpleKey s false _ (aliasArm_scan_ok h))⟩
    · split at h
      · split at h
        · simp at h
        generalize h_fn : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact ⟨NonDirExt.ofPush (scanTag_pushNonDir s s_t h_fn),
            keyEq_ok (scanTag_preserves_simpleKey s s_t h_fn)⟩
      · repeat (any_goals (split at h))
        any_goals contradiction
        all_goals (try simp only [Except.ok.injEq] at *)
        all_goals (try contradiction)
        all_goals (try subst_vars)
        all_goals first
          | exact ⟨NonDirExt.ofPush (scanBlockScalar_pushNonDir _ _ (by assumption)),
              keyCleared_ok (scanBlockScalar_clears_simpleKey _ _ (by assumption))⟩
          | exact ⟨NonDirExt.ofPush (scanPlainScalar_pushNonDir _ _ (by assumption)),
              keyEq_ok (scanPlainScalar_preserves_simpleKey _ _ (by assumption))⟩
          | exact ⟨NonDirExt.ofPush (scanDoubleQuoted_pushNonDir _ _ (by assumption)),
              keyEq_ok (scanDoubleQuoted_preserves_simpleKey _ _ (by assumption))⟩
          | exact ⟨NonDirExt.ofPush (scanSingleQuoted_pushNonDir _ _ (by assumption)),
              keyEq_ok (scanSingleQuoted_preserves_simpleKey _ _ (by assumption))⟩
          | exact ⟨(NonDirExt.ofPush (scanDoubleQuoted_pushNonDir _ _ (by assumption))).congr (by rfl),
              KeyTrans_of (scanDoubleQuoted_preserves_simpleKey _ _ (by assumption))
                (by simp_all) (by rfl)⟩
          | exact ⟨(NonDirExt.ofPush (scanSingleQuoted_pushNonDir _ _ (by assumption))).congr (by rfl),
              KeyTrans_of (scanSingleQuoted_preserves_simpleKey _ _ (by assumption))
                (by simp_all) (by rfl)⟩
          | (simp_all; done)

lemma PostInv_dispatchContent (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s')
    (hA : AllKeysValid s) (hP : PostInv s) : PostInv s' :=
  PostInv.transport s s' (dispatchContent_shape s c s' h).1
    (dispatchContent_preserves_simpleKeyStack s c s' h) (dispatchContent_shape s c s' h).2 hA hP

/-! ### One scanner step -/

lemma checkNoPendingDirectives_ok (s : ScannerState) (u : Unit)
    (h : scanNextToken_checkNoPendingDirectives s = .ok u) : s.directivesPresent = false := by
  unfold scanNextToken_checkNoPendingDirectives at h
  split at h
  · contradiction
  · rename_i hn; simpa using hn

lemma DirInv_scanNextToken (s s' : ScannerState) (hA : AllKeysValid s) (hI : DirInv s)
    (h : scanNextToken s = .ok (some s')) : DirInv s' := by
  unfold scanNextToken at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  rename_i s2 c h_pre
  have hA2 := preprocess_preserves_AllKeysValid s s2 c h_pre hA
  have hI2 := DirInv_preprocess s s2 c h_pre hA hI
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact DirInv_dispatchStructural s2 c _ (by assumption) hA2 hI2
  · split at h <;> (try (simp at h; done))
    rename_i u hchk
    have hdp2 := checkNoPendingDirectives_ok s2 u hchk
    have hP2 := PostInv.ofDirInv s2 hI2 hdp2
    split at h <;> (try (simp at h; done))
    have hA3 := allowDir_ite_preserves_AllKeysValid s2 hA2
    have hP3 : PostInv (if s2.allowDirectives = true then
        { s2 with allowDirectives := false, documentEverStarted := true } else s2) := by
      split
      · exact PostInv.transport s2 _ (NonDirExt.ofTokens rfl) rfl (keyEq_ok rfl) hA2 hP2
      · exact hP2
    have hdp3 : (if s2.allowDirectives = true then
        { s2 with allowDirectives := false, documentEverStarted := true } else s2).directivesPresent
          = false := by
      split <;> simpa using hdp2
    have had3 : (if s2.allowDirectives = true then
        { s2 with allowDirectives := false, documentEverStarted := true } else s2).allowDirectives
          = false := by
      split
      · rfl
      · rename_i hn; simpa using hn
    split at h <;> (try (simp at h; done))
    split at h
    · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
      refine DirInv.ofPost _ (PostInv_dispatchFlow _ c _ (by assumption) hA3 hP3) ?_ ?_
      · rw [dispatchFlowIndicators_preserves_directivesPresent (by assumption)]; split <;> simpa using hdp2
      · rw [dispatchFlowIndicators_preserves_allowDirectives (by assumption)]
        split
        · rfl
        · rename_i hn; simpa using hn
    · split at h <;> (try (simp at h; done))
      split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        refine DirInv.ofPost _ (PostInv_dispatchBlock _ c _ (by assumption) hA3 hP3) ?_ ?_
        · rw [dispatchBlockIndicators_preserves_directivesPresent (by assumption)]; split <;> simpa using hdp2
        · rw [dispatchBlockIndicators_preserves_allowDirectives (by assumption)]
          split
          · rfl
          · rename_i hn; simpa using hn
      · split at h <;> (try (simp at h; done))
        split at h <;> (try (simp at h; done))
        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        refine DirInv.ofPost _ (PostInv_dispatchContent _ c _ (by assumption) hA3 hP3) ?_ ?_
        · rw [dispatchContent_preserves_directivesPresent _ _ _ (by assumption)]; split <;> simpa using hdp2
        · rw [dispatchContent_preserves_allowDirectives _ _ _ (by assumption)]
          split
          · rfl
          · rename_i hn; simpa using hn

/-! ### The loop and the entry point -/

lemma DirInv_scanLoop : ∀ (fuel : Nat) (s : ScannerState) (ts : Array (Positioned YamlToken)),
    AllKeysValid s → DirInv s → scanLoop s fuel = .ok ts →
    dirRun false (toks ts) = some false := by
  intro fuel
  induction fuel with
  | zero => intro s ts _ _ h; simp [scanLoop] at h
  | succ n ih =>
    intro s ts hA hI h
    unfold scanLoop at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · rename_i hfl hdp
          split at h
          · contradiction
          · split at h
            · contradiction
            · simp only [Except.ok.injEq] at h; subst h
              have hc := hI.closed (by simpa using hdp)
              obtain ⟨M, hM, hall⟩ := unwindIndents_vals s (-1)
              show dirRun false (vals ((unwindIndents s (-1)).emit .streamEnd)) = some false
              rw [vals_emit, hM, List.append_assoc]
              refine dirRun_append_nonDir _ _ hc ?_
              intro t ht
              rcases List.mem_append.1 ht with ht | ht
              · rw [hall t ht]; rfl
              · simp at ht; subst ht; rfl
    · rename_i s' hs'
      exact ih s' ts (scanNextToken_preserves_AllKeysValid s s' hA hs')
        (DirInv_scanNextToken s s' hA hI hs') h

lemma DirInv_init (input : String) : DirInv ((ScannerState.mk' input).emit .streamStart) where
  ok := by simp [vals, toks, ScannerState.mk', ScannerState.emit, dirRun, dirStep]
  flag := by simp [vals, toks, ScannerState.mk', ScannerState.emit, dirRun, dirStep]
  dpAD := by simp [ScannerState.mk', ScannerState.emit]
  quiet := by intro _; left; simp [ScannerState.mk', ScannerState.emit]
  key := by intro h; simp [ScannerState.mk', ScannerState.emit] at h
  stack := by intro j hj; simp [ScannerState.mk', ScannerState.emit] at hj

lemma AllKeysValid_init (input : String) :
    AllKeysValid ((ScannerState.mk' input).emit .streamStart) := by
  constructor
  · intro h_poss; simp [ScannerState.mk', ScannerState.emit] at h_poss
  · intro j hj; simp [ScannerState.mk', ScannerState.emit] at hj

lemma consumeBOM_indents (s : ScannerState) : s.consumeBOM.indents = s.indents := by
  simp only [ScannerState.consumeBOM, ScannerState.advance]
  repeat' split
  all_goals rfl

lemma DirInv_consumeBOM (s : ScannerState) (hA : AllKeysValid s) (hI : DirInv s) :
    DirInv s.consumeBOM :=
  DirInv.ofFields s _ (consumeBOM_preserves_tokens s)
    (by simp [ScannerState.consumeBOM, advance_preserves_directivesPresent])
    (by simp [ScannerState.consumeBOM, advance_preserves_allowDirectives])
    (consumeBOM_indents s)
    (Or.inl (consumeBOM_preserves_simpleKey s)) (consumeBOM_preserves_simpleKeyStack s) hA hI

/-- Raw scanner output (placeholders included) has its directive run closed. -/
lemma scan_closed (input : String) (ts : Array (Positioned YamlToken)) (h : scan input = .ok ts) :
    dirRun false (toks ts) = some false := by
  unfold scan at h
  have hA0 := AllKeysValid_init input
  have hI0 := DirInv_init input
  have hA : AllKeysValid (match (ScannerState.mk' input).emit .streamStart |>.peek? with
      | some '\uFEFF' => ((ScannerState.mk' input).emit .streamStart).consumeBOM
      | _ => (ScannerState.mk' input).emit .streamStart) := by
    split
    · have h_tok := consumeBOM_preserves_tokens ((ScannerState.mk' input).emit .streamStart)
      exact AllKeysValid_mono _ _ hA0
        (consumeBOM_preserves_simpleKey _)
        (consumeBOM_preserves_simpleKeyStack _)
        (by simp [h_tok])
        (fun i hi => by simp [h_tok])
    · exact hA0
  have hI : DirInv (match (ScannerState.mk' input).emit .streamStart |>.peek? with
      | some '\uFEFF' => ((ScannerState.mk' input).emit .streamStart).consumeBOM
      | _ => (ScannerState.mk' input).emit .streamStart) := by
    split
    · exact DirInv_consumeBOM _ hA0 hI0
    · exact hI0
  exact DirInv_scanLoop _ _ ts hA hI h

lemma toks_filter (ts : Array (Positioned YamlToken)) :
    toks (ts.filter fun t => t.val != .placeholder) = (toks ts).filter nonPh := by
  simp only [toks, Array.toList_filter, List.filter_map]
  congr 2
  funext t
  show (t.val != .placeholder) = nonPh t.val
  generalize t.val = v
  cases v <;> first | rfl | simp [nonPh]

/-- `scanFiltered` output is directive-closed, as a list fact. -/
lemma scanFiltered_closedList (input : String) (ts : Array (Positioned YamlToken))
    (h : scanFiltered input = .ok ts) : ClosedList (toks ts) := by
  unfold scanFiltered at h
  split at h
  · rename_i ts0 h0
    simp only [Except.ok.injEq] at h; subst h
    rw [toks_filter]
    exact (dirRun_false_closed false _ (scan_closed input ts0 h0)).1
  · contradiction

end L4YAML.Proofs.DirectiveRuns

end Blanket
