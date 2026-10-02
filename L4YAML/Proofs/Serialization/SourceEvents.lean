import L4YAML.Surface.Node
import L4YAML.Proofs.Serialization.SerializationWellFormed

/-!
# Source-event lexemes for SerializationWellFormed

This module moves the semantic specification one layer closer to raw input
without calling the L4YAML scanner or token parser.

It defines small, independent character-list recognizers for the four source
lexemes that create the state relevant to `SerializationWellFormed`:

* `&name`  -> defineAnchor
* `*name`  -> useAlias
* `%TAG !h! ...` -> declareTag
* `!h!suffix` -> useTag

The recognizers intentionally operate on `List Char` and the YAML character
predicates only.  They are not a second YAML parser and are not yet claimed to
find every semantic occurrence inside an arbitrary YAML document.  The point
of this layer is to pin the *local source meaning* independently, so that the
remaining whole-input traversal problem is isolated from the semantic-state
problem.

All generalized lemmas below are ordinary kernel proofs; no `native_decide`.
-/

namespace L4YAMLSerializationSourceEvents

open L4YAML
open L4YAML.CharPredicates
open L4YAML.Surface
open L4YAMLSerializationWellFormed

/-- Boolean spelling of the surface grammar's anchor-name character class,
defined independently from the surface Prop so source recognition is
computable without adding a classical decidability instance. -/
def isAnchorCharBool (c : Char) : Bool :=
  (!isLineBreakBool c) &&
  (!isWhiteSpaceBool c) &&
  isPrintableBool c &&
  (c != '﻿') &&
  (!isFlowIndicatorBool c)

/-- Independent maximal-prefix splitter. -/
def spanWhile (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
      if p c then
        let (front, back) := spanWhile p cs
        (c :: front, back)
      else
        ([], c :: cs)

/-- Drop source horizontal whitespace. -/
def dropHSpace : List Char → List Char
  | ' ' :: cs => dropHSpace cs
  | '\t' :: cs => dropHSpace cs
  | cs => cs

/-- Parse an anchor definition or alias use at the *current source position*.
The returned remainder begins immediately after the anchor name. -/
def anchorEventAt : List Char → Option (Event × List Char)
  | '&' :: cs =>
      let (name, rest) := spanWhile isAnchorCharBool cs
      if name.isEmpty then none
      else some (.defineAnchor (String.ofList name), rest)
  | '*' :: cs =>
      let (name, rest) := spanWhile isAnchorCharBool cs
      if name.isEmpty then none
      else some (.useAlias (String.ofList name), rest)
  | _ => none

/-- Tail parser after the leading `!` of a possible custom tag use. -/
def namedTagUseTail (cs : List Char) : Option (Event × List Char) :=
  let (body, rest) := spanWhile isWordCharBool cs
  match body, rest with
  | [], _ => none
  | _, '!' :: suffix =>
      some (.useTag ("!" ++ String.ofList body ++ "!"), suffix)
  | _, _ => none

/-- Parse a *custom named* tag use `!h!suffix` at the current source
position. Builtin `!`, `!!`, and verbatim `!<...>` forms do not create a
well-formedness obligation and therefore return `none` here. -/
def namedTagUseAt : List Char → Option (Event × List Char)
  | '!' :: cs => namedTagUseTail cs
  | _ => none

/-- Tail parser after the first `!` of a custom %TAG handle. -/
def namedTagDeclarationTail (afterBang : List Char) : Option (Event × List Char) :=
  let (body, rest) := spanWhile isWordCharBool afterBang
  match body, rest with
  | [], _ => none
  | _, '!' :: tail =>
      some (.declareTag ("!" ++ String.ofList body ++ "!"), tail)
  | _, _ => none

/-- Parse a custom named handle declaration from a `%TAG` directive at the
current source position.  Prefix contents are irrelevant to the declaration
accept/reject state, so this projection deliberately stops after the handle. -/
def namedTagDeclarationAt : List Char → Option (Event × List Char)
  | '%' :: 'T' :: 'A' :: 'G' :: cs =>
      match dropHSpace cs with
      | '!' :: afterBang => namedTagDeclarationTail afterBang
      | _ => none
  | _ => none

/-! ## Generic prefix algebra -/

lemma spanWhile_all (p : Char → Bool) (xs : List Char)
    (h : ∀ c ∈ xs, p c = true) :
    spanWhile p xs = (xs, []) := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
      have hc : p c = true := h c (by simp)
      have htail : ∀ d ∈ cs, p d = true := by
        intro d hd
        exact h d (by simp [hd])
      simp [spanWhile, hc, ih htail]

lemma spanWhile_append_stop (p : Char → Bool) (xs : List Char) (stop : Char)
    (tail : List Char)
    (hxs : ∀ c ∈ xs, p c = true)
    (hstop : p stop = false) :
    spanWhile p (xs ++ stop :: tail) = (xs, stop :: tail) := by
  induction xs with
  | nil =>
      simp [spanWhile, hstop]
  | cons c cs ih =>
      have hc : p c = true := hxs c (by simp)
      have htail : ∀ d ∈ cs, p d = true := by
        intro d hd
        exact hxs d (by simp [hd])
      simp [spanWhile, hc, ih htail]

/-! ## Family-level source recognition -/

lemma anchor_definition_source_exact
    (nameChars : List Char)
    (hne : nameChars ≠ [])
    (hchars : ∀ c ∈ nameChars, isAnchorCharBool c = true) :
    anchorEventAt ('&' :: nameChars) =
      some (.defineAnchor (String.ofList nameChars), []) := by
  simp [anchorEventAt, spanWhile_all isAnchorCharBool nameChars hchars, hne]

lemma alias_use_source_exact
    (nameChars : List Char)
    (hne : nameChars ≠ [])
    (hchars : ∀ c ∈ nameChars, isAnchorCharBool c = true) :
    anchorEventAt ('*' :: nameChars) =
      some (.useAlias (String.ofList nameChars), []) := by
  simp [anchorEventAt, spanWhile_all isAnchorCharBool nameChars hchars, hne]

lemma named_tag_use_source_exact
    (handleChars suffix : List Char)
    (hne : handleChars ≠ [])
    (hchars : ∀ c ∈ handleChars, isWordCharBool c = true) :
    namedTagUseAt ('!' :: (handleChars ++ '!' :: suffix)) =
      some (.useTag ("!" ++ String.ofList handleChars ++ "!"), suffix) := by
  have hbang : isWordCharBool '!' = false := by decide
  simp only [namedTagUseAt, namedTagUseTail]
  rw [spanWhile_append_stop isWordCharBool handleChars '!' suffix hchars hbang]
  simp [hne]

lemma named_tag_declaration_source_exact
    (handleChars tail : List Char)
    (hne : handleChars ≠ [])
    (hchars : ∀ c ∈ handleChars, isWordCharBool c = true) :
    namedTagDeclarationAt
        ('%' :: 'T' :: 'A' :: 'G' :: ' ' :: '!' ::
          (handleChars ++ '!' :: tail)) =
      some (.declareTag ("!" ++ String.ofList handleChars ++ "!"), tail) := by
  have hbang : isWordCharBool '!' = false := by decide
  change namedTagDeclarationTail (handleChars ++ '!' :: tail) =
    some (.declareTag ("!" ++ String.ofList handleChars ++ "!"), tail)
  unfold namedTagDeclarationTail
  rw [spanWhile_append_stop isWordCharBool handleChars '!' tail hchars hbang]
  simp [hne]


/-! ## Bridge to the formal surface productions

The next lemmas show that the independent source recognizers are not merely
string conventions: on well-formed lexemes they construct the corresponding
L4YAML surface-production witnesses.
-/

lemma gstar_gchar_of_all
    (P : Char → Prop)
    (xs tail : List Char) (col : Nat)
    (h : ∀ c ∈ xs, P c) :
    GStar (GChar P)
      ⟨xs ++ tail, col⟩
      ⟨tail, col + xs.length⟩ := by
  induction xs generalizing col with
  | nil =>
      simp
      exact GStar.nil _
  | cons c cs ih =>
      have hc : P c := h c (by simp)
      have hcs : ∀ d ∈ cs, P d := by
        intro d hd
        exact h d (by simp [hd])
      have htail := ih (col := col + 1) hcs
      have hstep : GChar P
          ⟨c :: (cs ++ tail), col⟩
          ⟨cs ++ tail, col + 1⟩ :=
        GChar.mk c (cs ++ tail) col hc
      have hfull := GStar.cons
        ⟨c :: (cs ++ tail), col⟩
        ⟨cs ++ tail, col + 1⟩
        ⟨tail, (col + 1) + cs.length⟩
        hstep htail
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfull

lemma gplus_gchar_of_cons
    (P : Char → Prop)
    (c : Char) (cs tail : List Char) (col : Nat)
    (hc : P c) (hcs : ∀ d ∈ cs, P d) :
    GPlus (GChar P)
      ⟨(c :: cs) ++ tail, col⟩
      ⟨tail, col + (c :: cs).length⟩ := by
  have hrest := gstar_gchar_of_all P cs tail (col + 1) hcs
  have hfirst : GChar P
      ⟨c :: (cs ++ tail), col⟩
      ⟨cs ++ tail, col + 1⟩ :=
    GChar.mk c (cs ++ tail) col hc
  have hfull := GPlus.mk
    ⟨c :: (cs ++ tail), col⟩
    ⟨cs ++ tail, col + 1⟩
    ⟨tail, (col + 1) + cs.length⟩
    hfirst hrest
  simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfull

lemma anchor_char_bool_true_iff (c : Char) :
    isAnchorCharBool c = true ↔ isNsAnchorChar c := by
  constructor
  · intro h
    simp only [isAnchorCharBool, Bool.and_eq_true, Bool.not_eq_true] at h
    rcases h with ⟨⟨⟨⟨hbreak, hwhite⟩, hprint⟩, hbom⟩, hflow⟩
    have hnbreak : ¬ isLineBreakProp c := by
      intro hp
      have ht : isLineBreakBool c = true := (isLineBreak_iff c).2 hp
      simp [ht] at hbreak
    have hnwhite : ¬ isWhiteSpaceProp c := by
      intro hp
      have ht : isWhiteSpaceBool c = true := (isWhiteSpace_iff c).2 hp
      simp [ht] at hwhite
    have hpprint : isPrintableProp c :=
      (isPrintable_iff c).1 hprint
    have hnflow : ¬ isFlowIndicatorProp c := by
      intro hp
      have ht : isFlowIndicatorBool c = true := (isFlowIndicator_iff c).2 hp
      simp [ht] at hflow
    exact ⟨⟨hnbreak, hnwhite, hpprint, by simpa using hbom⟩, hnflow⟩
  · intro h
    rcases h with ⟨⟨hbreak, hwhite, hprint, hbom⟩, hflow⟩
    have hb : isLineBreakBool c = false := by
      cases hbc : isLineBreakBool c
      · rfl
      · exact False.elim (hbreak ((isLineBreak_iff c).1 hbc))
    have hw : isWhiteSpaceBool c = false := by
      cases hwc : isWhiteSpaceBool c
      · rfl
      · exact False.elim (hwhite ((isWhiteSpace_iff c).1 hwc))
    have hp : isPrintableBool c = true := (isPrintable_iff c).2 hprint
    have hf : isFlowIndicatorBool c = false := by
      cases hfc : isFlowIndicatorBool c
      · rfl
      · exact False.elim (hflow ((isFlowIndicator_iff c).1 hfc))
    simp [isAnchorCharBool, hb, hw, hp, hbom, hf]

lemma anchor_definition_surface
    (c : Char) (cs tail : List Char) (col : Nat)
    (hc : isAnchorCharBool c = true)
    (hcs : ∀ d ∈ cs, isAnchorCharBool d = true) :
    SCNsAnchorProperty
      ⟨'&' :: ((c :: cs) ++ tail), col⟩
      ⟨tail, col + 1 + (c :: cs).length⟩ := by
  have hc' : isNsAnchorChar c := (anchor_char_bool_true_iff c).mp hc
  have hcs' : ∀ d ∈ cs, isNsAnchorChar d := by
    intro d hd
    exact (anchor_char_bool_true_iff d).mp (hcs d hd)
  have hname := gplus_gchar_of_cons isNsAnchorChar c cs tail (col + 1) hc' hcs'
  exact SCNsAnchorProperty.mk
    ((c :: cs) ++ tail) col
    ⟨tail, col + 1 + (c :: cs).length⟩
    (by simpa [Nat.add_assoc] using hname)

lemma alias_use_surface
    (c : Char) (cs tail : List Char) (col : Nat)
    (hc : isAnchorCharBool c = true)
    (hcs : ∀ d ∈ cs, isAnchorCharBool d = true) :
    SCNsAliasNode
      ⟨'*' :: ((c :: cs) ++ tail), col⟩
      ⟨tail, col + 1 + (c :: cs).length⟩ := by
  have hc' : isNsAnchorChar c := (anchor_char_bool_true_iff c).mp hc
  have hcs' : ∀ d ∈ cs, isNsAnchorChar d := by
    intro d hd
    exact (anchor_char_bool_true_iff d).mp (hcs d hd)
  have hname := gplus_gchar_of_cons isNsAnchorChar c cs tail (col + 1) hc' hcs'
  exact SCNsAliasNode.mk
    ((c :: cs) ++ tail) col
    ⟨tail, col + 1 + (c :: cs).length⟩
    (by simpa [Nat.add_assoc] using hname)

lemma named_tag_use_surface
    (c : Char) (handleRest suffix tail : List Char) (col : Nat)
    (hc : isWordCharProp c)
    (hhandle : ∀ d ∈ handleRest, isWordCharProp d)
    (hsuffix : ∀ d ∈ suffix, isTagCharProp d) :
    SCNsTagProperty
      ⟨'!' :: ((c :: handleRest) ++ '!' :: (suffix ++ tail)), col⟩
      ⟨tail, col + 1 + (c :: handleRest).length + 1 + suffix.length⟩ := by
  let handle := c :: handleRest
  have hwords : GPlus (GChar isWordCharProp)
      ⟨handle ++ '!' :: (suffix ++ tail), col + 1⟩
      ⟨'!' :: (suffix ++ tail), col + 1 + handle.length⟩ := by
    simpa [handle, Nat.add_assoc] using
      (gplus_gchar_of_cons isWordCharProp c handleRest
        ('!' :: (suffix ++ tail)) (col + 1) hc hhandle)
  have hbang : GLit '!'
      ⟨'!' :: (suffix ++ tail), col + 1 + handle.length⟩
      ⟨suffix ++ tail, col + 1 + handle.length + 1⟩ :=
    GLit.mk (suffix ++ tail) (col + 1 + handle.length)
  have hsuffixStar : GStar (GChar isTagCharProp)
      ⟨suffix ++ tail, col + 1 + handle.length + 1⟩
      ⟨tail, col + 1 + handle.length + 1 + suffix.length⟩ := by
    simpa [Nat.add_assoc] using
      (gstar_gchar_of_all isTagCharProp suffix tail
        (col + 1 + handle.length + 1) hsuffix)
  exact SCNsTagProperty.named
    (handle ++ '!' :: (suffix ++ tail)) col
    ⟨'!' :: (suffix ++ tail), col + 1 + handle.length⟩
    ⟨suffix ++ tail, col + 1 + handle.length + 1⟩
    ⟨tail, col + 1 + handle.length + 1 + suffix.length⟩
    hwords hbang hsuffixStar

/-! ## Composition with the already-proved runtime guards

These lemmas are deliberately local: the source recognizer establishes which
semantic event/name a source lexeme denotes; the existing bridge establishes
that the runtime state makes exactly the same accept/reject decision for that
name.  No scanner/parser call appears in the source recognizers themselves.
-/

lemma source_alias_allowed_iff_scanner_guard
    (s : L4YAML.Scanner.ScannerState)
    (chars rest : List Char) (name : String)
    (hsrc : anchorEventAt chars = some (.useAlias name, rest)) :
    s.definedAnchors.any (fun x => x == name) = true ↔
      AliasAllowed (ofScannerAliases s) name := by
  exact scanner_alias_guard_exact s name

lemma source_named_tag_allowed_iff_parser_guard
    (ps : L4YAML.TokenParser.ParseState)
    (chars rest : List Char) (handle : String)
    (hsrc : namedTagUseAt chars = some (.useTag handle, rest)) :
    parserTagGuard ps handle = true ↔
      TagHandleAllowed (ofParserTags ps) handle := by
  exact parser_tag_guard_exact ps handle

end L4YAMLSerializationSourceEvents

#print axioms L4YAMLSerializationSourceEvents.spanWhile_all
#print axioms L4YAMLSerializationSourceEvents.alias_use_source_exact
#print axioms L4YAMLSerializationSourceEvents.named_tag_use_source_exact
#print axioms L4YAMLSerializationSourceEvents.source_alias_allowed_iff_scanner_guard
#print axioms L4YAMLSerializationSourceEvents.source_named_tag_allowed_iff_parser_guard

#print axioms L4YAMLSerializationSourceEvents.anchor_definition_surface
#print axioms L4YAMLSerializationSourceEvents.alias_use_surface
#print axioms L4YAMLSerializationSourceEvents.named_tag_use_surface
