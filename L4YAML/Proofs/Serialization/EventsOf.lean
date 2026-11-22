/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Surface.Document
public import L4YAML.Proofs.Serialization.SerializationWellFormed
public import L4YAML.Proofs.Serialization.SourceEvents
public import L4YAML.Proofs.Serialization.SurfaceEvents

public meta import L4YAML.Proofs.Serialization.SerializationWellFormed
public meta import L4YAML.Proofs.Serialization.SourceEvents

@[expose] public section Blanket

/-!
# `eventsOf` — the lexical skeleton (Step 5a(iii), slice 1)

`EVENTSOF-CONCEPT.md` §3.  An input's serialization trace is a function of a
*skeleton*: a canonical partition of the source into segments, each event
segment derivable by its surface relation at its column, each opaque segment a
quoted scalar / comment / block-scalar body / plain scalar, and the remaining
text in maximal `other` runs that contain no event lexeme.  No scanner or
parser definition is imported here.
-/

namespace L4YAML.Proofs.Serialization.EventsOf

open L4YAML
open L4YAML.Surface
open L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.SourceEvents
open L4YAML.Proofs.Serialization.SurfaceEvents

/-- A segment of the source.  `docStart dirs` carries the directive lines
(each with its own break, LF / CRLF / CR) that precede its `---`; `[]` for a
bare marker. -/
inductive Seg where
  | anchor (name : String)
  | alias (name : String)
  | tagUse (handle : String) (chars : List Char)
  | docStart (dirs : List (List Char))
  | docEnd
  | opaque (chars : List Char)
  | other (chars : List Char)
  deriving Repr, DecidableEq

/-- The handle a `%TAG` line declares, if it declares a custom one. -/
def declaredHandle (dir : List Char) : Option String :=
  match namedTagDeclarationAt dir with
  | some (.declareTag h, _) => some h
  | _ => none

/-- Source text of a segment. -/
def Seg.text : Seg → List Char
  | .anchor name => '&' :: name.toList
  | .alias name => '*' :: name.toList
  | .tagUse _ chars => chars
  | .docStart dirs => dirs.flatMap id ++ ['-', '-', '-']
  | .docEnd => ['.', '.', '.']
  | .opaque chars => chars
  | .other chars => chars

/-- Events of one segment; a document start resets BEFORE its declarations. -/
def Seg.events : Seg → List Event
  | .anchor name => [.defineAnchor name]
  | .alias name => [.useAlias name]
  | .tagUse handle _ => [.useTag handle]
  | .docStart dirs => .beginDocument :: (dirs.filterMap declaredHandle).map .declareTag
  | .docEnd => [.endDocument]
  | .opaque _ => []
  | .other _ => []

def Seg.isOther : Seg → Bool
  | .other _ => true
  | _ => false

def eventsOfSegs (segs : List Seg) : List Event := segs.flatMap Seg.events

lemma eventsOfSegs_append (a b : List Seg) :
    eventsOfSegs (a ++ b) = eventsOfSegs a ++ eventsOfSegs b := by
  simp [eventsOfSegs, List.flatMap_append]

/-- Column after consuming `chars` from column `col`; a break (LF, CR, and so
CRLF) resets to 0, as `SBBreak` does. -/
def colAfter (col : Nat) : List Char → Nat
  | [] => col
  | c :: cs => colAfter (if c = '\n' ∨ c = '\r' then 0 else col + 1) cs

/-- The handle a tag lexeme uses: a custom `!h!`, else `!!`, else `!`. -/
def handleOf (chars : List Char) : String :=
  match namedTagUseAt chars with
  | some (.useTag h, _) => h
  | _ => match chars with
    | '!' :: '!' :: _ => "!!"
    | _ => "!"

/-- `true` when `chars`, read from `col`, contains no event lexeme: none of
`& * ! %`, and no `---`/`...` at column 0. -/
def noEventLexeme : Nat → List Char → Bool
  | _, [] => true
  | col, c :: cs =>
    if c = '&' ∨ c = '*' ∨ c = '!' ∨ c = '%' then false
    else if col = 0 ∧ ((c = '-' ∧ cs.take 2 = ['-', '-']) ∨ (c = '.' ∧ cs.take 2 = ['.', '.'])) then false
    else noEventLexeme (if c = '\n' ∨ c = '\r' then 0 else col + 1) cs

/-- One quoted scalar, comment, block scalar, plain scalar or verbatim tag
derivable from `sp` to `sp'`. -/
def OpaqueSpan (sp sp' : SurfPos) : Prop :=
  (∃ n c, SCDoubleQuoted n c sp sp') ∨ (∃ n c, SCSingleQuoted n c sp sp') ∨
  SLComment sp sp' ∨ (∃ n, SCLLiteral n sp sp') ∨ (∃ n, SCLFolded n sp sp') ∨
  (∃ c, SNsPlainOneLine c sp sp') ∨ (∃ n c, SNsPlainMultiLine n c sp sp') ∨
  -- `[89] c-verbatim-tag`: names no handle, so no event (concept §6 Q4); only
  -- `SCNsTagProperty.verbatim` can start with `!<`.
  (sp.chars.take 2 = ['!', '<'] ∧ SCNsTagProperty sp sp')

/-- An opaque region: an `OpaqueSpan` followed by trailing white.  The scanner's
leaf lemmas (`scanPlainScalar_prod`: `SNsPlain … sp sp_gram ∧ GStar SSWhite
sp_gram sp'`) end past the grammar span, and white carries no event lexeme, so
the segment may absorb it (EVENTSOF-CONCEPT §9, S1). -/
def OpaqueAt (sp sp' : SurfPos) : Prop :=
  ∃ sp_mid, OpaqueSpan sp sp_mid ∧ GStar SSWhite sp_mid sp'

/-- A name/tag lexeme is maximal: the next character cannot extend it.  Without
this `&ab` could be read as `&a` before a plain `b`, and `!h!item` as the two
builtin uses `!h` `!item`. -/
def Maximal (p : Char → Bool) (rest : List Char) : Prop :=
  ∀ c ∈ rest.head?, p c = false

def isTagCharBool (c : Char) : Bool :=
  !(isWhiteSpaceBool c || isLineBreakBool c || isFlowIndicatorBool c)

def isBreak (c : Char) : Bool := c = '\n' || c = '\r'

/-- Side condition of one segment placed at column `col` before `rest`. -/
def SegAt (col : Nat) (seg : Seg) (rest : List Char) : Prop :=
  let sp : SurfPos := ⟨seg.text ++ rest, col⟩
  let sp' : SurfPos := ⟨rest, colAfter col seg.text⟩
  match seg with
  | .anchor name => PendingAnchorWitness sp sp' name ∧ Maximal isAnchorCharBool rest
  | .alias name => AliasEventWitness sp sp' name ∧ Maximal isAnchorCharBool rest
  | .tagUse handle chars =>
      SCNsTagProperty sp sp' ∧ handleOf chars = handle ∧
      (∀ c ∈ chars, isTagCharBool c = true) ∧ Maximal isTagCharBool rest
  | .docStart dirs =>
      col = 0 ∧ SCDirectivesEnd ⟨'-' :: '-' :: '-' :: rest, 0⟩ ⟨rest, 3⟩ ∧
      ∀ d ∈ dirs, (∃ c ∈ d.getLast?, isBreak c = true) ∧
        ∃ tail, SLDirective ⟨d ++ tail, 0⟩ ⟨tail, 0⟩
  | .docEnd => col = 0 ∧ SCDocumentEnd sp sp'
  | .opaque _ => OpaqueAt sp sp'
  | .other chars => chars ≠ [] ∧ noEventLexeme col chars = true

/-- `Skeleton col chars segs`: `segs` is a canonical partition of `chars` read
from column `col` — every segment satisfies `SegAt`, and `other` runs are
maximal (no two adjacent). -/
inductive Skeleton : Nat → List Char → List Seg → Prop where
  | nil (col : Nat) : Skeleton col [] []
  | cons (col : Nat) (seg : Seg) (rest : List Char) (segs : List Seg) :
      SegAt col seg rest →
      Skeleton (colAfter col seg.text) rest segs →
      (seg.isOther = true → ∀ s ∈ segs.head?, s.isOther = false) →
      Skeleton col (seg.text ++ rest) (seg :: segs)

/-- The input-level predicate the capstone's second conjunct will read. -/
def SerializationWellFormedInput (input : String) : Prop :=
  ∃ segs, Skeleton 0 input.toList segs ∧ SerializationWellFormed (eventsOfSegs segs)

lemma skeleton_text (col : Nat) (chars : List Char) (segs : List Seg)
    (h : Skeleton col chars segs) : segs.flatMap Seg.text = chars := by
  induction h with
  | nil => rfl
  | cons col seg rest segs _ _ _ ih => simp [List.flatMap_cons, ih]

/-! ## Rule-2 instantiations (traces of hand-built skeletons) -/

def wf (segs : List Seg) : Bool := checkFrom {} (eventsOfSegs segs)

#guard eventsOfSegs [.anchor "x", .other " [".toList, .alias "x", .other "]".toList]
  = [.defineAnchor "x", .useAlias "x"]
#guard wf [.anchor "x", .other " [".toList, .alias "x", .other "]".toList] = true
#guard wf [.alias "x"] = false
#guard wf [.opaque "\"&x\"".toList, .other " ".toList, .alias "x"] = false
#guard wf [.anchor "x", .other " ".toList, .opaque "# *x".toList] = true
#guard eventsOfSegs [.docStart ["%TAG !h! tag:e,2026:\n".toList], .other " ".toList,
    .tagUse "!h!" "!h!item".toList]
  = [.beginDocument, .declareTag "!h!", .useTag "!h!"]
#guard wf [.docStart ["%TAG !h! tag:e,2026:\n".toList], .other " ".toList,
    .tagUse "!h!" "!h!item".toList] = true
#guard wf [.tagUse "!h!" "!h!item".toList] = false
#guard wf [.tagUse "!!" "!!str".toList, .tagUse "!" "!foo".toList] = true
#guard wf [.anchor "x", .other " 1\n".toList, .docEnd, .other "\nb: ".toList, .alias "x"] = false
#guard wf [.docStart [], .other " ".toList, .anchor "x", .other " 1\n".toList,
    .docStart [], .other " ".toList, .alias "x"] = false
#guard wf [.anchor "x", .other " 1\n".toList, .alias "x"] = true
#guard handleOf "!h!item".toList = "!h!"
#guard handleOf "!!str".toList = "!!"
#guard handleOf "!foo".toList = "!"
#guard handleOf "!<tag:x>".toList = "!"
#guard colAfter 3 "ab\ncd".toList = 2
#guard colAfter 3 "ab\rcd".toList = 2
#guard colAfter 3 "ab\r\ncd".toList = 2
#guard noEventLexeme 0 "a\r---".toList = false
#guard (Seg.docStart ["%TAG !h! t:\r\n".toList]).text = "%TAG !h! t:\r\n---".toList
#guard eventsOfSegs [.docStart ["%TAG !h! t:\r\n".toList]] = [.beginDocument, .declareTag "!h!"]
#guard noEventLexeme 0 "- a: [b, c]".toList = true
#guard noEventLexeme 0 "---".toList = false
#guard noEventLexeme 1 "---".toList = true
#guard noEventLexeme 0 "a\n...".toList = false
#guard noEventLexeme 0 "a*b".toList = false
#guard declaredHandle "%TAG !h! tag:e,2026:".toList = some "!h!"
#guard declaredHandle "%YAML 1.2".toList = none
#guard declaredHandle "%TAG!e! tag:x:".toList = none
#guard declaredHandle "%TAG\t!e! tag:x:".toList = some "!e!"
#guard declaredHandle "%TAG  !e! tag:x:".toList = some "!e!"
#guard declaredHandle "%TAGX !e! tag:x:".toList = none

end L4YAML.Proofs.Serialization.EventsOf

#print axioms L4YAML.Proofs.Serialization.EventsOf.eventsOfSegs_append
#print axioms L4YAML.Proofs.Serialization.EventsOf.skeleton_text

end Blanket
