module

public import Scripts.Lean.BuildLog
meta import Scripts.Lean.BuildLog

@[expose] public section Blanket

/-!
# Scripts.Flip.Round — one build round of a flip, and the sorry step

A round builds a target, reads the log, and bills every error site in the
flipped file to its enclosing declaration (`Scripts.Lean.BuildLog`, the same
resolver as `scripts-flip-census`).  One round is a FLOOR: Lean stops at the
first failing module.  `sorryBodies` replaces the body of each broken
declaration with `sorry` so a next round can see past it; a spec asks for
`rounds > 1` to iterate to the fixpoint (no new sites).  The pushed tree never
carries a sorry: the driver restores the file byte-identically afterwards.
-/

open Scripts.Lean.BuildLog

namespace Scripts.Flip.Round

/-- One error site in the flipped file. -/
structure Site where
  line : Nat
  msg : String
  owner : String          -- declaration name, or `<file:line>` for a gate, or `?`
  deriving Repr, Inhabited, BEq

/-- Does the logged path name `rel`?  Lake logs the path as given; accept a
`./` prefix or an absolute path ending in `/rel`. -/
def namesFile (logged rel : String) : Bool :=
  logged == rel || logged == "./" ++ rel || logged.endsWith ("/" ++ rel)

#guard namesFile "L4YAML/A.lean" "L4YAML/A.lean"
#guard namesFile "/home/x/L4YAML/A.lean" "L4YAML/A.lean"
#guard namesFile "L4YAML/B.lean" "L4YAML/A.lean" == false
#guard namesFile "XL4YAML/A.lean" "L4YAML/A.lean" == false

/-- The sites of `rel` in a build log, resolved against the flipped text. -/
def sitesOf (log rel : String) (lines : Array String) : Array Site := Id.run do
  let mut out := #[]
  for raw in log.splitOn "\n" do
    if let some e := parseErr raw then
      if namesFile e.file rel then
        let owner := match enclosing rel lines e.line with
          | some o => o.name
          | none => "?"
        out := out.push ⟨e.line, e.msg, owner⟩
  return out

/-- Sites grouped by owner, in first-seen order (Python `dict.setdefault`). -/
def byOwner (sites : Array Site) : Array (String × Array Site) := Id.run do
  let mut out : Array (String × Array Site) := #[]
  for s in sites do
    match out.findIdx? (·.1 == s.owner) with
    | some i => out := out.modify i fun (k, v) => (k, v.push s)
    | none => out := out.push (s.owner, #[s])
  return out

/-- Replace the body of the declaration owning line `lineno` (1-based) with
`sorry`: from the opener line, every line up to the next column-0 opener,
command, `end`, or end of file is dropped and `:= by sorry` appended to the
opener's first line.  `none` when no opener encloses the line (a gate site
cannot be sorried). -/
def sorryBody (lines : Array String) (lineno : Nat) : Option (Array String) := Id.run do
  let top := min lineno lines.size
  let mut i := top
  let mut start : Option Nat := none
  while i > 0 do
    i := i - 1
    if (openerOf lines[i]!).isSome then
      start := some i
      break
  let some s := start | return none
  let mut e := s + 1
  while e < lines.size do
    let l := lines[e]!
    if (openerOf l).isSome || (commandOf l).isSome || l.startsWith "end" || l.startsWith "@[" then break
    e := e + 1
  let head := lines[s]!
  let cut := match head.splitOn " :=" with
    | h :: _ :: _ => h
    | _ => head
  return some ((lines.extract 0 s).push (cut ++ " := by sorry") ++ lines.extract e lines.size)

def exampleFile : Array String := #[
  "import X",
  "lemma foo : True := by",
  "  trivial",
  "",
  "lemma bar : 1 = 1 :=",
  "  rfl",
  "end"]

#guard sorryBody exampleFile 3 == some #["import X", "lemma foo : True := by sorry", "lemma bar : 1 = 1 :=", "  rfl", "end"]
#guard sorryBody exampleFile 6 == some #["import X", "lemma foo : True := by", "  trivial", "", "lemma bar : 1 = 1 := by sorry", "end"]
#guard sorryBody exampleFile 1 == none

/-- Sorry every owner of `sites` (one edit per declaration, last line first so
earlier line numbers stay valid). -/
def sorryBodies (lines : Array String) (sites : Array Site) : Array String := Id.run do
  let owners := (byOwner sites).filterMap fun (k, v) => if k.startsWith "<" || k == "?" then none else some v[0]!.line
  let mut cur := lines
  for ln in owners.qsort (· > ·) do
    if let some l := sorryBody cur ln then cur := l
  return cur

end Scripts.Flip.Round
