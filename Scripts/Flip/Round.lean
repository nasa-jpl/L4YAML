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

/-- One error site: the logged file, its line, the message, and its owner —
the declaration name (prefixed by the file when it is not the flipped one),
`<file:line>` for a gate command, `?` when nothing encloses it. -/
structure Site where
  file : String
  line : Nat
  msg : String
  owner : String
  deriving Repr, Inhabited, BEq

/-- Does the logged path name `rel`?  Lake logs the path as given; accept a
`./` prefix or an absolute path ending in `/rel`. -/
def namesFile (logged rel : String) : Bool :=
  logged == rel || logged == "./" ++ rel || logged.endsWith ("/" ++ rel)

#guard namesFile "L4YAML/A.lean" "L4YAML/A.lean"
#guard namesFile "/home/x/L4YAML/A.lean" "L4YAML/A.lean"
#guard namesFile "L4YAML/B.lean" "L4YAML/A.lean" == false
#guard namesFile "XL4YAML/A.lean" "L4YAML/A.lean" == false

/-- Every error line of a build log, both lake orderings, any file. -/
def errsOf (log : String) : Array ErrLine := Id.run do
  let mut out := #[]
  for raw in log.splitOn "\n" do
    if let some e := parseErr raw then out := out.push e
  return out

/-- The distinct logged files of `errs`, first-seen order. -/
def filesOf (errs : Array ErrLine) : Array String :=
  errs.foldl (fun acc e => if acc.contains e.file then acc else acc.push e.file) #[]

/-- The sites of `errs` that name `rel`, resolved against `lines` (the text of
`rel`); `label` decorates the owner (identity for the flipped file, the file
name for a dependent one). -/
def resolveSites (errs : Array ErrLine) (rel : String) (lines : Array String)
    (label : String → String := id) : Array Site :=
  errs.filterMap fun e =>
    if namesFile e.file rel then
      let owner := match enclosing rel lines e.line with
        | some o => o.name
        | none => "?"
      some ⟨rel, e.line, e.msg, label owner⟩
    else none

#guard (errsOf "x\nerror: A.lean:3:1: boom\nB.lean:7:0: error: bang\n").size == 2
#guard filesOf (errsOf "error: A.lean:3:1: boom\nB.lean:7:0: error: bang\nerror: A.lean:9:1: again") == #["A.lean", "B.lean"]
#guard resolveSites (errsOf "error: A.lean:3:1: boom\nB.lean:7:0: error: bang") "A.lean" #["def a := 1", "", "  x"]
  == #[⟨"A.lean", 3, "boom", "a"⟩]
#guard resolveSites (errsOf "B.lean:7:0: error: bang") "B.lean" #["lemma b : True := by", "", "", "", "", "", "  x"] (fun n => s!"B.lean {n}")
  == #[⟨"B.lean", 7, "bang", "B.lean b"⟩]

/-- Sites grouped by owner, in first-seen order (Python `dict.setdefault`). -/
def byOwner (sites : Array Site) : Array (String × Array Site) := Id.run do
  let mut out : Array (String × Array Site) := #[]
  for s in sites do
    match out.findIdx? (·.1 == s.owner) with
    | some i => out := out.modify i fun (k, v) => (k, v.push s)
    | none => out := out.push (s.owner, #[s])
  return out

/-- Bracket depth change of a line, ignoring text after `--`. -/
def depthDelta (l : String) : Int :=
  let code := (l.splitOn "--").headD ""
  code.foldl (fun d c =>
    if c == '(' || c == '[' || c == '{' || c == '⟨' then d + 1
    else if c == ')' || c == ']' || c == '}' || c == '⟩' then d - 1 else d) 0

/-- Position of the first top-level ` :=` of a line entered at bracket depth
`d0` (a `:=` inside `(h : x := default)` is skipped), with the depth at the
end of the line. -/
def topLevelAssign (l : String) (d0 : Int) : Option Nat × Int := Id.run do
  let code := (l.splitOn "--").headD ""
  let cs := code.toList.toArray
  let mut d := d0
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '(' || c == '[' || c == '{' || c == '⟨' then d := d + 1
    else if c == ')' || c == ']' || c == '}' || c == '⟩' then d := d - 1
    else if d == 0 && c == ':' && i + 1 < cs.size && cs[i + 1]! == '=' && (i == 0 || cs[i - 1]! == ' ' || cs[i - 1]! == ')')
        && (i + 2 ≥ cs.size || cs[i + 2]! == ' ') then
      return (some i, depthDelta l)
    i := i + 1
  return (none, d)

#guard (topLevelAssign "lemma f (n : Nat) : n = n := by" 0).1 == some 26
#guard (topLevelAssign "    (h : x := 3) :" 0).1 == none        -- inside the binder
#guard (topLevelAssign "  (h_x : A) -- note := here" 0).1 == none
#guard (topLevelAssign "    : n = n := rfl" 0).1 == some 12

/-- Replace the body of the declaration owning line `lineno` (1-based) with
`sorry`: the signature is kept up to its top-level `:=`, the text from there
to the next column-0 opener / command / `end` / attribute is dropped, and
`:= by sorry` is appended.  `none` when no opener encloses the line, or the
declaration has no top-level `:=` (a statement that fails to elaborate, an
`inductive`/`structure`), which a sorry cannot repair. -/
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
  let mut k := s
  let mut d : Int := 0
  while k < e do
    let (pos, d') := topLevelAssign lines[k]! d
    if let some p := pos then
      let sigHead := String.ofList (lines[k]!.toList.take p)
      return some ((lines.extract 0 k).push (sigHead.trimAsciiEnd.toString ++ " := by sorry") ++ lines.extract e lines.size)
    d := d'
    k := k + 1
  return none

def exampleFile : Array String := #[
  "import X",
  "lemma foo : True := by",
  "  trivial",
  "",
  "lemma bar (n : Nat)",
  "    (h : n = n := rfl) :",
  "    n = n := by",
  "  exact h",
  "inductive T where",
  "  | a",
  "end"]

#guard sorryBody exampleFile 3 == some #["import X", "lemma foo : True := by sorry", "lemma bar (n : Nat)", "    (h : n = n := rfl) :", "    n = n := by", "  exact h", "inductive T where", "  | a", "end"]
#guard sorryBody exampleFile 8 == some #["import X", "lemma foo : True := by", "  trivial", "", "lemma bar (n : Nat)", "    (h : n = n := rfl) :", "    n = n := by sorry", "inductive T where", "  | a", "end"]
#guard sorryBody exampleFile 10 == none      -- an inductive has no body to sorry
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
