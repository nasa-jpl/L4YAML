module

@[expose] public section Blanket

/-!
# Scripts.Lean.BuildLog — `file:line:col: error:` lines and the declaration that owns them

The port of `scripts/flip_census.py` (plan `Blueprint/09-scripts-in-lean.md` §3
phase 2.1).  A flip is priced by the DISTINCT DECLARATIONS it breaks, not by
error sites: one lemma can log four errors and is still one proof to repair.
This module reads a `lake build` log, resolves each error site against the
source on disk by scanning backwards for the nearest declaration opener at
column 0, and separates gate sites (`#guard`, `#eval`, `#guard_msgs`,
`#check`, `#print`, `#reduce`) from proofs — a gate is a decision to re-take,
not a proof to repair, and billing it to the preceding `def` is wrong
(measured 2026-10-18: three `#guard`s in `Serialization/Census.lean` all
reported as `def tagCases`).

**A single run reports a FLOOR, never the price.**  A failing module blocks
its dependents, so the next layer never elaborates.  To get the whole bill,
sorry the round's breakages, rebuild, re-run; repeat until a round adds
nothing but `sorryAx` artifacts.

The parsers are hand-written for the fixed line shapes (plan §6 Q1: no
regex dependency) and mirror the Python's `ERR`, `COMMAND` and `OPENER`
regexes one for one; the `#guard` rows below are the Python's cases.
-/

namespace Scripts.Lean.BuildLog

/-! ## Error lines -/

/-- One `error:` site in a build log. -/
structure ErrLine where
  file : String
  line : Nat
  col : Nat
  msg : String
  deriving DecidableEq, Repr, Inhabited

def isAsciiWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c' || c == '\x0b'

/-- Python `str.strip()`: ASCII and Unicode whitespace at both ends; the
log's lines only carry ASCII, so ASCII is what is stripped. -/
def pyStrip (s : String) : String :=
  String.ofList ((s.toList.dropWhile isAsciiWs).reverse.dropWhile isAsciiWs |>.reverse)

/-- Split `rest` at `PATH:LINE:COL: ` where `PATH` is non-blank and ends in
`.lean`, `LINE`/`COL` are digits: `(path, line, col, after)`.  The path is
the longest prefix that works (the regex `\S+\.lean` is greedy). -/
def splitLoc (s : String) : Option (String × Nat × Nat × String) := Id.run do
  let cs := s.toList
  -- candidate ends of the path: every position where ".lean:" starts
  let mut best : Option (String × Nat × Nat × String) := none
  let mut i := 0
  let mut pre : List Char := []
  let mut rest := cs
  while !rest.isEmpty do
    if (String.ofList (rest.take 6)) == ".lean:" then
      let path := String.ofList (pre.reverse ++ ".lean".toList)
      if !path.any isAsciiWs then
        let after := rest.drop 6
        let (d1, r1) := after.span Char.isDigit
        if !d1.isEmpty then
          match r1 with
          | ':' :: r2 =>
            let (d2, r3) := r2.span Char.isDigit
            if !d2.isEmpty then
              match r3 with
              | ':' :: ' ' :: r4 =>
                best := some (path, (String.ofList d1).toNat!, (String.ofList d2).toNat!, String.ofList r4)
              | _ => pure ()
          | _ => pure ()
    match rest with
    | c :: r => pre := c :: pre; rest := r; i := i + 1
    | [] => pure ()
  return best

/-- `ERR`: `error: FILE:L:C: MSG` or `FILE:L:C: error: MSG`, on the stripped
line (Python matches `raw.strip()` and anchors both ends). -/
def parseErr (raw : String) : Option ErrLine :=
  let s := pyStrip raw
  if s.startsWith "error: " then
    match splitLoc (String.ofList (s.toList.drop 7)) with
    | some (f, l, c, m) => some ⟨f, l, c, m⟩
    | none => none
  else
    match splitLoc s with
    | some (f, l, c, m) =>
      if m.startsWith "error: " then some ⟨f, l, c, String.ofList (m.toList.drop 7)⟩ else none
    | none => none

#guard parseErr "error: Tests/Guards/Proofs/MarkedColsDomain.lean:28:49: Unknown constant `Int.toNatX`"
  == some ⟨"Tests/Guards/Proofs/MarkedColsDomain.lean", 28, 49, "Unknown constant `Int.toNatX`"⟩
#guard parseErr "  L4YAML/Scanner.lean:12:3: error: unsolved goals  "
  == some ⟨"L4YAML/Scanner.lean", 12, 3, "unsolved goals"⟩
#guard parseErr "L4YAML/Scanner.lean:12:3: warning: unused variable" == none
#guard parseErr "Scripts/Ledger.lean:126:7: error(lean.synthInstanceFailed): failed" == none
#guard parseErr "error: build failed" == none
#guard parseErr "✖ [10/13] Building Scripts.Main.CheckScriptsLedger (443ms)" == none
#guard parseErr "trace: .> LEAN_PATH=… lean Scripts/Ledger.lean -o x.olean" == none

/-! ## Openers -/

/-- `COMMAND`: a line whose first non-blank token is a gate command.  The
alternation order of the regex matters only for `#guard_msgs` vs `#guard`
(`\b` after the name). -/
def commandKinds : List String := ["#guard_msgs", "#guard", "#eval", "#check", "#print", "#reduce"]

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- `re.match(r'^\s*(#guard_msgs|#guard|#eval|#check|#print|#reduce)\b', line)`. -/
def commandOf (line : String) : Option String :=
  let s := String.ofList (line.toList.dropWhile isAsciiWs)
  commandKinds.find? fun (k : String) =>
    s.startsWith k &&
      (match (s.toList.drop k.length) with
       | [] => true
       | c :: _ => !isWordChar c)

#guard commandOf "#guard probe \"? a\" 2 == some (3, [0])" == some "#guard"
#guard commandOf "  #guard_msgs in" == some "#guard_msgs"
#guard commandOf "#guardx y" == none
#guard commandOf "#eval 1" == some "#eval"
#guard commandOf "def x := 1" == none
#guard commandOf "-- #guard in a comment" == none

/-- `OPENER`: optional `@[…]` attribute, modifiers, the keyword, and an optional name.
Returns `(keyword, name?)`; `name` is `[A-Za-z_α-ω][^\s:({\[]*`. -/
def openerKeywords : List String :=
  ["theorem", "lemma", "def", "instance", "abbrev", "example", "structure", "inductive", "class"]

def openerModifiers : List String :=
  ["private", "protected", "partial", "noncomputable", "unsafe", "public"]

def isNameStart (c : Char) : Bool :=
  (c.isAlpha) || c == '_' || (c.val ≥ 0x3B1 && c.val ≤ 0x3C9)   -- `α`–`ω`

def isNameStop (c : Char) : Bool :=
  isAsciiWs c || c == ':' || c == '(' || c == '{' || c == '['

/-- Drop `@[...]` then any blanks, when the text starts with `@[`. -/
def dropAttr (cs : List Char) : List Char :=
  match cs with
  | '@' :: '[' :: rest =>
    let body := rest.dropWhile (· != ']')
    match body with
    | ']' :: r => r.dropWhile isAsciiWs
    | _ => cs            -- no `]`: the regex's optional group does not match
  | _ => cs

/-- Drop `(?:modifier\s+)*`. -/
partial def dropModifiers (cs : List Char) : List Char :=
  match openerModifiers.find? (fun (m : String) => (String.ofList cs).startsWith m &&
      (match cs.drop m.length with | c :: _ => isAsciiWs c | [] => false)) with
  | some m => dropModifiers ((cs.drop m.length).dropWhile isAsciiWs)
  | none => cs

def openerOf (line : String) : Option (String × Option String) := do
  let cs := dropModifiers (dropAttr line.toList)
  let kw ← openerKeywords.find? fun (k : String) => (String.ofList cs).startsWith k &&
    (match cs.drop k.length with | [] => true | c :: _ => !isWordChar c)
  let after := cs.drop kw.length
  -- `(?:\s+(name))?`
  let name :=
    match after with
    | c :: _ =>
      if isAsciiWs c then
        let t := after.dropWhile isAsciiWs
        match t with
        | d :: _ => if isNameStart d then some (String.ofList (t.takeWhile (!isNameStop ·))) else none
        | [] => none
      else none
    | [] => none
  return (kw, name)

-- the Python OPENER cases
#guard openerOf "theorem foo_bar (x : Nat) : x = x := rfl" == some ("theorem", some "foo_bar")
#guard openerOf "lemma Foo.bar : True := trivial" == some ("lemma", some "Foo.bar")
#guard openerOf "def markedCols (s : ScannerState) : List Nat :=" == some ("def", some "markedCols")
#guard openerOf "private def go : Nat → Nat" == some ("def", some "go")
#guard openerOf "@[simp] lemma x_eq : x = x := rfl" == some ("lemma", some "x_eq")
#guard openerOf "@[expose] public def main (args : List String) : IO UInt32 := do" == some ("def", some "main")
#guard openerOf "noncomputable instance : Inhabited Foo := ⟨x⟩" == some ("instance", none)
#guard openerOf "instance instFoo : Foo := ⟨⟩" == some ("instance", some "instFoo")
#guard openerOf "example : 1 = 1 := rfl" == some ("example", none)
#guard openerOf "structure Row where" == some ("structure", some "Row")
#guard openerOf "inductive Class where" == some ("inductive", some "Class")
#guard openerOf "class Foo (α : Type) where" == some ("class", some "Foo")
#guard openerOf "partial def dropModifiers (cs : List Char) : List Char :=" == some ("def", some "dropModifiers")
#guard openerOf "protected lemma αβ.x : True := trivial" == some ("lemma", some "αβ.x")
#guard openerOf "def α (n : Nat) := n" == some ("def", some "α")
#guard openerOf "  def indented := 1" == none          -- openers are at column 0
#guard openerOf "defn x" == none                        -- `\b`
#guard openerOf "theorem" == some ("theorem", none)
#guard openerOf "def (x) := 1" == some ("def", none)    -- name must start with a letter
#guard openerOf "#guard x == 1" == none
#guard openerOf "open Foo in" == none
#guard openerOf "@[simp lemma x : True := trivial" == none  -- unclosed attribute: no match

/-! ## Resolution -/

/-- What an error site resolves to: a gate command (`#guard <File.lean:N>`),
a declaration (`def name`), or nothing. -/
structure Owner where
  kind : String
  name : String
  deriving DecidableEq, Repr, Inhabited

def baseName (path : String) : String :=
  match (path.splitOn "/").getLast? with
  | some b => b
  | none => path

/-- `enclosing`, on the file's lines (0-based array) and the 1-based error
line.  A command on the error line or the line above it owns the site; else the nearest opener at or above it. -/
def enclosing (fileName : String) (lines : Array String) (lineno : Nat) : Option Owner := Id.run do
  let top := min lineno lines.size           -- Python: min(lineno, len(lines))
  -- for i in range(top - 1, max(top - 3, -1), -1): the error line and the one above it
  let mut i := top
  while i > 0 do
    i := i - 1
    if i + 2 < top then break
    match commandOf lines[i]! with
    | some k => return some ⟨k, s!"<{fileName}:{i + 1}>"⟩
    | none => pure ()
  let mut j := top
  while j > 0 do
    j := j - 1
    match openerOf lines[j]! with
    | some (k, n) => return some ⟨k, n.getD "<anonymous>"⟩
    | none => pure ()
  return none

def exampleFile : Array String := #[
  "import X",                         -- 1
  "",                                 -- 2
  "def tagCases : Nat := 3",          -- 3
  "",                                 -- 4
  "#guard tagCases == 4",             -- 5
  "lemma foo : True := by",           -- 6
  "  trivial",                        -- 7
  "  done",                           -- 8
  "@[simp] theorem bar : 1 = 1 :=",   -- 9
  "  rfl"]                            -- 10

#guard enclosing "F.lean" exampleFile 5 == some ⟨"#guard", "<F.lean:5>"⟩
#guard enclosing "F.lean" exampleFile 6 == some ⟨"#guard", "<F.lean:5>"⟩   -- one line above: the window
#guard enclosing "F.lean" exampleFile 7 == some ⟨"lemma", "foo"⟩           -- two lines above: outside it (Python's range(top-1, top-3, -1))
#guard enclosing "F.lean" exampleFile 2 == none                            -- top of file: lines 2 and 1 only
#guard enclosing "F.lean" #["#eval 1", "x"] 2 == some ⟨"#eval", "<F.lean:1>"⟩
#guard enclosing "F.lean" exampleFile 8 == some ⟨"lemma", "foo"⟩
#guard enclosing "F.lean" exampleFile 10 == some ⟨"theorem", "bar"⟩
#guard enclosing "F.lean" exampleFile 3 == some ⟨"def", "tagCases"⟩
#guard enclosing "F.lean" exampleFile 1 == none
#guard enclosing "F.lean" exampleFile 99 == some ⟨"theorem", "bar"⟩         -- past EOF: clamps to the last line
#guard enclosing "F.lean" #[] 1 == none

end Scripts.Lean.BuildLog
