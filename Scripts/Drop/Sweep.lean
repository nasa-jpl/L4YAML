module

/-!
# Scripts.Drop.Sweep — the pure half of `lake run drop-sweep`

The port of `scripts/drop_sweep.py` (DOCS item 238; Rule 9 phase 2).  Everything here
is a function of strings: which `.lean` files are entry points, how a refused import is
read off `lake env lean`'s output, how the `WIDE`/`MOD`/`HIT` lines are read, how the
`WIDE-LINE` is rendered and how the instrument's pin literal is read through a Lean
string gap.  The IO (the module walk, the scratch files, the `lake env lean` runs) is
`Scripts.Main.DropSweep`.  Each reading is pinned by a `#guard` on the Python's own
example shapes.
-/

namespace Scripts.Drop.Sweep

public section

/-- `List.drop`/`take` on a string by codepoint index. -/
def sub (s : String) (start : Nat) (stop : Nat := s.length) : String :=
  String.ofList ((s.toList.drop start).take (stop - start))

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

def isNameChar (c : Char) : Bool := isWordChar c || c == '.'

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\x0c' || c == '\x0b'

/-- `^\s*(?:unsafe |partial )*def main\b` on one line. -/
def isMainLine (line : String) : Bool := Id.run do
  let mut cs := line.toList.dropWhile isWs
  let mut go := true
  while go do
    if cs.take 7 == "unsafe ".toList then cs := cs.drop 7
    else if cs.take 8 == "partial ".toList then cs := cs.drop 8
    else go := false
  if cs.take 8 != "def main".toList then return false
  match (cs.drop 8).head? with
  | some c => return !isWordChar c
  | none => return true

#guard isMainLine "def main : IO Unit := pure ()"
#guard isMainLine "  unsafe def main (args : List String) : IO UInt32 := do"
#guard isMainLine "partial unsafe def main"
#guard !isMainLine "def mainLoop := 1"
#guard !isMainLine "-- def main"
#guard !isMainLine "public def main : IO Unit := pure ()"

/-- Does the source define a root `main`?  (`re.M`: any line.) -/
def hasMain (src : String) : Bool := (src.splitOn "\n").any isMainLine

/-- `L4YAML/Proofs/X.lean` → `L4YAML.Proofs.X`. -/
def moduleOf (rel : String) : String :=
  let r := if rel.endsWith ".lean" then sub rel 0 (rel.length - 5) else rel
  String.map (fun c => if c == '/' then '.' else c) r

#guard moduleOf "L4YAML/Proofs/Production/StreamAccum.lean" == "L4YAML.Proofs.Production.StreamAccum"

/-- The first (leftmost) refused module in `lake env lean`'s output:
    `import X failed` | `module X does not exist` | `lean/X/Y.olean', incompatible` (→ `X.Y`). -/
def refused? (out : String) : Option String := Id.run do
  let cs := out.toList.toArray
  let n := cs.size
  let at_ (i : Nat) (lit : String) : Bool :=
    let l := lit.toList
    i + l.length ≤ n && (List.range l.length).all fun k => cs[i + k]! == l[k]!
  let run (i : Nat) (ok : Char → Bool) : Nat := Id.run do
    let mut j := i
    while j < n && ok cs[j]! do j := j + 1
    return j
  for i in [0:n] do
    if at_ i "import " then
      let j := run (i + 7) isNameChar
      if j > i + 7 && at_ j " failed" then
        return some (String.ofList (cs.extract (i + 7) j).toList)
    if at_ i "module " then
      let j := run (i + 7) isNameChar
      if j > i + 7 && at_ j " does not exist" then
        return some (String.ofList (cs.extract (i + 7) j).toList)
    if at_ i "lean/" then
      let j := run (i + 5) (fun c => isWordChar c || c == '/')
      if j > i + 5 && at_ j ".olean', incompatible" then
        return some (String.map (fun c => if c == '/' then '.' else c)
          (String.ofList (cs.extract (i + 5) j).toList))
  return none

#guard refused? "x.lean:1:0: error: import Tests.Foo failed, environment already contains 'main'" == some "Tests.Foo"
#guard refused? "error: module Tests.Bar does not exist" == some "Tests.Bar"
#guard refused? "error: failed to read file '/r/.lake/build/lib/lean/Tests/Old.olean', incompatible header" == some "Tests.Old"
#guard refused? "error: unknown constant" == none

/-- `closure=(\d+)`. -/
def closure? (line : String) : Option Nat := Id.run do
  let parts := line.splitOn "closure="
  if parts.length < 2 then return none
  let d := String.ofList ((parts[1]!).toList.takeWhile Char.isDigit)
  if d.isEmpty then none else d.toNat?

/-- `(D=\d+ .*)$`: from the first `D=<digit>` to the end of the line. -/
def census? (line : String) : Option String := Id.run do
  let cs := line.toList.toArray
  for i in [0:cs.size] do
    if cs[i]! == 'D' && i + 2 < cs.size && cs[i+1]! == '=' && (cs[i+2]!).isDigit then
      return some (String.ofList (cs.extract i cs.size).toList)
  return none

#guard closure? "WIDE closure=931 D=4 S=0 R=0 T=27 capstonesInT=2 rawElim=11" == some 931
#guard census? "WIDE closure=931 D=4 S=0 R=0 T=27 capstonesInT=2 rawElim=11" == some "D=4 S=0 R=0 T=27 capstonesInT=2 rawElim=11"
#guard census? "WIDE-DIRECT [a, b]" == none

/-- `int(line.split("decls=")[1].split()[0])`. -/
def declsOf (line : String) : Nat :=
  match line.splitOn "decls=" with
  | _ :: rest :: _ => ((rest.splitOn " ").head!).toNat?.getD 0
  | _ => 0

#guard declsOf "MOD Tests.Foo decls=17 dropRefs=0" == 17

def wideLine (closure imported excluded readable unreadable decls hits : Nat) : String :=
  s!"closure={closure} imported={imported} excluded={excluded} readable={readable} unreadable={unreadable} excludedDecls={decls} excludedDropRefs={hits}"

/-- Lean's string gap: `\` followed by whitespace that contains a newline is dropped,
    whitespace included (the Python's `re.sub(r"\\\s*\n\s*", "", …)`). -/
def ungap (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  while i < cs.size do
    if cs[i]! == '\\' then
      let mut j := i + 1
      while j < cs.size && isWs cs[j]! do j := j + 1
      if (cs.extract (i + 1) j).any (· == '\n') then i := j
      else out := out.push cs[i]!; i := i + 1
    else out := out.push cs[i]!; i := i + 1
  return String.ofList out.toList

#guard ungap "closure=883 \\\nexcludedDecls=603" == "closure=883 excludedDecls=603"
#guard ungap "a \\  \n   b" == "a b"
#guard ungap "a \\n b" == "a \\n b"

/-- The literal of `def NAME : String :=` whose body lines are `body` (the `"…"` may span
    lines through a string gap): the text between the first two double quotes, ungapped. -/
def pinLiteral? (body : String) : Option String := do
  let cs := body.toList
  let afterOpen := (cs.dropWhile (· != '"')).drop 1
  if afterOpen.isEmpty && !(cs.any (· == '"')) then none
  let lit := afterOpen.takeWhile (· != '"')
  if (afterOpen.drop lit.length).isEmpty then none
  return ungap (String.ofList lit)

#guard pinLiteral? "  \"closure=883 imported=879 \\\nexcludedDecls=603\"\n" == some "closure=883 imported=879 excludedDecls=603"
#guard pinLiteral? "  42\n" == none

/-- The literal of a `def NAME : String :=` span: `same` is the rest of the definition line
    after `:=` (a short pin, as `scripts-repin` writes one), `body` the lines below it after
    the dated notes (a long pin, through its string gap).  Either layout reads. -/
def pinOfSpan? (same body : String) : Option String :=
  pinLiteral? (same ++ "\n" ++ body)

#guard pinOfSpan? "\"D=4 S=0 R=0 T=27 capstonesInT=2 rawElim=11\"" "" == some "D=4 S=0 R=0 T=27 capstonesInT=2 rawElim=11"
#guard pinOfSpan? "" "  \"closure=883 imported=879 \\\n excludedDecls=603 excludedDropRefs=0\"\n" == some "closure=883 imported=879 excludedDecls=603 excludedDropRefs=0"
#guard pinOfSpan? "" "" == none

def dropConst : String := "`L4YAML.Surface.SLYamlStream.scannerDrop"

/-- The wide walk, appended to the `import` list (the Python's `WALK_BODY`). -/
def walkBody : String :=
"
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let c ← Tests.Guards.DropDependents.census
  logInfo m!\"WIDE closure={c.closureModules} {Tests.Guards.DropDependents.render c}\"
  logInfo m!\"WIDE-DIRECT {c.direct}\"
  logInfo m!\"WIDE-TRANS {c.trans}\"
  logInfo m!\"WIDE-RAWELIM {c.rawElim}\"
"

/-- One entry point probed against its own closure (the Python's `ONE`). -/
def probeBody (mod : String) : String :=
"
open Lean
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let target := (`" ++ mod ++ " : Name)
  let mut hits : Nat := 0
  let mut decls : Nat := 0
  for (n, ci) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | none => pure ()
    | some i =>
      if env.header.moduleNames[i.toNat]! == target then
        decls := decls + 1
        let v := (ci.value? (allowOpaque := true)).getD ci.type
        if (v.getUsedConstants ++ ci.type.getUsedConstants).any
             (· == " ++ dropConst ++ ") then
          hits := hits + 1
          logInfo m!\"HIT {n}\"
  logInfo m!\"MOD " ++ mod ++ " decls={decls} dropRefs={hits}\"
"

#guard ((probeBody "Tests.Foo").splitOn "logInfo m!\"MOD Tests.Foo decls={decls} dropRefs={hits}\"").length == 2

end

end Scripts.Drop.Sweep
