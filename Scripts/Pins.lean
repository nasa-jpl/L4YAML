module

@[expose] public section Blanket

/-!
# Scripts.Pins — `def expected… :=` pins and the build log that moves them

The port of `scripts/repin.py` (plan `Blueprint/09-scripts-in-lean.md` §3
phase 2.1).  Every guard under `Tests/Guards/Proofs/` pins what its census
counted as a literal (`String`, `Nat`, `List String`, `List Name`) and
throws `"<title>.\nexpected: {expectedFoo}\ngot:      {got}"` when the tree
moves.  This reads one `lake build` log, finds each `expected:`/`got:`
block, locates the `throwError` whose message title matches, and rewrites
the named `def expected… : T :=` to what the build reported.

One run is a FLOOR: a guard that throws on its first check never reaches
its later ones, and a failing module blocks its dependents.  Rebuild and
re-run until the log reports no moved pin.  Then read every change — a pin
is a decision, and the script only does the typing.

A pin whose literal carries comments between or after its entries is
reported `skipped` and left for a hand edit.  The `got:` line is Lean's
`toString`, so a `List String` prints as `[a, b]` without quotes: elements
are split on `, `; an element that itself contains `, ` is re-glued only
when the OLD list had an element with the same prefix, and the result is
flagged `CHECK` either way.

Hand parsers for the Python's `ERR_HEAD`, `NEXT_BLOCK`, `THROW`, `DEF`
regexes (plan §6 Q1: no regex dependency), each with its `#guard` rows.
-/

namespace Scripts.Pins

def isAsciiWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c' || c == '\x0b'

def pyStrip (s : String) : String :=
  String.ofList ((s.toList.dropWhile isAsciiWs).reverse.dropWhile isAsciiWs |>.reverse)

def pyRstrip (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile isAsciiWs |>.reverse)

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- `\S+\.lean:\d+:\d+:` at the head of `s`, path greedy: `(path, line, col, rest)`. -/
def locHead? (s : String) : Option (String × Nat × Nat × String) := Id.run do
  let cs := s.toList
  let mut best : Option (String × Nat × Nat × String) := none
  let mut pre : List Char := []
  let mut rest := cs
  while !rest.isEmpty do
    if String.ofList (rest.take 6) == ".lean:" then
      let path := String.ofList (pre.reverse ++ ".lean".toList)
      if !path.isEmpty && !path.any isAsciiWs then
        let after := rest.drop 6
        let (d1, r1) := after.span Char.isDigit
        if !d1.isEmpty then
          match r1 with
          | ':' :: r2 =>
            let (d2, r3) := r2.span Char.isDigit
            if !d2.isEmpty then
              match r3 with
              | ':' :: r4 => best := some (path, (String.ofList d1).toNat!, (String.ofList d2).toNat!, String.ofList r4)
              | _ => pure ()
          | _ => pure ()
    match rest with
    | c :: r => pre := c :: pre; rest := r
    | [] => pure ()
  return best

/-- `ERR_HEAD`: `^(?:error: )?(\S+\.lean):(\d+):(\d+):(?: error:)? ?(.*)$` on the
raw line → `(file, line, body)`. -/
def errHead? (line : String) : Option (String × Nat × String) := do
  let s := if line.startsWith "error: " then String.ofList (line.toList.drop 7) else line
  let (f, l, _, r) ← locHead? s
  let r := if r.startsWith " error:" then String.ofList (r.toList.drop 7) else r
  let r := if r.startsWith " " then String.ofList (r.toList.drop 1) else r
  return (f, l, r)

#guard errHead? "error: Tests/Guards/Proofs/FreeSurfaceCensus.lean:230:4: the census's own import closure moved."
  == some ("Tests/Guards/Proofs/FreeSurfaceCensus.lean", 230, "the census's own import closure moved.")
#guard errHead? "Tests/G.lean:230:4: error: the free surface moved." == some ("Tests/G.lean", 230, "the free surface moved.")
#guard errHead? "Tests/G.lean:230:4: warning: unused" == some ("Tests/G.lean", 230, "warning: unused")
#guard errHead? "Tests/G.lean:230:4:" == some ("Tests/G.lean", 230, "")
#guard errHead? "  Tests/G.lean:230:4: error: x" == none
#guard errHead? "✖ [10/13] Building X (443ms)" == none
#guard errHead? "expected: modulesSeen=267" == none

/-- `NEXT_BLOCK`: the start of another log record. -/
def isNextBlock (line : String) : Bool :=
  (locHead? line).isSome || line.startsWith "error: " || line.startsWith "warning: " ||
  line.startsWith "info: " || line.startsWith "✖" || line.startsWith "⚠" || line.startsWith "✔" ||
  line.startsWith "Build " || line.startsWith "trace: " ||
  (match line.toList with
   | '[' :: rest =>
     let (d1, r1) := rest.span Char.isDigit
     !d1.isEmpty && (match r1 with
       | '/' :: r2 => let (d2, r3) := r2.span Char.isDigit; !d2.isEmpty && r3.head? == some ']'
       | _ => false)
   | _ => false)

#guard isNextBlock "✔ [1341/1342] Built Tests.Guards (1.2s)"
#guard isNextBlock "[12/40] Building X"
#guard isNextBlock "Build completed successfully (1349 jobs)."
#guard isNextBlock "info: L4YAML/X.lean:1:0: 'foo' depends on axioms: [propext]"
#guard !isNextBlock "expected: modulesSeen=267"
#guard !isNextBlock "got:      modulesSeen=268"
#guard !isNextBlock ""

/-- Python `str.splitlines()` for the shapes a lake log carries: `\n`-split, a
trailing `\r` dropped, no last empty line after a final newline. -/
def pySplitLines (s : String) : Array String :=
  let parts := ((s.splitOn "\n").map fun l => if l.endsWith "\r" then String.ofList l.toList.dropLast else l).toArray
  if parts.size > 0 && parts.back! == "" then parts.pop else parts

#guard pySplitLines "a\nb\n" == #["a", "b"]
#guard pySplitLines "a\r\nb" == #["a", "b"]
#guard pySplitLines "" == #[]

/-- `read_blocks`: `(file, line, body lines)` for each `ERR_HEAD` in the log. -/
def readBlocks (log : String) : Array (String × Nat × Array String) := Id.run do
  let lines := pySplitLines log
  let mut out : Array (String × Nat × Array String) := #[]
  let mut i := 0
  while i < lines.size do
    match errHead? lines[i]! with
    | none => i := i + 1
    | some (f, l, b0) =>
      let mut body := #[b0]
      i := i + 1
      while i < lines.size && !isNextBlock lines[i]! && (errHead? lines[i]!).isNone do
        body := body.push lines[i]!
        i := i + 1
      out := out.push (f, l, body)
  return out

#guard readBlocks "✖ [1/2] Building X\nerror: T/G.lean:230:4: the surface moved.\nexpected: a\ngot:      b\n  more\n✔ [2/2] Built Y\n"
  == #[("T/G.lean", 230, #["the surface moved.", "expected: a", "got:      b", "  more"])]
#guard readBlocks "T/A.lean:1:0: error: one\nT/B.lean:2:0: error: two\n" == #[("T/A.lean", 1, #["one"]), ("T/B.lean", 2, #["two"])]

/-! ## `throwError "…"` literals -/

/-- `THROW`: every `throwError\s+"…"` literal body (escapes kept), in order. -/
def throwLiterals (src : String) : List String := Id.run do
  let cs := src.toList
  let mut out : Array String := #[]
  let mut rest := cs
  let key := "throwError".toList
  while !rest.isEmpty do
    if rest.take key.length == key then
      let after := rest.drop key.length
      let ws := after.takeWhile isAsciiWs
      let after' := after.drop ws.length
      match after' with
      | '"' :: body =>
        if !ws.isEmpty then
          -- read to the unescaped closing quote
          let mut acc : Array Char := #[]
          let mut r := body
          let mut closed := false
          while !r.isEmpty && !closed do
            match r with
            | '\\' :: d :: r' => acc := acc.push '\\' |>.push d; r := r'
            | '"' :: r' => closed := true; r := r'
            | c :: r' => acc := acc.push c; r := r'
            | [] => pure ()
          if closed then
            out := out.push (String.ofList acc.toList)
            rest := r
          else rest := after
        else rest := after
      | _ => rest := after
    else
      rest := rest.drop 1
  return out.toList

#guard throwLiterals "  throwError \"the free surface moved.\\nexpected: {expectedCensus}\\ngot:      {got}\\n\\\n      read it\"\n  throwError s!\"x\"\n  throwError \"second\""
  == ["the free surface moved.\\nexpected: {expectedCensus}\\ngot:      {got}\\n\\\n      read it", "second"]
#guard throwLiterals "throwError\"no space\"" == []
#guard throwLiterals "throwError \"a \\\"quoted\\\" word\"" == ["a \\\"quoted\\\" word"]

/-- `normalise_literal`: drop `\`⏎ and the indentation after it, then `\n` → newline, `\"` → `"`. -/
partial def normaliseLiteralGo : List Char → List Char
    | '\\' :: '\n' :: rest => normaliseLiteralGo (rest.dropWhile isAsciiWs)
    | '\\' :: 'n' :: rest => '\n' :: normaliseLiteralGo rest
    | '\\' :: '"' :: rest => '"' :: normaliseLiteralGo rest
    | c :: rest => c :: normaliseLiteralGo rest
    | [] => []

def normaliseLiteral (s : String) : String := String.ofList (normaliseLiteralGo s.toList)

#guard normaliseLiteral "a.\\nexpected: {x}\\ngot: {y}\\n\\\n      tail" == "a.\nexpected: {x}\ngot: {y}\ntail"
#guard normaliseLiteral "say \\\"hi\\\"" == "say \"hi\""

/-- `expected:\s*\{([\w.]+)\}` → the identifier. -/
def expectedName? (lit : String) : Option String := Id.run do
  let mut rest := lit.toList
  let key := "expected:".toList
  while !rest.isEmpty do
    if rest.take key.length == key then
      let after := (rest.drop key.length).dropWhile isAsciiWs
      match after with
      | '{' :: r =>
        let name := r.takeWhile fun c => isWordChar c || c == '.'
        if !name.isEmpty && (r.drop name.length).head? == some '}' then
          return some (String.ofList name)
      | _ => pure ()
    rest := rest.drop 1
  return none

#guard expectedName? "the free surface moved.\nexpected: {expectedCensus}\ngot:      {got}" == some "expectedCensus"
#guard expectedName? "x\nexpected:   {Foo.bar}\n" == some "Foo.bar"
#guard expectedName? "expected: {a b}" == none
#guard expectedName? "no pin here" == none

/-- `pin_name_for`: the `expected…` identifiers of the throw literals whose
first line (normalised, stripped) equals `title.strip()`. -/
def pinNamesFor (src title : String) : List String :=
  (throwLiterals src).filterMap fun m =>
    let lit := normaliseLiteral m
    let first := (lit.splitOn "\n").headD ""
    if pyStrip first != pyStrip title then none else expectedName? lit

#guard pinNamesFor "throwError \"the free surface moved.\\nexpected: {expectedCensus}\\ngot: {g}\"\nthrowError \"other.\\nexpected: {expectedOther}\"" "the free surface moved."
  == ["expectedCensus"]
#guard pinNamesFor "throwError \"the free surface moved.\\nexpected: {expectedCensus}\"" "nope" == []

/-! ## Rendering the new literal -/

/-- `old_list_items`: the double-quoted bodies in the old literal, else the backquoted names. -/
def oldListItems (body : String) : List String := Id.run do
  let cs := body.toList
  let mut strs : Array String := #[]
  let mut r := cs
  while !r.isEmpty do
    match r with
    | '"' :: rest =>
      let mut acc : Array Char := #[]
      let mut rr := rest
      let mut closed := false
      while !rr.isEmpty && !closed do
        match rr with
        | '\\' :: d :: rr' => acc := acc.push '\\' |>.push d; rr := rr'
        | '"' :: rr' => closed := true; rr := rr'
        | c :: rr' => acc := acc.push c; rr := rr'
        | [] => pure ()
      if closed then strs := strs.push (String.ofList acc.toList); r := rr
      else r := rest
    | _ :: rest => r := rest
    | [] => pure ()
  if !strs.isEmpty then return strs.toList
  -- `([\w.«»']+)
  let mut names : Array String := #[]
  r := cs
  while !r.isEmpty do
    match r with
    | '`' :: rest =>
      let n := rest.takeWhile fun c => isWordChar c || c == '.' || c == '«' || c == '»' || c == '\''
      if !n.isEmpty then names := names.push (String.ofList n)
      r := rest.drop n.length
    | _ :: rest => r := rest
    | [] => pure ()
  return names.toList

#guard oldListItems "[\"a, b\",\n   \"c\"]" == ["a, b", "c"]
#guard oldListItems "[`L4YAML.Output.Events, `L4YAML.Output.Json]" == ["L4YAML.Output.Events", "L4YAML.Output.Json"]
#guard oldListItems "[]" == []

/-- `split_list(inner, old_items)` → `(items, flagged)`. -/
def splitList (inner : String) (old : List String) : List String × Bool := Id.run do
  if pyStrip inner == "" then return ([], false)
  let raw := (inner.splitOn ", ").toArray
  let mut out : Array String := #[]
  let mut flagged := false
  let mut i := 0
  while i < raw.size do
    let mut glued := raw[i]!
    let mut j := i
    while !old.contains glued && j + 1 < raw.size && old.any (·.startsWith (glued ++ ", ")) do
      j := j + 1
      glued := glued ++ ", " ++ raw[j]!
      flagged := true
    if (glued.splitOn ", ").length > 1 || old.any (fun o => (o.splitOn ", ").length > 1) then
      flagged := true
    out := out.push glued
    i := j + 1
  return (out.toList, flagged)

#guard splitList "a, b, c" [] == (["a", "b", "c"], false)
#guard splitList "a, b, c" ["a, b"] == (["a, b", "c"], true)
#guard splitList "a, b" ["x, y"] == (["a", "b"], true)
#guard splitList "  " ["a"] == ([], false)

/-- `lean_str`: backslash and quote escaped. -/
def leanStr (x : String) : String :=
  String.ofList (x.toList.flatMap fun c => if c == '\\' then ['\\', '\\'] else if c == '"' then ['\\', '"'] else [c])

#guard leanStr "a\"b\\c" == "a\\\"b\\\\c"

/-- `render(ty, value, old_body)` → `(text after :=, flagged)`; `none` for a
non-list where a list is needed (Python's `ValueError`). -/
def render (ty value oldBody : String) : Option (String × Bool) :=
  if ty == "Nat" then some (" " ++ pyStrip value, false)
  else if ty == "String" then
    let v := leanStr (pyRstrip value)
    if v.length ≤ 60 then some (s!" \"{v}\"", false)
    else
      -- wrap at 76 on single spaces (Python's split(" "): empties kept)
      let words := v.splitOn " "
      let (lines, cur) := words.foldl (fun (acc : List String × String) w =>
        let (ls, cur) := acc
        if !cur.isEmpty && cur.length + 1 + w.length > 76 then (ls ++ [cur], w)
        else (ls, if cur.isEmpty then w else cur ++ " " ++ w)) ([], "")
      let all := lines ++ [cur]
      some ("\n  \"" ++ " \\\n".intercalate all ++ "\"", false)
  else
    let v := pyStrip value
    if !(v.startsWith "[" && v.endsWith "]") then none
    else
      let inner := String.ofList (v.toList.drop 1 |>.dropLast)
      let (items, flagged) := splitList inner (oldListItems oldBody)
      let items := if ty == "List String" then items.map (fun x => s!"\"{leanStr x}\"") else items.map (fun x => s!"`{x}")
      if items.isEmpty then some (" []", flagged)
      else match items with
        | [one] => if one.length < 70 then some (s!" [{one}]", flagged) else some ("\n  [" ++ ",\n   ".intercalate items ++ "]", flagged)
        | _ => some ("\n  [" ++ ",\n   ".intercalate items ++ "]", flagged)

#guard render "Nat" " 273 " "" == some (" 273", false)
#guard render "String" "modulesSeen=268" "" == some (" \"modulesSeen=268\"", false)
#guard render "List String" "[a, b]" "[\"a\", \"x\"]" == some ("\n  [\"a\",\n   \"b\"]", false)
#guard render "List String" "[a]" "" == some (" [\"a\"]", false)
#guard render "List Name" "[L4YAML.A, L4YAML.B]" "" == some ("\n  [`L4YAML.A,\n   `L4YAML.B]", false)
#guard render "List String" "[]" "" == some (" []", false)
#guard render "List String" "not a list" "" == none
#guard (render "String" (String.ofList (List.replicate 30 'a') ++ " " ++ String.ofList (List.replicate 50 'b') ++ " c") "").map (·.1)
  == some ("\n  \"" ++ String.ofList (List.replicate 30 'a') ++ " \\\n" ++ String.ofList (List.replicate 50 'b') ++ " c\"")

/-! ## The `def expected… : T :=` span -/

structure DefHead where
  head : String      -- the text up to and including `:=`
  name : String
  ty : String
  same : String      -- the rest of the line after `:=` and blanks
  deriving DecidableEq, Repr, Inhabited

/-- `DEF`: `^(?:private |protected )?def (\w+)\s*:\s*(String|Nat|List String|List Name)\s*:=[ \t]*(.*)$`. -/
def defHead? (line : String) : Option DefHead := do
  let cs := line.toList
  let (pre, r0) :=
    if line.startsWith "private def " then ("private def ".toList, cs.drop 12)
    else if line.startsWith "protected def " then ("protected def ".toList, cs.drop 14)
    else if line.startsWith "def " then ("def ".toList, cs.drop 4)
    else ([], [])
  if pre.isEmpty then none else
  let name := r0.takeWhile isWordChar
  if name.isEmpty then none else
  let r1 := (r0.drop name.length).dropWhile isAsciiWs
  match r1 with
  | ':' :: r2 =>
    let r2' := r2.dropWhile isAsciiWs
    let ty ← ["List String", "List Name", "String", "Nat"].find? fun (t : String) => (String.ofList r2').startsWith t
    let r3 := (r2'.drop ty.length).dropWhile isAsciiWs
    match r3 with
    | ':' :: '=' :: r4 =>
      let same := r4.dropWhile (fun c => c == ' ' || c == '\t')
      let headLen := cs.length - r4.length
      return { head := String.ofList (cs.take headLen), name := String.ofList name, ty, same := String.ofList same }
    | _ => none
  | _ => none

#guard defHead? "def expectedClosure : String := \"modulesSeen=268\"" ==
  some ⟨"def expectedClosure : String :=", "expectedClosure", "String", "\"modulesSeen=268\""⟩
#guard defHead? "def expectedClosure : Nat := 274  -- +1: x" == some ⟨"def expectedClosure : Nat :=", "expectedClosure", "Nat", "274  -- +1: x"⟩
#guard defHead? "def expectedFree : List String :=" == some ⟨"def expectedFree : List String :=", "expectedFree", "List String", ""⟩
#guard defHead? "private def expectedNames : List Name :=" == some ⟨"private def expectedNames : List Name :=", "expectedNames", "List Name", ""⟩
#guard defHead? "def expectedX : List Nat := [1]" == none
#guard defHead? "  def indented : Nat := 1" == none
#guard defHead? "theorem expectedX : Nat := 1" == none

structure Span where
  start : Nat           -- index of the def line
  stop : Nat            -- exclusive end of the body
  head : DefHead
  comments : Array String
  annotated : Bool
  deriving Repr, Inhabited

/-- `def_span(lines, name)`. -/
def defSpan (lines : Array String) (name : String) : Option Span := Id.run do
  for i in [0:lines.size] do
    match defHead? lines[i]! with
    | some h =>
      if h.name != name then continue
      let mut j := i + 1
      while j < lines.size &&
          (pyStrip lines[j]! == "" || (lines[j]!.toList.head?.any fun c => c == ' ' || c == '\t') ||
           (pyRstrip lines[j-1]!).endsWith "\\") do
        j := j + 1
      while j > i + 1 && pyStrip lines[j-1]! == "" do
        j := j - 1
      let mut comments : Array String := #[]
      let mut k := i + 1
      while k < j && (pyStrip lines[k]!).startsWith "--" do
        comments := comments.push lines[k]!
        k := k + 1
      let annotated := (List.range (j - (i + 1 + comments.size))).any fun d =>
        ((lines[i + 1 + comments.size + d]!).splitOn "--").length > 1
      return some { start := i, stop := j, head := h, comments, annotated }
    | none => continue
  return none

def exampleSrc : Array String := #[
  "import X",
  "",
  "def expectedFree : List String :=",
  "  [\"a\",",
  "   \"b\"]",
  "-- 265 → 266 on 2026-10-28: note",
  "",
  "def expectedClosure : String := \"modulesSeen=268\"",
  "-- 265 → 266 note",
  "",
  "def expectedN : Nat :=",
  "  -- leading comment",
  "  274",
  "",
  "def expectedAnnotated : List String :=",
  "  [\"a\", -- why",
  "   \"b\"]",
  "end"]

#guard (defSpan exampleSrc "expectedFree").map (fun s => (s.start, s.stop, s.comments.size, s.annotated)) == some (2, 5, 0, false)
#guard (defSpan exampleSrc "expectedClosure").map (fun s => (s.start, s.stop, s.comments.size, s.annotated)) == some (7, 8, 0, false)
#guard (defSpan exampleSrc "expectedN").map (fun s => (s.start, s.stop, s.comments.size, s.annotated)) == some (10, 13, 1, false)
#guard (defSpan exampleSrc "expectedAnnotated").map (fun s => (s.start, s.stop, s.comments.size, s.annotated)) == some (14, 17, 0, true)
#guard (defSpan exampleSrc "missing").isNone

/-- `^expected:\s*(.*)$` / `^got:\s*(.*)$` with re.M over the joined body. -/
def fieldAfter? (key : String) (msg : String) : Option String := Id.run do
  let lines := msg.splitOn "\n"
  -- the regex may start on any line; `\s*` may cross newlines, `.*` runs to the line end
  let text := msg.toList
  let mut rest := text
  let mut atLineStart := true
  let k := key.toList
  while !rest.isEmpty do
    if atLineStart && rest.take k.length == k then
      let after := (rest.drop k.length).dropWhile isAsciiWs
      return some (String.ofList (after.takeWhile (· != '\n')))
    match rest with
    | c :: r => atLineStart := c == '\n'; rest := r
    | [] => pure ()
  let _ := lines
  return none

#guard fieldAfter? "expected:" "title.\nexpected: modulesSeen=267\ngot:      modulesSeen=268" == some "modulesSeen=267"
#guard fieldAfter? "got:" "title.\nexpected: modulesSeen=267\ngot:      modulesSeen=268" == some "modulesSeen=268"
#guard fieldAfter? "got:" "title.\nexpected: a\n" == none
#guard fieldAfter? "expected:" "not expected: x" == none

/-- Splice the new literal into the file's lines (`new_block`), returning the
new lines.  Mirrors the Python's two shapes: with leading comments the head
stays on its own line and the literal follows them; otherwise head and
literal share the Python's `(head + new_text).split("\n")`. -/
def splice (lines : Array String) (sp : Span) (newText : String) : Array String :=
  let block : List String :=
    if !sp.comments.isEmpty then
      let lit := (String.ofList (newText.toList.dropWhile (· == '\n'))).splitOn "\n"
      let lit := if !newText.startsWith "\n" then
          -- Python: new_block[-1] = "  " + new_block[-1].strip()
          match lit.reverse with
          | last :: rest => (("  " ++ pyStrip last) :: rest).reverse
          | [] => []
        else lit
      [sp.head.head] ++ sp.comments.toList ++ lit
    else (sp.head.head ++ newText).splitOn "\n"
  (lines.extract 0 sp.start) ++ block.toArray ++ (lines.extract sp.stop lines.size)

#guard (splice exampleSrc { start := 7, stop := 9, head := (defHead? exampleSrc[7]!).get!, comments := #["-- 265 → 266 note"], annotated := false } " \"modulesSeen=269\"").extract 7 10 == #["def expectedClosure : String :=", "-- 265 → 266 note", "  \"modulesSeen=269\""]
#guard (splice exampleSrc { start := 10, stop := 13, head := (defHead? exampleSrc[10]!).get!, comments := #["  -- leading comment"], annotated := false } " 275").extract 10 13 == #["def expectedN : Nat :=", "  -- leading comment", "  275"]
#guard (splice exampleSrc { start := 2, stop := 5, head := (defHead? exampleSrc[2]!).get!, comments := #[], annotated := false } "\n  [\"a\",\n   \"c\"]").extract 2 6
  == #["def expectedFree : List String :=", "  [\"a\",", "   \"c\"]", "-- 265 → 266 on 2026-10-28: note"]

end Scripts.Pins
