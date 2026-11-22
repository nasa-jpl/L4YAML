module

public import Scripts.Flip.Patch

/-!
# β.5's edit, its fixpoint and its dead arms — the readings (Rule 9, item 3.2b)

The pure half of `lake run flip-beta5` / `lake run beta5-arms`, ported from
`scripts/flip_beta5.py` (DOCS item 263), `scripts/beta5_arms.py` (item 264)
and the error-location mapper of `scripts/flip_210.py` (item 230):

* **the edit** — retire `PendingNode.pendingFlow` (constructor, docstring and
  `close_with_ssl`'s arm, `flip_supplier.py --end retire`), delete
  `SLYamlStream.scannerDrop` (arm and docstring, `flip_drop.py`), delete
  `dropClose`; every anchor is content, matched exactly once or refused;
* **the fixpoint round** — each error location of a build, classified against
  the round's own text: `SORRIED` (the proof replaced, the statement
  byte-identical), `RESTATEMENT` (the error is at or above the `:=`),
  `DELETED` (a `Tests/` data definition naming the deletion, neutralized with
  its docstring), `REFUSED` (a library data definition), `PIN MOVED` (a
  top-level command, neutralized), or unmappable — patches applied bottom-up;
* **the dead arms** — eight content-anchored blocks, each span computed
  structurally and refused when it would swallow a sibling arm;
* **the lines** — `FIXLINE …`, `ARMLINE …`, the pins read out of
  `Tests/Guards/Proofs/ParkBill.lean`.

Everything here is a function of strings; `Scripts/Main/Beta5.lean` does the
writing, building and restoring.  The regexes of the Python are hand scanners
with `#guard` rows beside them.
-/

namespace Scripts.Flip.Beta5

public section

def acc : String := "L4YAML/Proofs/Production/StreamAccum.lean"
def doc : String := "L4YAML/Surface/Document.lean"
def pinFile : String := "Tests/Guards/Proofs/ParkBill.lean"

/-! ## String helpers -/

/-- Split `s` at the first occurrence of `pat`: `(before, after)`. -/
def findSplit (s pat : String) : Option (String × String) :=
  match s.splitOn pat with
  | [] | [_] => none
  | p :: rest => some (p, pat.intercalate rest)

#guard findSplit "abcabc" "ca" == some ("ab", "bc")
#guard findSplit "abc" "x" == none

def countNewlines (s : String) : Nat := s.foldl (fun n c => if c == '\n' then n + 1 else n) 0

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

def startsWithL (cs : List Char) (s : String) : Bool := s.toList.isPrefixOf cs

/-- `\b` after a keyword that is a prefix of `cs`: the next char is not a word char. -/
def wordAt (cs : List Char) (w : String) : Bool :=
  startsWithL cs w && (match cs.drop w.length with | [] => true | c :: _ => !isWordChar c)

def rstrip (s : String) : String := String.ofList (s.toList.reverse.dropWhile Char.isWhitespace).reverse
def lstrip (s : String) : String := String.ofList (s.toList.dropWhile Char.isWhitespace)
def isBlank (s : String) : Bool := s.toList.all Char.isWhitespace

/-! ## Declaration heads, terminators, modifiers -/

/-- The head keywords of `flip_beta5.HEAD` (`flip_210.DECL_HEAD` plus `example`). -/
def headKeywords : List String :=
  ["lemma", "theorem", "def", "abbrev", "instance", "structure", "inductive", "example"]

/-- `(?:private |protected |@\[[^\]]*\]\s*)*`. -/
partial def dropHeadModifiers (cs : List Char) : List Char :=
  if startsWithL cs "private " then dropHeadModifiers (cs.drop 8)
  else if startsWithL cs "protected " then dropHeadModifiers (cs.drop 10)
  else match cs with
    | '@' :: '[' :: rest =>
      match rest.dropWhile (· != ']') with
      | ']' :: r => dropHeadModifiers (r.dropWhile Char.isWhitespace)
      | _ => cs
    | _ => cs

def isNameStart (c : Char) : Bool := c.isAlpha || c == '_'
def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || c == '.'

/-- `HEAD`: `(kw, name?)` when the line (column 0) opens a declaration; `example`
    counts, as do keywords whose name is absent (`instance : Foo`). -/
def headOf (line : String) : Option (String × Option String) := do
  let cs := dropHeadModifiers line.toList
  let kw ← headKeywords.find? fun k =>
    startsWithL cs k &&
      (match cs.drop k.length with
       | ' ' :: _ => true
       | [] => true
       | c :: _ => !isWordChar c)
  match cs.drop kw.length with
  | ' ' :: c :: rest =>
    if isNameStart c then some (kw, some (String.ofList (c :: rest.takeWhile isNameChar)))
    else some (kw, none)
  | _ => some (kw, none)

#guard headOf "lemma foo.bar' (x : Nat) : True := by" == some ("lemma", some "foo.bar'")
#guard headOf "@[simp] lemma x_eq : x = x := rfl" == some ("lemma", some "x_eq")
#guard headOf "private def go : Nat → Nat" == some ("def", some "go")
#guard headOf "@[simp]  protected theorem T.x : True := trivial" == some ("theorem", some "T.x")
#guard headOf "example : 1 = 1 := rfl" == some ("example", none)
#guard headOf "instance : Inhabited Foo := ⟨x⟩" == some ("instance", none)
#guard headOf "  lemma indented : True := trivial" == none
#guard headOf "definition x" == none
#guard headOf "deriving instance Repr for Foo" == none
#guard headOf "noncomputable def x := 1" == none      -- not one of HEAD's modifiers
#guard headOf "@[simp lemma x : True := trivial" == none

/-- Python's keyword of a head line: `split()[0].lstrip("@[")`, then the next
    word after `private`/`protected`/`noncomputable`.  Kept for the printed
    keyword only where it agrees with `headOf`; see `declSpan`. -/
def terminatorWords : List String :=
  ["end", "namespace", "section", "open", "variable", "attribute", "run_cmd", "set_option",
   "private", "protected", "noncomputable", "lemma", "theorem", "def", "abbrev", "instance",
   "structure", "inductive", "example", "macro", "syntax", "elab", "deriving", "import"]

/-- `TERMINATOR`: a column-0 line that opens a new top-level form. -/
def isTerminator (line : String) : Bool :=
  let cs := line.toList
  startsWithL cs "/--" || startsWithL cs "/-!" || startsWithL cs "--" || startsWithL cs "@[" ||
    startsWithL cs "#" || terminatorWords.any (wordAt cs ·)

#guard isTerminator "lemma x : True := trivial"
#guard isTerminator "/-- doc -/"
#guard isTerminator "---"
#guard isTerminator "#guard x"
#guard isTerminator "end Foo"
#guard isTerminator "endpoint x" == false
#guard isTerminator "  | a => b" == false
#guard isTerminator "" == false

def modifierWords : List String :=
  ["open", "set_option", "attribute", "variable", "universe", "local", "scoped", "private",
   "protected", "noncomputable"]

/-- `MODIFIER`: a top-level form ending in `in`, which binds to the command below it. -/
def isModifier (line : String) : Bool :=
  let cs := line.toList
  let opens := modifierWords.any (wordAt cs ·) ||
    (match cs with | '@' :: '[' :: c :: _ => isWordChar c | _ => false)
  let t := (rstrip line).toList
  opens && t.length ≥ 3 && t.reverse.take 2 == ['n', 'i'] && !isWordChar t.reverse[2]!

#guard isModifier "open Foo in"
#guard isModifier "set_option maxHeartbeats 400000 in  "
#guard isModifier "attribute [local simp] foo in"
#guard isModifier "open Foo" == false
#guard isModifier "lemma main : True := by" == false
#guard isModifier "@[simp] theorem foo_in" == false

/-! ## Literals, brackets, the `:=` of a declaration -/

def isIdentPrev (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

partial def closeString (cs : Array Char) (j : Nat) : Option Nat :=
  if h : j < cs.size then
    if cs[j] == '\\' then closeString cs (j + 2)
    else if cs[j] == '"' then some j
    else closeString cs (j + 1)
  else none

/-- `LITERAL.sub("", line)`: string literals and character literals (not the
    prime of an identifier) removed, left to right. -/
partial def stripLiterals (cs : Array Char) : Array Char := go 0 #[]
where
  go (i : Nat) (out : Array Char) : Array Char :=
    if h : i < cs.size then
      let c := cs[i]
      if c == '"' then
        match closeString cs (i + 1) with
        | some j => go (j + 1) out
        | none => go (i + 1) (out.push c)
      else if c == '\'' && (i == 0 || !isIdentPrev cs[i - 1]!) then
        if i + 3 < cs.size && cs[i + 1]! == '\\' && cs[i + 3]! == '\'' then go (i + 4) out
        else if i + 2 < cs.size && cs[i + 1]! != '\'' && cs[i + 1]! != '\\' && cs[i + 2]! == '\'' then
          go (i + 3) out
        else go (i + 1) (out.push c)
      else go (i + 1) (out.push c)
    else out

/-- `code_of`: the bracket-significant part of a line — literals gone, then the
    line comment. -/
def codeOf (line : String) : String :=
  let s := String.ofList (stripLiterals line.toList.toArray).toList
  match s.splitOn "--" with
  | p :: _ => p
  | [] => s

#guard codeOf "(h_c : c = '[' ∨ c = '{') : -- note (x" == "(h_c : c =  ∨ c = ) : "
#guard codeOf "  let s := \"a -- (b\" ++ s' -- c" == "  let s :=  ++ s' "
#guard codeOf "  have h : c = '\\n' := rfl" == "  have h : c =  := rfl"
#guard codeOf "  foo sp_scan' (x := 1)" == "  foo sp_scan' (x := 1)"
#guard codeOf "  x = \"unclosed" == "  x = \"unclosed"

/-- `body_start`: the first line (from `start`, before `stop`) at whose end the
    bracket depth is zero and whose code holds `:=`. -/
def bodyStart (lines : Array String) (start stop : Nat) : Option Nat := Id.run do
  let mut depth : Int := 0
  for i in [start:min stop lines.size] do
    let code := codeOf lines[i]!
    for ch in code.toList do
      if ch == '(' || ch == '[' || ch == '{' then depth := depth + 1
      else if ch == ')' || ch == ']' || ch == '}' then depth := depth - 1
    if depth == 0 && (code.splitOn ":=").length > 1 then return some i
  return none

/-! ## Spans -/

/-- `decl_span`: `(start, stop, keyword, name)` of the declaration containing
    line `idx` (0-based; `stop` exclusive); `none` outside any declaration. -/
def declSpan (lines : Array String) (idx : Nat) : Option (Nat × Nat × String × String) := Id.run do
  if lines.isEmpty then return none
  let mut i := min idx (lines.size - 1)
  repeat
    let l := lines[i]!
    match headOf l with
    | some (kw, name) =>
      let mut stop := lines.size
      for j in [i + 1:lines.size] do
        if isTerminator lines[j]! then stop := j; break
      return some (i, stop, kw, name.getD s!"example@{i + 1}")
    | none =>
      if isTerminator l then return none
    if i == 0 then break
    i := i - 1
  return none

/-- `command_span`: the top-level command containing line `idx` — walked back
    to its head, over its `… in` modifiers and the docstring that closes
    right above it; forward to the next terminator not bound by a modifier. -/
def commandSpan (lines : Array String) (idx : Nat) : Nat × Nat := Id.run do
  let n := lines.size
  let idx := min idx (n - 1)
  let mut start := idx
  while start > 0 && !isTerminator lines[start]! do start := start - 1
  while start > 0 && isModifier lines[start - 1]! do start := start - 1
  if start > 0 && (rstrip lines[start - 1]!).endsWith "-/" then
    let mut j : Int := start - 1
    while j ≥ 0 && !(lstrip lines[j.toNat]!).startsWith "/--" do
      let l := lines[j.toNat]!
      if (headOf l).isSome || l.startsWith "/-" then j := -1; break
      j := j - 1
    if j ≥ 0 then start := j.toNat
  let mut stop := n
  let mut k := idx + 1
  while k < n do
    if isTerminator lines[k]! && !isModifier lines[k - 1]! then stop := k; break
    k := k + 1
  return (start, stop)

/-- `with_docstring`: a declaration's span extended back over its attributes,
    modifiers and docstring. -/
def withDocstring (lines : Array String) (start : Nat) : Nat := Id.run do
  let mut start := start
  while start > 0 do
    let prev := lines[start - 1]!
    if prev.startsWith "@[" || isModifier prev then start := start - 1; continue
    if (rstrip prev).endsWith "-/" then
      let mut j : Int := start - 1
      while j ≥ 0 && !(lstrip lines[j.toNat]!).startsWith "/--" do
        let l := lines[j.toNat]!
        if (headOf l).isSome || l.startsWith "/-" then j := -1; break
        j := j - 1
      if j ≥ 0 then start := j.toNat; continue
    break
  return start

def neutralizeNote : String :=
  "/- β.5 fixpoint: this census's pins move with the deletion; neutralized to reach what is behind it"

/-- `neutralize`: comment out one top-level command; refused when the span
    declares something unless `allowDecl`. -/
def neutralize (lines : Array String) (start stop : Nat) (allowDecl : Bool := false) :
    Except String (Array String) := do
  if !allowDecl then
    for l in lines.extract start stop do
      if (headOf l).isSome then
        throw s!"the span to neutralize declares something: {String.ofList (l.toList.take 80)}"
  return lines.extract 0 start ++ #[neutralizeNote] ++ lines.extract start stop ++ #["-/"] ++
    lines.extract stop lines.size

/-! ## Classification and the sorry patch -/

inductive Verdict where
  | sorried | restatement | data | nobody | unmapped
  deriving Repr, BEq, Inhabited

structure Classified where
  verdict : Verdict
  kw : String := ""
  name : String := ""
  start : Nat := 0
  stop : Nat := 0
  split : Nat := 0
  deriving Repr, BEq, Inhabited

def propKeywords : List String := ["lemma", "theorem", "example"]

/-- `classify`: the verdict for the error at 1-based `lineNo`. -/
def classify (lines : Array String) (lineNo : Nat) : Classified :=
  match declSpan lines (lineNo - 1) with
  | none => { verdict := .unmapped }
  | some (start, stop, kw, name) =>
    if !propKeywords.contains kw then { verdict := .data, kw, name, start, stop }
    else match bodyStart lines start stop with
      | none => { verdict := .nobody, kw, name, start, stop }
      | some split =>
        if lineNo - 1 < split then { verdict := .restatement, kw, name, start, stop, split }
        else { verdict := .sorried, kw, name, start, stop, split }

/-- Index of `pat` in `cs` at or after `from`. -/
def findFrom (cs : Array Char) (pat : List Char) (from_ : Nat) : Option Nat := Id.run do
  for i in [from_:cs.size] do
    if pat.isPrefixOf (cs.extract i cs.size).toList then return some i
  return none

/-- `apply_sorry`: the proof of the declaration whose `:=` line is `split`
    replaced by `sorry`, the statement byte-identical; lines `split+1..stop` go. -/
def applySorry (lines : Array String) (stop split : Nat) : Array String :=
  let head := lines[split]!
  let cs := head.toList.toArray
  let inCode := (findFrom (codeOf head).toList.toArray [':', '='] 0).getD 0
  let cut := (findFrom cs [':', '='] inCode).getD 0
  lines.extract 0 split ++ #[String.ofList (cs.extract 0 cut).toList ++ ":= sorry"] ++
    lines.extract stop lines.size

def exampleFile : Array String := #[
  "import X",                                            -- 0
  "",
  "/-- doc -/",
  "lemma foo (h : c = '(' ∨ c = \"x\") : True := by",    -- 3
  "  trivial",
  "",
  "@[simp] lemma bar (n : Nat)",                         -- 6
  "    (h : (n := 0) =",
  "      n) :",
  "    n = n := by",                                      -- 9
  "  exact h",
  "def census : Nat := 3",                               -- 11
  "",
  "/-- expected -/",                                      -- 13
  "set_option maxHeartbeats 1 in",
  "run_cmd do",                                           -- 15
  "  check 1",
  "",
  "open Foo in",                                          -- 18
  "#eval 2",
  "end"]                                                  -- 20

#guard declSpan exampleFile 4 == some (3, 6, "lemma", "foo")      -- a blank line is not a terminator
#guard declSpan exampleFile 9 == some (6, 11, "lemma", "bar")
#guard declSpan exampleFile 16 == none                      -- inside run_cmd
#guard declSpan exampleFile 1 == none
#guard bodyStart exampleFile 3 6 == some 3
#guard bodyStart exampleFile 6 11 == some 9                 -- `(n := 0)` is inside brackets at the line's end
#guard classify exampleFile 5 == { verdict := .sorried, kw := "lemma", name := "foo", start := 3, stop := 6, split := 3 }
#guard classify exampleFile 8 == { verdict := .restatement, kw := "lemma", name := "bar", start := 6, stop := 11, split := 9 }
#guard classify exampleFile 11 == { verdict := .sorried, kw := "lemma", name := "bar", start := 6, stop := 11, split := 9 }
#guard classify exampleFile 12 == { verdict := .data, kw := "def", name := "census", start := 11, stop := 13 }
#guard classify exampleFile 17 == { verdict := .unmapped }
#guard commandSpan exampleFile 16 == (13, 18)               -- docstring + `set_option … in` + run_cmd
#guard commandSpan exampleFile 19 == (18, 20)               -- `open Foo in` binds to `#eval`
#guard withDocstring exampleFile 6 == 6
#guard withDocstring exampleFile 3 == 2
#guard (applySorry exampleFile 11 9).extract 6 11 == #["@[simp] lemma bar (n : Nat)", "    (h : (n := 0) =", "      n) :", "    n = n := sorry", "def census : Nat := 3"]
#guard (applySorry exampleFile 6 3).extract 3 5 == #["lemma foo (h : c = '(' ∨ c = \"x\") : True := sorry", "@[simp] lemma bar (n : Nat)"]
#guard (neutralize exampleFile 13 18).toOption.map (·.extract 13 20) ==
  some #[neutralizeNote, "/-- expected -/", "set_option maxHeartbeats 1 in", "run_cmd do", "  check 1", "", "-/"]
#guard (neutralize exampleFile 11 13).isOk == false
#guard (neutralize exampleFile 11 13 true).isOk

/-! ## Error locations -/

/-- `ERROR_LOC`: every `error: FILE.lean:LINE:COL:` of a log, as `(FILE, LINE)`,
    distinct and sorted (file, then line). -/
def errorLocs (log : String) : List (String × Nat) :=
  let hits := (log.splitOn "error: ").drop 1 |>.filterMap fun part =>
    let cs := part.toList
    let path := cs.takeWhile fun c => c != ' ' && c != ':'
    let p := String.ofList path
    if path.isEmpty || !p.endsWith ".lean" then none
    else match cs.drop path.length with
      | ':' :: rest =>
        let d1 := rest.takeWhile Char.isDigit
        match rest.drop d1.length with
        | ':' :: rest2 =>
          let d2 := rest2.takeWhile Char.isDigit
          match rest2.drop d2.length with
          | ':' :: _ => if d1.isEmpty || d2.isEmpty then none else some (p, (String.ofList d1).toNat!)
          | _ => none
        | _ => none
      | _ => none
  let uniq := hits.foldl (fun acc h => if acc.contains h then acc else acc ++ [h]) []
  uniq.mergeSort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

#guard errorLocs "x\nerror: B.lean:7:0: bang\nerror: A.lean:12:4: boom\nerror: A.lean:3:1: again\nerror: A.lean:12:9: twice\nerror: build failed" ==
  [("A.lean", 3), ("A.lean", 12), ("B.lean", 7)]
#guard errorLocs "A.lean:3:1: error: other ordering" == []
#guard errorLocs "error: Tests/Guards/Proofs/GateVocabulary.lean:112:6: failed" == [("Tests/Guards/Proofs/GateVocabulary.lean", 112)]

/-! ## One round over one file -/

inductive Kind where
  | sorried | pin | restatement | deleted | refused
  deriving Repr, BEq, Inhabited

/-- One patch or verdict of a round, in the order the Python prints them. -/
structure Event where
  kind : Kind
  kw : String := ""
  name : String := ""
  start : Nat
  stop : Nat
  deriving Repr, BEq, Inhabited

/-- The round's reading of one file: its patched text, the events (bottom-up),
    the unmappable locations (`nobody: …`). -/
structure FileRound where
  lines : Array String
  events : Array Event := #[]
  unmapped : Array String := #[]
  deriving Repr, Inhabited

/-- Merge sorted spans that touch or overlap (`a <= merged[-1][1]`). -/
def mergeSpans (spans : List (Nat × Nat)) : List (Nat × Nat) :=
  let sorted := (spans.foldl (fun acc s => if acc.contains s then acc else acc ++ [s]) []).mergeSort
    fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)
  sorted.foldl (fun acc (a, b) =>
    match acc.getLast? with
    | some (x, y) => if a ≤ y then acc.dropLast ++ [(x, max y b)] else acc ++ [(a, b)]
    | none => [(a, b)]) []

#guard mergeSpans [(5, 9), (1, 3), (3, 4), (5, 9)] == [(1, 4), (5, 9)]

/-- `rel.startswith("Tests/")`: a data definition there is deleted, in the library refused. -/
def isTestsFile (rel : String) : Bool := rel.startsWith "Tests/"

/-- One round over `rel`'s text, for the error lines (1-based) the build
    reported in it.  Every location is classified against THIS text before
    any patch; one declaration gets one verdict (a statement error outranks a
    body error); patches go bottom-up. -/
def roundFile (rel : String) (lines : Array String) (errLines : List Nat) :
    Except String FileRound := do
  let mut decls : Array ((Nat × Nat) × Classified) := #[]
  let mut pins : List (Nat × Nat) := []
  let mut unmapped : Array String := #[]
  for ln in errLines do
    let c := classify lines ln
    if c.verdict == .unmapped then
      pins := pins ++ [commandSpan lines (ln - 1)]
      continue
    let key := (c.start, c.stop)
    match decls.findIdx? (·.1 == key) with
    | some i =>
      let prev := decls[i]!.2
      if prev.verdict == .sorried && c.verdict != .sorried then decls := decls.set! i (key, c)
    | none => decls := decls.push (key, c)
  let rows : List ((Nat × Nat) × Option Classified) :=
    decls.toList.map (fun (k, c) => (k, some c)) ++ (mergeSpans pins).map (fun s => (s, none))
  let rows := rows.mergeSort fun a b => a.1.1 ≥ b.1.1
  let mut cur := lines
  let mut events : Array Event := #[]
  for ((start, stop), c?) in rows do
    match c? with
    | none =>
      cur ← neutralize cur start stop
      events := events.push { kind := .pin, start, stop }
    | some c =>
      match c.verdict with
      | .sorried =>
        cur := applySorry cur stop c.split
        events := events.push { kind := .sorried, kw := c.kw, name := c.name, start, stop }
      | .restatement =>
        events := events.push { kind := .restatement, kw := c.kw, name := c.name, start, stop }
      | .data =>
        if isTestsFile rel then
          cur ← neutralize cur (withDocstring cur start) stop true
          events := events.push { kind := .deleted, kw := c.kw, name := c.name, start, stop }
        else
          events := events.push { kind := .refused, kw := c.kw, name := c.name, start, stop }
      | .nobody => unmapped := unmapped.push s!"nobody: {rel}:{c.name} @{start + 1}"
      | .unmapped => pure ()
  return { lines := cur, events, unmapped }

/-- Does an event patch the text (counts as progress)? -/
def Event.progress (e : Event) : Bool :=
  e.kind == .sorried || e.kind == .pin || e.kind == .deleted

/-- The Python's round line for one event. -/
def eventLine (rnd : Nat) (rel : String) (e : Event) : String :=
  match e.kind with
  | .sorried => s!"ROUND {rnd} SORRIED   {e.kw} {e.name}  ({rel})"
  | .pin => s!"ROUND {rnd} PIN MOVED {rel}:{e.start + 1}-{e.stop}  — a census the deletion re-reads; neutralized"
  | .restatement => s!"ROUND {rnd} RESTATEMENT {e.kw} {e.name}  ({rel}:{e.start + 1})  — the error is in the STATEMENT; no proof repairs it"
  | .deleted => s!"ROUND {rnd} DELETED   {e.kw} {e.name}  ({rel}:{e.start + 1})  — a data definition whose VALUE names the deletion; not sorriable"
  | .refused => s!"ROUND {rnd} REFUSED   {e.kw} {e.name}  ({rel}:{e.start + 1})  — a LIBRARY data definition names the deletion; sorrying it would change a VALUE and deleting it is not this gate's call"

-- a round over the example: errors in `foo`'s body, `bar`'s statement and body, the run_cmd, the def
#guard (roundFile "Tests/X.lean" exampleFile [5, 8, 11, 16, 12]).toOption.map (·.events) ==
  some #[{ kind := .pin, start := 13, stop := 18 },
         { kind := .deleted, kw := "def", name := "census", start := 11, stop := 13 },
         { kind := .restatement, kw := "lemma", name := "bar", start := 6, stop := 11 },
         { kind := .sorried, kw := "lemma", name := "foo", start := 3, stop := 6 }]
#guard (roundFile "Tests/X.lean" exampleFile [5, 8, 11, 16, 12]).toOption.map (·.lines) ==
  some #["import X", "", "/-- doc -/", "lemma foo (h : c = '(' ∨ c = \"x\") : True := sorry",
         "@[simp] lemma bar (n : Nat)", "    (h : (n := 0) =", "      n) :", "    n = n := by", "  exact h",
         neutralizeNote, "def census : Nat := 3", "", "-/",
         neutralizeNote, "/-- expected -/", "set_option maxHeartbeats 1 in", "run_cmd do", "  check 1", "", "-/",
         "open Foo in", "#eval 2", "end"]
#guard (roundFile "L4YAML/X.lean" exampleFile [12]).toOption.map (·.events) ==
  some #[{ kind := .refused, kw := "def", name := "census", start := 11, stop := 13 }]

/-! ## The edit -/

/-- `flip_supplier.CTOR_HEAD`: the park's docstring. -/
def ctorHead : String := "  /-- Flow indicator scanned (`]`, `}`, `,`), or deferred block dispatch."
/-- `flip_supplier.CTOR_TAIL`: the park's last field and the conclusion beneath it. -/
def ctorTail : String :=
  "      (h_live0 : sc.simpleKeyAllowed = true ∨ sc.simpleKey.possible = true) :\n" ++
  "      PendingNode sc false sp_start sp_block sp_scan\n"
/-- `flip_supplier.ARM`: `close_with_ssl`'s flow arm. -/
def supplierArm : String :=
  "  | pendingFlow =>\n" ++
  "    -- Absorb opaque scanner content (flow/block indicators) via scannerDrop.\n" ++
  "    exact SLYamlStream.scannerDrop sp_start sp_block sp_scan sp_mid h_stream h_ssl\n"
/-- `flip_beta5.DROPCLOSE`: `dropClose`, docstring and body. -/
def dropClose : String :=
  "/-- The flow share of the escape, spent at one place: the OPAQUE resume a\n" ++
  "    depth-0 flow open hands `pendingFlow`, the one park with nothing to\n" ++
  "    compose through.  The gap constructor absorbs any span, so one captured\n" ++
  "    stream serves every position. -/\n" ++
  "lemma dropClose {sp_start sp_x : SurfPos} (h_stream : SLYamlStream sp_start sp_x) :\n" ++
  "    ∀ sp_e sp_m, SSLComments sp_e sp_m → SLYamlStream sp_start sp_m :=\n" ++
  "  fun _ sp_m h_ssl => SLYamlStream.scannerDrop sp_start sp_x _ sp_m h_stream h_ssl\n"
/-- `flip_drop.ARM`: the first line of the docstring, then (lazily) the arm. -/
def dropArmHead : String := "\n  /-- Scanner content absorption:"
def dropArmTail : String :=
  "\n  | scannerDrop (s s₁ s₂ s' : SurfPos) :\n      SLYamlStream s s₁ →\n" ++
  "      SSLComments s₂ s' →\n      SLYamlStream s s'\n"

/-- `flip_supplier._sub1`: exactly one occurrence or refused. -/
def sub1 (src old new : String) : Except String String :=
  let n := Patch.countOccurrences src old
  if n != 1 then
    .error s!"expected exactly one occurrence of\n---\n{old}---\nin {acc}, found {n}; the statement moved and this gate needs re-aiming"
  else .ok (Patch.replaceAll src old new)

/-- `flip_supplier._edit_retire`: the park (docstring to conclusion) and its arm. -/
def editRetire (src : String) : Except String String := do
  if Patch.countOccurrences src ctorHead != 1 then
    throw "the park's docstring is no longer unique; this gate needs re-aiming"
  let some (pre, fromHead) := findSplit src ctorHead | throw "unreachable"
  let some (mid, after) := findSplit fromHead ctorTail
    | throw s!"the park's last field is not below its docstring in {acc}; this gate needs re-aiming"
  let block := ctorHead ++ mid ++ ctorTail
  if Patch.countOccurrences block "\n  | " != 1 || Patch.countOccurrences block "\n  | pendingFlow (" != 1 then
    throw s!"the span this gate would delete is not one constructor:\n{String.ofList (block.toList.take 400)}\n... ({block.length} chars)"
  sub1 (pre ++ after) supplierArm ""

/-- The lazy `flip_drop.ARM` matches of `doc`: `(before, after)` of each, non-overlapping. -/
partial def dropArmMatches (text : String) : List (String × String) :=
  match findSplit text dropArmHead with
  | none => []
  | some (pre, rest) =>
    match findSplit rest dropArmTail with
    | none => []
    | some (_, after) => (pre, after) :: (dropArmMatches after).map fun (b, a) => (pre ++ "\n" ++ b, a)

/-- `beta5_edits`: β.5's three deletions on `(StreamAccum, Document)`. -/
def beta5Edits (accText docText : String) : Except String (String × String) := do
  let a ← editRetire accText
  let n := Patch.countOccurrences a dropClose
  if n != 1 then
    throw s!"expected exactly one `dropClose` block in {acc}, found {n}; the lemma moved and this gate needs re-aiming"
  let a := Patch.replaceAll a dropClose ""
  let hits := dropArmMatches docText
  if hits.length != 1 then
    throw s!"expected exactly one `scannerDrop` arm in {doc}, found {hits.length}; the production moved and this gate needs re-aiming"
  let (pre, after) := hits.head!
  return (a, pre ++ "\n" ++ after)

#guard dropArmMatches ("x\n  /-- Scanner content absorption: blah\n      more -/" ++ dropArmTail ++ "  | next") ==
  [("x", "  | next")]
#guard dropArmMatches "x\n  /-- Scanner content absorption: no arm" == []

/-! ## The dead arms -/

/-- `beta5_arms.DEAD`: `(tag, owner, anchor)`; the anchor's first line heads the block. -/
def dead : List (String × String × String) := [
  ("nic0", "PendingNode.nic0", "  | pendingFlow => assumption\n"),
  ("arm_tight_or_col", "PendingNode.arm_tight_or_col", "  | pendingFlow _ _ _ _ h_arm _ _ => exact h_arm\n"),
  ("dirRoute", "PendingNode.dirRoute",
   "  | pendingFlow =>\n    exact absurd h_allow (by simp [show sc.allowDirectives = false from by assumption])\n"),
  ("accum_block_pending", "accum_block_pending", "  | pendingFlow _ _ _ _ h_arm77 _ h_nic0F =>\n"),
  ("accum_content_pending", "accum_content_pending",
   "  | pendingFlow _ _ _ _ _ _ _ h_live0F =>\n    -- Item 284: the opaque park defers at EVERY landing"),
  ("flow_arm", "accum_flow_open_depth0",
   "  | pendingFlow _ _ _ _ _ _ _ h_live0F =>\n    -- The deferred state: its own closing strategy is the drop, and the flow\n"),
  ("flow_opaque_resume", "accum_flow_open_depth0", "  have opaque_resume : s_prep.simpleKey.possible = true →\n"),
  ("flow_drop_ride", "accum_flow_open_depth0", "  have drop_ride : s_prep.simpleKey.possible = true →\n")]

def indentOf (line : String) : Nat := (line.toList.takeWhile (· == ' ')).length
def isCommentLine (line : String) : Bool := (lstrip line).startsWith "--"

/-- `block_span`: `[start, stop)` of the block headed by `lines[head]` — forward
    to the first non-blank line at or left of the head's indent, back over the
    comment lines at exactly that indent. -/
def blockSpan (lines : Array String) (head : Nat) : Nat × Nat := Id.run do
  let ind := indentOf lines[head]!
  let mut stop := head + 1
  while stop < lines.size do
    let l := lines[stop]!
    if !isBlank l && indentOf l ≤ ind then break
    stop := stop + 1
  let mut start := head
  while start > 0 && isCommentLine lines[start - 1]! && indentOf lines[start - 1]! == ind do
    start := start - 1
  return (start, stop)

/-- `delete_dead`: every block of `dead` deleted bottom-up; the notes top-down. -/
def deleteDead (src : String) : Except String (String × List String) := do
  let lines := (src.splitOn "\n").toArray
  let mut spans : List (Nat × Nat × String) := []
  for (tag, owner, anchor) in dead do
    let n := Patch.countOccurrences src anchor
    if n != 1 then
      throw s!"anchor `{tag}` matches {n} times in {acc}, expected 1; the proof moved and this gate needs re-aiming"
    let some (pre, _) := findSplit src anchor | throw "unreachable"
    let head := countNewlines pre
    let (start, stop) := blockSpan lines head
    let ind := indentOf lines[head]!
    let sibs := (List.range (stop - start)).map (· + start) |>.filter fun i =>
      (lstrip lines[i]!).startsWith "| " && indentOf lines[i]! == ind
    if (lstrip lines[head]!).startsWith "| " && sibs != [head] then
      throw s!"the span for `{tag}` covers {sibs.length} arms, not one: lines {sibs.map (· + 1)}"
    spans := spans ++ [(start, stop, s!"{tag} [{owner}] lines {start + 1}-{stop} ({stop - start})")]
  let desc := spans.mergeSort fun a b => a.1 > b.1 || (a.1 == b.1 && a.2.1 ≥ b.2.1)
  let mut cur := lines
  for (start, stop, _) in desc do
    cur := cur.extract 0 start ++ cur.extract stop cur.size
  return ("\n".intercalate cur.toList, desc.reverse.map (·.2.2))

#guard blockSpan #["  cases h with", "  -- the arm", "  | a =>", "    exact x", "", "  | b => y"] 2 == (1, 5)

/-- `owner_of`: the declaration containing 1-based `lineNo`, by `HEAD`. -/
def ownerOf (lines : Array String) (lineNo : Nat) : String := Id.run do
  let mut i : Int := (min lineNo lines.size : Nat) - 1
  while i ≥ 0 do
    match headOf lines[i.toNat]! with
    | some (_, name) => return name.getD s!"<anonymous@{i + 1}>"
    | none => i := i - 1
  return "<none>"

#guard ownerOf exampleFile 9 == "bar"
#guard ownerOf exampleFile 17 == "census"       -- HEAD walks over commands; `beta5_arms` does too
#guard ownerOf exampleFile 1 == "<none>"

/-- `broken`: `(file, declaration, line)` per error of the log, one row per
    `(file, declaration)`, owners read off the edited texts (`<not-edited>` elsewhere). -/
def brokenRows (log : String) (texts : List (String × Array String)) : List (String × String × Nat) :=
  let hits := (log.splitOn "error: ").drop 1 |>.filterMap fun part =>
    match errorLocs ("error: " ++ part) with
    | [(rel, line)] => some (rel, line)
    | _ => none
  (hits.foldl (fun (acc : List (String × String × Nat)) (rel, line) =>
    let name := match texts.lookup rel with
      | some ls => ownerOf ls line
      | none => "<not-edited>"
    if acc.any (fun (r, n, _) => r == rel && n == name) then acc else acc ++ [(rel, name, line)]) [])

#guard brokenRows "error: A.lean:4:1: x\nerror: A.lean:9:1: y\nerror: A.lean:5:0: z\nerror: B.lean:1:0: w"
  [("A.lean", exampleFile)] == [("A.lean", "foo", 4), ("A.lean", "bar", 9), ("B.lean", "<not-edited>", 1)]

/-! ## Lines and pins -/

structure Tally where
  rounds : Nat := 0
  clean : Bool := false
  sorried : Array (Nat × String × String) := #[]     -- (round, kw, rel:name)
  restated : Array (Nat × String × String) := #[]
  refused : Array (Nat × String × String) := #[]
  deleted : Array (Nat × String × String) := #[]
  pinned : Array (Nat × String × Nat) := #[]          -- (round, rel, line)
  unmapped : Array String := #[]
  deriving Repr, Inhabited

/-- The rounds that produced anything, ascending (`WAVES`). -/
def Tally.waves (t : Tally) : List Nat :=
  let rs := t.sorried.map (·.1) ++ t.restated.map (·.1) ++ t.deleted.map (·.1) ++ t.pinned.map (·.1)
  (rs.toList.foldl (fun acc r => if acc.contains r then acc else acc ++ [r]) []).mergeSort (· ≤ ·)

def Tally.sorriedIn (t : Tally) (w : Nat) : Nat := (t.sorried.filter (·.1 == w)).size

/-- The summary block after the rounds (`ROUNDS … WAVES …`). -/
def summaryLines (t : Tally) (rc : UInt32) : Array String := Id.run do
  let mut out := #[s!"ROUNDS {t.rounds}  rc={rc}"]
  let block (title : String) (rows : Array (Nat × String × String)) : Array String :=
    #[s!"{title} {rows.size}"] ++ rows.map fun (r, kw, n) => s!"  wave{r} {kw} {n}"
  out := out ++ block "SORRIED" t.sorried ++ block "RESTATEMENTS" t.restated ++
    block "REFUSED" t.refused ++ block "DELETED" t.deleted
  out := out.push s!"PINSMOVED {t.pinned.size}"
  out := out ++ t.pinned.map fun (r, rel, ln) => s!"  wave{r} {rel}:{ln}"
  out := out.push s!"UNMAPPED {t.unmapped.size}"
  out := out ++ t.unmapped.map (s!"  {·}")
  out := out.push ("WAVES " ++ "  ".intercalate (t.waves.map fun w => s!"w{w}={t.sorriedIn w}"))
  return out

/-- `CENSUS gone=(\d+) carried=(\d+) free=(\d+)` out of the probe's log. -/
def census? (axlog : String) : Option String := Id.run do
  for part in (axlog.splitOn "CENSUS gone=").drop 1 do
    let cs := part.toList
    let g := cs.takeWhile Char.isDigit
    let r1 := cs.drop g.length
    if g.isEmpty || !startsWithL r1 " carried=" then continue
    let r1 := r1.drop 9
    let c := r1.takeWhile Char.isDigit
    let r2 := r1.drop c.length
    if c.isEmpty || !startsWithL r2 " free=" then continue
    let f := (r2.drop 6).takeWhile Char.isDigit
    if f.isEmpty then continue
    return some s!"gone={String.ofList g} carried={String.ofList c} free={String.ofList f}"
  return none

#guard census? "x\nCENSUS gone=1 carried=21 free=4\n" == some "gone=1 carried=21 free=4"
#guard census? "CENSUS gone=1 carried=x" == none

/-- The one line `ParkBill.lean` pins. -/
def fixline (t : Tally) (census : String) : String :=
  s!"rounds={t.rounds} clean={if t.clean then 1 else 0} sorried={t.sorried.size} restated={t.restated.size} " ++
  s!"deleted={t.deleted.size} refused={t.refused.size} pins={t.pinned.size} " ++
  s!"waves=[{",".intercalate (t.waves.map fun w => toString (t.sorriedIn w))}] {census}"

/-- `def NAME : String :=\s*"([^"]*)"` out of a guard file. -/
def pinLiteral? (src name : String) : Option String := do
  let (_, rest) ← findSplit src s!"def {name} : String :="
  match rest.toList.dropWhile Char.isWhitespace with
  | '"' :: cs => some (String.ofList (cs.takeWhile (· != '"')))
  | _ => none

#guard pinLiteral? "x\ndef expectedFixpoint : String :=\n  \"rounds=23 clean=1\"\n" "expectedFixpoint" == some "rounds=23 clean=1"
#guard pinLiteral? "def expectedFixpoint : String := \"a\"" "expectedFixpoint" == some "a"
#guard pinLiteral? "def expectedFixpoint : String :=\n  -- note\n  \"a\"" "expectedFixpoint" == none
#guard pinLiteral? "nothing" "expectedFixpoint" == none

/-- `FIX-PIN` / `ARM-PIN` verdict lines, from the pin file's text (or its absence). -/
def pinVerdict (tag name : String) (got : String) (pinSrc : Option String) : Array String :=
  match pinSrc with
  | none => #[s!"{tag} MISSING — {pinFile} is not in the tree; nothing pins this reading"]
  | some src =>
    match pinLiteral? src name with
    | none => #[s!"{tag} MISSING — ParkBill.lean no longer carries `{name}`; this gate has nothing to agree with"]
    | some exp => if exp == got then #[s!"{tag} agrees"] else #[s!"{tag} MOVED", s!"  got      {got}", s!"  expected {exp}"]

/-- Python's `repr` of a sorted list of names: `['a', 'b']`. -/
def pyList (xs : List String) : String := "[" ++ ", ".intercalate (xs.map fun s => s!"'{s}'") ++ "]"

/-- `ARMLINE control= arms= dead= left=[…]` and the second-wave note. -/
def armLines (ctl arm : List String) : String × Array String :=
  let ctlU := ctl.eraseDups
  let armU := arm.eraseDups
  let deadN := (ctlU.filter (!armU.contains ·)).length
  let left := armU.mergeSort (· ≤ ·)
  let line := s!"control={ctlU.length} arms={armU.length} dead={deadN} left=[{",".intercalate left}]"
  let new := (armU.filter (!ctlU.contains ·)).mergeSort (· ≤ ·)
  (line, if new.isEmpty then #[] else #[s!"  NEW under `arms` (a second wave): {pyList new}"])

#guard armLines ["a", "b", "c", "a"] ["c", "z"] ==
  ("control=3 arms=2 dead=2 left=[c,z]", #["  NEW under `arms` (a second wave): ['z']"])
#guard (armLines ["a"] ["a"]).1 == "control=1 arms=1 dead=0 left=[a]"

/-! ## The item-210 mapper (`flip_210.py --map`) -/

def mapperKeywords : List String :=
  ["lemma", "theorem", "def", "abbrev", "instance", "structure", "inductive"]

/-- `flip_210.DECL_HEAD`: a named declaration head (no `example`). -/
def declHead210 (line : String) : Option String := do
  let cs := dropHeadModifiers line.toList
  let kw ← mapperKeywords.find? fun k => startsWithL cs (k ++ " ")
  match cs.drop (kw.length + 1) with
  | c :: rest => if isNameStart c then some (String.ofList (c :: rest.takeWhile isNameChar)) else none
  | [] => none

#guard declHead210 "lemma foo (x : Nat) : True := by" == some "foo"
#guard declHead210 "example : True := trivial" == none
#guard declHead210 "instance : Foo := ⟨⟩" == none

/-- `broken_definitions`: `(definitions sorted, locations, complaints)` for the
    log's locations, given each file's lines (`none` = no such file). -/
def brokenDefinitions (locs : List (String × Nat)) (file : String → Option (Array String)) :
    List String × Nat × List String := Id.run do
  let mut defs : List String := []
  let mut complaints : List String := []
  for (path, line) in locs do
    match file path with
    | none => complaints := complaints ++ [s!"no such file: {path}"]
    | some src =>
      let mut i : Int := (min line src.size : Nat) - 1
      let mut found := false
      while i ≥ 0 do
        match declHead210 src[i.toNat]! with
        | some d =>
          if !defs.contains d then defs := defs ++ [d]
          found := true
          break
        | none => i := i - 1
      if !found then complaints := complaints ++ [s!"no enclosing definition: {path}:{line}"]
  return (defs.mergeSort (· ≤ ·), locs.length, complaints)

/-- `flip_210.report`'s lines: `BROKEN d` …, `UNMAPPED c` …, `COUNT …`. -/
def mapperReport (defs : List String) (nlocs : Nat) (complaints : List String) : Array String :=
  (defs.map (s!"BROKEN {·}")).toArray ++ (complaints.map (s!"UNMAPPED {·}")).toArray ++
    #[s!"COUNT {defs.length} definitions from {nlocs} locations"]

#guard (brokenDefinitions [("A.lean", 9), ("A.lean", 4), ("B.lean", 2), ("A.lean", 16)]
  fun p => if p == "A.lean" then some exampleFile else none) ==
  (["bar", "census", "foo"], 4, ["no such file: B.lean"])     -- the walk crosses commands, as DECL_HEAD's does

end

end Scripts.Flip.Beta5
