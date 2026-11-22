module

public import Scripts.Lean.BuildLog
public import Scripts.Lean.Regex
meta import Scripts.Lean.BuildLog
meta import Scripts.Lean.Regex

@[expose] public section Blanket

/-!
# Scripts.Pack.Census — the PACK flip census (the pure half of `pack-census flip|residue`)

The port of `scripts/pack_flip_census.py`: the value-line PACK family's punt surface, read by
ONE flip of its named alternative in `L4YAML/Proofs/Production/StreamAccum.lean` (item 311's
instrument; the `--alt refused` residue is item 312's).  Everything that does not touch the
file system or run `lake env lean` is here, so a round's rewrite decisions are `#guard`-able:

* `prepare` — the patched text: the two `abbrev PackAlt…/PackAltG… : Prop := True` bodies
  flipped (`False`/`False`, or `ExplicitValueRefused _sc`/kept), every `trivial -- refused: P`
  body sorried (`stubs`) or given its promise `(P)` (`promised`), the two frame stubs
  `PackAltG.ofPark`/`PackAlt.ofGateClose` sorried per mode, and the probe theorems
  (`ofTrue_probe`, in the residue also `alt_probe`) spliced before the first declaration;
* `parseErrors` — the `lake env lean` output as the Python read it: one entry per
  `StreamAccum.lean:L:C: error:` site (first head wins, cut at 100 chars), the following
  non-header lines stripped as the body;
* `step` — one round's classification: each site, bottom-up, is a DECLINE (`trivial` /
  `True.intro` / `⟨⟩` → `sorry`), a RELAY (`(…)` or a lone identifier whose mismatch message
  names the expected type → wrapped in `ofTrue_probe`, or in the residue `.imp id alt_probe`
  / `alt_probe` → RELAY-STATE), a CASCADE (not a mismatch, or a keyword head: skipped this
  round), or UNHANDLED (stops the census);
* `summary` — the per-declaration counts, the `nested-?` roster (item 361/365's elim-conditioned
  declines), and the pinned line `PACK-FLIP sites=… decls=… rounds=… decline=… relay=… leaf=…
  uncond=… stubs=…` / `PACK-RESIDUE … relayTrue=… relayState=… … promised=…`.

Strings are sliced by code point, as the Python did; columns are Lean's (code points).
-/

open Scripts.Lean.BuildLog (pyStrip)
open Scripts.Lean

namespace Scripts.Pack.Census

/-! ## Code-point string helpers -/

/-- `s[a:b]` by code points (`b` absent = to the end). -/
def sub (s : String) (a : Nat) (b : Option Nat := none) : String :=
  let cs := s.toList
  String.ofList ((cs.drop a).take ((b.getD cs.length) - a))

def isWordChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || ('₀' ≤ c && c ≤ '₉')

/-- `" ".join(t.split())`. -/
def collapseWs (t : String) : String :=
  " ".intercalate ((t.toList.splitBy (fun a b => !a.isWhitespace && !b.isWhitespace)).map String.ofList |>.filter (fun w => w ≠ "" && !w.all Char.isWhitespace))

/-- `str.rstrip()`. -/
def rstrip (s : String) : String := String.ofList (s.toList.reverse.dropWhile Char.isWhitespace).reverse

/-- `s[:n]` by code points. -/
def take (s : String) (n : Nat) : String := String.ofList (s.toList.take n)

#guard collapseWs "  a ∨\n  b   c " == "a ∨ b c"
#guard rstrip "x  \t" == "x"

/-- Position of the first occurrence of `pat` in `s` at or after `from`, by code points. -/
def findFrom (s pat : String) (from_ : Nat := 0) : Option Nat := Id.run do
  let cs := s.toList.toArray
  let ps := pat.toList.toArray
  if ps.size == 0 then return some from_
  let mut i := from_
  while i + ps.size ≤ cs.size do
    if (List.range ps.size).all (fun k => cs[i + k]! == ps[k]!) then return some i
    i := i + 1
  return none

/-- Position of the last occurrence of `pat` in `s` that starts before `before` (`str.rfind(pat, 0, before)`). -/
def rfindBefore (s pat : String) (before : Nat) : Option Nat := Id.run do
  let cs := s.toList.toArray
  let ps := pat.toList.toArray
  let mut best : Option Nat := none
  let mut i := 0
  while i + ps.size ≤ cs.size && i + ps.size ≤ before do
    if (List.range ps.size).all (fun k => cs[i + k]! == ps[k]!) then best := some i
    i := i + 1
  return best

/-- Python's `repr` of a `str`, as far as these diagnostics need it. -/
def pyRepr (s : String) : String := Id.run do
  let q := if s.contains '\'' && !s.contains '"' then '"' else '\''
  let mut out := q.toString
  for c in s.toList do
    out := out ++ (if c == '\\' then "\\\\" else if c == q then "\\" ++ q.toString
      else if c == '\n' then "\\n" else if c == '\t' then "\\t" else if c == '\r' then "\\r"
      else if c.val < 32 || c.val == 127 then
        (let h := String.ofList (Nat.toDigits 16 c.toNat); "\\x" ++ (if h.length < 2 then "0" ++ h else h))
      else c.toString)
  return out ++ q.toString

#guard pyRepr "ab" == "'ab'"
#guard pyRepr "a'b" == "\"a'b\""
#guard pyRepr "a'b\"" == "'a\\'b\"'"
#guard pyRepr "x\ty" == "'x\\ty'"

/-! ## The two modes -/

structure Mode where
  name : String
  /-- Body of `PackAlt` (`none` = left as it is). -/
  alt : Option String
  /-- Body of `PackAltG`. -/
  altG : Option String
  /-- The two frame stubs: line head, and what their `trivial` becomes. -/
  stubs : List (String × Option String)
  deriving Repr, Inhabited

def ofPark := "lemma PackAltG.ofPark "
def ofGateClose := "lemma PackAlt.ofGateClose "

def modeFalse : Mode :=
  { name := "false", alt := some "False", altG := some "False",
    stubs := [(ofPark, some "sorry"), (ofGateClose, some "sorry")] }

def modeRefused : Mode :=
  { name := "refused", alt := some "ExplicitValueRefused _sc", altG := none,
    stubs := [(ofPark, none), (ofGateClose, some "sorry")] }

def packAlt := "abbrev PackAlt (_sc : ScannerState) : Prop := True"
def packAltG := "abbrev PackAltG (_g : Option ScannerState) : Prop := True"

/-- The source file, relative to the repository root. -/
def rel := "L4YAML/Proofs/Production/StreamAccum.lean"

/-! ## prepare -/

/-- `REFUSED = \btrivial(\s+)-- refused: (.+?)\s*$` on one line: the match start and the promise. -/
def refusedMatch (l : String) : Option (Nat × String) := Id.run do
  let cs := l.toList.toArray
  let mut i := 0
  while i + 7 ≤ cs.size do
    if (i == 0 || !isWordChar cs[i-1]!) && sub l i (some (i + 7)) == "trivial" then
      let mut j := i + 7
      while j < cs.size && cs[j]!.isWhitespace do j := j + 1
      if j > i + 7 && sub l j (some (j + 12)) == "-- refused: " then
        let rest := rstrip (sub l (j + 12))
        if rest ≠ "" then return some (i, rest)
    i := i + 1
  return none

#guard refusedMatch "  (_h : PackAlt sc) : P := trivial -- refused: _h" == some (27, "_h")
#guard refusedMatch "  nontrivial -- refused: x" == none
#guard refusedMatch "  trivial -- refused:" == none

def declHeads : List String := ["lemma", "theorem", "def", "abbrev", "structure", "inductive"]

/-- `^(private )?(lemma|theorem|def|abbrev|structure|inductive) (\S+)`: the declared name. -/
def declName? (l : String) : Option String :=
  let l := if l.startsWith "private " then sub l 8 else l
  match declHeads.find? (fun k => l.startsWith (k ++ " ")) with
  | some k =>
    let rest := sub l (k.length + 1)
    let name := String.ofList (rest.toList.takeWhile (fun c => !c.isWhitespace))
    if name.isEmpty then none else some name
  | none => none

#guard declName? "lemma foo.bar {x : Nat} : True := trivial" == some "foo.bar"
#guard declName? "private def q := 1" == some "q"
#guard declName? "  lemma indented" == none
#guard declName? "theorem " == none

structure Prepared where
  lines : Array String
  flipped : Nat
  stubs : Nat
  promised : Nat
  /-- Index of the first probe line (the first declaration's paragraph start). -/
  i0 : Nat
  /-- Number of probe lines spliced in. -/
  shift : Nat
  deriving Repr, Inhabited

def probeLines (m : Mode) : Array String :=
  if m.name == "false" then
    #["theorem ofTrue_probe {P : Prop} (h : P ∨ True) : P ∨ False :=",
      "  h.elim Or.inl (fun _ => Or.inr sorry)", ""]
  else
    #["theorem ofTrue_probe {P : Prop} {sc : ScannerState} (h : P ∨ True) : P ∨ PackAlt sc :=",
      "  h.elim Or.inl (fun _ => Or.inr sorry)", "",
      "theorem alt_probe {sc sc' : ScannerState} (_h : PackAlt sc) : PackAlt sc' := sorry", ""]

/-- The patched text of one mode (the Python's edits before round 1), or why it cannot be made. -/
def prepare (m : Mode) (orig : Array String) : Except String Prepared := do
  let mut L := orig
  let mut flipped := 0
  for (old, body) in [(packAlt, m.alt), (packAltG, m.altG)] do
    let hits := (List.range L.size).filter (fun i => L[i]! == old)
    if hits.length ≠ 1 then throw s!"expected exactly one `{old}` line, found {hits.length} (at {hits})"
    if let some b := body then
      L := L.set! hits.head! (sub old 0 (some (old.length - 4)) ++ b)
      flipped := flipped + 1
  let mut promised := 0
  let mut stubs := 0
  for i in [0:L.size] do
    if let some (start, proof) := refusedMatch L[i]! then
      if m.name == "refused" then
        L := L.set! i (sub L[i]! 0 (some start) ++ "(" ++ proof ++ ")")
        promised := promised + 1
      else
        L := L.set! i (sub L[i]! 0 (some start) ++ "sorry")
        stubs := stubs + 1
  for (head, body) in m.stubs do
    let some i := (List.range L.size).find? (fun i => L[i]!.startsWith head)
      | throw s!"no line starts with `{head}`"
    let some j := (List.range 3).map (· + i) |>.find? (fun k => k < L.size && L[k]!.endsWith ":= trivial")
      | throw s!"no `:= trivial` within three lines of `{head}`"
    if let some b := body then
      L := L.set! j (sub L[j]! 0 (some (L[j]!.length - 7)) ++ b)
      if b == "sorry" then stubs := stubs + 1
  let some first := (List.range L.size).find? (fun i => (declName? L[i]!).isSome)
    | throw "no declaration in the file"
  let mut i0 := first
  while i0 > 0 && pyStrip L[i0 - 1]! ≠ "" do i0 := i0 - 1
  let probe := probeLines m
  let L' := L.extract 0 i0 ++ probe ++ L.extract i0 L.size
  return { lines := L', flipped, stubs, promised, i0, shift := probe.size }

def exampleFile : Array String := #[
  "module", "", "import X", "",
  "/-- doc -/",
  packAlt, "",
  packAltG, "",
  "lemma PackAltG.ofPark {sc : ScannerState} {g : Option ScannerState} (_h : PackAlt sc) :",
  "    PackAltG g := trivial", "",
  "lemma PackAlt.ofGateClose {g : Option ScannerState} {s' : ScannerState} (_h : PackAltG g) :",
  "    PackAlt s' := trivial", "",
  "lemma PackAlt.ofRefused {sc : ScannerState} (_h : ExplicitValueRefused sc) : PackAlt sc := trivial -- refused: _h",
  "lemma use : True ∨ PackAlt sc := Or.inr trivial", ""]

#guard (prepare modeFalse exampleFile).toOption.map (fun p => (p.flipped, p.stubs, p.promised, p.i0, p.shift))
  == some (2, 3, 0, 4, 3)
#guard (prepare modeRefused exampleFile).toOption.map (fun p => (p.flipped, p.stubs, p.promised, p.i0, p.shift))
  == some (1, 1, 1, 4, 5)
#guard (prepare modeFalse exampleFile).toOption.map (fun p => p.lines[4 + 3 + 1]!)
  == some "abbrev PackAlt (_sc : ScannerState) : Prop := False"
#guard (prepare modeRefused exampleFile).toOption.map (fun p => p.lines[5 + 5 + 10]!)
  == some "lemma PackAlt.ofRefused {sc : ScannerState} (_h : ExplicitValueRefused sc) : PackAlt sc := (_h)"
#guard (prepare modeFalse exampleFile).toOption.map (fun p => p.lines[5 + 3 + 5]!)
  == some "    PackAltG g := sorry"
#guard (prepare modeRefused exampleFile).toOption.map (fun p => p.lines[5 + 5 + 5]!)
  == some "    PackAltG g := trivial"
#guard (prepare modeFalse (exampleFile.push packAlt)).isOk == false

/-- The original line number (1-based) of patched index `ln`. -/
def oline (p : Prepared) (ln : Nat) : Nat :=
  if ln ≥ p.i0 + p.shift then ln + 1 - p.shift else ln + 1

/-- `odecl`: the last declaration named at or before original line `n` (1-based), `?` when none. -/
def declTable (orig : Array String) : Array String := Id.run do
  let mut out := Array.mkEmpty orig.size
  let mut d := "?"
  for l in orig do
    if let some n := declName? l then d := n
    out := out.push d
  return out

def odecl (tbl : Array String) (n : Nat) : String :=
  if n == 0 then "?" else tbl[min n tbl.size - 1]!

/-! ## parseErrors -/

/-- One error site of a round: `(line0, col)`, the head cut at 100 chars, the head plus the
stripped body lines (`has type` / `but is expected to have type` are NOT indented). -/
structure Err where
  line : Nat
  col : Nat
  head : String
  body : Array String
  deriving Repr, Inhabited

/-- `ERR`: `L4YAML/Proofs/Production/StreamAccum.lean:L:C: error: MSG` at the start of the raw line. -/
def errLine? (l : String) : Option (Nat × Nat × String) := do
  guard (l.startsWith (rel ++ ":"))
  let r := (sub l (rel.length + 1)).toList
  let (d1, r1) := r.span Char.isDigit
  guard (!d1.isEmpty)
  let ':' :: r2 := r1 | none
  let (d2, r3) := r2.span Char.isDigit
  guard (!d2.isEmpty)
  let rest := String.ofList r3
  guard (rest.startsWith ": error: ")
  some ((String.ofList d1).toNat!, (String.ofList d2).toNat!, sub rest 9)

/-- `HEADER`: `^\S+\.lean:\d+:\d+: (error|warning|info)` — a diagnostic head of any file. -/
def headerLine (l : String) : Bool :=
  match l.toList with
  | [] => false
  | c :: _ =>
    !c.isWhitespace &&
    match Scripts.Lean.BuildLog.splitLoc l with
    | some (_, _, _, m) => m.startsWith "error" || m.startsWith "warning" || m.startsWith "info"
    | none => false

/-- The sites of one round, in first-seen order, keyed by `(line0, col)` (first head wins; a repeated
key's body lines join the first's, as the Python's `setdefault` did). -/
def parseErrors (log : String) : Array Err := Id.run do
  let mut out : Array Err := #[]
  let mut cur : Option Nat := none
  for l in log.splitOn "\n" do
    match errLine? l with
    | some (ln, col, msg) =>
      let key := (ln - 1, col)
      match out.findIdx? (fun e => (e.line, e.col) == key) with
      | some k => cur := some k
      | none =>
        out := out.push { line := ln - 1, col, head := take msg 100, body := #[msg] }
        cur := some (out.size - 1)
    | none =>
      if headerLine l then cur := none
      else if let some k := cur then
        out := out.modify k (fun e => { e with body := e.body.push (pyStrip l) })
  return out

#guard (parseErrors (rel ++ ":12:4: error: Type mismatch\n  h\nhas type\n  A\nbut is expected to have type\n  B\n" ++
    rel ++ ":20:1: warning: unused\n  x\n" ++ rel ++ ":30:2: error: boom")).map (fun e => (e.line, e.col, e.head, e.body))
  == #[(11, 4, "Type mismatch", #["Type mismatch", "h", "has type", "A", "but is expected to have type", "B"]),
       (29, 2, "boom", #["boom"])]

/-! ## Readings of a message -/

/-- `relay_types`: from a type-mismatch body, the type the term HAS and the type the position
EXPECTS, each flattened to one line. -/
def relayTypes (body : Array String) : Option (String × String) := Id.run do
  let text := "\n".intercalate body.toList
  let mut from_ := 0
  while true do
    let some i := findFrom text "has type\n" from_ | return none
    let hasStart := i + 9
    match findFrom text "\nbut is expected to have type\n" hasStart with
    | none => from_ := i + 1
    | some j =>
      let has := sub text hasStart (some j)
      let expStart := j + 30
      let expEnd := (findFrom text "\nin the application" expStart).getD text.length
      return some (collapseWs has, collapseWs (sub text expStart (some expEnd)))
  return none

#guard relayTypes #["Type mismatch", "h", "has type", "A ∨", "True", "but is expected to have type", "A ∨ PackAlt s'", ""]
  == some ("A ∨ True", "A ∨ PackAlt s'")
#guard relayTypes #["Application type mismatch: In the application", "f h", "the argument", "h", "has type",
    "P x : Prop", "but is expected to have type", "Q x : Prop", "in the application", "g (f h)"]
  == some ("P x : Prop", "Q x : Prop")
#guard relayTypes #["unsolved goals"] == none

def opens : List Char := ['(', '[', '{', '⟨']
def closes : List Char := [')', ']', '}', '⟩']

/-- `outer_alt`: the right disjunct of a flattened type's OUTERMOST `∨`. -/
def outerAlt (t : String) : Option String := Id.run do
  let cs := t.toList.toArray
  let mut depth : Int := 0
  let mut last : Option Nat := none
  for i in [0:cs.size] do
    let c := cs[i]!
    if opens.contains c then depth := depth + 1
    else if closes.contains c then depth := depth - 1
    else if depth == 0 && sub t i (some (i + 3)) == " ∨ " then last := some i
  return last.map (fun i => pyStrip (sub t (i + 3)))

#guard outerAlt "A ∨ (B ∨ True)" == some "(B ∨ True)"
#guard outerAlt "(A ∨ True) ∨ PackAlt sc" == some "PackAlt sc"
#guard outerAlt "PackAlt sc → PackAlt s'" == none

/-- `balanced_end`: from `(ln, col)` on an opener, the `(line, col)` of its closer, skipping
line comments; `none` when the group never closes. -/
def balancedEnd (lines : Array String) (ln col : Nat) : Option (Nat × Nat) := Id.run do
  let mut depth : Int := 0
  let mut i := ln
  let mut j := col
  while i < lines.size do
    let cs := lines[i]!.toList.toArray
    let mut stop := false
    while j < cs.size && !stop do
      if j + 1 < cs.size && cs[j]! == '-' && cs[j+1]! == '-' then stop := true
      else
        if opens.contains cs[j]! then depth := depth + 1
        else if closes.contains cs[j]! then
          depth := depth - 1
          if depth == 0 then return some (i, j)
        j := j + 1
    i := i + 1
    j := 0
  return none

#guard balancedEnd #["x (a (b) -- (", "  c) y"] 0 2 == some (1, 3)
#guard balancedEnd #["(⟨a, b⟩)"] 0 0 == some (0, 7)
#guard balancedEnd #["(a"] 0 0 == none

/-- `^(\s+)id\b` on the text after a closer: the whitespace run. -/
def wsThenId? (after : String) : Option String :=
  let cs := after.toList
  let ws := cs.takeWhile Char.isWhitespace
  let rest := cs.drop ws.length
  if ws.isEmpty then none
  else match rest with
    | 'i' :: 'd' :: r => if r.head?.all (fun c => !isWordChar c) then some (String.ofList ws) else none
    | _ => none

#guard wsThenId? " id)" == some " "
#guard wsThenId? " idx" == none
#guard wsThenId? "id" == none

/-- `(fun|by|match|if|let|have|show|do|⟨)\b` at the start of the site's text, or a `⟨` head. -/
def keywordHead (text : String) : Bool :=
  text.startsWith "⟨" ||
  ["fun", "by", "match", "if", "let", "have", "show", "do"].any (fun k =>
    text.startsWith k && ((text.toList.drop k.length).head?.all (fun c => !isWordChar c)))

#guard keywordHead "fun h => x"
#guard keywordHead "funny" == false
#guard keywordHead "⟨a, b⟩"
#guard keywordHead "trivial" == false

/-- `[A-Za-z_][A-Za-z0-9_'.₀-₉]*` at the start of the text. -/
def identHead? (text : String) : Option String :=
  match text.toList with
  | c :: r =>
    if c.isAlpha || c == '_' then
      some (String.ofList (c :: r.takeWhile (fun d => d.isAlphanum || d == '_' || d == '\'' || d == '.' || ('₀' ≤ d && d ≤ '₉'))))
    else none
  | [] => none

/-- After an identifier: `\s*($|[),⟩])`, or whitespace when the message is an application mismatch. -/
def identArgument (after : String) (head : String) : Bool :=
  let cs := after.toList
  let rest := cs.dropWhile Char.isWhitespace
  (match rest with
   | [] => true
   | c :: _ => c == ')' || c == ',' || c == '⟩') ||
  (cs.head?.any Char.isWhitespace && head.startsWith "Application type mismatch")

#guard identHead? "h_vslot51.imp x" == some "h_vslot51.imp"
#guard identHead? "(x)" == none
#guard identArgument ")" "Type mismatch"
#guard identArgument " x" "Type mismatch" == false
#guard identArgument " x" "Application type mismatch"

/-- `\(+\s*PackAlt\.` at the start of the text (a producer paying the alternative with a real fact). -/
def paidGroup (text : String) : Bool :=
  let cs := text.toList
  let r := cs.dropWhile (· == '(')
  cs.head? == some '(' && (String.ofList (r.dropWhile Char.isWhitespace)).startsWith "PackAlt."

#guard paidGroup "((PackAlt.ofRefused h))"
#guard paidGroup "( PackAlt.step_x h)"
#guard paidGroup "(Or.inr (PackAlt.ofRefused h))" == false

/-! ## step — one round -/

structure Entry where
  round : Nat
  line : Nat
  col : Nat
  kind : String
  decl : String
  msg : String
  src : String
  deriving Repr, Inhabited, DecidableEq

def Entry.tsv (e : Entry) : String :=
  s!"{e.round}\t{e.line}\t{e.col}\t{e.kind}\t{e.decl}\t{e.msg}\t{e.src}"

structure State where
  lines : Array String
  seen : Array (Nat × Nat) := #[]
  census : Array Entry := #[]
  out : Array String := #[]
  stop : Bool := false
  deriving Repr, Inhabited

/-- The `Invalid ⟨…⟩` sites that are the pattern of an already-probed `.imp (fun ⟨…⟩ => …) (fun h => alt_probe h)`
relay (item 358): settled, not new. -/
def settledProbes (lines : Array String) (errs : Array Err) : Array Err :=
  errs.filter fun e =>
    e.head.startsWith "Invalid `⟨...⟩` notation" &&
    (sub lines[e.line]! e.col).startsWith "⟨" &&
    match rfindBefore lines[e.line]! "(fun " e.col with
    | none => false
    | some kk =>
      match balancedEnd lines e.line kk with
      | none => false
      | some (bl, bc) =>
        let after := (sub lines[bl]! (bc + 1)).toList
        let ws := after.takeWhile Char.isWhitespace
        !ws.isEmpty && (String.ofList (after.drop ws.length)).startsWith "(fun h => alt_probe h)"

/-- Sites bottom-up: by line descending, then column descending (Python's `sorted(…, reverse=True)`). -/
def bottomUp (errs : Array Err) : Array Err :=
  errs.qsort (fun a b => a.line > b.line || (a.line == b.line && a.col > b.col))

def mkEntry (_p : Prepared) (orig : Array String) (tbl : Array String) (rnd o col : Nat) (kind msg : String) : Entry :=
  { round := rnd, line := o, col, kind, decl := odecl tbl o, msg,
    src := take (pyStrip (orig.getD (o - 1) "")) 110 }

/-- One round's rewrite of the sites `errs` (already filtered of settled probes), as the Python's
inner loop: the edits to the patched lines, the census entries, the diagnostics to print, and
whether an UNHANDLED site stops the census.  `none` only when a group never closes. -/
def step (m : Mode) (p : Prepared) (orig : Array String) (tbl : Array String) (rnd : Nat)
    (st : State) (errs : Array Err) : Option State := Id.run do
  let isFalse := m.name == "false"
  let mut st := st
  for e in bottomUp errs do
    let ln := e.line
    let mut col := e.col
    let s := st.lines[ln]!
    let mut o := oline p ln
    let text := sub s col
    let isMismatch := e.head.startsWith "Application type mismatch" || e.head.startsWith "type mismatch" ||
      e.head.startsWith "Type mismatch"
    let kw := keywordHead text
    let mut kind := ""
    let mut skip := false
    if e.head.startsWith "maximum number of errors" then
      st := { st with out := st.out.push s!"  cap notice at L{o}:{col} — raise LEAN_ARGS' maxErrors" }
      skip := true
    else if st.seen.contains (ln, col) then
      kind := "UNHANDLED"
      st := { st with stop := true }
      st := { st with out := st.out.push s!"  UNHANDLED recurrence at L{o}:{col}: {pyRepr (take text 60)} :: {e.head}" }
    else
      let impId? : Option (Nat × Nat × String) :=
        if e.head.startsWith "Invalid `⟨...⟩` notation" && text.startsWith "⟨" then
          match rfindBefore s "(fun " col with
          | none => none
          | some k =>
            match balancedEnd st.lines ln k with
            | none => none
            | some (el, ec) => (wsThenId? (sub st.lines[el]! (ec + 1))).map fun ws => (el, ec, ws)
        else none
      match impId? with
      | some (el, ec, ws) =>
        let tail := sub st.lines[el]! (ec + 1)
        let newLine := sub st.lines[el]! 0 (some (ec + 1)) ++ ws ++ "(fun h => alt_probe h)" ++ sub tail (ws.length + 2)
        st := { st with lines := st.lines.set! el newLine }
        kind := "RELAY-STATE"
        o := oline p el
        col := ec + 1 + ws.length
      | none =>
        if !isMismatch || kw then
          kind := "CASCADE"
          st := { st with out := st.out.push s!"  cascade at L{o}:{col}: {pyRepr (take text 50)} :: {take e.head 60}" }
        else if let some tok := ["trivial", "True.intro", "⟨⟩"].find? (fun t => text.startsWith t) then
          st := { st with lines := st.lines.set! ln (sub s 0 (some col) ++ "sorry" ++ sub s (col + tok.length)) }
          kind := "DECLINE"
        else
          let ident? := identHead? text
          let identOk := match ident? with
            | some id => identArgument (sub text id.length) e.head
            | none => false
          if text.startsWith "(" || identOk then
            let types := relayTypes e.body
            let has := types.map (·.1)
            let expects := types.map (·.2)
            let altHas := has.bind outerAlt
            let stateRelay := !isFalse && has.isSome &&
              ((altHas.isSome && altHas ≠ some "True") || (altHas.isNone && ((has.getD "").splitOn "PackAlt").length > 1))
            if text.startsWith "(" && isFalse && paidGroup text then
              let some (el, ec) := balancedEnd st.lines ln col | return none
              if el == ln then
                st := { st with lines := st.lines.set! ln (sub s 0 (some col) ++ "sorry" ++ sub s (ec + 1)) }
              else
                let mut L := st.lines.set! el (sub st.lines[el]! (ec + 1))
                L := L.set! ln (sub s 0 (some col) ++ "sorry")
                for mid in [ln + 1:el] do L := L.set! mid ""
                st := { st with lines := L }
              kind := "DECLINE"
            else if text.startsWith "(" then
              let some (el, ec) := balancedEnd st.lines ln col | return none
              let (hd, tl) := if stateRelay then ("(", ".imp id alt_probe)") else ("(ofTrue_probe (", "))")
              if el == ln then
                let s2 := sub s 0 (some (ec + 1)) ++ tl ++ sub s (ec + 1)
                st := { st with lines := st.lines.set! ln (sub s2 0 (some col) ++ hd ++ sub s2 col) }
              else
                let mut L := st.lines.set! el (sub st.lines[el]! 0 (some (ec + 1)) ++ tl ++ sub st.lines[el]! (ec + 1))
                L := L.set! ln (sub s 0 (some col) ++ hd ++ sub s col)
                st := { st with lines := L }
              kind := if stateRelay then "RELAY-STATE" else "RELAY"
            else
              let ident := ident?.getD ""
              let after := sub s (col + ident.length)
              let repl :=
                if stateRelay && ident == "id" then "(fun h => alt_probe h)"
                else if stateRelay && (expects.getD "").startsWith "PackAlt " then "alt_probe (" ++ ident ++ ")"
                else if stateRelay then "((" ++ ident ++ ").imp id alt_probe)"
                else "(ofTrue_probe (" ++ ident ++ "))"
              st := { st with lines := st.lines.set! ln (sub s 0 (some col) ++ repl ++ after) }
              kind := if stateRelay then "RELAY-STATE" else "RELAY"
          else
            kind := "UNHANDLED"
            st := { st with stop := true }
            st := { st with out := st.out.push s!"  UNHANDLED shape at L{o}:{col}: {pyRepr (take text 70)} :: {e.head}" }
    if !skip then
      st := { st with seen := st.seen.push (ln, col) }
      st := { st with census := st.census.push (mkEntry p orig tbl rnd o col kind e.head) }
  return some st

/-- A one-round fixture: the example file flipped `false`, with the errors Lean would raise at its
one site (`Or.inr trivial` in `use`). -/
def exampleStep : Option State :=
  (prepare modeFalse exampleFile).toOption.bind fun p =>
    let orig := exampleFile
    let site := p.lines.findIdx? (·.startsWith "lemma use ") |>.getD 0
    let col := (sub p.lines[site]! 0).length - "trivial".length
    step modeFalse p orig (declTable orig) 1 { lines := p.lines }
      #[{ line := site, col, head := "Type mismatch", body := #["Type mismatch", "trivial", "has type", "True", "but is expected to have type", "False"] }]

#guard exampleStep.map (fun st => st.census.map (fun e => (e.kind, e.decl, e.line, e.msg, e.src))) ==
  some #[("DECLINE", "use", 17, "Type mismatch", "lemma use : True ∨ PackAlt sc := Or.inr trivial")]
#guard exampleStep.map (fun st => st.lines[st.lines.size - 2]!) == some "lemma use : True ∨ PackAlt sc := Or.inr sorry"

/-- A relay site: a parenthesised group with a `∨ True` outer alternative in `false` mode, and the
same under the residue (state relay: the outer alternative is `PackAlt s`). -/
def relayStep (m : Mode) (body : Array String) (head := "Type mismatch") : Option (String × String) :=
  let orig : Array String := #["lemma a : True := trivial", "lemma b : P ∨ PackAlt s' := (h.imp id id) -- c"]
  let p : Prepared := { lines := orig, flipped := 0, stubs := 0, promised := 0, i0 := 0, shift := 0 }
  (step m p orig (declTable orig) 1 { lines := orig } #[{ line := 1, col := 28, head, body }]).map
    fun st => (st.lines[1]!, st.census[0]!.kind)

#guard relayStep modeFalse #["Type mismatch", "h.imp id id", "has type", "P ∨ True", "but is expected to have type", "P ∨ False"]
  == some ("lemma b : P ∨ PackAlt s' := (ofTrue_probe ((h.imp id id))) -- c", "RELAY")
#guard relayStep modeRefused #["Type mismatch", "h.imp id id", "has type", "P ∨ PackAlt s", "but is expected to have type", "P ∨ PackAlt s'"]
  == some ("lemma b : P ∨ PackAlt s' := ((h.imp id id).imp id alt_probe) -- c", "RELAY-STATE")
#guard relayStep modeRefused #["Type mismatch", "h.imp id id", "has type", "P ∨ True", "but is expected to have type", "P ∨ PackAlt s'"]
  == some ("lemma b : P ∨ PackAlt s' := (ofTrue_probe ((h.imp id id))) -- c", "RELAY")
#guard relayStep modeRefused #["unsolved goals"] "unsolved goals" == some ("lemma b : P ∨ PackAlt s' := (h.imp id id) -- c", "CASCADE")

/-! ## summary -/

def leafRe := "^(\\| .*=> (exact )?Or\\.inr trivial|else Or\\.inr trivial|· exact Or\\.inr trivial)"
def elimLeafRe := "\\.elim \\(fun \\w+ => Or\\.inr \\(PackAlt\\.\\w+ .+\\)\\) \\(fun _ => Or\\.inr trivial\\)"
def elimArgRe := "\\.elim \\(fun \\w+ => PackAlt\\.\\w+ \\w+\\) \\(fun _ => trivial\\)"

#guard Regex.test leafRe "| _ => exact Or.inr trivial"
#guard Regex.test leafRe "· exact Or.inr trivial"
#guard Regex.test leafRe "exact Or.inr trivial" == false
#guard Regex.test elimLeafRe "h_ref.elim (fun h => Or.inr (PackAlt.ofRefused h)) (fun _ => Or.inr trivial)"
#guard Regex.test elimArgRe "(h_alt := h_refused.elim (fun h => PackAlt.ofRefused h) (fun _ => trivial))"

/-- Counts of `f` over the entries, by key, in ascending key order. -/
def counter (xs : Array Entry) (f : Entry → String) : Array (String × Nat) := Id.run do
  let mut out : Array (String × Nat) := #[]
  for x in xs do
    let k := f x
    match out.findIdx? (·.1 == k) with
    | some i => out := out.modify i (fun (k, n) => (k, n + 1))
    | none => out := out.push (k, 1)
  return out.qsort (fun a b => a.1 < b.1)

def count (c : Array (String × Nat)) (k : String) : Nat := (c.find? (·.1 == k)).map (·.2) |>.getD 0

structure Summary where
  out : Array String
  label : String
  pin : String
  line : String
  deriving Repr, Inhabited, BEq

/-- The report after the rounds: per-declaration counts, the `nested-?` roster, the pinned line. -/
def summary (m : Mode) (orig : Array String) (census : Array Entry) (rounds stubs promised : Nat) : Summary := Id.run do
  let isFalse := m.name == "false"
  let by_ := counter (census.filter (·.kind ≠ "CASCADE")) (·.decl)
  let mut out : Array String := #[]
  for (d, n) in by_ do
    out := out.push s!"  {"".pushn ' ' (3 - min 3 (toString n).length)}{n}  {d}"
  let kinds := counter census (·.kind)
  let src (e : Entry) := pyStrip (orig.getD (e.line - 1) "")
  let elimSites := census.filter fun e =>
    e.kind == "DECLINE" && !Regex.test leafRe (src e) && (Regex.test elimLeafRe (src e) || Regex.test elimArgRe (src e))
  let leaf := (census.filter fun e => e.kind == "DECLINE" && Regex.test leafRe (src e)).size + elimSites.size
  let uncond := count kinds "DECLINE" - leaf
  for e in elimSites do
    out := out.push s!"  nested-? {e.decl}:{e.line}"
  let mut line := ""
  let mut label := ""
  let mut pin := ""
  if isFalse then
    line := s!"sites={census.size} decls={by_.size} rounds={rounds} decline={count kinds "DECLINE"} " ++
      s!"relay={count kinds "RELAY"} leaf={leaf} uncond={uncond} stubs={stubs}"
    label := "PACK-FLIP"; pin := "expectedPackFlip"
  else
    let sites := census.size - count kinds "CASCADE"
    line := s!"sites={sites} decls={by_.size} rounds={rounds} decline={count kinds "DECLINE"} " ++
      s!"relayTrue={count kinds "RELAY"} relayState={count kinds "RELAY-STATE"} leaf={leaf} uncond={uncond} " ++
      s!"stubs={stubs} promised={promised}"
    label := "PACK-RESIDUE"; pin := "expectedPackResidue"
  if count kinds "CASCADE" > 0 then line := line ++ s!" cascade={count kinds "CASCADE"}"
  if count kinds "UNHANDLED" > 0 then line := line ++ s!" unhandled={count kinds "UNHANDLED"}"
  return { out, label, pin, line }

#guard (summary modeFalse exampleFile
    #[{ round := 1, line := 16, col := 40, kind := "DECLINE", decl := "use", msg := "Type mismatch", src := "" }] 2 3 0)
  == { out := #["    1  use"], label := "PACK-FLIP", pin := "expectedPackFlip",
       line := "sites=1 decls=1 rounds=2 decline=1 relay=0 leaf=0 uncond=1 stubs=3" }

/-- `check_pin`: the literal in the guard file — `def NAME : String :=\n  "…"` — against the
reading.  `none` = absent; `some true` = agrees; `some false` = moved. -/
def checkPin (pinText name line : String) : Option Bool := do
  let i ← findFrom pinText s!"def {name} : String :=\n  \""
  let start := i + s!"def {name} : String :=\n  \"".length
  let j ← findFrom pinText "\"" start
  return sub pinText start (some j) == line

#guard checkPin "def x : String :=\n  \"a=1\"\n" "x" "a=1" == some true
#guard checkPin "def x : String :=\n  \"a=1\"\n" "x" "a=2" == some false
#guard checkPin "def x : String :=\n  -- note\n  \"a=1\"\n" "x" "a=1" == none

end Scripts.Pack.Census

