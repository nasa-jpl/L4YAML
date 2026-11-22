module

public import Lean.Environment
public import Std.Data.HashSet
public meta import Std.Data.HashSet.Basic

@[expose] public section Blanket

/-!
# Scripts.Lean.GateVocab — every gate named in the tree's prose resolves

Formerly `scripts/gate_vocab.py` (DOCS items 265, 266): a backticked
identifier in a docstring is a claim about the environment, and nothing in
the build checks it.  Two vocabularies are read off every `L4YAML/**` and
`Tests/**` source line (the pin file itself excepted, counted as `self`):

* the GATES — `scanNextToken_…`, `scanLoop_…`, `scanLoopIx_…` in full, and the
  short `check<Upper><Upper>…` form (two capitalized segments, so one-letter
  macros such as `checkM` stay out);
* the REFUTATIONS — `…_refuted`.

A name resolves when it is the final component of a constant in the wide
environment, bare or under any of the three prefixes.  Family references
(`…_*`) and names a line break splits (`wrapped`) are counted, not scored.
The five Python regexes are hand scanners here, each with its `#guard` rows,
scanned independently as `re.finditer` did (a name two patterns both match is
two mentions of one name, as before).  The environment is read off the
`.olean` headers of the built modules and their transitive imports
(`Lean.readModuleData` → `constNames`), which is what the Python's `run_cmd`
dump of `env.constants` saw — minus the merge, so the exe root modules (each
with its own `main`) can be read too.  The reading line
(`GATEVOCAB names=… unresolved=…`) is compared with the pin
`expectedGateVocab` in `Tests/Guards/Proofs/GateVocabulary.lean`.
-/

namespace Scripts.Lean.GateVocab

def prefixes : List String := ["scanNextToken_", "scanLoop_", "scanLoopIx_"]

def pinFile : String := "Tests/Guards/Proofs/GateVocabulary.lean"

/-- `[A-Za-z0-9_']` -/
def isNameChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

def startsWithAny (cs : List Char) (ps : List String) : Option String :=
  ps.find? fun p => cs.take p.length == p.toList

/-- Leading `([A-Z][a-z0-9']+)*` blocks: their count and the remainder. -/
partial def segments : List Char → Nat → Nat × List Char
  | c :: t, n =>
    if c.isUpper then
      let body := t.takeWhile fun d => d.isLower || d.isDigit || d == '\''
      if body.isEmpty then (n, c :: t) else segments (t.drop body.length) (n + 1)
    else (n, c :: t)
  | [], n => (n, [])

/-- QUAL: `(?:scanNextToken_|scanLoop_|scanLoopIx_)[A-Za-z0-9_']+` at the head of `cs`. -/
def qualName (cs : List Char) : Option (List Char) := do
  let p ← startsWithAny cs prefixes
  let name := (cs.drop p.length).takeWhile isNameChar
  guard (!name.isEmpty)
  pure (p.toList ++ name)

/-- SHORT: `check(?:[A-Z][a-z0-9']+){2,}[A-Za-z0-9_']*` at the head of `cs`. -/
def shortName (cs : List Char) : Option (List Char) := do
  guard (cs.take 5 == "check".toList)
  let rest := cs.drop 5
  let (n, after) := segments rest 0
  guard (n ≥ 2)
  let tail := after.takeWhile isNameChar
  pure (cs.take (5 + (rest.length - after.length) + tail.length))

/-- REFUTED: `[a-zA-Z][A-Za-z0-9_']*_refuted` at the head of `cs`. -/
def refutedName (cs : List Char) : Option (List Char) := do
  guard (cs.headD ' ' |>.isAlpha)
  let name := cs.takeWhile isNameChar
  guard ((String.ofList name).endsWith "_refuted" && name.length > "_refuted".length)
  pure name

/-- `re.finditer` of `` `(<name>)` `` for one name shape: left to right,
non-overlapping, each match consuming through its closing backtick. -/
partial def backticked (shape : List Char → Option (List Char)) (line : String) : List String :=
  go line.toList []
where
  go : List Char → List String → List String
    | [], acc => acc.reverse
    | '`' :: t, acc =>
      match shape t with
      | some name =>
        if (t.drop name.length).headD ' ' == '`' then go (t.drop (name.length + 1)) (String.ofList name :: acc)
        else go t acc
      | none => go t acc
    | _ :: t, acc => go t acc

/-- The three vocabularies' mentions on a line, QUAL then SHORT then REFUTED. -/
def mentions (line : String) : List String :=
  backticked qualName line ++ backticked shortName line ++ backticked refutedName line

/-- `(?:scanNextToken_|scanLoop_|scanLoopIx_|check[A-Z])[A-Za-z0-9_']*` at the head of `cs`
(the gate-ish opener the WRAP and family patterns share): the matched run. -/
def gateOpener (cs : List Char) : Option (List Char) :=
  match startsWithAny cs prefixes with
  | some p => some (p.toList ++ (cs.drop p.length).takeWhile isNameChar)
  | none =>
    match cs with
    | 'c' :: 'h' :: 'e' :: 'c' :: 'k' :: u :: t =>
      if u.isUpper then some ("check".toList ++ [u] ++ t.takeWhile isNameChar) else none
    | _ => none

/-- Family references `` `<opener>*` `` on a line (counted, not scored). -/
partial def families (line : String) : Nat :=
  go line.toList 0
where
  go : List Char → Nat → Nat
    | [], n => n
    | '`' :: t, n =>
      match gateOpener t with
      | some run =>
        match t.drop run.length with
        | '*' :: '`' :: rest => go rest (n + 1)
        | _ => go t n
      | none => go t n
    | _ :: t, n => go t n

/-- WRAP: a backticked gate opener whose name chars run to the end of the line. -/
partial def wrapOpen (line : String) : Bool :=
  go line.toList
where
  go : List Char → Bool
    | [] => false
    | '`' :: t =>
      match gateOpener t with
      | some run => if (t.drop run.length).isEmpty then true else go t
      | none => go t
    | _ :: t => go t

/-- WRAPPED_TAIL: at line start, optional whitespace, an optional comment marker
(two dashes, slash-dash, or `*`), optional whitespace, then a name-char run
ending in `refuted` followed by a backtick — the continuation line of a split
refutation name. -/
def wrapTail (line : String) : Bool :=
  let cs := line.toList.dropWhile Char.isWhitespace
  let variants : List (List Char) :=
    [cs] ++ (match cs with
      | '-' :: '-' :: t => [t]
      | '/' :: '-' :: t => [t]
      | '*' :: t => [t]
      | _ => [])
  variants.any fun v =>
    let v := v.dropWhile Char.isWhitespace
    let run := v.takeWhile isNameChar
    (String.ofList run).endsWith "refuted" && (v.drop run.length).headD ' ' == '`'

def wrapped (line : String) : Bool := wrapOpen line || wrapTail line

/-- Python: `def expectedGateVocab : String :=\s*\n?\s*"([^"]*)"` -/
def expectedPin (text : String) : Option String := do
  let parts := text.splitOn "def expectedGateVocab : String :="
  guard (parts.length ≥ 2)
  let after := (parts.drop 1).head!.toList.dropWhile Char.isWhitespace
  match after with
  | '"' :: t => some (String.ofList (t.takeWhile (· != '"')))
  | _ => none

/-- `^\s*(?:unsafe |partial )*def main\b` on some line: an exe root module. -/
def definesMain (text : String) : Bool :=
  (text.splitOn "\n").any fun l =>
    let cs := l.toList.dropWhile Char.isWhitespace
    let rec strip : List Char → Nat → List Char
      | cs, 0 => cs
      | cs, k + 1 =>
        if cs.take 7 == "unsafe ".toList then strip (cs.drop 7) k
        else if cs.take 8 == "partial ".toList then strip (cs.drop 8) k else cs
    let cs := strip cs 4
    cs.take 8 == "def main".toList && !((cs.drop 8).headD ' ' |> fun c => c.isAlphanum || c == '_')

/-- Python `sorted(Path)`: component-wise. -/
def pathLt (a b : String) : Bool :=
  go (a.splitOn "/") (b.splitOn "/")
where
  go : List String → List String → Bool
    | [], [] => false
    | [], _ => true
    | _, [] => false
    | x :: xs, y :: ys => if x == y then go xs ys else x < y

structure Scan where
  hits : Array (String × Array (String × Nat)) := #[]   -- name ↦ mentions (file, line), first-seen order
  families : Nat := 0
  wrapped : Nat := 0
  self : Nat := 0

def Scan.add (s : Scan) (name file : String) (line : Nat) : Scan :=
  match s.hits.findIdx? (·.1 == name) with
  | some i => { s with hits := s.hits.modify i fun (n, ms) => (n, ms.push (file, line)) }
  | none => { s with hits := s.hits.push (name, #[(file, line)]) }

/-- Scan one source file's text (`isPin`: the pin file, counted as `self`). -/
def scanFile (s : Scan) (file : String) (text : String) (isPin : Bool) : Scan := Id.run do
  let mut s := s
  let mut lineno := 0
  for line in text.splitOn "\n" do
    lineno := lineno + 1
    let ms := mentions line
    if isPin then
      s := { s with self := s.self + ms.length }
    else
      for m in ms do s := s.add m file lineno
      s := { s with families := s.families + families line }
      if wrapped line then s := { s with wrapped := s.wrapped + 1 }
  return s

def resolves (names : Std.HashSet String) (n : String) : Bool :=
  names.contains n || prefixes.any fun p => names.contains (p ++ n)

structure Reading where
  got : String
  unresolved : Array String
  sortedNames : Array String

def reading (s : Scan) (names : Std.HashSet String) : Reading :=
  let sortedNames := (s.hits.map (·.1)).qsort (· < ·)
  let unresolved := sortedNames.filter (!resolves names ·)
  let mentionsN := s.hits.foldl (fun acc (_, ms) => acc + ms.size) 0
  let refuted := (s.hits.filter fun (n, _) => n.endsWith "_refuted").size
  { got := s!"names={s.hits.size} mentions={mentionsN} families={s.families} refuted={refuted} wrapped={s.wrapped} self={s.self} unresolved={unresolved.size}",
    unresolved, sortedNames }

-- QUAL / SHORT / REFUTED
#guard mentions "see `scanNextToken_checkFlowValueIndent` and `checkBareDocument`." == ["scanNextToken_checkFlowValueIndent", "checkBareDocument"]
#guard mentions "`checkM` `checkFoo` `checkFooBar` `checkFoo2Bar_x'`" == ["checkFooBar", "checkFoo2Bar_x'"]
#guard mentions "`checkFooBAR` `checkFooBarXY`" == ["checkFooBarXY"]
#guard mentions "`flowOpen_underRunEnd_refuted` `_refuted` `x_refuted` `refuted`" == ["flowOpen_underRunEnd_refuted", "x_refuted"]
#guard mentions "`checkFoo_refuted` twice" == ["checkFoo_refuted"]            -- SHORT needs 2 segments; REFUTED matches
#guard mentions "`checkFooBar_refuted`" == ["checkFooBar_refuted", "checkFooBar_refuted"]  -- both patterns, as the Python
#guard mentions "`scanLoopIx_step` `scanLoop_` `scanLoop_a``scanLoop_b`" == ["scanLoopIx_step", "scanLoop_a", "scanLoop_b"]
#guard mentions "no closing `scanNextToken_foo" == []
#guard mentions "no closing `missing_refuted either" == []   -- the Python's REFUTED also required the closing backtick
#guard wrapTail "`missing_refuted` yes" == false && wrapTail "missing_refuted` yes"
-- families, wraps
#guard families "`dispatchStructural_none_*` `checkFoo_*` `scanLoop_x*` `scanLoop_*x`" == 2
#guard wrapOpen "the gate `scanNextToken_checkBlock" && wrapOpen "  `checkFlow" && !wrapOpen "`checkflow" && !wrapOpen "`scanLoop_x` done"
#guard wrapTail "  -- underRunTab_refuted` is" && wrapTail "refuted` x" && wrapTail "   * flowOpen_refuted`" && !wrapTail "refuted x" && !wrapTail "-- x refuted`"
#guard wrapTail "/-refuted`" && !wrapTail "--refuted"
-- pin, main
#guard expectedPin "def expectedGateVocab : String :=\n  \"names=1 mentions=2\"\n" == some "names=1 mentions=2"
#guard expectedPin "def expectedGateVocab : String := \"x\"" == some "x"
#guard expectedPin "nothing" == none
#guard definesMain "import X\n\nunsafe def main (args : List String) : IO UInt32 := do\n" && definesMain "  partial unsafe def main:IO Unit"
#guard !definesMain "def mainLoop := 1\ndef maint := 2" && !definesMain "-- def main\n  x"
#guard pathLt "L4YAML/A/B.lean" "L4YAML/A.lean" && !pathLt "L4YAML/A.lean" "L4YAML/A/B.lean"
-- reading
#guard (reading (scanFile (scanFile {} "a.lean" "`checkFooBar` `x_refuted`\n`checkFooBar`" false) pinFile "`checkFooBar`" true)
  (Std.HashSet.ofList ["checkFooBar"])).got == "names=2 mentions=3 families=0 refuted=1 wrapped=0 self=1 unresolved=1"

end Scripts.Lean.GateVocab
