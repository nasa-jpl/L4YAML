module

public import Scripts.Price.Pin
meta import Scripts.Price.Pin
public import Scripts.Lean.DeclRanges
meta import Scripts.Lean.DeclRanges

/-! # Scripts.Price.InlineClass — `inline_class_price.py` (items 286/287): the escape's INLINE class

`feeders` narrows `h_stream_fallback` to `False` (item 286's tree; retired since item 287 — the
instrument says so and stops), `arms` deletes the wrapper `block_dispatch_deferred_inline` and
locates every application it then lacks, `census` asks the runtime (a probe written to
`Scratch/InlineClassCensus.lean`, elaborated, deleted) what the class's reasons stand for.  Pins
`expectedInlineFeeders` / `expectedInlineArms` / `expectedInlineCensus` in
`Tests/Guards/Proofs/BlockDeferralClasses.lean`, checked from this side. -/

namespace Scripts.Price.InlineClass

open Scripts.Punt.Price (take drop padLeft padRight)
open Scripts.Price.Attribute (strip)

public section

def pin : String := "Tests/Guards/Proofs/BlockDeferralClasses.lean"
def rel : String := "L4YAML/Proofs/Production/StreamAccum.lean"
def probePath : String := "Scratch/InlineClassCensus.lean"
def wrapper : String := "block_dispatch_deferred_inline"
def narrowed : List String := ["accum_block_on_closeThenBlock", "accum_block_on_pendingContent", "accum_block_on_pendingBlockContent"]

/-- The census probe, verbatim (`CANDIDATES_HERE` is filled by `program`). -/
def programTemplate : String := r#"import Tests.SuiteRunner.Meta
import L4YAML.Scanner.IndexedDispatch

open L4YAML L4YAML.Scanner Tests.SuiteRunner

def trace (input : String) : Array ScannerState × Bool := Id.run do
  let mut s := (ScannerState.mk' input).emit .streamStart
  let mut out : Array ScannerState := #[s]
  for _ in [0:400] do
    match scanNextToken s with
    | .ok (some s') => s := s'; out := out.push s'
    | .ok none =>
      match scanLoop_checkDanglingNode s, scanLoop_checkFlowValueIndent s with
      | .ok (), .ok () => return (out, true)
      | _, _ => return (out, false)
    | .error _ => return (out, false)
  return (out, false)

def kindOf : Option YamlToken → String
  | some (.scalar _ _) | some (.alias _) | some .flowSequenceEnd | some .flowMappingEnd => "content"
  | some (.anchor _) | some (.tag _ _) => "props"
  | _ => "other"

def landing (sc0 : ScannerState) : String :=
  match scanNextToken_preprocess sc0 with
  | .ok (some (s0, _)) =>
    if s0.indents.size < sc0.indents.size then
      match s0.indents.back? with
      | some e =>
        if e.column == (s0.col : Int) then
          (if e.isSequence then "onto-seq" else "onto-map")
        else "off-level"
      | none => "off-level"
    else "no-pop"
  | _ => "?"

def rows (tag input : String) : Array String := Id.run do
  let (ss, ok) := trace input
  let mut out := #[]
  for i in [1:ss.size] do
    let sc := ss[i]!
    match scanNextToken_preprocess sc with
    | .ok (some (s_prep, ':')) =>
      let s_dis := if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true } else s_prep
      let disp := match scanNextToken_dispatchBlockIndicators s_dis ':' with
        | .ok (some _) => true | _ => false
      let k := kindOf (lastRealTokenVal? sc.tokens)
      if !s_prep.inFlow && s_prep.line == sc.line && sc.col != 0 && disp && k != "other" then
        let live := sc.simpleKey.possible && sc.simpleKey.pos.line == sc.line
        out := out.push s!"ROW\t{k}\tacc={ok}\tlive={live}\t{landing ss[i-1]!}\t{tag}\t{repr input}"
    | _ => pure ()
  return out

def candidates : List String := CANDIDATES_HERE

#eval show IO Unit from do
  let dir : System.FilePath := "yaml-test-suite/src"
  let mut n := 0
  for e in ((← dir.readDir).qsort (fun a b => a.fileName < b.fileName)) do
    if e.path.extension == some "yaml" then
      n := n + 1
      let id := e.path.fileStem.getD "?"
      let mut j := 0
      for tc in parseTestFile id (← IO.FS.readFile e.path) do
        for r in rows s!"{id}#{j}" (unescapeTestYaml tc.yaml) do IO.println r
        j := j + 1
  IO.println s!"SOURCES {n}"
  for c in candidates do
    for r in rows "cand" c do IO.println r
"#

def candidates : List String := [
  "\"a\" b : c\n",
  "&x a\n*x : b\n",
  "a: *x : b\n",
  "[a] b : c\n",
  "--- a : b\n",
  "- a : b\n",
  "a: b : c\n",
  "? a : b\n",
  "? a\n: b : c\n",
  "\"a\nb\" : c\n",
  "a\n b : c\n",
  "- !t a : b\n",
  "&x a : b\n",
  "&p : v\n",
  "!t : v\n",
  "k: &p : 1\n",
  "- &p : v\n",
  "? &p : v\n",
  "k:\n  :\n&p : 2\n",
  "&a !t : v\n",
  "k:\n  :\nb: 2\n",
  "- a:\n    b:\n  c: 1\n",
  "a:\n  b:\n    c:\nd: 1\n",
  "[a] : b\n",
  "{a: 1} : b\n",
  "- [a] : b\n",
  "k: [a] : b\n",
  "'a' : b\n",
  "\"a\" : b\n",
  "a\t: b\n",
  "*x : b\n"
]

/-- `lean_str`: a Lean string literal for a candidate. -/
def leanStr (t : String) : String :=
  "\"" ++ (t.toList.foldl (fun acc c =>
    acc ++ (if c == '\\' then "\\\\" else if c == '"' then "\\\"" else if c == '\n' then "\\n" else if c == '\t' then "\\t" else c.toString)) "") ++ "\""

#guard leanStr "a\tb\n" == "\"a\\tb\\n\""
#guard leanStr "\"a\"" == "\"\\\"a\\\"\""

def program : String :=
  let parts := programTemplate.splitOn "CANDIDATES_HERE"
  "[" ++ ", ".intercalate (candidates.map leanStr) ++ "]" |> fun cs => cs.intercalate parts

#guard (program.splitOn "CANDIDATES_HERE").length == 1
#guard candidates.length == 31

/-- The pin verdict as the Python prints it: `absent` is not an error, `MOVED` is. -/
def pinVerdict (label : String) (want : Option String) (line : String) : Array String × UInt32 :=
  match want with
  | none => (#[s!"{label} absent"], 0)
  | some w => if w == line then (#[s!"{label} agrees"], 0)
              else (#[s!"{label} MOVED", s!"  got      {line}", s!"  expected {w}"], 1)

-- feeders (item 286's tree)

def fallbackHead : String := "    (h_stream_fallback :"
def streamLine : String := "      SLYamlStream sp_start sp_block_ctx)"

/-- `(head line, replacement)` of the two inline applications; each spans `siteLen` lines. -/
def sites : List (String × String × String) :=
  [("closeThenBlock", "      exact block_dispatch_deferred_inline sp_start sp_block_ctx sp_scan' s'",
    "      exact (h_stream_fallback h_res h_mid.2.2.1).elim"),
   ("pendingBlockContent", "      block_dispatch_deferred_inline sp_start sp_block_ctx sp_scan' s'",
    "      (h_stream_fallback h_res h_mid.2.2.1).elim)")]
def siteLen : Nat := 5

def hasFallback (lines : Array String) : Bool := lines.any (·.startsWith fallbackHead)

def retiredLine : String :=
  "feeders: `h_stream_fallback` retired at item 287 -- `arms` reads the class's sites on this tree"

/-- `narrow`: the fallback of each narrowed declaration (whose first line is `start d`, 0-based,
    off the declaration ranges) becomes `False`, both applications `.elim`. -/
def narrow (lines : Array String) (start : String → Option Nat) : Except String (Array String) := do
  let mut out := lines
  for d in narrowed do
    let some s := start d | throw s!"KeyError: {d}"
    let some p := (List.range (out.size - s)).find? (fun k => out[s + k]!.startsWith fallbackHead) | throw s!"StopIteration: {d}"
    let p := s + p
    let some q := (List.range 8).find? (fun k => p + k < out.size && out[p + k]! == streamLine) | throw s!"StopIteration: {d}"
    out := out.set! (p + q) "      False)"
  for (name, head, repl) in sites do
    let hits := (List.range out.size).filter fun i => out[i]! == head
    if hits.length != 1 then throw s!"AssertionError: ('{name}', {hits})"
    let i := hits.head!
    if !((out[i + 1]!).splitOn "(h_stream_fallback h_res h_mid.2.2.1)").length > 1 then
      throw s!"AssertionError: ('{name}', {repr out[i + 1]!})"
    if !(strip out[i + siteLen - 1]!).startsWith "(nic0_of_block_dispatch" then
      throw s!"AssertionError: ('{name}', {repr out[i + 4]!})"
    let tl := Scripts.Price.Attribute.rstrip out[i + siteLen - 1]!
    let extra := tl.length - (tl.toList.reverse.dropWhile (· == ')')).length - 1
    if extra != (if name == "pendingBlockContent" then 1 else 0) then throw s!"AssertionError: ('{name}', {repr tl})"
    out := (out.extract 0 i) ++ #[repl] ++ (out.extract (i + siteLen) out.size)
  return out

/-- `arm_of`: the nearest `  | pendingX …` arm above line `i` (0-based) inside its declaration (first line `declLine`). -/
def armOf (lines : Array String) (i declLine : Nat) : String := Id.run do
  let mut j := i
  while j > declLine do
    let l := lines[j]!
    if l.startsWith "  | " then
      let w := String.ofList ((drop l 4).toList.takeWhile fun c => c.isAlphanum || c == '_')
      if w != "" then return w
    j := j - 1
  return "-"

#guard armOf #["lemma a", "  | pendingFlow x =>", "    y", "    z"] 3 0 == "pendingFlow"
#guard armOf #["lemma a", "    y"] 1 0 == "-"

/-- `^REL:(\d+):(\d+): error(?:\([\w.]+\))?: (.*)$` → `(line, col, msg)`. -/
def errRow? (l : String) : Option (Nat × Nat × String) := do
  let rest ← if l.startsWith (rel ++ ":") then some (drop l (rel.length + 1)) else none
  let p := rest.splitOn ":"
  guard (p.length ≥ 3)
  let ln ← p[0]!.toNat?
  let col ← p[1]!.toNat?
  let tail := ":".intercalate (p.drop 2)
  let tail ← if tail.startsWith " error" then some (drop tail 6) else none
  let tail := if tail.startsWith "(" then (match tail.splitOn ")" with | _ :: r => ")".intercalate r | [] => tail) else tail
  let msg ← if tail.startsWith ": " then some (drop tail 2) else none
  return (ln, col, msg)

#guard errRow? "L4YAML/Proofs/Production/StreamAccum.lean:12:4: error: boom: x" == some (12, 4, "boom: x")
#guard errRow? "L4YAML/Proofs/Production/StreamAccum.lean:12:4: error(lean.unknownIdentifier): Unknown identifier `b`" == some (12, 4, "Unknown identifier `b`")
#guard errRow? "Other.lean:1:1: error: x" == none

-- arms (item 287 on)

def reasons : List String := ["tab", "implicitValue", "markerLine", "noKeyContext"]

def indentOf (l : String) : Nat := l.length - (Scripts.Price.Attribute.lstrip l).length

/-- `arm_label`: the application's own `| reason`, the nearest `  | pendingX` above, or the
    `by_cases` at its indent it negates. -/
def armLabel (lines : Array String) (i declLine : Nat) : String := Id.run do
  let l := lines[i]!
  let s := Scripts.Price.Attribute.lstrip l
  if s.startsWith "| " then
    let w := String.ofList ((drop s 2).toList.takeWhile fun c => c.isAlphanum || c == '_')
    if reasons.contains w then return w
  let ind := indentOf l
  let mut j := i
  while j > declLine + 1 do
    j := j - 1
    let t := lines[j]!
    let ts := strip t
    if ts == "" || ts.startsWith "--" then continue
    if t.startsWith "  | pending" then
      return String.ofList ((drop t 4).toList.takeWhile fun c => c.isAlphanum || c == '_')
    if indentOf t == ind then
      let u := Scripts.Price.Attribute.lstrip t
      if u.startsWith "by_cases " then
        return "¬" ++ String.ofList ((drop u 9).toList.takeWhile fun c => c.isAlphanum || c == '_')
  return "-"

#guard armLabel #["lemma a", "  | pendingFlow x =>", "    | noKeyContext => foo"] 2 0 == "noKeyContext"
#guard armLabel #["lemma a", "  | pendingFlow x =>", "    foo"] 2 0 == "pendingFlow"
#guard armLabel #["lemma a", "  by_cases hk : p", "  · x", "  foo"] 3 0 == "¬hk"
#guard armLabel #["lemma a", "  foo"] 1 0 == "-"

def deletedMarker : String := "-- WRAPPER DELETED (lake run price -- inline-class arms)"

-- census

def kinds : List String := ["content", "props"]

/-- A `ROW\t…` line split on tabs: `kind, acc, live, landing, tag, input`. -/
def rowOf? (l : String) : Option (Array String) :=
  if l.startsWith "ROW\t" then some (l.splitOn "\t").toArray else none

end

end Scripts.Price.InlineClass
