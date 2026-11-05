module

public import Lean.Data.Json
public import Tests.SuiteRunner.HtmlReport

/-!
# Test-result reports — the pure half of `suiterunner --compare` / `--reports`

Ported from `scripts/cross-lang-compare.py` and `scripts/generate-test-reports.py`
(Rule 9 phase 4, row 1).  Everything here is a function of strings:

* `parseTotal?` reads a backend's `TOTAL:` line; `presetLines` / `verdictLines`
  are the comparison's stdout; `crossLangJson` its `cross-lang-results.json`;
* `crossLangHtml` renders that JSON as `cross-lang-comparison.html`;
* `junitCases` reads a JUnit XML file (a hand reader for `testsuite` /
  `testcase` / `failure` / `skipped` and their attributes — no dependency) and
  `pythonFfiHtml` renders the sections as `python-ffi-tests.html`.

The HTML is the Python's byte for byte (`"\n".join(parts)`, Python's
`html.escape` with `&#x27;`); `Tests/SuiteRunner/Main.lean` does the spawning
and the files.
-/

namespace Tests.SuiteRunner.Reports

@[expose] public section

instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e, .error f => e == f
    | _, _ => false

def backends : List String := ["lean", "c", "python", "rust"]
def presets : List String := ["unlimited", "default", "strict", "permissive", "safe_tags"]

/-- `passed, failed, skipped, total`. -/
structure Counts where
  passed : Nat
  failed : Nat
  skipped : Nat
  total : Nat
  deriving Repr, BEq, Inhabited

def Counts.pyTuple (c : Counts) : String := s!"({c.passed}, {c.failed}, {c.skipped}, {c.total})"

/-- Python `str.split()`: on runs of whitespace, no empties. -/
def pySplit (s : String) : List String :=
  go s.toList [] []
where
  go : List Char → List Char → List String → List String
    | [], cur, acc => (if cur.isEmpty then acc else String.ofList cur.reverse :: acc).reverse
    | c :: t, cur, acc =>
      if c.isWhitespace then go t [] (if cur.isEmpty then acc else String.ofList cur.reverse :: acc)
      else go t (c :: cur) acc

#guard pySplit "  a\tb  c " == ["a", "b", "c"]

/-- The `TOTAL:` line of a suiterunner run: `parts[1] parts[3] parts[5] parts[7].strip("()")`. -/
def parseTotal? (out : String) : Option Counts := Id.run do
  for line in out.splitOn "\n" do
    if (line.splitOn "TOTAL:").length > 1 then
      let parts := (pySplit line).toArray
      if parts.size < 8 then return none
      let strip (s : String) : String := String.ofList ((s.toList.dropWhile (· == '(')).reverse.dropWhile (· == ')') |>.reverse)
      return (do
        let p ← parts[1]!.toNat?; let f ← parts[3]!.toNat?; let s ← parts[5]!.toNat?
        let t ← (strip parts[7]!).toNat?
        some ⟨p, f, s, t⟩)
  return none

#guard parseTotal? "══\n  TOTAL: 869 passed, 0 failed, 151 skipped (1020 total)\n══" == some ⟨869, 0, 151, 1020⟩
#guard parseTotal? "no total here" == none

/-- Python `f"{preset:12s}"`: left-justified, padded to 12. -/
def pad12 (s : String) : String := s ++ String.ofList (List.replicate (12 - s.length) ' ')

/-- The line printed for one preset: all four identical, or the MISMATCH dict. -/
def presetLine (preset : String) (vals : List (String × Counts)) : String × Bool :=
  let cs := vals.map (·.2)
  let same := cs.all (· == cs.headD default)
  if same then
    let c := cs.headD default
    (s!"{pad12 preset}: {c.passed} passed, {c.failed} failed, {c.skipped} skipped ({c.total} total) — all 4 backends identical", true)
  else
    let d := ", ".intercalate (vals.map fun (b, c) => s!"'{b}': {c.pyTuple}")
    (s!"MISMATCH for preset '{preset}': \{{d}}", false)

#guard presetLine "strict" (backends.map fun b => (b, ⟨1, 2, 3, 6⟩)) ==
  ("strict      : 1 passed, 2 failed, 3 skipped (6 total) — all 4 backends identical", true)
#guard (presetLine "safe_tags" [("lean", ⟨1, 0, 0, 1⟩), ("c", ⟨0, 0, 0, 0⟩)]).1 ==
  "MISMATCH for preset 'safe_tags': {'lean': (1, 0, 0, 1), 'c': (0, 0, 0, 0)}"

def verdictLine (allMatch : Bool) : String :=
  if allMatch then "✓ All backends produce identical results for every preset" else "✗ Backend mismatch detected!"

/-- `json.dumps(indent=2)` of `{preset: {backend: {passed, failed, skipped, total}}}`, insertion order. -/
def crossLangJson (results : List (String × List (String × Counts))) : String :=
  let obj (rows : List (String × String)) (ind : String) : String :=
    if rows.isEmpty then "{}" else
    "{\n" ++ ",\n".intercalate (rows.map fun (k, v) => s!"{ind}  \"{k}\": {v}") ++ s!"\n{ind}}"
  obj (results.map fun (preset, bs) =>
    (preset, obj (bs.map fun (b, c) =>
      (b, obj [("passed", toString c.passed), ("failed", toString c.failed),
               ("skipped", toString c.skipped), ("total", toString c.total)] "    ")) "  ")) ""

#guard crossLangJson [("default", [("lean", ⟨1, 2, 3, 6⟩)])] ==
  "{\n  \"default\": {\n    \"lean\": {\n      \"passed\": 1,\n      \"failed\": 2,\n      \"skipped\": 3,\n      \"total\": 6\n    }\n  }\n}"

/-- Python `html.escape` (quote=True): `&`, `<`, `>`, `"`, `'` → `&#x27;`. -/
def pyEscape (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;" |>.replace "\"" "&quot;" |>.replace "'" "&#x27;"

#guard pyEscape "a<b>&'\"" == "a&lt;b&gt;&amp;&#x27;&quot;"

/-- `cross-lang-results.json` read back: presets in file order, each backend's counts. -/
def readCrossLang (j : Lean.Json) : Except String (List (String × List (String × Counts))) := do
  let .obj top := j | throw "cross-lang-results.json: not an object"
  let mut out := []
  for (preset, v) in top.toArray.toList do
    let .obj bs := v | throw s!"{preset}: not an object"
    let mut row := []
    for (b, c) in bs.toArray.toList do
      let get (k : String) : Except String Nat := match c.getObjValAs? Nat k with
        | .ok n => .ok n | .error e => .error s!"{preset}/{b}/{k}: {e}"
      row := row ++ [(b, ⟨← get "passed", ← get "failed", ← get "skipped", ← get "total"⟩)]
    out := out ++ [(preset, row)]
  return out

/-- `generate_cross_lang_html`'s document. -/
def crossLangHtml (data : List (String × List (String × Counts))) : String := Id.run do
  let mut parts : Array String := #[
    "<!DOCTYPE html>",
    "<html lang=\"en\"><head><meta charset=\"utf-8\">",
    "<title>Cross-Language yaml-test-suite Comparison</title>",
    "<style>",
    "body{font-family:system-ui,sans-serif;margin:2em;background:#f8f9fa}",
    "h1{color:#1a1a2e} h2{color:#16213e;margin-top:1.5em}",
    "table{border-collapse:collapse;margin:1em 0}",
    "th,td{border:1px solid #dee2e6;padding:6px 14px;text-align:right}",
    "th{background:#343a40;color:#fff;text-align:center}",
    "td:first-child{text-align:left;font-weight:bold}",
    ".match{background:#d4edda;color:#155724}",
    ".mismatch{background:#f8d7da;color:#721c24}",
    ".summary{font-size:1.1em;margin:1em 0}",
    "</style></head><body>",
    "<h1>Cross-Language yaml-test-suite Comparison</h1>",
    "<p>All four backends (Lean, C, Python, Rust) run the same yaml-test-suite test cases through the verified parser via their respective FFI layers.</p>"]
  let mut allMatch := true
  parts := parts.push "<h2>Results by Limit Preset</h2>"
  parts := parts.push "<table><tr><th>Preset</th><th>Passed</th><th>Failed</th><th>Skipped</th><th>Total</th><th>Backends Match?</th></tr>"
  for preset in presets do
    let some row := data.lookup preset | continue
    let vals := backends.filterMap fun b => row.lookup b
    let match_ := vals.all (· == vals.headD default)
    if !match_ then allMatch := false
    let css := if match_ then "match" else "mismatch"
    let icon := if match_ then "✓" else "✗"
    let c := vals.headD default
    parts := parts.push s!"<tr><td>{pyEscape preset}</td><td>{c.passed}</td><td>{c.failed}</td><td>{c.skipped}</td><td>{c.total}</td><td class=\"{css}\">{icon} {if match_ then "All identical" else "MISMATCH"}</td></tr>"
  parts := parts.push "</table>"
  parts := parts.push "<h2>Full Matrix (Backend × Preset)</h2>"
  parts := parts.push "<table><tr><th>Backend</th>"
  for preset in presets do parts := parts.push s!"<th>{pyEscape preset}</th>"
  parts := parts.push "</tr>"
  for b in backends do
    parts := parts.push s!"<tr><td>{pyEscape b}</td>"
    for preset in presets do
      match data.lookup preset >>= (·.lookup b) with
      | some d => parts := parts.push s!"<td>{d.passed}/{d.failed}/{d.skipped}</td>"
      | none => parts := parts.push "<td>—</td>"
    parts := parts.push "</tr>"
  parts := parts.push "</table>"
  let color := if allMatch then "match" else "mismatch"
  let icon := if allMatch then "✓" else "✗"
  let msg := if allMatch then "All backends produce identical results for every preset" else "Backend mismatch detected!"
  parts := parts.push s!"<p class=\"summary {color}\">{icon} {msg}</p>"
  parts := parts.push "</body></html>"
  return "\n".intercalate parts.toList

/-! ## JUnit XML -/

/-- One `testcase`: `classname.name`, status, css class, `time`. -/
structure Case where
  name : String
  status : String
  css : String
  time : String
  deriving Repr, BEq, Inhabited

/-- Parse hexadecimal XML character references, shared by display and validation. -/
def xmlHexNat (hs : List Char) : Option Nat :=
  if hs.isEmpty || !hs.all (fun c => c.isDigit || "abcdefABCDEF".toList.contains c) then none
  else some (hs.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - '0'.toNat else (c.toLower.toNat - 'a'.toNat + 10))) 0)

/-- XML entities and character references. -/
def xmlUnescape (s : String) : String := Id.run do
  let mut out := ""
  let mut rest := s.toList
  while !rest.isEmpty do
    match rest with
    | '&' :: t =>
      let ent := t.takeWhile (· != ';')
      let after := t.drop (ent.length + 1)
      let e := String.ofList ent
      let rep : Option String :=
        if e == "amp" then some "&" else if e == "lt" then some "<" else if e == "gt" then some ">"
        else if e == "quot" then some "\"" else if e == "apos" then some "'"
        else match ent with
          | '#' :: 'x' :: hs => (xmlHexNat hs).map fun n => String.singleton (Char.ofNat n)
          | '#' :: ds => ((String.ofList ds).toNat?).map fun n => String.singleton (Char.ofNat n)
          | _ => none
      match rep with
      | some r => if t.length > ent.length then out := out ++ r; rest := after else out := out.push '&'; rest := t
      | none => out := out.push '&'; rest := t
    | c :: t => out := out.push c; rest := t
    | [] => pure ()
  return out

#guard xmlUnescape "a &lt;b&gt; &amp;&quot;&apos;&#65;&#x42; &bogus; &" == "a <b> &\"'AB &bogus; &"

/-- Recognized XML entities and scalar-valued numeric character references.
    Reject malformed references before the permissive display unescaper runs. -/
def validXmlEntities : List Char → Bool
  | [] => true
  | '&' :: t =>
    let ent := t.takeWhile (· != ';')
    let e := String.ofList ent
    let num : Option Nat :=
      if e.startsWith "#x" then xmlHexNat (ent.drop 2)
      else if e.startsWith "#" then (String.ofList (ent.drop 1)).toNat? else none
    let scalar := match num with
      | some n => n == 9 || n == 10 || n == 13 || (n ≥ 32 && n ≤ 0xD7FF) || (n ≥ 0xE000 && n ≤ 0xFFFD) || (n ≥ 0x10000 && n ≤ 0x10FFFF)
      | none => false
    t.length > ent.length && (["amp", "lt", "gt", "quot", "apos"].contains e || scalar) &&
      validXmlEntities (t.drop (ent.length + 1))
  | _ :: t => validXmlEntities t
termination_by cs => cs.length
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- A start tag's attributes: `name="value"` / `name='value'`, unescaped; an
    unquoted or missing value is an error, as for `xml.etree`. -/
partial def attrsOf (tag : String) : Except String (List (String × String)) :=
  go (tag.toList.dropWhile fun c => !c.isWhitespace) []
where
  go (cs : List Char) (acc : List (String × String)) : Except String (List (String × String)) :=
    let cs := cs.dropWhile Char.isWhitespace
    if cs.isEmpty then .ok acc.reverse else
    let name := cs.takeWhile fun c => c != '=' && !c.isWhitespace && c != '/' && c != '>'
    if name.isEmpty then go (cs.drop 1) acc else
    let rest := (cs.drop name.length).dropWhile Char.isWhitespace
    match rest with
    | '=' :: t =>
      if acc.any (fun kv => kv.1 == String.ofList name) then
        .error s!"duplicate attribute {String.ofList name}"
      else
      match t.dropWhile Char.isWhitespace with
      | q :: v =>
        if q == '"' || q == '\'' then
          let val := v.takeWhile (· != q)
          if val.length == v.length then .error s!"unterminated value of attribute {String.ofList name}"
          else if !validXmlEntities val || val.contains '<' then .error s!"invalid value of attribute {String.ofList name}"
          else
            let afterVal := v.drop (val.length + 1)
            if !(afterVal.headD ' ').isWhitespace && afterVal.headD ' ' != '/' && afterVal.headD ' ' != '>' then
              .error "attributes must be separated by whitespace"
            else
              go afterVal ((String.ofList name, xmlUnescape (String.ofList val)) :: acc)
        else .error s!"unquoted value of attribute {String.ofList name}"
      | [] => .error s!"attribute {String.ofList name} has no value"
    | _ => .error s!"attribute {String.ofList name} has no value"

#guard attrsOf "testcase classname=\"tests.A\" name='t &amp; u' time=\"0.01\"" ==
  .ok [("classname", "tests.A"), ("name", "t & u"), ("time", "0.01")]
#guard attrsOf "testcase name=bare" == .error "unquoted value of attribute name"
#guard attrsOf "testcase name=\"open" == .error "unterminated value of attribute name"
#guard attrsOf "testcase name" == .error "attribute name has no value"
#guard attrsOf "testcase name=\"a\"time=\"1\"" == .error "attributes must be separated by whitespace"

/-- The elements of an XML text as a flat list: `(name, attrs, isStart, isEnd)` —
    comments, declarations and CDATA skipped; `<x/>` is start and end.
    This deliberately bounded JUnit reader rejects a DOCTYPE declaration
    with an internal subset rather than attempting general DTD/entity support.
    An unterminated tag, comment, CDATA or declaration is an error. -/
partial def tokens (s : String) : Except String (List (String × List (String × String) × Bool × Bool)) :=
  go s.toList [] 0
where
  go (cs : List Char) (acc : List (String × List (String × String) × Bool × Bool)) (depth : Nat) :
      Except String (List (String × List (String × String) × Bool × Bool)) :=
    match cs with
    | [] => .ok acc.reverse
    | '<' :: '!' :: '-' :: '-' :: t => do go (← skipTo t ['-', '-', '>'] "comment") acc depth
    | '<' :: '!' :: '[' :: 'C' :: 'D' :: 'A' :: 'T' :: 'A' :: '[' :: t => do go (← skipTo t [']', ']', '>'] "CDATA section") acc depth
    | '<' :: '!' :: 'D' :: 'O' :: 'C' :: 'T' :: 'Y' :: 'P' :: 'E' :: t => do
      go (← skipDoctype t none) acc depth
    | '<' :: '!' :: t | '<' :: '?' :: t => do go (← skipTo t ['>'] "declaration") acc depth
    | '<' :: '/' :: t => do
      let name := t.takeWhile fun c => c != '>' && !c.isWhitespace
      let afterName := (t.drop name.length).dropWhile Char.isWhitespace
      match afterName with
      | '>' :: rest => go rest ((String.ofList name, [], false, true) :: acc) (depth - 1)
      | _ => throw s!"invalid end tag </{String.ofList name}>"
    | '<' :: t => do
      let body := takeTag t
      if body.length == t.length then throw s!"unterminated tag <{String.ofList (body.take 20)}"
      let rest := t.drop body.length |>.drop 1
      let selfClose := body.getLast? == some '/'
      let name := body.takeWhile fun c => !c.isWhitespace && c != '/' && c != '>'
      let attrs ← attrsOf (String.ofList body)
      go rest ((String.ofList name, attrs, true, selfClose) :: acc) (depth + if selfClose then 0 else 1)
    | '&' :: t => do
      if depth == 0 then throw "text outside root element"
      let ent := t.takeWhile (· != ';')
      if t.length == ent.length || !validXmlEntities ('&' :: ent ++ [';']) then throw "invalid entity in content"
      go (t.drop (ent.length + 1)) acc depth
    | c :: t => do
      if depth == 0 && !c.isWhitespace then throw "text outside root element"
      go t acc depth
  /-- Skip a DOCTYPE without accepting internal subsets; delimiters in quoted
      external identifiers are ordinary characters, not markup boundaries. -/
  skipDoctype (cs : List Char) (quoted : Option Char) : Except String (List Char) :=
    match cs with
    | [] => .error "unterminated declaration"
    | c :: t =>
      match quoted with
      | some q => skipDoctype t (if c == q then none else some q)
      | none =>
        if c == '[' then .error "DOCTYPE internal subset unsupported"
        else if c == '"' || c == '\'' then skipDoctype t (some c)
        else if c == '>' then .ok t
        else skipDoctype t none
  skipTo (cs : List Char) (pat : List Char) (what : String) : Except String (List Char) :=
    match cs with
    | [] => .error s!"unterminated {what}"
    | _ :: t => if pat.isPrefixOf cs then .ok (cs.drop pat.length) else skipTo t pat what
  /-- the tag body up to its `>`, quotes respected -/
  takeTag (cs : List Char) : List Char :=
    let rec loop (cs : List Char) (q : Option Char) (acc : List Char) : List Char :=
      match cs with
      | [] => acc.reverse
      | c :: t =>
        match q with
        | some qc => loop t (if c == qc then none else q) (c :: acc)
        | none => if c == '>' then acc.reverse else if c == '"' || c == '\'' then loop t (some c) (c :: acc) else loop t none (c :: acc)
    loop cs none []

/-- `generate_python_ffi_html`'s reading of one JUnit file: every `testcase`
    (document order), with `failure` / `skipped` children.  The document must
    be well formed the way `xml.etree` demanded it: tags nest and match, one
    root element, closed, nothing after it — a truncated file is an error, not
    a shorter report. -/
def junitCases (xml : String) : Except String (List Case) := do
  let toks ← tokens xml
  let mut out : List Case := []
  let mut cur : Option (String × String) := none    -- (name, time) of the open testcase
  let mut failed := false
  let mut skipped := false
  let mut stack : List String := []
  let mut rootsClosed := 0
  for (name, attrs, isStart, isEnd) in toks do
    if rootsClosed > 0 then throw s!"element <{name}> after the root element closed"
    if isStart && !isEnd then stack := name :: stack
    if isEnd then
      if isStart then
        if stack.isEmpty then rootsClosed := rootsClosed + 1
      else
        match stack with
        | top :: rest =>
          if top != name then throw s!"end tag </{name}> closes <{top}>"
          stack := rest
          if rest.isEmpty then rootsClosed := rootsClosed + 1
        | [] => throw s!"end tag </{name}> with no open element"
    if name == "testcase" && isStart then
      let n := (attrs.lookup "classname").getD "" ++ "." ++ (attrs.lookup "name").getD ""
      cur := some (n, (attrs.lookup "time").getD "0")
      failed := false; skipped := false
      if isEnd then
        out := out ++ [⟨n, "PASS", "pass", (attrs.lookup "time").getD "0"⟩]; cur := none
    else if name == "failure" && isStart && cur.isSome then failed := true
    else if name == "skipped" && isStart && cur.isSome then skipped := true
    else if name == "testcase" && isEnd then
      if let some (n, t) := cur then
        let (st, css) := if failed then ("FAIL", "fail") else if skipped then ("SKIP", "skip") else ("PASS", "pass")
        out := out ++ [⟨n, st, css, t⟩]
      cur := none
  if let top :: _ := stack then throw s!"document ends inside <{top}>"
  if rootsClosed == 0 then throw "no root element"
  return out

def exampleJunit : String :=
  "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<testsuites><testsuite name=\"pytest\" tests=\"3\">\n" ++
  "<testcase classname=\"tests.A\" name=\"ok\" time=\"0.001\" />\n" ++
  "<testcase classname=\"tests.A\" name=\"bad &lt;x&gt;\" time=\"0.2\"><failure message=\"boom\">trace &amp; more</failure></testcase>\n" ++
  "<testcase classname=\"tests.B\" name=\"later\" time=\"0\"><skipped type=\"pytest.skip\" message=\"no lib\"/></testcase>\n" ++
  "<!-- <testcase name=\"commented\"/> --></testsuite></testsuites>\n"

#guard junitCases exampleJunit == .ok
  [⟨"tests.A.ok", "PASS", "pass", "0.001"⟩, ⟨"tests.A.bad <x>", "FAIL", "fail", "0.2"⟩, ⟨"tests.B.later", "SKIP", "skip", "0"⟩]

structure Section where
  title : String
  rows : List Case
  deriving Repr, Inhabited

def Section.count (s : Section) (css : String) : Nat := (s.rows.filter (·.css == css)).length

/-- `generate_python_ffi_html`'s document, and the test count it prints. -/
def pythonFfiHtml (sections : List Section) : String × Nat := Id.run do
  let mut parts : Array String := #[
    "<!DOCTYPE html>",
    "<html lang=\"en\"><head><meta charset=\"utf-8\">",
    "<title>Python API Test Results</title>",
    "<style>",
    "body{font-family:system-ui,sans-serif;margin:2em;background:#f8f9fa}",
    "h1{color:#1a1a2e} h2{color:#16213e;margin-top:2em}",
    "table{border-collapse:collapse;width:100%;margin:1em 0}",
    "th,td{border:1px solid #dee2e6;padding:6px 12px;text-align:left}",
    "th{background:#343a40;color:#fff}",
    ".pass{background:#d4edda;color:#155724}",
    ".fail{background:#f8d7da;color:#721c24}",
    ".skip{background:#fff3cd;color:#856404}",
    ".summary{font-size:1.1em;margin:0.5em 0}",
    "</style></head><body>",
    "<h1>Python API Test Results</h1>"]
  let mut gt := 0; let mut gp := 0; let mut gf := 0; let mut gs := 0
  for sec in sections do
    let total := sec.rows.length
    let p := sec.count "pass"; let f := sec.count "fail"; let s := sec.count "skip"
    gt := gt + total; gp := gp + p; gf := gf + f; gs := gs + s
    parts := parts.push s!"<h2>{pyEscape sec.title}</h2>"
    parts := parts.push s!"<p class=\"summary\">Total: {total} &mdash; <span class=\"pass\">Passed: {p}</span> &middot; <span class=\"fail\">Failed: {f}</span> &middot; <span class=\"skip\">Skipped: {s}</span></p>"
    parts := parts.push "<table><tr><th>Test</th><th>Status</th><th>Time (s)</th></tr>"
    for c in sec.rows do
      parts := parts.push s!"<tr><td>{pyEscape c.name}</td><td class=\"{c.css}\">{c.status}</td><td>{pyEscape c.time}</td></tr>"
    parts := parts.push "</table>"
  parts := parts.push "<hr>"
  let color := if gf == 0 then "pass" else "fail"
  parts := parts.push s!"<p class=\"summary {color}\">Grand Total: {gt} &mdash; Passed: {gp}, Failed: {gf}, Skipped: {gs}</p>"
  parts := parts.push "</body></html>"
  return ("\n".intercalate parts.toList, gt)

#guard junitCases "<testsuites><testsuite><testcase name=\"first\"/></testsuite>" ==
  .error "document ends inside <testsuites>"
#guard junitCases "<testsuite><testcase name=\"a\"></testsuite>" == .error "end tag </testsuite> closes <testcase>"
#guard junitCases "<testsuite/><testsuite/>" == .error "element <testsuite> after the root element closed"
#guard junitCases "<testsuite><testcase name=\"a\" time=1/></testsuite>" == .error "unquoted value of attribute time"
#guard junitCases "<testsuite><!-- open" == .error "unterminated comment"
#guard junitCases "<testsuite><testcase name=\"a\"" == .error "unterminated tag <testcase name=\"a\""
#guard junitCases "<?xml version=\"1.0\"?>\n" == .error "no root element"
#guard junitCases "</testsuite>" == .error "end tag </testsuite> with no open element"

-- Malformed JUnit documents must not become green one-test reports.  The
-- original Python ElementTree reader rejects all seven inputs.
#guard junitCases "garbage<testsuite><testcase name=\"ok\"/></testsuite>" == .error "text outside root element"
#guard junitCases "<testsuite><testcase name=\"ok\"/></testsuite>garbage" == .error "text outside root element"
#guard junitCases "<testsuite><testcase name=\"a\" name=\"b\"/></testsuite>" == .error "duplicate attribute name"
#guard junitCases "<testsuite><testcase name=\"&unknown;\"/></testsuite>" == .error "invalid value of attribute name"
#guard junitCases "<testsuite><testcase name=\"a\"/> &broken; </testsuite>" == .error "invalid entity in content"
#guard junitCases "<testsuite><testcase name=\"a\"/></testsuite garbage>" == .error "invalid end tag </testsuite>"

-- This bounded reader deliberately refuses DTD internal subsets; lock the boundary.
#guard junitCases "<!DOCTYPE testsuite [<!ELEMENT testsuite ANY>]><testsuite><testcase name=\"a\"/></testsuite>" ==
  .error "DOCTYPE internal subset unsupported"
-- Ordinary DOCTYPE declarations without an internal subset remain accepted.
#guard junitCases "<!DOCTYPE testsuite><testsuite><testcase name=\"a\"/></testsuite>" ==
  .ok [⟨".a", "PASS", "pass", "0"⟩]
-- Quoted delimiters in a system identifier are not an internal subset.
#guard junitCases "<!DOCTYPE testsuite SYSTEM \"report[1].dtd\"><testsuite><testcase name=\"ok\"/></testsuite>" ==
  .ok [⟨".ok", "PASS", "pass", "0"⟩]
#guard junitCases "<!DOCTYPE testsuite SYSTEM \"report>1.dtd\"><testsuite><testcase name=\"ok\"/></testsuite>" ==
  .ok [⟨".ok", "PASS", "pass", "0"⟩]
-- An actual subset is rejected even after a quoted bracket in an identifier.
#guard junitCases "<!DOCTYPE testsuite SYSTEM \"report[1].dtd\" [<!ELEMENT testsuite ANY>]><testsuite><testcase name=\"ok\"/></testsuite>" ==
  .error "DOCTYPE internal subset unsupported"
-- Rejected missing attribute separators must not create green reports.
#guard junitCases "<testsuite><testcase name=\"a\"time=\"1\"/></testsuite>" ==
  .error "attributes must be separated by whitespace"

-- Legitimate whitespace, escaping, and CDATA remain accepted.
#guard junitCases "\n<testsuite><testcase name=\"a &amp; b\"/></testsuite> \n" ==
  .ok [⟨".a & b", "PASS", "pass", "0"⟩]
#guard junitCases "<testsuite><testcase name=\"ok\"/><![CDATA[&broken;]]></testsuite>" ==
  .ok [⟨".ok", "PASS", "pass", "0"⟩]

-- Protect valid XML syntax against stricter token/entity rejection.
#guard junitCases "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<testsuite><testcase name=\"ok\"/></testsuite>" ==
  .ok [⟨".ok", "PASS", "pass", "0"⟩]
#guard junitCases "<testsuite><testcase name=\"&#65;&#x42;\"/></testsuite>" ==
  .ok [⟨".AB", "PASS", "pass", "0"⟩]
#guard junitCases "<testsuite><testcase name=\"ok\"/>&#65;&#x42;</testsuite>" ==
  .ok [⟨".ok", "PASS", "pass", "0"⟩]

-- Numeric references to non-XML characters must remain errors.
#guard junitCases "<testsuite><testcase name=\"&#xD800;\"/></testsuite>" == .error "invalid value of attribute name"

def exampleCases : List Case := (junitCases exampleJunit).toOption.getD []
#guard (pythonFfiHtml [⟨"T", exampleCases⟩]).2 == 3
#guard ((pythonFfiHtml [⟨"T", exampleCases⟩]).1.splitOn "\n").length == 25

end

end Tests.SuiteRunner.Reports
