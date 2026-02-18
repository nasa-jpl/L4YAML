import Lean4Yaml.Types

/-!
# yaml-test-suite Metadata Parser

Line-based parser for the yaml-test-suite test file format.
We cannot use our own YAML parser here (bootstrapping problem),
so we parse the structured test metadata with a simple state machine.

## References

- <https://github.com/yaml/yaml-test-suite>
- <https://yaml.org/spec/1.2.2/>
-/

namespace Tests.SuiteRunner

/-! ## Test Case Data -/

/-- A single test case from the yaml-test-suite. -/
structure TestCase where
  /-- Four-character test ID (e.g., "229Q"). -/
  id : String
  /-- Human-readable test name. -/
  name : String
  /-- Space-separated tags (e.g., "sequence mapping spec"). -/
  tags : List String
  /-- Whether this test expects a parse failure. -/
  expectFail : Bool
  /-- The raw YAML input to parse. -/
  yaml : String
  /-- The expected event tree (optional). -/
  tree : String
  /-- Variant index within the test file. -/
  variant : Nat
  deriving Repr, Inhabited

/-- Test stages, ordered by feature complexity. -/
inductive Stage where
  | scalar     -- plain, double-quoted, single-quoted scalars
  | flow       -- flow sequences and mappings
  | block      -- block sequences and mappings
  | document   -- directives, multi-document, markers
  | advanced   -- anchors, aliases, tags, complex keys
  | error      -- expected parse failures
  | all        -- everything
  deriving Repr, BEq, Inhabited

instance : ToString Stage where
  toString
    | .scalar   => "scalar"
    | .flow     => "flow"
    | .block    => "block"
    | .document => "document"
    | .advanced => "advanced"
    | .error    => "error"
    | .all      => "all"

/-- Classify a test case into a stage based on its tags. -/
def TestCase.stage (tc : TestCase) : Stage :=
  if tc.tags.any (· == "error") then .error
  else if tc.tags.any (fun t => t == "anchor" || t == "alias" || t == "tag"
      || t == "complex-key" || t == "explicit-key") then .advanced
  else if tc.tags.any (fun t => t == "directive" || t == "footer"
      || t == "header" || t == "document") then .document
  else if tc.tags.any (· == "flow") then .flow
  else if tc.tags.any (fun t => t == "scalar" || t == "double"
      || t == "single" || t == "literal" || t == "folded") then .scalar
  else .block

/-- Check whether a test case belongs to a given stage (or below). -/
def TestCase.inStage (tc : TestCase) (s : Stage) : Bool :=
  match s with
  | .all => true
  | .error => tc.stage == .error
  | .advanced => tc.stage == .advanced || tc.stage == .document
      || tc.stage == .flow || tc.stage == .scalar || tc.stage == .block
  | .document => tc.stage == .document || tc.stage == .flow
      || tc.stage == .scalar || tc.stage == .block
  | .block => tc.stage == .block || tc.stage == .flow || tc.stage == .scalar
  | .flow => tc.stage == .flow || tc.stage == .scalar
  | .scalar => tc.stage == .scalar

/-! ## Line-based Meta-Parser

The yaml-test-suite files use a restricted YAML subset:
```
---
- name: Test Name
  from: ...
  tags: tag1 tag2 tag3
  fail: true
  yaml: |
    content lines
  tree: |
    event lines
```

We parse this with a state machine tracking the current field and
block scalar indentation level.
-/

/-- Fields we track while parsing a test entry. -/
inductive Field where
  | none
  | yaml
  | tree
  | other  -- json, dump, etc. (skip)
  deriving BEq

/-- State of the line-based parser. -/
structure ParseState where
  /-- Accumulated test cases. -/
  cases : Array TestCase := #[]
  /-- Current test case being built. -/
  current : TestCase := default
  /-- Whether we are inside a list item. -/
  inItem : Bool := false
  /-- Current field being parsed. -/
  field : Field := .none
  /-- Block scalar base indentation (number of leading spaces). -/
  blockIndent : Nat := 0

/-- Count leading spaces in a string. -/
private def countLeadingSpaces (s : String) : Nat :=
  s.toList.takeWhile (· == ' ') |>.length

/-- Trim ASCII whitespace from both ends of a string. -/
private def trim (s : String) : String :=
  s.trimAscii.toString

/-- Trim ASCII whitespace from the left side of a string. -/
private def trimLeft (s : String) : String :=
  String.ofList (s.toList.dropWhile fun c => c == ' ' || c == '\t'
      || c == '\n' || c == '\r')

/-- Strip exactly `n` leading spaces, or return the line as-is if fewer. -/
private def stripIndent (n : Nat) (s : String) : String :=
  let chars := s.toList
  let stripped := chars.drop n
  String.ofList stripped

/-- Process a single line in a block scalar field. -/
private def processBlockLine (st : ParseState) (line : String) : ParseState :=
  let indent := countLeadingSpaces line
  -- First content line of block scalar sets the base indent
  let blockIndent :=
    if st.blockIndent == 0 && indent > 0 then indent
    else st.blockIndent
  let trimmed := trimLeft line
  if indent < blockIndent && !trimmed.isEmpty then
    -- Dedented non-empty line → end of block scalar
    st
  else
    let content := if trimmed.isEmpty then "\n"
        else stripIndent blockIndent line ++ "\n"
    let cur := st.current
    match st.field with
    | .yaml =>
      let cur := { cur with yaml := cur.yaml ++ content }
      { st with current := cur, blockIndent := blockIndent }
    | .tree =>
      let cur := { cur with tree := cur.tree ++ content }
      { st with current := cur, blockIndent := blockIndent }
    | _ => { st with blockIndent := blockIndent }

/-- Finalize the current test case and add it to the accumulated list. -/
private def finalizeItem (st : ParseState) : ParseState :=
  if st.inItem then
    let cases := st.cases.push st.current
    { cases := cases, inItem := false,
        current := default, field := .none, blockIndent := 0 }
  else
    { st with field := .none, blockIndent := 0 }

/-- Process a key-value line (e.g., "  name: Test Name"). -/
private def processKeyValue (st : ParseState) (key : String)
    (value : String) : ParseState :=
  let st := { st with field := .none, blockIndent := 0 }
  let val := trim value
  let cur := st.current
  match key with
  | "name" =>
    { st with current := { cur with name := val } }
  | "tags" =>
    let tags := val.splitOn " " |>.filter (·.isEmpty.not)
    { st with current := { cur with tags := tags } }
  | "fail" =>
    { st with current := { cur with expectFail := val == "true" } }
  | "yaml" =>
    if val.startsWith "|" then
      let cur := { cur with yaml := "" }
      { st with field := .yaml, current := cur, blockIndent := 0 }
    else
      { st with current := { cur with yaml := val } }
  | "tree" =>
    if val.startsWith "|" then
      let cur := { cur with tree := "" }
      { st with field := .tree, current := cur, blockIndent := 0 }
    else
      { st with current := { cur with tree := val } }
  | "json" | "dump" | "from" | "tidy" =>
    if val.startsWith "|" then
      { st with field := .other, blockIndent := 0 }
    else st
  | _ => st

/-- Parse a line that starts a new list item ("- key: value"). -/
private def processListItem (st : ParseState) (rest : String) : ParseState :=
  let st := finalizeItem st
  let newCase : TestCase :=
    { id := "", name := "", tags := [], expectFail := false,
      yaml := "", tree := "", variant := st.cases.size }
  let st := { st with inItem := true, current := newCase }
  -- The rest after "- " is typically "key: value"
  match rest.splitOn ": " with
  | key :: valueParts =>
    let k := trim key
    processKeyValue st k (String.intercalate ": " valueParts)
  | [] => st

/-- Process a single line of the test file. -/
private partial def processLine (st : ParseState) (line : String) :
    ParseState :=
  -- If we're in a block scalar, check if this line continues it
  -- (must check BEFORE the `---` separator check, because `---` can appear
  -- as content inside a yaml block scalar)
  if st.field != .none then
    let indent := countLeadingSpaces line
    let trimmed := trimLeft line
    if trimmed.isEmpty then
      -- Empty/whitespace-only line inside block scalar
      processBlockLine st line
    else if st.blockIndent > 0 && indent < st.blockIndent then
      -- Dedented → end of block scalar, process as normal line
      let st := { st with field := .none, blockIndent := 0 }
      processLine st line
    else if st.blockIndent == 0 && indent >= 4 then
      -- First content line of block scalar
      processBlockLine st line
    else if st.blockIndent > 0 then
      processBlockLine st line
    else
      -- No indent established yet, dedented line → end block
      let st := { st with field := .none, blockIndent := 0 }
      processLine st line
  else
    -- Document separator (only checked when NOT inside a block scalar)
    if trim line == "---" then finalizeItem st
    else
    -- Check for list item start
    let trimmed := trimLeft line
    if trimmed.startsWith "- " then
      processListItem st (trimmed.drop 2 |>.toString)
    else
      -- Regular key: value line
      let kv := trimmed.splitOn ": "
      match kv with
      | key :: valueParts =>
        let k := trim key
        processKeyValue st k (String.intercalate ": " valueParts)
      | [] => st

/-- Parse a yaml-test-suite test file into test cases. -/
def parseTestFile (testId : String) (content : String) : Array TestCase :=
  let lines := content.splitOn "\n"
  let finalState := lines.foldl processLine {}
  let finalState := finalizeItem finalState
  finalState.cases.map fun tc => { tc with id := testId }

/-- Replace special characters from yaml-test-suite format.

The yaml-test-suite uses special Unicode characters to make whitespace
visible in its YAML descriptor files (see yaml-test-suite/ReadMe.md):

- `␣` (U+2423) → space (trailing space characters)
- Hard tabs (expanding to 4 spaces) are shown as one of:
  - `———»` (3 em-dashes + ») — tab at column % 4 == 0
  - `——»`  (2 em-dashes + ») — tab at column % 4 == 1
  - `—»`   (1 em-dash + »)   — tab at column % 4 == 2
  - `»`    (» alone)          — tab at column % 4 == 3
- `→` (U+2192) → tab (alternative tab representation)
- `←` (U+2190) → carriage return
- `↵` (U+21B5) → removed (trailing newline marker, cosmetic)
- `∎` (U+220E) → removed (end-without-newline marker, cosmetic)
- `⇔` (U+21D4) → BOM (U+FEFF)

Order matters: remove em-dash fill characters first, then replace `»` with tab.
The em-dash (`—`, U+2014) is used ONLY as visual tab-fill in the
yaml-test-suite format and can be safely removed entirely.
-/
def unescapeTestYaml (s : String) : String :=
  let s := s.replace "␣" " "
  -- Tabs: first remove em-dash tab-fill characters, then replace tab markers.
  -- Em-dash is ONLY used as visual fill before `»` in the yaml-test-suite
  -- format (e.g., `————»` for a tab spanning 5 columns at that position).
  let s := s.replace "—" ""
  let s := s.replace "»" "\t"
  let s := s.replace "→" "\t"
  -- Carriage return
  let s := s.replace "←" "\r"
  -- Cosmetic markers
  let s := s.replace "↵" ""
  let s := s.replace "∎" ""
  -- BOM
  let s := s.replace "⇔" "\uFEFF"
  s

end Tests.SuiteRunner
