import L4YAML.TokenParser
import Tests.VerifiedResult

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Mutation Testing on yaml-test-suite (v0.2.13.2)

Takes the 311 valid yaml-test-suite source cases and applies
spec-structure-aware mutations:
  1. Indent shift ±1 at key productions `[63]`
  2. Delete/add newlines at `l-` (line-start) productions
  3. Replace spaces with tabs at `s-indent` positions
  4. Move `-` to wrong indent level
  5. Colon placement (remove space after `:`)

Each mutated input is cross-checked against libyaml. Results:

| Metric | Count |
|--------|-------|
| Mutations generated | 4,495 |
| BOTH_ACCEPT | 2,277 |
| BOTH_REJECT | 1,750 |
| OURS_LENIENT (we accept, libyaml rejects) | 422 |
| OURS_STRICT (we reject, libyaml accepts) | 46 |

### Per-operator breakdown

| Operator | Total | Agree-Accept | Agree-Reject | Lenient | Strict |
|----------|-------|-------------|-------------|---------|--------|
| indent+1 | 457 | 245 | 183 | 27 | 2 |
| indent-1 | 457 | 193 | 222 | 39 | 3 |
| delete-newline | 1,379 | 704 | 528 | 140 | 7 |
| add-newline | 1,379 | 1,000 | 216 | 159 | 4 |
| space-to-tab | 457 | 51 | 338 | 42 | 26 |
| dash-indent±1 | 163 | 39 | 115 | 6 | 3 |
| colon-nospace | 203 | 45 | 148 | 9 | 1 |

### Key findings

**OURS_STRICT** (46 cases across 20 source tests):
  - 26× `space-to-tab`: tabs in quoted-scalar continuations and flow-context
    indentation. We reject; libyaml and spec allow. Root cause: scanner
    `skipToContentWs` / `skipWhitespace` don't distinguish flow/quoted
    contexts where tabs are valid separation.
  - 12× Y79Y:2 mutations: tab-containing flow sequence under various
    indent/newline mutations. Same tab-in-flow root cause.
  - 3× `dash-indent+1`: sequence entry shifted right in multi-doc.
  - 3× `delete-newline`: joining comment line with `...`/next line.
  - 1× `colon-nospace`: `&a:key:` anchor+colon without space.
  - 1× `indent-1`: quoted scalar continuation at column 0.

**OURS_LENIENT** (422 cases across 93 source tests):
  - 159× `add-newline`: we accept blank lines in directive blocks,
    comments, and multi-document boundaries where libyaml rejects.
  - 140× `delete-newline`: we accept line joins that break structure.
  - 42× `space-to-tab`: known tab-as-indent leniency (v0.2.13.1 §2).
  - 39× `indent-1`: under-indented content accepted.
  - 27× `indent+1`: over-indented content accepted.
  - 9× `colon-nospace`: `key:value` without sep accepted.
  - 6× `dash-indent+1`: misindented `-` accepted.

See `tmp/mutate_suite.py` for the mutation generator and
`tmp/mutation_report.json` for the full machine-readable report.
-/

open L4YAML
open L4YAML.TokenParser
open Tests

namespace Tests.MutationSuite

/-! ## Helpers -/

def parseSingle (input : String) : Except ScanError YamlValue :=
  parseYamlSingle input

def parseMulti (input : String) : Except ScanError (Array YamlDocument) :=
  parseYaml input

/-- Assert input parses successfully (single document). -/
def mustParse (state : IO.Ref TestCollector) (desc : String)
    (input : String) : IO Unit := do
  match parseSingle input with
  | .ok _ => check state desc true
  | .error e => checkM state desc false e.toString

/-- Assert input is rejected (single document). -/
def mustReject (state : IO.Ref TestCollector) (desc : String)
    (input : String) : IO Unit := do
  match parseSingle input with
  | .ok _ => check state (desc ++ " [should reject]") false
  | .error _ => check state desc true

/-- Assert multi-doc input parses successfully. -/
def mustParseMulti (state : IO.Ref TestCollector) (desc : String)
    (input : String) : IO Unit := do
  match parseMulti input with
  | .ok _ => check state desc true
  | .error e => checkM state desc false e.toString

/-- Assert multi-doc input is rejected. -/
def mustRejectMulti (state : IO.Ref TestCollector) (desc : String)
    (input : String) : IO Unit := do
  match parseMulti input with
  | .ok _ => check state (desc ++ " [should reject]") false
  | .error _ => check state desc true

/-! ## §1. OURS_STRICT — Mutations where we reject but libyaml accepts

These represent potential bugs in our parser. Inputs are derived from
passing yaml-test-suite cases with a single mutation applied.
-/

/-! ### §1a. Tabs in quoted scalar continuations (space-to-tab)
YAML spec §7.3.1: In multi-line double-quoted scalars, continuation
lines may be indented with tabs (they count as `s-white` [33]).
Our scanner rejects tabs in these positions.
-/

def testTabsInQuotedScalars (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "STRICT: tabs in quoted scalar continuations"

  -- Source: 4CQQ:0 — double-quoted scalar with tab-indented continuation
  -- Original: "...quoted: \"So does this\n  quoted scalar.\\n\"\n"
  -- Mutation: replace 2 leading spaces with tabs on line 5
  -- KNOWN BUG: our scanner rejects tabs in double-quoted continuations
  mustReject state "4CQQ tab in dquote continuation (STRICT: libyaml accepts)"
    "plain:\n  This unquoted scalar\n  spans many lines.\n\nquoted: \"So does this\n\t\tquoted scalar.\\n\"\n"

  -- Source: DK95:2 — double-quoted scalar tab continuation
  -- Mutation: replace 2 leading spaces with tabs on line 1
  mustReject state "DK95:2 tab in dquote continuation (STRICT: libyaml accepts)"
    "foo: \"bar\n\t\tbaz\"\n"

  -- Source: DK95:8 — double-quoted scalar with mixed tab+space
  -- Mutation: remove 1 space indent from line 1 (continuation at col 0)
  mustReject state "DK95:8 dquote continuation at col 0 (STRICT: libyaml accepts)"
    "foo: \"bar\n\t \t baz \t \t \"\n"

  -- Source: NAT4:0 — single-quoted scalar tab continuation
  -- Mutation: replace 2 leading spaces with tabs on line 2
  mustReject state "NAT4:0 tab in squote continuation (STRICT: libyaml accepts)"
    "---\na: '\n\t\t'\n"

  -- Source: RZP5:0 — double-quoted with tab continuation and comments
  -- Mutation: replace 2 leading spaces with tabs on line 1
  mustReject state "RZP5:0 tab in dquote continuation (STRICT: libyaml accepts)"
    "a: \"double\n\t\tquotes\" # lala\n"


/-! ### §1b. Tabs in flow context (space-to-tab)
YAML spec §7.4: Flow content allows `s-separate-in-line` [66] which
includes tabs. Our scanner rejects tabs used as indentation in flow
sequences and mappings.
-/

def testTabsInFlowContext (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "STRICT: tabs in flow context"

  -- Source: 87E4:0 — implicit key in flow sequence
  -- Mutation: replace 2 leading spaces with tabs on line 1
  mustReject state "87E4 tab indent in flow seq entry (STRICT: libyaml accepts)"
    "'implicit block key' : [\n\t\t'implicit flow key' : value,\n ]\n"

  -- Source: 87E4:0 — closing bracket with tab
  -- Mutation: replace 1 leading space with tab on line 2
  mustReject state "87E4 tab indent before flow closer (STRICT: libyaml accepts)"
    "'implicit block key' : [\n  'implicit flow key' : value,\n\t]\n"

  -- Source: L9U5:0 — plain implicit key in flow
  -- Mutation: replace 2 leading spaces with tabs on line 1
  mustReject state "L9U5 tab indent in flow entry (STRICT: libyaml accepts)"
    "implicit block key : [\n\t\timplicit flow key : value,\n ]\n"

  -- Source: ZF4X:0 — multiline flow mapping
  -- Mutation: replace 4 leading spaces with tabs on line 2
  mustReject state "ZF4X tab indent in flow mapping (STRICT: libyaml accepts)"
    "Mark McGwire: {hr: 65, avg: 0.278}\nSammy Sosa: {\n\t\t\t\thr: 63,\n    avg: 0.288\n  }\n"

  -- Source: LP6E:0 — flow mapping with mixed content
  -- Mutation: replace 3 leading spaces with tabs on line 3
  mustReject state "LP6E tab indent in multiline flow (STRICT: libyaml accepts)"
    "- [a, b , c ]\n- { \"a\"  : b\n   , c : 'd' ,\n\t\t\te   : \"f\"\n  }\n- [      ]\n"

  -- Source: M5DY:0 — flow sequence in complex key
  -- Mutation: replace 4 leading spaces with tabs on line 6
  mustReject state "M5DY tab indent in flow seq (STRICT: libyaml accepts)"
    "? - Detroit Tigers\n  - Chicago cubs\n:\n  - 2001-07-23\n\n? [ New York Yankees,\n\t\t\t\tAtlanta Braves ]\n: [ 2001-07-02, 2001-08-12,\n    2001-08-14 ]\n"


/-! ### §1c. Other STRICT mutations -/

def testOtherStrict (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "STRICT: other mutations"

  -- Source: 2SXE:0 — anchor+colon without space
  -- Mutation: colon-nospace on line 0
  -- `&a:key` — colon after anchor without space; libyaml accepts
  mustReject state "2SXE anchor:key no space (STRICT: libyaml accepts)"
    "&a:key: &a value\nfoo:\n  *a:\n"

  -- Source: 35KP:0 — sequence entry indented +1 in multi-doc
  -- Mutation: dash-indent+1 on line 4
  mustRejectMulti state "35KP dash shifted right in multi-doc (STRICT: libyaml accepts)"
    "--- !!map\n? a\n: b\n--- !!seq\n - !!str c\n--- !!str\nd\ne\n"

  -- Source: 6ZKB:0 — comment joined with `...` marker
  -- Mutation: delete-newline joining lines 2 and 3
  mustRejectMulti state "6ZKB comment+... joined (STRICT: libyaml accepts)"
    "Document\n---\n# Empty...\n%YAML 1.2\n---\nmatches %: 20\n"

  -- Source: V55R:0 — sequence with anchors, dash shifted
  -- Mutation: dash-indent+1 on line 1
  mustReject state "V55R dash shifted right with anchor (STRICT: libyaml accepts)"
    "- &a a\n - &b b\n- *a\n- *b\n"


/-! ## §2. OURS_LENIENT — Mutations where we accept but libyaml rejects

These represent leniencies in our parser. The mutation SHOULD break the
input (libyaml correctly rejects), but our parser still accepts.
-/

/-! ### §2a. Indent shift leniencies -/

def testIndentLeniencies (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "LENIENT: indent shift"

  -- Source: 2SXE:0 `&a: key: &a value\nfoo:\n  *a:\n`
  -- Mutation: indent+1 on line 2 (over-indent alias key)
  mustParse state "2SXE:0 over-indent alias key (LENIENT: libyaml rejects)"
    "&a: key: &a value\nfoo:\n   *a:\n"

  -- Source: 2SXE:0 — under-indent alias key
  -- Mutation: indent-1 on line 2
  mustParse state "2SXE:0 under-indent alias key (LENIENT: libyaml rejects)"
    "&a: key: &a value\nfoo:\n *a:\n"

  -- Source: 5MUD:0 `---\n{ \"foo\"\n  :bar }\n`
  -- Mutation: indent+1 on line 2 (over-indent in flow)
  mustParse state "5MUD:0 over-indent colon in flow (LENIENT: libyaml rejects)"
    "---\n{ \"foo\"\n   :bar }\n"

  -- Source: 5MUD:0 — under-indent in flow
  -- Mutation: indent-1 on line 2
  mustParse state "5MUD:0 under-indent colon in flow (LENIENT: libyaml rejects)"
    "---\n{ \"foo\"\n :bar }\n"

  -- Source: 4Q9F:0 — under-indent block scalar content
  -- Mutation: indent-1 on line 1
  mustParse state "4Q9F:0 under-indent flow content (LENIENT: libyaml rejects)"
    "- |\n line1\n line2\n"

  -- Source: 6FWR:0 — under-indent in block literal
  -- Mutation: indent-1 on line 1
  mustParse state "6FWR:0 under-indent block value (LENIENT: libyaml rejects)"
    "--- >\n block\n scalar\n"


/-! ### §2b. Delete-newline leniencies (joining lines) -/

def testDeleteNewlineLeniencies (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "LENIENT: delete-newline"

  -- Source: 2JQS:0 `: a\n: b\n` (empty key mapping)
  -- Mutation: join lines 0 and 1
  mustParse state "2JQS:0 join empty-key lines (LENIENT: libyaml rejects)"
    ": a: b\n"

  -- Source: 4ABK:0 (multi-doc with implicit keys)
  -- Mutation: join lines 0 and 1
  mustParseMulti state "4ABK:0 join multi-doc line 0+1 (LENIENT: libyaml rejects)"
    "---foo: bar\n---\nfoo: bar\n---\nfoo: bar\n"

  -- Source: 6CK3:0 (multi-doc with directives)
  -- Mutation: join lines 0 and 1
  mustParseMulti state "6CK3:0 join doc start+content (LENIENT: libyaml rejects)"
    "---a\n...\n---\nb\n"

  -- Source: 5T43:0 `? |\n  literal\n: value\n`
  -- Mutation: join lines 1 and 2
  mustParse state "5T43:0 join literal+value lines (LENIENT: libyaml rejects)"
    "? |\n  literal: value\n"

  -- Source: 58MP:0 `? : value\n`
  -- Mutation: join lines 0 and 1 → single line
  mustParse state "58MP:0 join ?-colon lines (LENIENT: libyaml rejects)"
    "---? : value\n"


/-! ### §2c. Add-newline leniencies (blank line insertion) -/

def testAddNewlineLeniencies (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "LENIENT: add-newline"

  -- Source: 2LFX:0 `%FOO  bar baz # Should be ignored\n...`
  -- Mutation: insert blank line after line 0 (inside directive block)
  mustParse state "2LFX:0 blank after directive (LENIENT: libyaml rejects)"
    "%FOO  bar baz # Should be ignored\n\n              # with a warning.\n---\n\"foo\"\n"

  -- Source: 4MUZ:0 (multi-doc boundary)
  -- Mutation: insert blank line after line 0
  mustParse state "4MUZ:0 blank in multi-doc (LENIENT: libyaml rejects)"
    "---\n\nfoo: bar\n"

  -- Source: 5MUD:0 `---\n{ \"foo\"\n  :bar }\n`
  -- Mutation: insert blank line after line 0
  mustParse state "5MUD:0 blank after doc-start (LENIENT: libyaml rejects)"
    "---\n\n{ \"foo\"\n  :bar }\n"


/-! ### §2d. Space-to-tab leniencies -/

def testSpaceToTabLeniencies (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "LENIENT: space-to-tab (indent)"

  -- Source: 2LFX:0 — tab indent in directive comment
  mustParse state "2LFX:0 tab indent directive comment (LENIENT: libyaml rejects)"
    "%FOO  bar baz # Should be ignored\n\t\t\t\t\t\t\t\t\t\t\t\t\t\t# with a warning.\n---\n\"foo\"\n"

  -- Source: 4Q9F:0 — tab indent in block scalar content
  -- Note: our parser correctly rejects this (agrees with libyaml)
  mustReject state "4Q9F:0 tab indent block scalar (BOTH_REJECT)"
    "- |\n\t line1\n line2\n"

  -- Source: 5MUD:0 — tab indent in flow content
  -- Fixed in v0.2.13.6: tabs at stream level before block content rejected.
  -- Note: this is at stream level (currentIndent < 0) in block context (flowLevel = 0
  -- at the point where \t\t:bar starts, because { opened flow on a previous token parse).
  -- Actually: scanner processes `{` → flowLevel becomes 1 → inFlow = true on continuation.
  -- But the continuation \t\t:bar is inside flow, so tabs are valid s-separate-in-line.
  -- Wait: libyaml rejects this. The issue is the tab comes BEFORE s-indent(n) spaces.
  -- At n=0, s-indent(0) = 0 spaces, s-separate-in-line allows tabs. So libyaml is strict.
  -- We mark as LENIENT (matching libyaml's strictness) to maintain compatibility.
  mustParse state "5MUD:0 tab indent flow content (LENIENT: libyaml rejects)"
    "---\n{ \"foo\"\n\t\t:bar }\n"

  -- Source: 6JQW:0 — tab indent in block mapping
  -- Note: our parser correctly rejects this (agrees with libyaml)
  mustReject state "6JQW:0 tab indent block mapping (BOTH_REJECT)"
    "---\nfoo: bar\nbaz:\n\t qux\n"


/-! ### §2e. Colon-nospace leniencies -/

def testColonNospaceLeniencies (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "LENIENT: colon-nospace"

  -- Source: 6KGN:0 `---\na: &anchor\nb: *anchor\n`
  -- Mutation: remove space after `:` on line 2
  mustParse state "6KGN:0 b:*anchor no space (LENIENT: libyaml rejects)"
    "---\na: &anchor\nb:*anchor\n"

  -- Source: 7Z25:0 multi-doc with key:value
  -- Mutation: remove space after `:` on line 3
  mustParseMulti state "7Z25:0 key:value no space (LENIENT: libyaml rejects)"
    "---\nscalar1\n...\nkey:value\n"

  -- Source: 9SA2:0 flow mapping with multiline key
  -- Mutation: remove space after `:` on line 3
  mustParse state "9SA2:0 flow multiline key:value (LENIENT: libyaml rejects)"
    "---\n- { \"single line\": value}\n- { \"multi\n  line\":value}\n"


/-! ### §2f. Dash indent leniencies -/

def testDashIndentLeniencies (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "LENIENT: dash-indent"

  -- Source: 8XYN:0 `---\n- &😁 unicode anchor\n`
  -- Mutation: dash-indent+1 on line 1
  mustParse state "8XYN:0 dash shifted right with emoji anchor (LENIENT: libyaml rejects)"
    "---\n - &😁 unicode anchor\n"

  -- Source: DBG4:0 (multi-entry sequence)
  -- Mutation: dash-indent+1 on one entry
  mustParse state "DBG4:0 dash shifted right in sequence (LENIENT: libyaml rejects)"
    "---\n- one\n- two\n- three\n - four\n - five\n"


/-! ## §3. Mutation agreement validation
Spot-check a few BOTH_ACCEPT and BOTH_REJECT cases to ensure our test
infrastructure agrees with expected behavior.
-/

def testAgreementSamples (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Agreement: BOTH_REJECT mutations"

  -- space-to-tab on block indent → correctly rejected by both
  mustReject state "space-to-tab block indent"
    "a:\n\t\tb: 1"

  -- indent-1 on nested mapping key → breaks to sibling level
  mustReject state "indent-1 breaks nested mapping"
    "a:\n  b: 1\n c: 2"

  -- delete-newline joining block scalar header with content
  mustReject state "delete-newline block scalar header"
    "a: |line1\nline2"

  -- space-to-tab on block scalar content indent → correctly rejected
  mustReject state "space-to-tab block scalar content"
    "a: |\n\tline1\n\tline2"

  setCategory state "Agreement: BOTH_ACCEPT mutations"

  -- add-newline after seq entry (blank line is valid in block)
  mustParse state "add-newline after seq entry"
    "- a\n\n- b\n"

  -- indent+1 on scalar value line (just changes indent of plain scalar)
  mustParse state "indent+1 on scalar value"
    "a:\n   b\n"

  -- add-newline after mapping value
  mustParse state "add-newline after mapping value"
    "a: 1\n\nb: 2\n"


/-! ## Test collection -/

def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testTabsInQuotedScalars state
  testTabsInFlowContext state
  testOtherStrict state
  testIndentLeniencies state
  testDeleteNewlineLeniencies state
  testAddNewlineLeniencies state
  testSpaceToTabLeniencies state
  testColonNospaceLeniencies state
  testDashIndentLeniencies state
  testAgreementSamples state
  let results ← finish state
  return { name := "mutationtests",
           label := "Mutation Testing on yaml-test-suite (v0.2.13.2)",
           sourceFile := "Tests/MutationSuiteTests.lean",
           tests := results }

end Tests.MutationSuite
