import L4YAML.TokenParser
import Tests.VerifiedResult

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Adversarial Grammar-Directed Tests (v0.2.13.1)

Systematic boundary-violation tests for YAML 1.2.2 position-sensitive
productions. For each constrained production, generates canonical valid
input plus boundary variants: ±1 indent, tab injection, and
constraint-specific perturbations.

Cross-validated against libyaml (C binding via PyYAML CSafeLoader).

## Productions Tested

| Production | Constraint | Section |
|------------|-----------|---------|
| [63] `s-indent(n)` | exactly n spaces | §1–§2 |
| [180] `l+block-sequence` | `-` at col m > n | §3 |
| [184] `l+block-mapping` | key at col m > n | §4 |
| [187] `s-l+block-indented` | content more indented | §5 |
| [170/174] block scalars | content at auto/explicit indent | §6 |
| [197] `l-block-map-explicit-value` | `:` at col n, own line | §7 |
| Multi-level nesting | combined productions | §8 |
| Tab injection | cross-cutting §6.1 [63] | §9 |

## Adversarial Boundaries NOT Yet Tested

The productions above cover the **position-sensitive** (indent-counting)
subset of the grammar. Other spec areas with adversarial boundary potential:

| Area | Productions | Boundary condition |
|------|-----------|-------------------|
| Plain scalar termination | [126–130] `ns-plain-*` | `:` + space terminates in block but not flow; `?`/`-` at line start terminate; multi-line continuation indent ≥ n+1 |
| Comment attachment | [75–78] `c-nb-comment-text` | `#` requires preceding `s-separate-in-line` [66]; `a#b` is plain scalar, `a #b` has comment |
| Implicit key length | [107] `c-s-implicit-json-key` | ≤ 1024 chars; single-line only; applies in flow AND block |
| Block scalar header | [162–165, 170, 176, 178] | Indicator ordering `\|2+` vs `\|+2`; indent digit range 1–9; `\|0` is invalid |
| seq-spaces context | [198–199] | BLOCK-OUT allows seq at n−1; BLOCK-IN requires n; affects `-` under mapping key vs value |
| Reserved indicators | [207–208] `c-reserved` | `@` and `` ` `` must be rejected at token start |
| Line break normalization | [28–31] `b-char` | CR, LF, CRLF; bare CR → LF; affects indent counting across platforms |
| Double-quoted escapes | [34–61] `c-ns-esc-char` | Invalid escapes `\z`; `\x`/`\u`/`\U` hex digit count; line folding in double-quoted scalars |
| Directive placement | [82–86] `l-directive` | `%YAML`/`%TAG` must precede document content; duplicate `%YAML`; unknown directive |
| Empty nodes | [71] `e-node` | Empty mapping values, empty seq entries, null vs missing in flow/block |
| Node property separation | [96–98] `c-ns-properties` | Anchor/tag require `s-separate` [80–81] before content; no separation → parse as plain scalar |
| Compact notation | [183, 195] | `- key: val` (compact map-in-seq); first entry on same line as `-` |
| Flow pair rules | [145–153] | Single-pair restriction in `{? k : v}`; adjacent flow indicators `{},[]` |
| BOM handling | [3] `c-byte-order-mark` | Allowed at stream start only; mid-stream BOM is content |

These could form the basis for a v0.2.13.2 or later test expansion.
-/

open L4YAML
open L4YAML.TokenParser
open Tests

namespace Tests.AdversarialGrammar

/-! ## Helpers -/

def parseSingle (input : String) : Except ScanError YamlValue :=
  parseYamlSingle input

def parseMulti (input : String) : Except ScanError (Array YamlDocument) :=
  parseYaml input

/-- Assert input parses successfully. -/
def mustParse (state : IO.Ref TestCollector) (desc : String)
    (input : String) : IO Unit := do
  match parseSingle input with
  | .ok _ => check state desc true
  | .error e => checkM state desc false e.toString

/-- Assert input is rejected. -/
def mustReject (state : IO.Ref TestCollector) (desc : String)
    (input : String) : IO Unit := do
  match parseSingle input with
  | .ok _ => check state (desc ++ " [should reject]") false
  | .error _ => check state desc true

/-- Assert input parses as a mapping with expected pair count. -/
def mustParseMapping (state : IO.Ref TestCollector) (desc : String)
    (input : String) (pairs : Nat) : IO Unit := do
  match parseSingle input with
  | .ok v =>
    check state (desc ++ " is mapping") v.isMapping
    match v.asPairs? with
    | some ps => check state (desc ++ s!" has {pairs} pairs") (ps.size == pairs)
    | none => check state (desc ++ " has pairs") false
  | .error e => checkM state desc false e.toString

/-- Assert input parses as a sequence with expected item count. -/
def mustParseSequence (state : IO.Ref TestCollector) (desc : String)
    (input : String) (items : Nat) : IO Unit := do
  match parseSingle input with
  | .ok v =>
    check state (desc ++ " is sequence") v.isSequence
    match v with
    | .sequence _ arr => check state (desc ++ s!" has {items} items") (arr.size == items)
    | _ => check state (desc ++ " is seq") false
  | .error e => checkM state desc false e.toString

/-! ## §1. Block Mapping Indentation — [63] s-indent(n) -/

def testBlockMappingIndent (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "[63] Block mapping indentation"

  -- Canonical: nested mapping at indent=2
  mustParseMapping state "a:\\n  b: 1 (indent=2)" "a:\n  b: 1" 1
  -- Indent=1 also valid
  mustParseMapping state "a:\\n b: 1 (indent=1)" "a:\n b: 1" 1
  -- Key at parent indent → two top-level keys (sibling)
  mustParseMapping state "a:\\nb: 1 (sibling)" "a:\nb: 1" 2
  -- Under-indent mid-mapping: 2nd key at col 1 when mapping at col 2
  mustReject state "a:\\n  first: 1\\n second: 2 (under-indent)"
    "a:\n  first: 1\n second: 2"
  -- Three-level nesting: correct indents
  mustParse state "3-level 0→2→4" "a:\n  b:\n    c: 1"
  -- Three-level: 0→1→2
  mustParse state "3-level 0→1→2" "a:\n b:\n  c: 1"
  -- Three-level: inner at middle level (sibling of b)
  mustParse state "3-level inner=middle (sibling)" "a:\n  b:\n  c: 1"
  -- Three-level: inner at top level (sibling of a)
  mustParseMapping state "3-level inner=top (a,c siblings)" "a:\n  b:\nc: 1" 2
  -- Mixed indent siblings → reject
  mustReject state "mixed indent siblings (col 2 vs 3)"
    "a:\n  b: 1\n   c: 2"
  -- 5-deep nesting
  mustParse state "5-deep 0→1→2→3→4" "a:\n b:\n  c:\n   d:\n    e: 1"
  -- 3-key mapping then under-indent
  mustReject state "3-key then under-indent"
    "a:\n  b: 1\n  c: 2\n d: 3"

/-! ## §2. Block Mapping Indentation — Tab Variants -/

def testBlockMappingTab (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "[63] Tab as indentation (§6.1)"

  -- Fixed in v0.2.13.6: tabs at document start are now correctly rejected.
  -- §6.1 s-indent [63] = spaces only; tabs before block content at stream
  -- level (currentIndent < 0) are indentation, not separation.
  mustReject state "\\ta: 1 (tab indent)" "\ta: 1"
  mustReject state " \\ta: 1 (space+tab)" " \ta: 1"
  mustReject state "\\t a: 1 (tab+space)" "\t a: 1"
  mustReject state "\\t\\ta: 1 (double tab)" "\t\ta: 1"
  -- Tab at col 0 under indent-0 mapping: col ≤ currentIndent → correctly rejected
  mustReject state "a:\\n\\tb: 1 (tab indent nested)" "a:\n\tb: 1"
  -- Tab at col 0 then space: col ≤ currentIndent → correctly rejected
  mustReject state "a:\\n\\t b: 1 (tab+space nested)" "a:\n\t b: 1"
  -- Space meets indent (col 1 > currentIndent 0), tab is separation → valid per spec (DK95:0)
  mustParse state "a:\\n \\tb: 1 (space+tab = separation)" "a:\n \tb: 1"
  -- Tab as VALUE separation is okay per §6.2 [66]
  mustParse state "a:\\tb (tab as value sep)" "a:\tb"

/-! ## §3. Block Sequence Indentation — [180] l+block-sequence -/

def testBlockSequenceIndent (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "[180] Block sequence indentation"

  -- Top-level sequence
  mustParseSequence state "top-level - a\\n- b" "- a\n- b" 2
  -- Sequence under mapping at indent+2
  mustParse state "a:\\n  - x\\n  - y (indent+2)" "a:\n  - x\n  - y"
  -- Sequence under mapping at indent+1
  mustParse state "a:\\n - x\\n - y (indent+1)" "a:\n - x\n - y"
  -- Sequence at parent indent (valid per seq-spaces rule)
  -- §198: seq-spaces(n, BLOCK-OUT) = n-1, so seq at col 0 when mapping at 0 means m=0, n-1=-1, 0>-1 ✓
  mustParse state "a:\\n- x\\n- y (seq-spaces)" "a:\n- x\n- y"
  -- Sequence deeper indent
  mustParse state "a:\\n      - x (deep indent)" "a:\n      - x\n      - y"
  -- Inconsistent sequence indent (2 then 3)
  -- NOTE: libyaml accepts this — second dash starts a nested sequence
  mustParse state "seq indent 2→3 (nested)" "a:\n  - x\n   - y"
  -- Seq-in-seq compact
  mustParseSequence state "- - a\\n  - b (seq-in-seq)" "- - a\n  - b" 1
  -- Seq-in-seq separate
  mustParseSequence state "- - a\\n- - b (separate)" "- - a\n- - b" 2
  -- Seq entry under-indent in nested context
  mustReject state "- a:\\n  - x\\n - y (under-indent)"
    "- a:\n  - x\n - y"
  -- Tab before dash in nested context → reject (hasTabInPrecedingWhitespace in scanBlockEntry)
  mustReject state "a:\\n\\t- x (tab before dash)" "a:\n\t- x"
  -- Tab after dash: tab is s-separate-in-line [66] between indicator and content → valid
  -- (cf. Y79Y:10 "-\t-1" valid, 6BCT:0 "  -\tbaz" valid in yaml-test-suite)
  mustParse state "-\\ta (tab = separation after dash)" "-\ta"
  -- Seq indent matters with multi-key
  mustParse state "multi-key seq" "a:\n  - x\n  - y\nb:\n  - z"
  -- Sequence entry at col 0 under indent-2 mapping
  mustReject state "a:\\n  b:\\n- x (seq at col 0 under deep)" "a:\n  b:\n- x"
  -- Deeply nested sequences
  mustParse state "- - - - a (4-deep compact)" "- - - - a"

/-! ## §4. Block Mapping Key Indentation — [184] l+block-mapping -/

def testBlockMappingKeyIndent (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "[184] Block mapping key indentation"

  -- Mapping in sequence
  mustParse state "- a: 1\\n  b: 2 (map in seq)" "- a: 1\n  b: 2"
  -- Mapping in sequence under-indent
  mustReject state "- a: 1\\n b: 2 (map in seq under)" "- a: 1\n b: 2"
  -- Mapping in sequence at col 0 → new top-level
  mustReject state "- a: 1\\nb: 2 (map at col 0 after seq)" "- a: 1\nb: 2"
  -- 3-level map correct
  mustParse state "3-level map correct" "a:\n  b:\n    c: 1\n    d: 2"
  -- 3-level map inner drift (c at col 3, d at col 4)
  mustReject state "3-level map inner drift" "a:\n  b:\n   c: 1\n    d: 2"
  -- Nested mapping then sibling at correct indent
  mustParseMapping state "a:\\n  b: 1\\nc: 2 (sibling)" "a:\n  b: 1\nc: 2" 2
  -- Mapping value multi-line scalar
  mustParse state "a:\\n  long\\n  value (multiline)" "a:\n  long\n  value"
  -- Mapping after sequence (different top-level doc)
  mustReject state "- x\\na: 1 (map after seq)" "- x\na: 1"
  -- Map in seq with multiple entries
  mustParse state "- a: 1\\n  b: 2\\n- c: 3 (multi-entry)" "- a: 1\n  b: 2\n- c: 3"
  -- Two mappings different indent depths
  mustParse state "a→indent2, c→indent4" "a:\n  b: 1\nc:\n    d: 2"
  -- Empty value then new key
  mustParseMapping state "a:\\nb: 1 (empty value)" "a:\nb: 1" 2
  -- Value on next line indented
  mustParse state "a:\\n  1 (value on next line)" "a:\n  1"

/-! ## §5. Flow in Block Context — [187] s-l+block-indented -/

def testFlowInBlockIndent (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "[187] Flow in block context"

  -- Flow mapping at col 0 under mapping → reject (fixed v0.2.11)
  mustReject state "a:\\n{b: c} (flow@0)" "a:\n{b: c}"
  -- Flow mapping at col 1 → accept
  mustParse state "a:\\n {b: c} (flow@1)" "a:\n {b: c}"
  -- Flow mapping at col 2
  mustParse state "a:\\n  {b: c} (flow@2)" "a:\n  {b: c}"
  -- Flow seq at col 0 → reject
  mustReject state "a:\\n[1, 2] (flowseq@0)" "a:\n[1, 2]"
  -- Flow seq at col 1 → accept
  mustParse state "a:\\n [1, 2] (flowseq@1)" "a:\n [1, 2]"
  -- Flow at root level (no parent block)
  mustParse state "{a: 1} (root flow map)" "{a: 1}"
  mustParse state "[1, 2] (root flow seq)" "[1, 2]"
  -- Nested flow at parent indent → reject
  mustReject state "a:\\n  b:\\n  {c: d} (flow at parent)" "a:\n  b:\n  {c: d}"
  -- Nested flow at proper indent
  mustParse state "a:\\n  b:\\n    {c: d} (flow proper)" "a:\n  b:\n    {c: d}"
  -- Empty flow at indent
  mustParse state "a:\\n  {} (empty flow map)" "a:\n  {}"
  mustParse state "a:\\n  [] (empty flow seq)" "a:\n  []"
  -- Empty flow at col 0 under mapping → reject
  mustReject state "a:\\n{} (empty flow@0)" "a:\n{}"
  mustReject state "a:\\n[] (empty flowseq@0)" "a:\n[]"
  -- Flow in sequence
  mustParse state "- {a: 1} (flow in seq)" "- {a: 1}"
  mustParse state "- [1, 2] (flow seq in seq)" "- [1, 2]"
  -- Flow at indent+1 nested
  mustParse state "a:\\n  b:\\n   {c: d} (indent+1)" "a:\n  b:\n   {c: d}"
  -- Block in flow (multiline)
  mustParse state "a: {b:\\n  c} (block in flow)" "a: {b:\n  c}"
  -- Flow as block seq entry wrong indent
  mustReject state "- a:\\n{b: c} (flow seq entry @0)" "- a:\n{b: c}"
  -- Nested 3-deep flow at wrong level
  mustReject state "a→b→c: flow at c's indent"
    "a:\n  b:\n    c:\n    {d: e}"
  -- Nested 3-deep flow at correct level
  mustParse state "a→b→c: flow at c+2"
    "a:\n  b:\n    c:\n      {d: e}"
  -- Tab before flow in block → reject
  mustReject state "a:\\n\\t{b: c} (tab before flow)" "a:\n\t{b: c}"

/-! ## §6. Block Scalar Indentation — [170/174] -/

def testBlockScalarIndent (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "[170/174] Block scalar indentation"

  -- Literal scalar: auto-detect indent=2
  mustParse state "literal indent=2 auto" "a: |\n  line1\n  line2"
  -- Literal: auto-detect indent=1
  mustParse state "literal indent=1 auto" "a: |\n line1\n line2"
  -- Literal: auto-detect indent=4
  mustParse state "literal indent=4 auto" "a: |\n    line1\n    line2"
  -- Literal: under-indent → reject
  mustReject state "literal under-indent (2→1)" "a: |\n  line1\n line2"
  -- Literal: content at col 0 → reject
  mustReject state "literal content at col 0" "a: |\n  line1\nline2"
  -- Literal: explicit indent indicator 2
  mustParse state "literal |2 explicit" "a: |2\n  xx\n  yy"
  -- Literal: explicit indent indicator 1
  mustParse state "literal |1 explicit" "a: |1\n x\n y"
  -- Literal: empty
  mustParse state "literal empty" "a: |\n"
  -- Literal: tab in content → reject (§6.1)
  mustReject state "literal tab in content" "a: |\n  x\n\ty"
  -- Folded scalar: auto-detect indent=2
  mustParse state "folded indent=2 auto" "a: >\n  line1\n  line2"
  -- Folded: under-indent → reject
  mustReject state "folded under-indent (2→1)" "a: >\n  line1\n line2"
  -- Folded: content at col 0 → reject
  mustReject state "folded content at col 0" "a: >\n  line1\nline2"
  -- Folded: auto-detect indent=1
  mustParse state "folded indent=1 auto" "a: >\n line1\n line2"
  -- Folded: auto-detect indent=4
  mustParse state "folded indent=4 auto" "a: >\n    line1\n    line2"
  -- Chomp indicators
  mustParse state "literal strip chomp |-" "a: |-\n  text"
  mustParse state "literal keep chomp |+" "a: |+\n  text\n"
  -- Literal nested under mapping
  mustParse state "a→b: literal nested" "a:\n  b: |\n    text"
  -- Literal nested under-indent → reject
  mustReject state "literal nested under-indent"
    "a:\n  b: |\n    text\n  extra"
  -- Block scalar content then new key at parent indent
  mustParse state "literal then sibling key" "a: |\n  x\nb: c"
  -- Folded content less indented than auto → reject
  mustReject state "folded content less than auto"
    "a: >\n    line1\n  line2"
  -- Literal continued after dedent
  mustParse state "literal then mapping" "a: |\n  x\nb: c"
  -- Folded then mapping
  mustParse state "folded then mapping" "a: >\n  x\nb: c"
  -- Block scalar with tab-only line
  mustReject state "literal with tab-only line" "a: |\n  x\n\t\n  y"

/-! ## §7. Explicit Key/Value — [197] l-block-map-explicit-value -/

def testExplicitKeyValue (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "[197] Explicit key/value indentation"

  -- Canonical: explicit key then value on next line
  mustParse state "? key\\n: value (canonical)" "? key\n: value"
  -- Nested explicit key with indent
  mustParse state "?\\n  key\\n:\\n  value (nested)" "?\n  key\n:\n  value"
  -- Explicit value at indent+1 → accept (value content indented)
  mustParse state "? key\\n:\\n value (value indent+1)" "? key\n:\n value"
  -- Explicit value `:` at wrong indent → reject
  mustReject state "? key\\n :\\n value (: at col 1)" "? key\n :\n value"
  -- Multiline explicit key
  mustParse state "? a\\n  b\\n: c (multiline key)" "? a\n  b\n: c"
  -- Explicit key with tab after ? → reject
  mustReject state "?\\tkey (tab after ?)" "?\tkey"
  -- ? with flow key (valid YAML, complex key)
  mustParse state "? {a: 1}\\n: val (flow key)" "? {a: 1}\n: val"
  -- ? with seq key (valid YAML, complex key)
  mustParse state "? [1, 2]\\n: val (seq key)" "? [1, 2]\n: val"
  -- ? empty key
  mustParse state "?\\n: val (empty key)" "?\n: val"
  -- ? key value same line (simple key context)
  mustParse state "? key : val (simple key)" "? key : val"
  -- ? with anchored key
  mustParse state "? &a key\\n: val (anchored)" "? &a key\n: val"
  -- Sequence inside explicit key
  mustParse state "?\\n  - a\\n  - b\\n: val (seq key)" "?\n  - a\n  - b\n: val"
  -- Mapping inside explicit key
  mustParse state "?\\n  a: 1\\n  b: 2\\n: val (map key)" "?\n  a: 1\n  b: 2\n: val"
  -- Nested explicit key within explicit key
  mustParse state "? ? inner\\n  : ival\\n: oval (nested ?)"
    "? ? inner\n  : ival\n: oval"
  -- Tab before explicit value
  mustReject state "? a\\n\\t: b (tab before :)" "? a\n\t: b"

/-! ## §8. Multi-level Nesting Combinations -/

def testMultiLevelNesting (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Multi-level nesting combinations"

  -- 4-deep correct
  mustParse state "4-deep 0→2→4→6" "a:\n  b:\n    c:\n      d: 1"
  -- Map-seq-map
  mustParse state "map→seq→map" "a:\n  - b: 1\n    c: 2"
  -- Seq-map-seq
  mustParse state "seq→map→seq" "- a:\n  - x\n  - y"
  -- Map-seq-map-seq
  mustParse state "map→seq→map→seq" "a:\n  - b:\n    - x"
  -- Deeply nested sequences
  mustParse state "4-deep compact seq" "- - - - a"
  -- Alternating map-seq 3 levels
  mustParse state "map→seq→map 3 levels" "a:\n  - b:\n      c: 1"
  -- Seq with nested map indent
  mustParse state "seq with nested map indent"
    "- first:\n    a: 1\n  second:\n    b: 2"
  -- Return to top level after deep nesting
  mustParseMapping state "deep nest then sibling"
    "a:\n  b:\n    c: 1\nd: 2" 2
  -- Nested under-indent after 3 levels
  mustParse state "3-level then de-indent"
    "a:\n  b:\n    c: 1\n  d: 2"
  -- Seq-map-seq-map
  mustParse state "seq→map→seq→map" "- a:\n    - b: 1"
  -- Map value is seq of maps
  mustParse state "map→seq of maps" "a:\n  - b: 1\n  - c: 2"
  -- Complex keys with nested structures
  mustParse state "? nested then mapping"
    "? a\n: b\nc: d"

/-! ## §9. Tab Injection — Cross-cutting §6.1 [63] -/

def testTabInjection (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Tab injection (§6.1)"

  -- Fixed in v0.2.13.6: tabs at document start are now correctly rejected.
  mustReject state "\\ta: 1 (tab at doc start)" "\ta: 1"
  mustReject state " \\ta: 1 (space+tab at doc start)" " \ta: 1"
  mustReject state "\\t a: 1 (tab+space at doc start)" "\t a: 1"
  mustReject state "\\t\\ta: 1 (double tab at doc start)" "\t\ta: 1"
  -- Tab as nested indent: col ≤ currentIndent → correctly rejected
  mustReject state "a:\\n\\tb: 1" "a:\n\tb: 1"
  -- Space meets indent, tab is separation → valid per spec (DK95:0)
  mustParse state "a:\\n \\tb: 1 (separation)" "a:\n \tb: 1"
  -- Tab at col 0 then space: col ≤ currentIndent → correctly rejected
  mustReject state "a:\\n\\t b: 1" "a:\n\t b: 1"
  -- Tab before dash: hasTabInPrecedingWhitespace catches it
  mustReject state "a:\\n\\t- x" "a:\n\t- x"
  mustReject state "a:\\n \\t- x" "a:\n \t- x"
  -- Tab after dash: tab is s-separate-in-line [66] → valid (cf. Y79Y:10, 6BCT:0)
  mustParse state "-\\ta (separation)" "-\ta"
  -- Tab before flow in block
  mustReject state "a:\\n\\t{b: c}" "a:\n\t{b: c}"
  mustReject state "a:\\n\\t[1, 2]" "a:\n\t[1, 2]"
  -- Tab as value separation IS allowed (§6.2 [66] s-white)
  mustParse state "a:\\tb (tab value sep)" "a:\tb"
  mustParse state "a: b\\tc (tab in value)" "a: b\tc"
  -- Tab before comment is okay
  mustParse state "a: b \\t# comment (tab before comment)" "a: b \t# comment"
  -- Tab in explicit key context
  mustReject state "?\\tkey" "?\tkey"
  mustReject state "? a\\n\\t: b" "? a\n\t: b"
  -- Tab after colon as separator IS allowed
  mustParse state "a:\\t1 (tab after colon)" "a:\t1"
  -- Tab in block scalar header
  -- §8.1: block scalar header indicators don't have tab
  mustParse state "a: |\\t\\n  text (tab in header comment area)" "a: |\t\n  text"
  -- Tab in three-level nesting
  mustReject state "a:\\n  b:\\n\\tc: 1 (tab at level 3)" "a:\n  b:\n\tc: 1"
  -- Tab for indent in sequence context
  mustReject state "-\\n\\ta: 1 (tab indent in seq item)" "-\n\ta: 1"

/-! ## §10. Document Boundary Interaction -/

def testDocumentBoundary (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Document boundary interaction"

  -- `...` as indented content (not a doc boundary)
  mustParse state "a:\\n  ... (indented doc-end)" "a:\n  ..."
  -- `---` as indented content (not a doc boundary)
  mustParse state "a:\\n  --- (indented doc-start)" "a:\n  ---"
  -- Key after document start
  match parseMulti "---\na: 1" with
  | .ok docs => check state "---\\na: 1 (post-docstart)" (docs.size >= 1)
  | .error e => checkM state "---\\na: 1" false e.toString
  -- Key indented after doc start
  mustParse state "---\\n  a: 1 (indented after docstart)" "---\n  a: 1"

/-! ## §11. Anchor/Tag Interaction with Indent -/

def testAnchorTagIndent (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Anchor/tag interaction with indent"

  -- Anchored value at correct indent
  mustParse state "a:\\n  &x b: 1 (anchor indent)" "a:\n  &x b: 1"
  -- Tagged value at correct indent
  mustParse state "a:\\n  !!str b: 1 (tag indent)" "a:\n  !!str b: 1"
  -- Anchor in sequence
  mustParse state "- &x a\\n- *x (anchor in seq)" "- &x a\n- *x"

/-! ## Collect All Tests -/

/-- Collect all adversarial grammar test results. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testBlockMappingIndent state
  testBlockMappingTab state
  testBlockSequenceIndent state
  testBlockMappingKeyIndent state
  testFlowInBlockIndent state
  testBlockScalarIndent state
  testExplicitKeyValue state
  testMultiLevelNesting state
  testTabInjection state
  testDocumentBoundary state
  testAnchorTagIndent state
  let results ← finish state
  return { name := "adversarialtests",
           label := "Adversarial Grammar-Directed Tests (v0.2.13.1)",
           sourceFile := "Tests/AdversarialGrammarTests.lean",
           tests := results }

end Tests.AdversarialGrammar
