import L4YAML.Output.Dump
import L4YAML.Output.Emitter
import L4YAML.Parser.Composition
import L4YAML.Proofs.DumpRoundTrip
import Tests.VerifiedResult

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Dump Round-Trip Verified Tests

Runtime verification tests for the style-aware dump function. These
mirror the `native_decide` theorems and `#guard` checks in
`Proofs/DumpRoundTrip.lean`, providing explicit coverage tracking
in the HTML dashboard.

## Categories

1. **Structural** — dump output shape and non-emptiness
2. **Content analysis** — `isPlainSafe` correctness
3. **Style preservation** — config overrides, block scalars, anchors/tags
4. **Dump→Parse round-trip** — dump, parse back, verify `contentEq`
5. **Document dump** — directives, markers, multi-document streams
-/

open L4YAML
open L4YAML.Dump
open L4YAML.Emit
open L4YAML.TokenParser
open Tests

namespace Tests.DumpRoundTrip

/-! ## Helpers -/

/-- Dump a value, parse it back, check content equivalence. -/
private def dumpRoundTrips (v : YamlValue) (cfg : DumpConfig := {}) : Bool :=
  match parseYamlSingle (dump v cfg) with
  | .ok v' => contentEq v v'
  | .error _ => false

/-! ## §1: Structural Properties -/

def testStructural (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Structural properties"

  -- Output shape
  check state "plain scalar → content itself"
    (dump (.plainScalar "hello") == "hello")
  check state "empty string → double-quoted \"\""
    (dump (.plainScalar "") == "\"\"")
  check state "reserved 'true' → auto-quoted"
    (dump (.plainScalar "true") == "\"true\"")
  check state "reserved 'null' → auto-quoted"
    (dump (.plainScalar "null") == "\"null\"")
  check state "reserved 'yes' → auto-quoted"
    (dump (.plainScalar "yes") == "\"yes\"")
  check state "empty flow sequence → []"
    (dump (.sequence .flow #[]) == "[]")
  check state "empty flow mapping → {}"
    (dump (.mapping .flow #[]) == "{}")
  check state "empty block sequence → [] (degenerate)"
    (dump (.sequence .block #[]) == "[]")
  check state "empty block mapping → {} (degenerate)"
    (dump (.mapping .block #[]) == "{}")
  check state "alias → *name"
    (dump (.alias "anchor1") == "*anchor1")

  -- Non-emptiness
  check state "plain scalar output non-empty"
    ((dump (.plainScalar "x")).length > 0)
  check state "empty scalar output non-empty (quotes)"
    ((dump (.plainScalar "")).length > 0)
  check state "flow sequence output non-empty"
    ((dump (.sequence .flow #[])).length > 0)
  check state "flow mapping output non-empty"
    ((dump (.mapping .flow #[])).length > 0)

/-! ## §2: Content Analysis Correctness -/

def testContentAnalysis (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Content analysis (isPlainSafe)"

  -- Plain-safe positive
  check state "simple word is plain-safe"
    (isPlainSafe "hello" == true)
  check state "number is plain-safe"
    (isPlainSafe "42" == true)
  check state "mixed alphanum is plain-safe"
    (isPlainSafe "hello123" == true)
  check state "interior space is plain-safe"
    (isPlainSafe "two words" == true)

  -- Plain-safe negative: structure
  check state "empty string not plain-safe"
    (isPlainSafe "" == false)
  check state "leading space not plain-safe"
    (isPlainSafe " leading" == false)
  check state "trailing space not plain-safe"
    (isPlainSafe "trailing " == false)
  check state "newline not plain-safe"
    (isPlainSafe "line\nnewline" == false)
  check state "': ' (colon-space) not plain-safe"
    (isPlainSafe "key: val" == false)
  check state "' #' (space-hash) not plain-safe"
    (isPlainSafe "word #comment" == false)

  -- Flow indicators
  check state "'{' not plain-safe"
    (isPlainSafe "{flow}" == false)
  check state "'[' not plain-safe"
    (isPlainSafe "[arr]" == false)

  -- Reserved words
  check state "'true' not plain-safe"
    (isPlainSafe "true" == false)
  check state "'false' not plain-safe"
    (isPlainSafe "false" == false)
  check state "'null' not plain-safe"
    (isPlainSafe "null" == false)
  check state "'~' not plain-safe"
    (isPlainSafe "~" == false)
  check state "'Yes' not plain-safe"
    (isPlainSafe "Yes" == false)
  check state "'NO' not plain-safe"
    (isPlainSafe "NO" == false)

  -- Leading indicators (§5.3)
  check state "'-item' not plain-safe"
    (isPlainSafe "-item" == false)
  check state "'?key' not plain-safe"
    (isPlainSafe "?key" == false)
  check state "':val' not plain-safe"
    (isPlainSafe ":val" == false)
  check state "'&anchor' not plain-safe"
    (isPlainSafe "&anchor" == false)
  check state "'*alias' not plain-safe"
    (isPlainSafe "*alias" == false)
  check state "'!tag' not plain-safe"
    (isPlainSafe "!tag" == false)
  check state "'|literal' not plain-safe"
    (isPlainSafe "|literal" == false)
  check state "'>folded' not plain-safe"
    (isPlainSafe ">folded" == false)
  check state "single-quote leader not plain-safe"
    (isPlainSafe "'quoted" == false)
  check state "double-quote leader not plain-safe"
    (isPlainSafe "\"quoted" == false)
  check state "'%directive' not plain-safe"
    (isPlainSafe "%directive" == false)
  check state "'@reserved' not plain-safe"
    (isPlainSafe "@reserved" == false)
  check state "'`reserved' not plain-safe"
    (isPlainSafe "`reserved" == false)

/-! ## §3: Style Preservation -/

def testStylePreservation (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Style preservation"

  -- Config overrides
  check state "config doubleQuoted forces quoting"
    (dump (.plainScalar "hello") { scalarStyle := .doubleQuoted } == "\"hello\"")
  check state "config singleQuoted forces quoting"
    (dump (.plainScalar "hello") { scalarStyle := .singleQuoted } == "'hello'")
  check state "singleQuoted falls back to double for newlines"
    (dump (.scalar ⟨"a\nb", .plain, none, none, none⟩) { scalarStyle := .singleQuoted } ==
      "\"a\\nb\"")

  -- Block scalar styles
  check state "literal block scalar honored"
    (dump (.scalar ⟨"line1\nline2", .literal, none, none, none⟩) ==
      "|\n  line1\n  line2")
  check state "folded block scalar honored"
    (dump (.scalar ⟨"line1\nline2", .folded, none, none, none⟩) ==
      ">\n  line1\n  line2")
  check state "literal strip chomp (|-)"
    (dump (.scalar ⟨"text\nhere", .literal, none, none, some ⟨.strip, none⟩⟩) ==
      "|-\n  text\n  here")
  check state "literal keep chomp (|+)"
    (dump (.scalar ⟨"text\nhere", .literal, none, none, some ⟨.keep, none⟩⟩) ==
      "|+\n  text\n  here")

  -- Collection style overrides
  check state "config flow overrides block sequence"
    (dump (.sequence .block #[.plainScalar "a"]) { defaultStyle := .flow } ==
      "[a]")
  check state "config flow overrides block mapping"
    (dump (.mapping .block #[(.plainScalar "k", .plainScalar "v")])
      { defaultStyle := .flow } == "{k: v}")
  check state "flow annotation preserved with block config"
    (dump (.sequence .flow #[.plainScalar "a"]) { defaultStyle := .block } ==
      "[a]")

  -- Anchor/tag emission
  check state "anchor emitted"
    (dump (.scalar ⟨"val", .plain, none, some "a1", none⟩) == "&a1 val")
  check state "tag emitted"
    (dump (.scalar ⟨"42", .plain, some "!!int", none, none⟩) == "!!int 42")
  check state "tag + anchor both emitted"
    (dump (.scalar ⟨"v", .plain, some "!!str", some "anc", none⟩) ==
      "!!str &anc v")

/-! ## §4: Dump→Parse Round-Trip -/

def testDumpRoundTrip (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Dump→Parse round-trip"

  -- Plain scalars
  check state "plain 'hello' round-trips"
    (dumpRoundTrips (.plainScalar "hello"))
  check state "plain 'two words' round-trips"
    (dumpRoundTrips (.plainScalar "two words"))
  check state "plain '123' round-trips"
    (dumpRoundTrips (.plainScalar "123"))

  -- Auto-quoted reserved words
  check state "reserved 'true' round-trips"
    (dumpRoundTrips (.plainScalar "true"))
  check state "reserved 'false' round-trips"
    (dumpRoundTrips (.plainScalar "false"))
  check state "reserved 'null' round-trips"
    (dumpRoundTrips (.plainScalar "null"))
  check state "reserved 'yes' round-trips"
    (dumpRoundTrips (.plainScalar "yes"))
  check state "reserved '~' round-trips"
    (dumpRoundTrips (.plainScalar "~"))

  -- Auto-quoted special chars
  check state "empty string round-trips"
    (dumpRoundTrips (.plainScalar ""))
  check state "'key: value' round-trips"
    (dumpRoundTrips (.plainScalar "key: value"))
  check state "'has #comment' round-trips"
    (dumpRoundTrips (.plainScalar "has #comment"))
  check state "'{flow}' round-trips"
    (dumpRoundTrips (.plainScalar "{flow}"))
  check state "'[array]' round-trips"
    (dumpRoundTrips (.plainScalar "[array]"))

  -- Config-forced quoting
  check state "double-quoted config round-trips"
    (dumpRoundTrips (.plainScalar "hello") { scalarStyle := .doubleQuoted })
  check state "single-quoted config round-trips"
    (dumpRoundTrips (.plainScalar "hello") { scalarStyle := .singleQuoted })

  -- Flow collections
  check state "empty flow seq round-trips"
    (dumpRoundTrips (.sequence .flow #[]))
  check state "flow seq [a] round-trips"
    (dumpRoundTrips (.sequence .flow #[.plainScalar "a"]))
  check state "flow seq [a, b] round-trips"
    (dumpRoundTrips (.sequence .flow #[.plainScalar "a", .plainScalar "b"]))
  check state "empty flow map round-trips"
    (dumpRoundTrips (.mapping .flow #[]))
  check state "flow map {k: v} round-trips"
    (dumpRoundTrips (.mapping .flow #[
      (.plainScalar "k", .plainScalar "v")]))
  check state "flow map 2 pairs round-trips"
    (dumpRoundTrips (.mapping .flow #[
      (.plainScalar "k1", .plainScalar "v1"),
      (.plainScalar "k2", .plainScalar "v2")]))

  -- Block collections
  check state "block seq [a] round-trips"
    (dumpRoundTrips (.sequence .block #[.plainScalar "a"]))
  check state "block seq [a, b] round-trips"
    (dumpRoundTrips (.sequence .block #[.plainScalar "a", .plainScalar "b"]))
  check state "block map {key: val} round-trips"
    (dumpRoundTrips (.mapping .block #[
      (.plainScalar "key", .plainScalar "val")]))
  check state "block map 2 pairs round-trips"
    (dumpRoundTrips (.mapping .block #[
      (.plainScalar "a", .plainScalar "1"),
      (.plainScalar "b", .plainScalar "2")]))

  -- Nested structures
  check state "mapping with seq value round-trips"
    (dumpRoundTrips (.mapping .block #[
      (.plainScalar "items", .sequence .block #[
        .plainScalar "a", .plainScalar "b"])]))
  check state "nested mapping round-trips"
    (dumpRoundTrips (.mapping .block #[
      (.plainScalar "outer", .mapping .block #[
        (.plainScalar "inner", .plainScalar "val")])]))
  check state "mixed block/flow round-trips"
    (dumpRoundTrips (.mapping .block #[
      (.plainScalar "list", .sequence .flow #[.plainScalar "a", .plainScalar "b"])]))
  check state "nested flow round-trips"
    (dumpRoundTrips (.sequence .flow #[
      .sequence .flow #[.plainScalar "a"],
      .mapping .flow #[(.plainScalar "k", .plainScalar "v")]]))

  -- Escapes
  check state "tab escape round-trips"
    (dumpRoundTrips (.plainScalar "tab\there"))
  check state "backslash round-trips"
    (dumpRoundTrips (.plainScalar "back\\slash"))
  check state "embedded quotes round-trips"
    (dumpRoundTrips (.plainScalar "say \"hi\""))

  -- Config overrides
  check state "flow config on block seq round-trips"
    (dumpRoundTrips (.sequence .block #[.plainScalar "a"]) { defaultStyle := .flow })
  check state "flow config on block map round-trips"
    (dumpRoundTrips (.mapping .block #[(.plainScalar "k", .plainScalar "v")])
      { defaultStyle := .flow })
  check state "custom indent round-trips"
    (dumpRoundTrips (.mapping .block #[
      (.plainScalar "key", .sequence .block #[.plainScalar "a"])]) { indent := 4 })

/-! ## §5: Document Dump Properties -/

def testDocumentDump (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Document dump"

  check state "dumpDirective YAML"
    (dumpDirective (.yaml "1.2") == "%YAML 1.2")
  check state "dumpDirective TAG"
    (dumpDirective (.tag "!!" "tag:yaml.org,2002:") ==
      "%TAG !! tag:yaml.org,2002:")
  check state "document no directives"
    (dumpDocument ⟨.plainScalar "hello", #[], #[], #[], #[]⟩ == "hello")
  check state "document with YAML directive"
    (dumpDocument ⟨.plainScalar "hello", #[.yaml "1.2"], #[], #[], #[]⟩ ==
      "%YAML 1.2\n---\nhello")
  check state "document multiple directives"
    (dumpDocument ⟨.plainScalar "v", #[.yaml "1.2", .tag "!e!" "tag:e.com,2000:"], #[], #[], #[]⟩ ==
      "%YAML 1.2\n%TAG !e! tag:e.com,2000:\n---\nv")
  check state "dumpDocuments empty"
    (dumpDocuments #[] == "")
  check state "dumpDocuments single"
    (dumpDocuments #[⟨.plainScalar "hello", #[], #[], #[], #[]⟩] == "hello")
  check state "dumpDocuments two → ---/..."
    (dumpDocuments #[⟨.plainScalar "a", #[], #[], #[], #[]⟩, ⟨.plainScalar "b", #[], #[], #[], #[]⟩] ==
      "a\n---\nb\n...")
  check state "dumpDocuments three"
    (dumpDocuments #[⟨.plainScalar "a", #[], #[], #[], #[]⟩, ⟨.plainScalar "b", #[], #[], #[], #[]⟩,
                     ⟨.plainScalar "c", #[], #[], #[], #[]⟩] ==
      "a\n---\nb\n---\nc\n...")

/-! ### §6: Flow-context edge cases (v0.2.13.4) -/

/-- Test flow-context-aware dumping: scalars with `:`, `#`, etc. inside
    flow collections, and block-in-flow auto-promotion. -/
def testFlowContextEdgeCases (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Flow-context edge cases (v0.2.13.4)"
  -- Colon-containing scalars in flow sequence must be quoted
  check state "flow seq: colon in value quotes"
    (dumpRoundTrips (.sequence .flow #[.plainScalar "a:b"]))
  check state "flow seq: trailing colon quotes"
    (dumpRoundTrips (.sequence .flow #[.plainScalar "abc:"]))
  -- Flow mapping with colon in value
  check state "flow map: colon in value quotes"
    (dumpRoundTrips (.mapping .flow #[(.plainScalar "k", .plainScalar "v:w")]))
  -- Nested colon patterns
  check state "flow seq: key:value pattern quotes"
    (dumpRoundTrips (.sequence .flow #[.plainScalar "key: value"]))
  check state "flow map: colon-only value quotes"
    (dumpRoundTrips (.mapping .flow #[(.plainScalar "k", .plainScalar ":")]))
  -- Block collection inside flow auto-promoted to flow
  check state "block seq in flow map → flow"
    (dumpRoundTrips (.mapping .flow #[
      (.plainScalar "k", .sequence .block #[.plainScalar "a", .plainScalar "b"])]))
  check state "block map in flow seq → flow"
    (dumpRoundTrips (.sequence .flow #[
      .mapping .block #[(.plainScalar "x", .plainScalar "y")]]))
  -- Deep nesting: block inside flow inside block
  check state "block-in-flow-in-block round-trip"
    (dumpRoundTrips (.mapping .block #[
      (.plainScalar "outer",
       .sequence .flow #[
         .mapping .block #[(.plainScalar "a", .plainScalar "1")]])]))
  -- Verify block-in-flow actually becomes flow (structural check)
  check state "block seq in flow renders as flow brackets"
    (let yaml := dump (.mapping .flow #[
       (.plainScalar "k", .sequence .block #[.plainScalar "a", .plainScalar "b"])])
     (yaml.splitOn "[a, b]").length > 1)
  -- Multi-line content in flow context → double-quoted (not block scalar)
  check state "flow seq: multiline scalar double-quoted"
    (dumpRoundTrips (.sequence .flow #[
      .scalar { content := "line1\nline2", style := .literal }]))
  -- Trailing dash in flow context
  check state "flow seq: trailing dash quotes"
    (dumpRoundTrips (.sequence .flow #[.plainScalar "abc-"]))
  -- Config override: flow config + block-annotated children
  check state "flow config forces all to flow"
    (dumpRoundTrips (.sequence .block #[.plainScalar "a", .plainScalar "b"])
      { defaultStyle := .flow })
  -- Hash in flow value
  check state "flow seq: hash in value quotes"
    (dumpRoundTrips (.sequence .flow #[.plainScalar "a #b"]))
  -- Trailing colon in block context also quotes
  check state "block seq: trailing colon quotes"
    (dumpRoundTrips (.sequence .block #[.plainScalar "abc:"]))
  check state "block map key: trailing colon quotes"
    (dumpRoundTrips (.mapping .block #[(.plainScalar "abc:", .plainScalar "v")]))

/-- Collect all dump round-trip test results. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testStructural state
  testContentAnalysis state
  testStylePreservation state
  testDumpRoundTrip state
  testDocumentDump state
  testFlowContextEdgeCases state
  let results ← finish state
  return {
    name := "dumproundtrip"
    label := "Dump Round-Trip Tests"
    sourceFile := "Tests/DumpRoundTrip.lean"
    tests := results
  }

end Tests.DumpRoundTrip
