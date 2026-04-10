import L4YAML
import Tests.VerifiedResult

/-!
# Parser Security Limit Tests

Exercises all limit categories from `L4YAML/Limits.lean`:

1. **Alias limits** — depth, expansion count, node count, cycle detection
2. **Structural limits** — nesting depth, collection size, scalar bytes, total nodes
3. **Document limits** — document count, anchor count, input size
4. **Tag security** — core schema whitelist, language tags, custom handles
5. **Preset configurations** — strict, permissive, unlimited, safeTagsOnly
6. **Normal YAML** — defaults must not reject well-formed input
-/

open L4YAML
open Tests

namespace Tests.Limits

/-! ## Helpers -/

/-- Check that `parseYamlSafe` succeeds. -/
private def parseOk (input : String) (limits : ParserLimits := {}) : Bool :=
  match parseYamlSafe input limits with
  | .ok _ => true
  | .error _ => false

/-- Check that `parseYamlSafe` fails with a limit error (not a scan error). -/
private def parseLimitError (input : String) (limits : ParserLimits := {}) : Bool :=
  match parseYamlSafe input limits with
  | .ok _ => false
  | .error (.limitError _) => true
  | .error (.scanError _) => false

/-- Check that `parseYamlSafe` fails with a specific limit error category. -/
private def parseAliasError (input : String) (limits : ParserLimits := {}) : Bool :=
  match parseYamlSafe input limits with
  | .error (.limitError (.aliasLimit _)) => true
  | _ => false

private def parseStructuralError (input : String) (limits : ParserLimits := {}) : Bool :=
  match parseYamlSafe input limits with
  | .error (.limitError (.structuralLimit _)) => true
  | _ => false

private def parseDocumentError (input : String) (limits : ParserLimits := {}) : Bool :=
  match parseYamlSafe input limits with
  | .error (.limitError (.documentLimit _)) => true
  | _ => false

private def parseTagError (input : String) (limits : ParserLimits := {}) : Bool :=
  match parseYamlSafe input limits with
  | .error (.limitError (.tagSecurity _)) => true
  | _ => false

/-! ## §1  Alias Limits -/

def testAliasLimits (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Alias Limits"

  -- Billion-laugh: exponential alias expansion
  -- The parser eagerly resolves anchors during scanning, so anchor values
  -- grow exponentially. composeLimited catches this via anchor node count.
  let billionLaugh := "---\n" ++
    "a0: &a0 x\n" ++
    "a1: &a1 [*a0, *a0]\n" ++
    "a2: &a2 [*a1, *a1]\n" ++
    "a3: &a3 [*a2, *a2]\n" ++
    "a4: &a4 [*a3, *a3]\n" ++
    "a5: &a5 [*a4, *a4]\n" ++
    "a6: &a6 [*a5, *a5]\n" ++
    "a7: &a7 [*a6, *a6]\n" ++
    "a8: &a8 [*a7, *a7]\n" ++
    "a9: &a9 [*a8, *a8]\n" ++
    "result: *a9\n"

  -- 10-level billion-laugh produces ~2036 anchor nodes; use tight limit
  let blLimits : ParserLimits := {
    alias := { maxResolvedNodes := 500 }
    tag := { policy := .allowAll } }
  check state "billion-laugh rejected by anchor node count"
    (parseAliasError billionLaugh blLimits)

  -- Simple alias within limits
  let simpleAlias := "---\nanchor: &a hello\nref: *a\n"
  check state "simple alias within limits"
    (parseOk simpleAlias)

  -- Alias expansion count limit (post-parse resolution)
  let manyExpansions := "---\n" ++
    "a: &a x\n" ++
    "b: [*a, *a, *a, *a, *a, *a, *a, *a, *a, *a]\n"
  let fewExpansions : ParserLimits := {
    alias := { maxAliasDepth := 50, maxAliasExpansions := 5,
               maxResolvedNodes := 10000 } }
  check state "expansion count limit enforced"
    (parseAliasError manyExpansions fewExpansions)

  -- Node count limit after resolution
  let nodeCountInput := "---\n" ++
    "a: &a [1, 2, 3, 4, 5]\n" ++
    "b: [*a, *a, *a]\n"
  let fewNodes : ParserLimits := {
    alias := { maxAliasDepth := 50, maxAliasExpansions := 10000,
               maxResolvedNodes := 10 } }
  check state "resolved node count limit enforced"
    (parseAliasError nodeCountInput fewNodes)

  -- Anchor count limit
  let manyAnchors := "---\n" ++ String.intercalate "\n"
    (List.range 15 |>.map (fun i => s!"a{i}: &a{i} val{i}")) ++ "\n"
  let fewAnchorsLimits : ParserLimits := {
    document := { maxAnchors := 5 }
    tag := { policy := .allowAll } }
  check state "anchor count limit enforced"
    (parseDocumentError manyAnchors fewAnchorsLimits)

/-! ## §2  Structural Limits -/

def testStructuralLimits (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Structural Limits"

  -- Deep nesting
  -- Build: [[[[[[...]]]]]] with depth > limit
  let depth := 20
  let deepNest := "---\n" ++ String.ofList (List.replicate depth '[') ++ "x" ++
    String.ofList (List.replicate depth ']') ++ "\n"
  let shallowStruct : ParserLimits := {
    structural := { maxDepth := 10, maxSequenceLength := 100000,
                    maxMappingSize := 100000, maxScalarBytes := 10485760,
                    maxTotalNodes := 1000000 }
    tag := { policy := .allowAll } }
  check state "deep nesting rejected by shallow depth limit"
    (parseStructuralError deepNest shallowStruct)

  -- Normal nesting within limits
  let normalNest := "---\na:\n  b:\n    c: value\n"
  check state "normal nesting within limits"
    (parseOk normalNest)

  -- Large scalar (exceed byte limit)
  let bigScalar := "---\nkey: " ++ String.ofList (List.replicate 2000 'x') ++ "\n"
  let smallScalar : ParserLimits := {
    structural := { maxDepth := 100, maxSequenceLength := 100000,
                    maxMappingSize := 100000, maxScalarBytes := 100,
                    maxTotalNodes := 1000000 }
    tag := { policy := .allowAll } }
  check state "oversized scalar rejected"
    (parseStructuralError bigScalar smallScalar)

  -- Sequence length limit
  let longSeq := "---\n" ++ String.intercalate "\n" (List.range 20 |>.map (fun i => s!"- item{i}")) ++ "\n"
  let shortSeq : ParserLimits := {
    structural := { maxDepth := 100, maxSequenceLength := 5,
                    maxMappingSize := 100000, maxScalarBytes := 10485760,
                    maxTotalNodes := 1000000 }
    tag := { policy := .allowAll } }
  check state "sequence length limit enforced"
    (parseStructuralError longSeq shortSeq)

  -- Mapping size limit
  let bigMap := "---\n" ++ String.intercalate "\n" (List.range 20 |>.map (fun i => s!"key{i}: val{i}")) ++ "\n"
  let smallMap : ParserLimits := {
    structural := { maxDepth := 100, maxSequenceLength := 100000,
                    maxMappingSize := 5, maxScalarBytes := 10485760,
                    maxTotalNodes := 1000000 }
    tag := { policy := .allowAll } }
  check state "mapping size limit enforced"
    (parseStructuralError bigMap smallMap)

/-! ## §3  Document Limits -/

def testDocumentLimits (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Document Limits"

  -- Multiple documents exceeding limit
  let threeDocs := "---\na: 1\n---\nb: 2\n---\nc: 3\n"
  let twoDocMax : ParserLimits := {
    document := { maxDocuments := 2, maxAnchors := 10000,
                  maxInputBytes := 104857600 }
    tag := { policy := .allowAll } }
  check state "document count limit enforced"
    (parseDocumentError threeDocs twoDocMax)

  -- Single document within limits
  check state "single document within limits"
    (parseOk "---\nkey: value\n")

  -- Input size limit
  let bigInput := String.ofList (List.replicate 200 'x')
  let smallInput : ParserLimits := {
    document := { maxDocuments := 100, maxAnchors := 10000,
                  maxInputBytes := 50 }
    tag := { policy := .allowAll } }
  check state "input size limit enforced"
    (parseDocumentError bigInput smallInput)

/-! ## §4  Tag Security -/

def testTagSecurity (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Tag Security"

  -- Python tag rejection (language-specific)
  let pythonTag := "---\nobj: !!python/object:os.system echo pwned\n"
  check state "python tag rejected by default"
    (parseTagError pythonTag)

  -- Ruby tag rejection
  let rubyTag := "---\nobj: !!ruby/object:Gem::Requirement\n"
  check state "ruby tag rejected by default"
    (parseTagError rubyTag)

  -- Java tag rejection
  let javaTag := "---\nobj: !!java/object:java.lang.Runtime\n"
  check state "java tag rejected by default"
    (parseTagError javaTag)

  -- Core schema tags accepted
  let coreSchemaYaml := "---\nstr: !!str hello\nnum: !!int 42\n"
  -- Core schema tags should pass with default limits
  let coreResult := match parseYamlSafe coreSchemaYaml with
    | .ok _ => true
    | .error e => dbg_trace s!"core schema err: {e}"; false
  check state "core schema tags accepted"
    coreResult

  -- Non-core tag rejection under coreSchemaOnly policy
  let customTag := "---\nval: !custom hello\n"
  check state "non-core custom tag rejected under coreSchemaOnly"
    (parseTagError customTag)

  -- allowAll policy accepts everything
  let allowAllLimits : ParserLimits := { tag := { policy := .allowAll, rejectLanguageTags := false } }
  check state "allowAll policy accepts language tags"
    (parseOk pythonTag allowAllLimits)

  -- rejectAll policy rejects even core tags
  let rejectAllLimits : ParserLimits := { tag := { policy := .rejectAll } }
  check state "rejectAll policy rejects core schema tags"
    (parseTagError coreSchemaYaml rejectAllLimits)

/-! ## §5  Preset Configurations -/

def testPresets (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Preset Configurations"

  let normalYaml := "---\nserver:\n  host: localhost\n  port: 8080\n  tags:\n    - web\n    - api\n"

  check state "strict preset: normal YAML accepted"
    (parseOk normalYaml .strict)

  check state "permissive preset: normal YAML accepted"
    (parseOk normalYaml .permissive)

  check state "unlimited preset: normal YAML accepted"
    (parseOk normalYaml .unlimited)

  check state "safeTagsOnly preset: normal YAML accepted"
    (parseOk normalYaml .safeTagsOnly)

  -- Strict rejects billion-laugh (14 levels → ~32K anchor nodes > 10K limit)
  let billionLaugh14 := "---\n" ++
    "a0: &a0 x\n" ++
    "a1: &a1 [*a0, *a0]\n" ++
    "a2: &a2 [*a1, *a1]\n" ++
    "a3: &a3 [*a2, *a2]\n" ++
    "a4: &a4 [*a3, *a3]\n" ++
    "a5: &a5 [*a4, *a4]\n" ++
    "a6: &a6 [*a5, *a5]\n" ++
    "a7: &a7 [*a6, *a6]\n" ++
    "a8: &a8 [*a7, *a7]\n" ++
    "a9: &a9 [*a8, *a8]\n" ++
    "a10: &a10 [*a9, *a9]\n" ++
    "a11: &a11 [*a10, *a10]\n" ++
    "a12: &a12 [*a11, *a11]\n" ++
    "a13: &a13 [*a12, *a12]\n" ++
    "result: *a13\n"
  check state "strict preset: billion-laugh rejected"
    (parseLimitError billionLaugh14 .strict)

  -- Unlimited allows everything (no limit errors)
  let smallBl := "---\na0: &a0 x\na1: &a1 [*a0, *a0]\na2: &a2 [*a1, *a1]\nresult: *a2\n"
  check state "unlimited preset: billion-laugh allowed"
    (parseOk smallBl .unlimited)

/-! ## §6  Normal YAML Not Rejected -/

def testNormalYaml (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Normal YAML Passthrough"

  -- Empty document
  check state "empty string" (parseOk "")

  -- Simple scalar
  check state "plain scalar" (parseOk "hello")

  -- Mapping
  check state "simple mapping" (parseOk "key: value")

  -- Sequence
  check state "simple sequence" (parseOk "- a\n- b\n- c")

  -- Multi-document
  check state "multi-document" (parseOk "---\na: 1\n---\nb: 2\n")

  -- Anchors and aliases
  check state "simple anchor/alias" (parseOk "---\na: &ref hello\nb: *ref\n")

  -- Nested structure
  check state "nested mapping+sequence" (parseOk "servers:\n  - host: a\n    port: 80\n  - host: b\n    port: 443\n")

  -- Block scalars
  check state "block literal scalar" (parseOk "text: |\n  line1\n  line2\n")
  check state "block folded scalar" (parseOk "text: >\n  line1\n  line2\n")

  -- Quoted strings
  check state "double-quoted scalar" (parseOk "msg: \"hello world\"")
  check state "single-quoted scalar" (parseOk "msg: 'hello world'")

  -- Flow collections
  check state "flow sequence" (parseOk "[1, 2, 3]")
  check state "flow mapping" (parseOk "{a: 1, b: 2}")

/-! ## §7  parseYamlSingleSafe -/

def testSingleSafe (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "parseYamlSingleSafe"

  -- Single document returns value
  let singleResult := match parseYamlSingleSafe "key: value" with
    | .ok v => match v with
      | .mapping _ _ _ _ => true
      | _ => false
    | .error _ => false
  check state "single doc returns mapping" singleResult

  -- Empty returns null
  let emptyResult := match parseYamlSingleSafe "" with
    | .ok v => match v with
      | .scalar s => s.content == "null" || s.content == ""
      | _ => true  -- null representation
    | .error _ => false
  check state "empty returns null-like" emptyResult

  -- Multi-doc rejects
  let multiResult := match parseYamlSingleSafe "---\na: 1\n---\nb: 2\n" with
    | .ok _ => false
    | .error _ => true
  check state "multi-doc rejected by single" multiResult

  -- Limits applied
  let pythonTag := "---\nobj: !!python/object:os.system echo\n"
  let tagResult := match parseYamlSingleSafe pythonTag with
    | .ok _ => false
    | .error (.limitError (.tagSecurity _)) => true
    | _ => false
  check state "tag limits applied in single mode" tagResult

/-! ## Collect and report -/

def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testAliasLimits state
  testStructuralLimits state
  testDocumentLimits state
  testTagSecurity state
  testPresets state
  testNormalYaml state
  testSingleSafe state
  let results ← finish state
  return { name := "limittests", label := "Parser Security Limit Tests",
           sourceFile := "Tests/LimitTests.lean", tests := results }

end Tests.Limits
