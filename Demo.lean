/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml
import Tests.VerifiedResult

/-!
# Demo: Verified YAML Parser

Simple demonstration of the lean4-yaml-verified parser.
Each example becomes a pass/fail test: parse succeeds → pass.
Produces a `VerifiedSuiteResult` for structured reporting.
-/

open Lean4Yaml
open Lean4Yaml.Parse
open Tests

namespace Demo

/-- Collect all demo test results as structured data. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  setCategory state "Parser examples"

  -- Example 1: Simple scalar
  match parseYamlSingle "hello world" with
  | .ok _ => check state "Plain scalar" true
  | .error e => checkM state "Plain scalar" false e

  -- Example 2: Flow sequence
  match parseYamlSingle "[a, b, c]" with
  | .ok _ => check state "Flow sequence" true
  | .error e => checkM state "Flow sequence" false e

  -- Example 3: Flow mapping
  match parseYamlSingle "{name: test, version: 1}" with
  | .ok _ => check state "Flow mapping" true
  | .error e => checkM state "Flow mapping" false e

  -- Example 4: Block mapping
  match parseYamlSingle "name: test\nversion: 1\n" with
  | .ok _ => check state "Block mapping" true
  | .error e => checkM state "Block mapping" false e

  -- Example 5: Nested structure
  let yaml := "server:\n  host: localhost\n  port: 8080\nclients:\n  - alice\n  - bob\n"
  match parseYamlSingle yaml with
  | .ok _ => check state "Nested block structure" true
  | .error e => checkM state "Nested block structure" false e

  -- Example 6: Double-quoted scalar with escapes
  match parseYamlSingle "\"hello\\nworld\"" with
  | .ok _ => check state "Double-quoted scalar" true
  | .error e => checkM state "Double-quoted scalar" false e

  -- Example 7: Multi-document stream
  match parseYaml "---\nfirst\n---\nsecond\n" with
  | .ok _ => check state "Multi-document stream" true
  | .error e => checkM state "Multi-document stream" false e

  let results ← finish state
  return { name := "demo", label := "Demo", sourceFile := "Demo.lean", tests := results }

end Demo
