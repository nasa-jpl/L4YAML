/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml

/-!
# Demo: Verified YAML Parser

Simple demonstration of the lean4-yaml-verified parser.
-/

open Lean4Yaml
open Lean4Yaml.Parse

def main : IO Unit := do
  IO.println "=== Lean4Yaml Verified Parser Demo ==="
  IO.println ""

  -- Example 1: Simple scalar
  IO.println "--- Example 1: Plain scalar ---"
  match parseYamlSingle "hello world" with
  | .ok v => IO.println s!"  Parsed: {repr v}"
  | .error e => IO.println s!"  Error: {e}"
  IO.println ""

  -- Example 2: Flow sequence
  IO.println "--- Example 2: Flow sequence ---"
  match parseYamlSingle "[a, b, c]" with
  | .ok v => IO.println s!"  Parsed: {repr v}"
  | .error e => IO.println s!"  Error: {e}"
  IO.println ""

  -- Example 3: Flow mapping
  IO.println "--- Example 3: Flow mapping ---"
  match parseYamlSingle "{name: test, version: 1}" with
  | .ok v => IO.println s!"  Parsed: {repr v}"
  | .error e => IO.println s!"  Error: {e}"
  IO.println ""

  -- Example 4: Block mapping
  IO.println "--- Example 4: Block mapping ---"
  match parseYamlSingle "name: test\nversion: 1\n" with
  | .ok v => IO.println s!"  Parsed: {repr v}"
  | .error e => IO.println s!"  Error: {e}"
  IO.println ""

  -- Example 5: Nested structure
  IO.println "--- Example 5: Nested block structure ---"
  let yaml := "server:\n  host: localhost\n  port: 8080\nclients:\n  - alice\n  - bob\n"
  match parseYamlSingle yaml with
  | .ok v => IO.println s!"  Parsed: {repr v}"
  | .error e => IO.println s!"  Error: {e}"
  IO.println ""

  -- Example 6: Double-quoted scalar with escapes
  IO.println "--- Example 6: Double-quoted scalar ---"
  match parseYamlSingle "\"hello\\nworld\"" with
  | .ok v => IO.println s!"  Parsed: {repr v}"
  | .error e => IO.println s!"  Error: {e}"
  IO.println ""

  -- Example 7: Multi-document stream
  IO.println "--- Example 7: Multi-document stream ---"
  match parseYaml "---\nfirst\n---\nsecond\n" with
  | .ok docs => IO.println s!"  {docs.size} documents parsed"
  | .error e => IO.println s!"  Error: {e}"

  IO.println ""
  IO.println "=== Done ==="
