import Lean4Yaml.Parser.Document
import Tests.VerifiedResult

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# YAML 1.2.2 Spec Example Test Suite

Reads the YAML examples extracted from the YAML 1.2.2 specification
(§2–§10) and attempts to parse each one, tracking pass/fail per
section. This gives a concrete measure of spec coverage.

## Directory Layout

```
examples/
  2/   — §2 Preview (28 examples, clean YAML)
  5/   — §5 Characters
  6/   — §6 Basic Structures
  7/   — §7 Flow Styles
  8/   — §8 Block Styles
  9/   — §9 Document Stream
  10/  — §10 Schemas
```

## Annotation Handling

Some spec examples (§5–§10) contain `<mark>` HTML annotation tags from
the spec page, used to highlight character classes:
- `·` → space
- `→` → tab
- `↓` → newline

The test suite strips these annotations before parsing so that the
examples reflect actual YAML content.

## Usage

```
lake build specexamples && ./.lake/build/bin/specexamples
```
-/

open Lean4Yaml
open Lean4Yaml.Parse
open Tests

namespace Tests.SpecExamples

/-! ## Annotation / HTML Stripping -/

/-- Check if `s` contains substring `sub`. -/
private def stringContains (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Strip `<mark ...>...</mark>` tags, keeping inner text. -/
private def stripMarkTags (s : String) : String :=
  let rec go (input : String) (fuel : Nat) : String :=
    match fuel with
    | 0 => input
    | fuel' + 1 =>
      let parts := input.splitOn "<mark"
      if parts.length ≤ 1 then
        -- No more <mark tags — also strip </mark>
        String.join (input.splitOn "</mark>")
      else
        let rebuilt := parts.foldl (init := "") fun acc part =>
          if acc.isEmpty && parts.head? == some part then
            part
          else
            -- Find closing > of <mark ...>
            let chars := part.toList
            let rec findClose (cs : List Char) (idx : Nat) : Nat :=
              match cs with
              | [] => idx
              | '>' :: _ => idx + 1
              | _ :: rest => findClose rest (idx + 1)
            let closeIdx := findClose chars 0
            acc ++ String.ofList (chars.drop closeIdx)
        go rebuilt fuel'
  let noOpen := go s 30
  String.join (noOpen.splitOn "</mark>")

/-- Replace spec annotation symbols with actual characters. -/
private def replaceAnnotationSymbols (s : String) : String :=
  let s := s.replace "·" " "
  let s := s.replace "→" "\t"
  let s := s.replace "↓" "\n"
  s

/-- Decode common HTML entities. -/
private def decodeHtmlEntities (s : String) : String :=
  let s := s.replace "&gt;" ">"
  let s := s.replace "&lt;" "<"
  let s := s.replace "&amp;" "&"
  let s := s.replace "&quot;" "\""
  let s := s.replace "&#39;" "'"
  s

/-- Full cleanup pipeline for a raw spec example file. -/
private def cleanupExample (s : String) : String :=
  -- Only apply HTML stripping if the content has HTML artifacts
  if stringContains s "<mark" || stringContains s "&gt;" ||
     stringContains s "&lt;" || stringContains s "&amp;" then
    decodeHtmlEntities (replaceAnnotationSymbols (stripMarkTags s))
  else
    s

/-! ## File Discovery -/

/-- Spec sections to test, in order. -/
private def specSections : Array String := #["2", "5", "6", "7", "8", "9", "10"]

/-- List YAML files in a directory, sorted. -/
private def listYamlFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut files : Array System.FilePath := #[]
  let entries ← dir.readDir
  for entry in entries do
    let name := entry.fileName
    if name.endsWith ".yaml" || name.endsWith ".yml" then
      files := files.push entry.path
  -- Sort by filename for deterministic order
  let sorted := files.toList.mergeSort (fun a b => toString a < toString b)
  pure sorted.toArray

/-- Extract example number from filename like "example-2.7.yaml". -/
private def exampleLabel (path : System.FilePath) : String :=
  let name := path.fileName.getD "unknown"
  let name := name.dropSuffix ".yaml" |>.dropSuffix ".yml" |>.copy
  name.dropSuffix "example-" |>.copy

/-! ## Parse Testing -/

/-- Try to parse one spec example file.
    Returns `(exampleLabel, parsed?, errorMsg)`. -/
private def testOneExample (path : System.FilePath) :
    IO (String × Bool × String) := do
  let raw ← IO.FS.readFile path
  let cleaned := cleanupExample raw
  let exId := exampleLabel path
  match parseYaml cleaned with
  | .ok _ => pure (exId, true, "")
  | .error e =>
    -- Also try single-document parse (some examples have extra whitespace)
    match parseYamlSingle cleaned with
    | .ok _ => pure (exId, true, "")
    | .error _ => pure (exId, false, e)

/-- Run all spec example tests and collect results. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  let baseDir : System.FilePath := "examples"

  for sec in specSections do
    let secDir := baseDir / sec
    setCategory state s!"§{sec} Spec Examples"

    -- Check if directory exists
    if ← secDir.pathExists then
      let files ← listYamlFiles secDir
      for file in files do
        let (exId, parsed, errMsg) ← testOneExample file
        let label := s!"Example {exId}"
        if parsed then
          checkImpl state label true
        else
          checkImpl state label false (message := errMsg)
    else
      checkImpl state s!"Section {sec} directory missing" false
        (message := s!"expected {secDir}")

  let results ← finish state
  pure {
    name := "specexamples"
    label := "YAML 1.2.2 Spec Examples"
    sourceFile := "Tests/SpecExamples.lean"
    tests := results
  }

end Tests.SpecExamples
