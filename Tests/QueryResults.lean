import Lean.Data.Json

/-!
# Query Results Tool

Reads `coverage-summary.json` and supports common queries on test results.
Eliminates the need for ad-hoc `jq`/`python` one-liners to analyze test outcomes.

## Usage

```bash
# List all UPs grouped by stage
.lake/build/bin/queryresults docs/coverage-summary.json ups --by-stage

# List all verified test failures with error messages
.lake/build/bin/queryresults docs/coverage-summary.json verified-failures

# Summary table (README-ready markdown)
.lake/build/bin/queryresults docs/coverage-summary.json summary

# Filter by test ID pattern (prefix match)
.lake/build/bin/queryresults docs/coverage-summary.json filter --id "Y79Y"

# Export UP list (IDs only, one per line)
.lake/build/bin/queryresults docs/coverage-summary.json ups --ids-only

# Diff two runs (additions, removals, outcome changes)
.lake/build/bin/queryresults diff results-before.json results-after.json
```
-/

open Lean (Json ToJson FromJson)

/-! ## JSON Accessors -/

private def getStr (j : Json) (key : String) : String :=
  match j.getObjValAs? String key with
  | .ok s => s
  | .error _ => ""

private def getNat (j : Json) (key : String) : Nat :=
  match j.getObjValAs? Nat key with
  | .ok n => n
  | .error _ => 0

private def getBool (j : Json) (key : String) : Bool :=
  match j.getObjValAs? Bool key with
  | .ok b => b
  | .error _ => false

private def getArr (j : Json) (key : String) : Array Json :=
  match j.getObjVal? key with
  | .ok (.arr a) => a
  | _ => #[]

private def getObj (j : Json) (key : String) : Json :=
  match j.getObjVal? key with
  | .ok v => v
  | .error _ => .null

/-! ## Commands -/

/-- Print all unexpected-pass tests, optionally grouped by stage. -/
private def cmdUps (tests : Array Json) (byStage : Bool) (idsOnly : Bool) : IO Unit := do
  let ups := tests.filter (fun t => getStr t "outcome" == "unexpected-pass")
  if idsOnly then
    for t in ups do
      IO.println (getStr t "id")
    return
  if byStage then
    let stages := #["scalar", "flow", "block", "document", "advanced", "error"]
    for stage in stages do
      let stageUps := ups.filter (fun t => getStr t "stage" == stage)
      if stageUps.size > 0 then
        IO.println s!"\n## {stage} ({stageUps.size})"
        for t in stageUps do
          let err := getStr t "error"
          let errSuffix := if err.isEmpty then "" else s!" — {err}"
          IO.println s!"  {getStr t "id"}: {getStr t "name"}{errSuffix}"
  else
    IO.println s!"Unexpected passes: {ups.size}"
    for t in ups do
      let err := getStr t "error"
      let errSuffix := if err.isEmpty then "" else s!" — {err}"
      IO.println s!"  [{getStr t "stage"}] {getStr t "id"}: {getStr t "name"}{errSuffix}"

/-- Print all verified test failures with error messages. -/
private def cmdVerifiedFailures (root : Json) : IO Unit := do
  let verified := getObj root "verified"
  if verified == .null then
    IO.println "No verified section in JSON."
    return
  let suites := getArr verified "suites"
  let mut totalFails : Nat := 0
  for s in suites do
    let tests := getArr s "tests"
    let fails := tests.filter (fun t => getStr t "outcome" == "fail")
    if fails.size > 0 then
      IO.println s!"\n## {getStr s "label"} ({fails.size} failures)"
      for t in fails do
        let err := getStr t "error"
        let errSuffix := if err.isEmpty then "" else s!": {err}"
        IO.println s!"  [{getStr t "category"}] {getStr t "name"}{errSuffix}"
      totalFails := totalFails + fails.size
  IO.println s!"\nTotal verified failures: {totalFails}"

/-- Print a markdown-ready summary table. -/
private def cmdSummary (root : Json) : IO Unit := do
  let overall := getObj root "overall"
  let date := getStr root "date"
  IO.println s!"# Test Summary ({date})\n"
  IO.println "| Metric | Value |"
  IO.println "|--------|------:|"
  IO.println s!"| Total tests | {getNat overall "total"} |"
  IO.println s!"| Applicable (YAML 1.2.2) | {getNat overall "applicable"} |"
  IO.println s!"| Passed | {getNat overall "passed"} |"
  IO.println s!"| Failed | {getNat overall "failed"} |"
  IO.println s!"| Expected fail | {getNat overall "expectedFail"} |"
  IO.println s!"| Unexpected pass | {getNat overall "unexpectedPass"} |"
  IO.println s!"| Skipped | {getNat overall "skipped"} |"
  IO.println s!"| Timeout | {getNat overall "timeout"} |"
  IO.println s!"| **Correct** | **{getNat overall "correct"}/{getNat overall "applicable"}** |"
  -- Verified section
  let verified := getObj root "verified"
  if verified != .null then
    IO.println s!"\n## Verified Tests\n"
    IO.println "| Suite | Passed | Total |"
    IO.println "|-------|-------:|------:|"
    let suites := getArr verified "suites"
    for s in suites do
      IO.println s!"| {getStr s "label"} | {getNat s "passed"} | {getNat s "total"} |"
    IO.println s!"| **Total** | **{getNat verified "totalPassed"}** | **{getNat verified "totalTests"}** |"

/-- Filter tests by ID prefix. -/
private def cmdFilter (tests : Array Json) (idPrefix : String) : IO Unit := do
  let matched := tests.filter (fun t => (getStr t "id").startsWith idPrefix)
  IO.println s!"Matching tests ({matched.size}):\n"
  for t in matched do
    let err := getStr t "error"
    let errSuffix := if err.isEmpty then "" else s!" — {err}"
    IO.println s!"  [{getStr t "stage"}] {getStr t "id"}: {getStr t "name"} ({getStr t "outcome"}){errSuffix}"

/-- Diff two JSON result files: show outcome changes, additions, removals. -/
private def cmdDiff (pathA pathB : String) : IO UInt32 := do
  let contentsA ← IO.FS.readFile pathA
  let contentsB ← IO.FS.readFile pathB
  let rootA ← match Json.parse contentsA with
    | .ok j => pure j
    | .error e => IO.eprintln s!"Error parsing {pathA}: {e}"; return 1
  let rootB ← match Json.parse contentsB with
    | .ok j => pure j
    | .error e => IO.eprintln s!"Error parsing {pathB}: {e}"; return 1
  let testsA := getArr rootA "tests"
  let testsB := getArr rootB "tests"
  -- Build id→outcome maps
  let mapA := testsA.foldl (fun (m : Std.HashMap String String) t =>
    m.insert (getStr t "id") (getStr t "outcome")) {}
  let mapB := testsB.foldl (fun (m : Std.HashMap String String) t =>
    m.insert (getStr t "id") (getStr t "outcome")) {}
  -- Outcome changes
  IO.println s!"# Diff: {pathA} → {pathB}\n"
  let mut changes : Nat := 0
  let mut added : Nat := 0
  let mut removed : Nat := 0
  IO.println "## Outcome Changes"
  for t in testsB do
    let id := getStr t "id"
    let outcomeB := getStr t "outcome"
    match mapA.get? id with
    | some outcomeA =>
      if outcomeA != outcomeB then
        IO.println s!"  {id}: {outcomeA} → {outcomeB}"
        changes := changes + 1
    | none =>
      added := added + 1
  -- Removals (in A but not in B)
  for t in testsA do
    let id := getStr t "id"
    if mapB.get? id |>.isNone then
      removed := removed + 1
  if changes == 0 then IO.println "  (none)"
  IO.println s!"\n## Summary"
  IO.println s!"  Outcome changes: {changes}"
  IO.println s!"  Tests added: {added}"
  IO.println s!"  Tests removed: {removed}"
  return 0

/-! ## Main -/

def main (args : List String) : IO UInt32 := do
  -- Special case: diff command takes two file arguments
  match args with
  | ["diff", pathA, pathB] => return ← cmdDiff pathA pathB
  | _ => pure ()

  -- All other commands: <json-file> <command> [options...]
  match args with
  | [] =>
    IO.eprintln "Usage: queryresults <coverage-summary.json> <command> [options]"
    IO.eprintln "       queryresults diff <before.json> <after.json>"
    IO.eprintln ""
    IO.eprintln "Commands: summary, ups, verified-failures, filter"
    IO.eprintln "  ups [--by-stage] [--ids-only]"
    IO.eprintln "  filter --id <prefix>"
    return 1
  | [_] =>
    IO.eprintln "Error: missing command. Use: summary, ups, verified-failures, filter, diff"
    return 1
  | jsonPath :: cmd :: rest =>
    let contents ← IO.FS.readFile jsonPath
    let root ← match Json.parse contents with
      | .ok j => pure j
      | .error e => IO.eprintln s!"Error parsing {jsonPath}: {e}"; return 1
    let tests := getArr root "tests"
    match cmd with
    | "summary" =>
      cmdSummary root
      return 0
    | "ups" =>
      let byStage := rest.contains "--by-stage"
      let idsOnly := rest.contains "--ids-only"
      cmdUps tests byStage idsOnly
      return 0
    | "verified-failures" =>
      cmdVerifiedFailures root
      return 0
    | "filter" =>
      match rest with
      | "--id" :: idPat :: _ =>
        cmdFilter tests idPat
        return 0
      | _ =>
        IO.eprintln "Usage: queryresults <file> filter --id <prefix>"
        return 1
    | other =>
      IO.eprintln s!"Unknown command: {other}"
      IO.eprintln "Commands: summary, ups, verified-failures, filter, diff"
      return 1
