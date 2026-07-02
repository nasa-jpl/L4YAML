import L4YAML.Output.Events
import Tests.SuiteRunner.Meta

/-!
# Event / error structural scorer

Runs L4YAML's event emitter (`L4YAML.Events.streamToEvents`) over every
yaml-test-suite case and compares the emitted event stream against the test's
expected `tree:` — the same structural check the
[YAML matrix](https://matrix.yaml.info) applies to every processor.  This is
strictly stronger than the accept/reject check in `SuiteRunner/Main.lean`, which
only asks whether parsing succeeds.

Outcomes:

* `event-pass`   — valid test, emitted events match the expected tree
* `event-diff`   — valid test, parsed but the events differ
* `event-reject` — valid test, but the parser errored (false negative)
* `error-ok`     — error test, the parser errored as required
* `error-miss`   — error test, but the parser accepted it (false positive)
* `skip-empty`   — empty YAML input (no events to compare)

Usage: `l4yaml-eventscore [--details <file>] [--all-13]`
-/

open L4YAML
open Tests.SuiteRunner

/-- Drop leading spaces from a line (the yaml-test-suite `tree:` field indents
    events for readability; the canonical event stream is flat). -/
private def leftTrim (s : String) : String :=
  String.ofList (s.toList.dropWhile (· == ' '))

/-- Normalize an event stream to a list of non-empty, left-trimmed lines. -/
private def normEvents (s : String) : List String :=
  (s.splitOn "\n").map leftTrim |>.filter (fun l => !l.isEmpty)

/-- Read every `.yaml` file in the suite `src/` directory, sorted by id. -/
private def readSrc (suiteDir : String) : IO (Array (String × String)) := do
  let entries ← System.FilePath.readDir (suiteDir ++ "/src")
  let mut files : Array (String × String) := #[]
  for entry in entries do
    if entry.path.extension == some "yaml" then
      let content ← IO.FS.readFile entry.path
      files := files.push (entry.path.fileStem.getD "??", content)
  return files.insertionSort (fun a b => a.1 < b.1)

/-- 1.3-specific tests whose 1.2.2 tree we still handle (see SuiteRunner/Main). -/
private def yaml13Include : List String := ["6VJK", "7T8X", "MJS9", "M9B4"]

def main (args : List String) : IO UInt32 := do
  let detailsPath : Option String := do
    let i ← args.idxOf? "--details"
    args[i + 1]?
  let all13 := args.contains "--all-13"
  let suiteDir : String := (do
    let i ← args.idxOf? "--suite"
    args[i + 1]?).getD "yaml-test-suite"
  let diffDir : Option String := do
    let i ← args.idxOf? "--diffdir"
    args[i + 1]?
  match diffDir with
  | some d => IO.FS.createDirAll d
  | none => pure ()
  let files ← readSrc suiteDir
  let mut cases : Array TestCase := #[]
  for (id, content) in files do
    cases := cases ++ parseTestFile id content

  let mut total := 0
  let mut eventPass := 0
  let mut eventDiff := 0
  let mut eventReject := 0
  let mut errorOk := 0
  let mut errorMiss := 0
  let mut skipEmpty := 0
  let mut skip13 := 0
  let mut details : Array String := #[]
  for tc in cases do
    let yaml := unescapeTestYaml tc.yaml
    let is13 := tc.tags.any (fun t => t == "1.3-err" || t == "1.3-mod")
    if yaml.isEmpty then
      skipEmpty := skipEmpty + 1
    else if is13 && !all13 && !yaml13Include.contains tc.id then
      skip13 := skip13 + 1
    else
      total := total + 1
      let res := L4YAML.Events.streamToEvents yaml
      if tc.expectFail then
        match res with
        | .error _ =>
          errorOk := errorOk + 1
          details := details.push (tc.id ++ "\terror-ok")
        | .ok _ =>
          errorMiss := errorMiss + 1
          details := details.push (tc.id ++ "\terror-miss")
      else
        match res with
        | .error e =>
          eventReject := eventReject + 1
          details := details.push (tc.id ++ "\tevent-reject\t" ++ toString e)
        | .ok events =>
          let expected := unescapeTestYaml tc.tree
          if normEvents events == normEvents expected then
            eventPass := eventPass + 1
            details := details.push (tc.id ++ "\tevent-pass")
          else
            eventDiff := eventDiff + 1
            details := details.push (tc.id ++ "\tevent-diff")
            match diffDir with
            | some d =>
              let base := s!"{d}/{tc.id}-{tc.variant}"
              IO.FS.writeFile (base ++ ".exp")
                (String.intercalate "\n" (normEvents expected) ++ "\n")
              IO.FS.writeFile (base ++ ".got")
                (String.intercalate "\n" (normEvents events) ++ "\n")
            | none => pure ()

  -- Report
  IO.println "════════════════════════════════════════════════════════"
  IO.println "  L4YAML event-stream structural score vs yaml-test-suite"
  IO.println "════════════════════════════════════════════════════════"
  let validTotal := eventPass + eventDiff + eventReject
  let errorTotal := errorOk + errorMiss
  IO.println s!"  Scored tests:        {total}  (skipped empty: {skipEmpty}, skipped 1.3: {skip13})"
  IO.println ""
  IO.println s!"  VALID tests:         {validTotal}"
  IO.println s!"    event-pass   ✓     {eventPass}"
  IO.println s!"    event-diff   ✗     {eventDiff}   (parsed, events differ)"
  IO.println s!"    event-reject ✗     {eventReject}   (valid input rejected)"
  IO.println ""
  IO.println s!"  ERROR tests:         {errorTotal}"
  IO.println s!"    error-ok     ✓     {errorOk}"
  IO.println s!"    error-miss   ✗     {errorMiss}   (invalid input accepted)"
  IO.println ""
  let correct := eventPass + errorOk
  let pct := if total == 0 then 0 else correct * 100 / total
  IO.println s!"  CORRECT (event-pass + error-ok): {correct}/{total} ({pct}%)"
  IO.println "════════════════════════════════════════════════════════"

  match detailsPath with
  | some p =>
    IO.FS.writeFile p (String.intercalate "\n" details.toList ++ "\n")
    IO.println s!"  Per-test details written to {p}"
  | none => pure ()
  return 0
