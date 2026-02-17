import Lean.Elab.Term

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Verified Test Result Types

Shared result types for all verified test suites. Every suite produces
a `VerifiedSuiteResult` — an array of `VerifiedTestCase`s with suite
metadata. The reporter (HtmlReport.lean) renders these directly from
the typed data, with no stdout parsing.

## Design Principle

Separation of concerns:
- **Test** produces a `VerifiedSuiteResult` (pure data)
- **Runner** prints it to console for standalone use
- **Reporter** renders it to HTML for the coverage dashboard

This eliminates fragile `parseTestOutput` string scanning and makes
per-test HTML rows trivial to generate.
-/

namespace Tests

/-- Outcome of a single test case. -/
inductive VerifiedOutcome where
  | pass
  | fail (message : String := "")
  deriving Repr

namespace VerifiedOutcome

def isPass : VerifiedOutcome → Bool
  | .pass => true
  | .fail _ => false

def isFail : VerifiedOutcome → Bool
  | .pass => false
  | .fail _ => true

def message : VerifiedOutcome → String
  | .pass => ""
  | .fail m => m

end VerifiedOutcome

/-- A single test case result with category and test name. -/
structure VerifiedTestCase where
  category : String
  name : String
  outcome : VerifiedOutcome
  sourceLine : Nat := 0
  deriving Repr

/-- Aggregate result from running a complete test suite. -/
structure VerifiedSuiteResult where
  name : String       -- executable identifier (e.g. "stringlemmas")
  label : String      -- human-readable name (e.g. "String Lemma Tests")
  sourceFile : String  -- path relative to project root (e.g. "Tests/StringLemmas.lean")
  tests : Array VerifiedTestCase
  deriving Repr

namespace VerifiedSuiteResult

def passed (r : VerifiedSuiteResult) : Nat :=
  r.tests.filter (fun t => t.outcome.isPass) |>.size

def total (r : VerifiedSuiteResult) : Nat :=
  r.tests.size

def failed (r : VerifiedSuiteResult) : Nat :=
  r.total - r.passed

def allPass (r : VerifiedSuiteResult) : Bool :=
  r.tests.all (fun t => t.outcome.isPass)

def categories (r : VerifiedSuiteResult) : Array String :=
  r.tests.foldl (fun acc t =>
    if acc.contains t.category then acc else acc.push t.category) #[]

end VerifiedSuiteResult

/-! ## TestCollector — Mutable state for building results -/

/-- Mutable test collector. Thread through test functions,
    then extract the accumulated `VerifiedTestCase` array. -/
structure TestCollector where
  category : String := ""
  results : Array VerifiedTestCase := #[]

/-- Set the current category for subsequent `check` calls. -/
def setCategory (ref : IO.Ref TestCollector) (cat : String) : IO Unit :=
  ref.modify fun tc => { tc with category := cat }

/-- Record a test result. Implementation; prefer the `check` elab for auto line capture. -/
def checkImpl (ref : IO.Ref TestCollector) (name : String) (cond : Bool)
    (message : String := "") (srcLine : Nat := 0) : IO Unit :=
  ref.modify fun tc =>
    let outcome := if cond then VerifiedOutcome.pass
                   else VerifiedOutcome.fail message
    { tc with results := tc.results.push {
        category := tc.category, name := name, outcome := outcome, sourceLine := srcLine } }

/-! ## `check` / `checkM` — auto-capture source line number

The `check` macro replaces the direct function call and automatically
embeds the source line number into the test result at elaboration time.
Use `checkM` when a `message` string is needed on failure.

Note: macros can only capture byte offset, not true line number. We use
`elab` with `MonadFileMap` to get accurate line numbers.
-/

end Tests

open Lean Elab Term in
/-- `check ref name cond` — records a test result, auto-capturing the
    source line number for precise HTML hyperlinks. -/
elab "check " ref:term:max name:term:max cond:term : term => do
  let fm ← getFileMap
  let pos := (← getRef).getPos?.getD 0
  let line := fm.toPosition pos |>.line
  let lineLit := Lean.Syntax.mkNumLit (toString line)
  let newStx ← `(Tests.checkImpl $ref $name $cond (srcLine := $lineLit))
  elabTerm newStx none

open Lean Elab Term in
/-- `checkM ref name cond msg` — like `check` but includes an error message. -/
elab "checkM " ref:term:max name:term:max cond:term:max msg:term : term => do
  let fm ← getFileMap
  let pos := (← getRef).getPos?.getD 0
  let line := fm.toPosition pos |>.line
  let lineLit := Lean.Syntax.mkNumLit (toString line)
  let newStx ← `(Tests.checkImpl $ref $name $cond (message := $msg) (srcLine := $lineLit))
  elabTerm newStx none

namespace Tests

/-- Extract the accumulated test cases. -/
def finish (ref : IO.Ref TestCollector) : IO (Array VerifiedTestCase) := do
  let tc ← ref.get
  return tc.results

/-! ## Console output -/

/-- Print a suite result to console in the standard `✓`/`✗` format.
    Used by each suite's standalone `main`. -/
def printSuiteResult (r : VerifiedSuiteResult) : IO Unit := do
  IO.println s!"=== {r.label} ===\n"
  let mut currentCat := ""
  for t in r.tests do
    if t.category != currentCat then
      if currentCat != "" then IO.println ""
      IO.println s!"--- {t.category} ---"
      currentCat := t.category
    match t.outcome with
    | .pass => IO.println s!"  ✓ {t.name}"
    | .fail msg =>
      if msg.isEmpty then IO.println s!"  ✗ {t.name}"
      else IO.println s!"  ✗ {t.name}: {msg}"
  IO.println ""
  IO.println s!"=== Results: {r.passed}/{r.total} passed ==="
  if !r.allPass then
    IO.println s!"    {r.failed} FAILED"

end Tests
