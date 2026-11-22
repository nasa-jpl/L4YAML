module

public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx
public meta import L4YAML.Output.EventsIx
public import L4YAML.Scanner.Scanner
public meta import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Flow collections at a nonzero reading index (DOCS item 46)

Item 46 threads the reading index through the accumulation: the flow stack
opens at the PENDING'S index, so an indented entry's flow value —
`  - [1]`, `  a: [1,2]`, `  - &a [b]` — re-enters the stream through the
resume instead of riding `scannerDrop`, and a mid-flight renounce event (an
under-run landing, a multi-line scalar token) collapses the stack to a shape
that closes through the ONE remaining drop.

§1 pins the served family: every shape here is scanner- and parser-accepted,
and after item 46 its derivation runs through the real resume (the
accumulation compiles those arms with no escape).  §2 pins the collapse's
DOMAIN — the accepted inputs whose grammar reading at the entry's index does
not exist (spec-invalid, R2's class), which stay with the drop — and the
neighbours the scanner refuses outright.  All verdicts are unchanged from
before the item (zero runtime edits); what the pins fix is the boundary the
DOCS text claims.
-/

namespace L4YAML.Tests.Guards.ScannerIndexedFlowCompose

open L4YAML L4YAML.Events L4YAML.Scanner

private def scanAccepts (input : String) : Bool :=
  match Scanner.scan input with
  | .ok _ => true
  | .error _ => false

private def parses (input : String) : Bool :=
  match streamToEvents input with
  | .ok _ => true
  | .error _ => false

private def parsesIx (input : String) : Bool :=
  match streamToEventsIx input with
  | .ok _ => true
  | .error _ => false

private def accepted (input : String) : Bool :=
  scanAccepts input && parses input && parsesIx input

private def rejected (input : String) : Bool :=
  !scanAccepts input && !parses input && !parsesIx input

/-! ## §1  The served family: indexed flow values compose -/

#guard accepted "k:\n  - [1]\n"
#guard accepted "k:\n  - [1, 2, 3]\n"
#guard accepted "k:\n  a: [1,2]\n"
#guard accepted "k:\n  a: {b: 1}\n"
#guard accepted "k:\n  - {a: 1, b: 2}\n"
#guard accepted "k:\n  - &a [b]\n"
#guard accepted "k:\n  - !!seq [b]\n"
#guard accepted "k:\n  - [[1], [2]]\n"
#guard accepted "k:\n  - [a, \"b\", 'c', *x, [d]]\n" |> not  -- *x unresolved: parser rejects
#guard accepted "k:\n  - [a, \"b\", 'c']\n"
-- interior breaks that land ABOVE the entry's index: separators at n derive
#guard accepted "k:\n  - [1,\n   2]\n"
#guard accepted "k:\n  - [1, # c\n   2]\n"
#guard accepted "k:\n  a: [1,\n   2]\n"
#guard accepted "k:\n  - [\"a\n   b\"]\n"

/-! ## §2  The floor, closed (item 50), and the refused neighbours

Four shapes used to be accepted here although the reading at the entry's
index does not exist (`[69] s-flow-line-prefix(n)` fails on the landing) —
the derivation renounced and rode the drop.  Item 50 closes the floor: the
`]`/`}` exemption is gone from the structural guard (`[137]`/`[140]` sit
inside `s-l+flow-in-block(n)`'s `ns-flow-node(n+1)`, so the closers clear
the same floor), the fold's §6.1 tab gate applies in flow, and a flow plain
continuation is checked against the enclosing block indent. -/

-- the once-exempt closing bracket, below the index
#guard rejected "k:\n  - [1,\n]\n"
#guard rejected "k:\n  a: {b: 1,\n}\n"
-- plain-scalar continuation line, now floor-checked inside a flow
#guard rejected "k:\n  - [a\nb]\n"
-- tab-led quoted continuation inside a flow: §6.1 refuses the tab
#guard rejected "k:\n  - [\"a\n\t\t\tb\"]\n"

-- the refused neighbours: the checks that already ran, at the entry's level
#guard rejected "k:\n  - [1,\n  2]\n"       -- under-indented continuation
#guard rejected "k:\n  - [1,\n\t\t\t2]\n"   -- tab as indentation
#guard rejected "k:\n  - [\"a\nb\"]\n"      -- under-indented quoted continuation
#guard rejected "k:\n  a:\n[1]\n"           -- flow open below the block level

end L4YAML.Tests.Guards.ScannerIndexedFlowCompose

end Blanket
