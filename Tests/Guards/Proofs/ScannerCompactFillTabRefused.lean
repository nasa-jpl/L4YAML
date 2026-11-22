module

public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The tab in front of a compact fill is refused (DOCS item 58)

The `?`'s key slot and the explicit `:`'s value slot are filled by a same-line
`-`/`?`/`:` (item 51's compact alternatives).  A TAB in the whites in front of
that indicator is §6.1's — `[63] s-indent(n)` is spaces — and the scanner
refuses every shape; what the production proof lacked was the COORDINATE the
`:` half of the refutation reads, the park's own `simpleKeyAllowed`, which
`scanKey`/`scanValue` both set and the pending now carries.

ZERO runtime edits: the pins below are the scanner's own behavior, and what
moved is that the arm refutes them instead of deferring. -/

namespace L4YAML.Tests.Guards.ScannerCompactFillTabRefused

open L4YAML

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok _, .ok _ => true
  | _, _ => false

-- The `?`'s key slot: a tab in front of each of the three fills.
#guard refuses "? \t- a\n"
#guard refuses "? \t? a\n"
#guard refuses "? \t: a\n"
#guard refuses "?  \t- a\n"
-- The explicit `:`'s value slot, on its own line.
#guard refuses "? a\n: \t- w\n"
#guard refuses "? a\n: \t: w\n"

-- The same shapes with spaces are the compact fills item 51 pays.
#guard accepts "? - a\n"
#guard accepts "? ? a\n"
#guard accepts "? : a\n"
#guard accepts "? a\n: - w\n"

end L4YAML.Tests.Guards.ScannerCompactFillTabRefused

end Blanket
