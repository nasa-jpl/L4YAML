import L4YAML.Scanner.Scanner

/-!
# The marked-column domain at a park (item 354, Rule 2)

Item 354 priced the domain conjunct `MarkedColsIn sc ns` (every marked `pendingKeys`
column is in `ns`) on the six `∃ ns` faces.  This table reads the domain itself off the
scanner at the parks the flip left STARVED: inside an open `?` the marked columns are the
enclosing `?`s, so the `ns := []` payments and the singleton `ns := [n]` producers are
refused there, and only the park chain (every enclosing `?`'s own route) can fill `ns`.
-/

open L4YAML Scanner

namespace MarkedColsDomain

def stepN (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | k + 1 =>
    match scanNextToken s with
    | Except.ok (some s') => stepN s' k
    | _ => none

/-- The columns of the marked slots, innermost last. -/
def markedCols (s : ScannerState) : List Nat :=
  (List.range s.pendingKeys.size).filterMap fun i =>
    match s.pendingKeys[i]? with
    | some (some _) => (s.indentColumns[i]?).map Int.toNat
    | _ => none

/-- `(column, marked columns)` after `n` tokens. -/
def probe (input : String) (n : Nat) : Option (Nat × List Nat) :=
  (stepN (ScannerState.mk' input) n).map fun s => (s.col, markedCols s)

-- `? a⏎b: 1`: at `a` the compact `?` is marked at column 0; the column-0 landing `b` clears it.
#guard probe "? a\nb: 1\n" 2 == some (3, [0])
#guard probe "? a\nb: 1\n" 3 == some (1, [])
-- `?⏎  b: c⏎  d: e⏎: v`: both inner `:` parks sit under the open outer `?` — the domain is
-- `[0]`, so `ns := []` (item 350's nine arms) and the inner singleton `ns := [2]` are refused.
#guard probe "?\n  b: c\n  d: e\n: v\n" 3 == some (4, [0])
#guard probe "?\n  b: c\n  d: e\n: v\n" 6 == some (4, [0])
-- `?⏎  ? a⏎  b`: the inner `?` is closed by the landing `b`; the outer stays — domain `[0]`.
#guard probe "?\n  ? a\n  b\n: v\n" 4 == some (3, [0])
-- `? ? a⏎  : b⏎c: 1`: both compact `?`s marked while `a` is scanned (`[0, 2]`); the inner `:`
-- closes column 2; the column-0 `c` closes the outer.
#guard probe "? ? a\n  : b\nc: 1\n" 3 == some (5, [0, 2])
#guard probe "? ? a\n  : b\nc: 1\n" 4 == some (3, [0])
#guard probe "? ? a\n  : b\nc: 1\n" 6 == some (1, [])

end MarkedColsDomain
