import L4YAML.Scanner.Scanner

/-!
# Marked slots at a park are the strictly enclosing `?`s (item 353, Rule 2)

K2's domain: the `:` that closes an explicit key is emitted only at the innermost
marked `pendingKeys` column (`scanValue`), so the value lines a park owes are the
marked columns.  Since items 348/349 a landing at column `k` closes every marked slot
at a column `≥ k`, so after any landing the marked slots are exactly the `?`s that
strictly enclose the cursor — the enclosing entries' value lines, i.e. the park-chain
composition, not a relay.  This table pins that reading on the scanner itself.
-/

open L4YAML Scanner

namespace MarkedSlotsEnclosing

def stepN (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | k + 1 =>
    match scanNextToken s with
    | Except.ok (some s') => stepN s' k
    | _ => none

/-- `(column, marked slots, register line)` after `n` tokens. -/
def probe (input : String) (n : Nat) : Option (Nat × Array (Option Nat) × Option Nat) :=
  (stepN (ScannerState.mk' input) n).map fun s => (s.col, s.pendingKeys, s.explicitKeyLine)

-- `? a⏎b: 1`: the `?` at column 0 is marked while `a` is scanned …
#guard probe "? a\nb: 1\n" 2 == some (3, #[none, some 0], some 0)
-- … and a landing AT its column (`b`, column 0) closes it: no enclosing `?`.
#guard probe "? a\nb: 1\n" 3 == some (1, #[none, none], none)

-- `?⏎  ? a⏎  b`: at `b` (column 2) the inner `?` (column 2) is closed, the outer `?`
-- (column 0) stays marked — the one strictly enclosing `?`.
#guard probe "?\n  ? a\n  b\n: v\n" 4 == some (3, #[none, some 0, none], some 0)

-- `?⏎  b: c⏎  d: e⏎: v`: the outer `?` stays marked through both inner parks
-- (after `b`'s `:` and after `d`'s `:`).
#guard probe "?\n  b: c\n  d: e\n: v\n" 3 == some (4, #[none, some 0, none], some 0)
#guard probe "?\n  b: c\n  d: e\n: v\n" 6 == some (4, #[none, some 0, none], some 0)

-- `?⏎  ? a⏎c: 1`: a column-0 landing closes BOTH `?`s (item 348).
#guard (probe "?\n  ? a\nc: 1\n" 4).map (fun p => (p.2.1.all Option.isNone, p.2.2)) == some (true, none)

-- `? ? a⏎  : b⏎c: 1`: while `a` is scanned both `?`s are marked (compact inner at the
-- same line); the inner `:` closes the inner one, the outer stays; the column-0 `c`
-- closes the outer.
#guard probe "? ? a\n  : b\nc: 1\n" 3 == some (5, #[none, some 0, some 0], some 0)
#guard probe "? ? a\n  : b\nc: 1\n" 4 == some (3, #[none, some 0, none], some 0)
#guard probe "? ? a\n  : b\nc: 1\n" 6 == some (1, #[none, none], none)

end MarkedSlotsEnclosing
