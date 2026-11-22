import L4YAML.Scanner.Scanner

/-! # The explicit-key register at column-0 content landings (items 347–349, Rule 2)

The register (`explicitKeyLine`) read after the token scanned at each landing.  A column-0
content landing leaves `none` — also after an inner `?` that never met its `:` (item 348: the
hook closes every marked level at or right of the cursor), and also when the content starts
with a `-` or `:` that is NOT an indicator, i.e. not followed by a blank (item 349: `-x`, the
gate reads the dispatcher's lookahead).  A column-0 `-` indicator and an indented landing keep
the register. -/

open L4YAML L4YAML.Scanner

namespace Col0LandingDead

/-- The register after the `n`-th token of `input` (0-based), `none` on error/EOF. -/
def eklAfter (input : String) (n : Nat) : Option (Option Nat) :=
  go (ScannerState.mk' input) (n + 1)
where
  go (s : ScannerState) : Nat → Option (Option Nat)
    | 0 => none
    | k + 1 =>
      match scanNextToken s with
      | .ok (some s') => if k = 0 then some s'.explicitKeyLine else go s' k
      | _ => none

-- content at column 0 under an open `?`: dead
#guard eklAfter "?\na: 1\n" 1 = some none
#guard eklAfter "?\n  a: 1\nb: 2\n" 4 = some none
-- nested `?`, the column-0 landing closes BOTH keys
#guard eklAfter "? ? a\n  : b\nc: 1\n" 4 = some (some 0)
#guard eklAfter "? ? a\n  : b\nc: 1\n" 5 = some none
#guard eklAfter "?\n  ? a\n  : b\nc: 1\n" 5 = some none
-- an inner `?` never closed by `:` (item 347's LIVE rows): the widened hook closes the
-- outer key too — these were `some (some 0)` under the one-level hook
#guard eklAfter "?\n  ? a\nc: 1\n" 3 = some none
#guard eklAfter "?\n  ? a\n  ? b\nc: 1\n" 5 = some none
#guard eklAfter "? ? a\nc: 1\n" 4 = some none
-- item 349: a `-` that is content (not followed by a blank) closes; the `-` indicator keeps
#guard eklAfter "?\n-x: 1\n" 1 = some none
#guard eklAfter "?\n  ? a\n-x: 1\n" 3 = some none
-- the two excluded shapes: a column-0 `-` indicator keeps the register, an indented landing keeps it
#guard eklAfter "?\n- a\n" 1 = some (some 0)
#guard eklAfter "?\n  a: 1\n  b: 2\n: v\n" 4 = some (some 0)

end Col0LandingDead
