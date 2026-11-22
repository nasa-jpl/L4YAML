import L4YAML.Scanner.Scanner

/-! # A content park awaits no node (item 352, Rule 2)

What the scanner does with the line AFTER a complete content node.  The node-domained
value-line twin `accum_block_on_closeThenBlock.h_valFV` asks a content park (`pendingContent`,
`pendingBlockContent`) what the stack is once a block node is scanned at the park — and no
content park can answer it: a new-line landing at a column greater than the node's start
is `invalidBareDocument` (the bare-document check, `h_bare` at every step), a column-0 `-` is a
sibling entry (the `-` arm's `nn < k` is refuted at `k = 0`), and a plain scalar FOLDS its
continuation lines into itself, so no second node ever starts at the park.  Pinned here so the
`∨ True` alternative item 352 gave `h_valFV` stays a measured fact, not a recollection. -/

open L4YAML L4YAML.Scanner

namespace ContentParkNoNode

/-- The scan outcome after `n + 1` steps: the error position, `EOF`, or the last token scanned. -/
inductive Outcome where
  | error (line col : Nat)
  | eof
  | tok (t : YamlToken)
  deriving Repr, BEq

def after (input : String) (n : Nat) : Outcome :=
  go (ScannerState.mk' input) (n + 1)
where
  go (s : ScannerState) : Nat → Outcome
    | 0 => .eof
    | k + 1 =>
      match scanNextToken s with
      | .ok (some s') =>
        if k = 0 then
          match s'.tokens.back? with
          | some p => .tok p.val
          | none => .eof
        else go s' k
      | .ok none => .eof
      | .error (.invalidBareDocument l c) => .error l c
      | .error _ => .error 0 0

-- a deeper landing after a complete quoted/flow content node, under an open `?`: rejected
#guard after "?\n  \"a\"\n  - b\n: v\n" 2 == .error 2 2
#guard after "?\n  \"a\"\n    - b\n: v\n" 2 == .error 2 4
#guard after "?\n  [a]\n  - b\n: v\n" 4 == .error 2 2
#guard after "?\n  \"a\"\n  b: 1\n: v\n" 2 == .error 2 2
-- the same after an entry-content park and at the root
#guard after "- \"a\"\n  - b\n" 2 == .error 1 2
#guard after "\"a\"\n  - b\n" 1 == .error 1 2
-- a column-0 `-` after an entry-content park is the sibling entry (`k = 0`)
#guard after "- \"a\"\n- b\n" 2 == .tok .blockEntry
-- a plain scalar folds the deeper line: ONE node, no second node at the park
#guard after "?\n  a\n  - b\n: v\n" 1 == .tok (.scalar "a - b" .plain)
#guard after "?\n  a\n  - b\n: v\n" 2 == .tok .value
#guard after "a\n  - b\n" 0 == .tok (.scalar "a - b" .plain)
-- and a column-0 landing under the open `?` that is not an indicator of the key is rejected
#guard after "?\n  a\n- b\n: v\n" 2 == .error 2 0

end ContentParkNoNode
