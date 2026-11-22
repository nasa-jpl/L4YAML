module

public import L4YAML.Scanner.Scanner

public meta import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch

public meta import L4YAML.Scanner.IndexedDispatch
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # A flow `?` is delimited (DOCS item 9j)

Item 9g pinned the `?`'s *predecessor*.  This pins its *successor*, and it is the
same production read left to right:

    [150] ns-flow-pair(n,c) ::= ( "?" s-separate(n,c)
                                   ns-flow-map-explicit-entry(n,c) )
                              | ns-flow-pair-entry(n,c)

The `s-separate` is mandatory.  Inside a flow collection it is
`s-separate-lines(n)`, whose only zero-width arm is `/* Start of line */` — which
a `?` sitting mid-line cannot take.  So the character directly after the
indicator is a blank or a break, never a flow indicator.

`isKeyCandidate` admitted one anyway (`isBlankBool n || (s.inFlow &&
isFlowIndicatorBool n)`), and `[?]`, `[?,a]`, `{?}`, `{?,a}` all scanned clean in
BOTH pipelines.  §1 pins the rejections.

The EMPTY explicit entry is legal and stays accepted: `[142]
c-ns-flow-map-explicit-entry` has an `( e-node e-node )` arm, so `[? ]` and
`[? , a]` derive — what they have and the rejected forms do not is the
separation.  §2 pins that this is a rule about the separator, one space wide.

**Why the error is `unexpectedChar`.**  Same as 9g: the test rides on the `?`
arm's dispatch condition rather than an `if … then throw` of its own, so a `?`
that fails it falls through to `scanNextToken_dispatchContent`.  The follower
that got it here is a flow indicator, and `[131] ns-plain-first` admits a leading
`?` only before an `ns-plain-safe(c)` character — which in flow context subtracts
exactly `c-flow-indicator`.  So `canStartPlainScalarBool` is false and the
fall-through is always the error.
-/

namespace Tests.Guards.ScannerFlowKeyFollower

open L4YAML
open L4YAML.Scanner

/-- Legacy and indexed verdicts as a comparable pair: `none` on success,
    `some e` on rejection.  Equal pairs mean the two pipelines agree. -/
private def verdicts (input : String) : Option ScanError × Option ScanError :=
  ( (match scan input with | .ok _ => none | .error e => some e)
  , (match Indexed.ScannerStateIx.scanIx input with | .ok _ => none | .error e => some e) )

/-- Both pipelines reject `input` at the `?`, with the same position. -/
private def rejects9j (input : String) (line col : Nat) : Bool :=
  verdicts input == (some (.unexpectedChar '?' line col),
                     some (.unexpectedChar '?' line col))

/-- Both pipelines accept `input`. -/
private def bothAccept (input : String) : Bool := verdicts input == (none, none)

/-! ## §1  A `?` with no separation after it

The follower is a flow indicator in every case — the four `isKeyCandidate`
admitted that `[150]` does not. -/

#guard rejects9j "[?]\n" 0 1                      -- closed immediately
#guard rejects9j "{?}\n" 0 1
#guard rejects9j "[?,a]\n" 0 1                    -- `,` directly after
#guard rejects9j "{?,a}\n" 0 1
#guard rejects9j "[?[a]]\n" 0 1                   -- a nested open directly after
#guard rejects9j "[?{a: b}]\n" 0 1
#guard rejects9j "[a, ?]\n" 0 4                   -- …at a later entry too
#guard rejects9j "[a, ?,b]\n" 0 4
#guard rejects9j "[[?]]\n" 0 2                    -- …and at depth 2

/-! ## §2  The rule is exactly one space wide

Each accepted input below differs from the rejected one above it by the
`s-separate` alone, and the empty explicit entry (`e-node e-node`) is what it
derives to. -/

#guard bothAccept "[? ]\n"                        -- empty key, empty value
#guard bothAccept "{? }\n"
#guard bothAccept "[? , a]\n"
#guard bothAccept "{? , a}\n"
#guard bothAccept "[? [a]]\n"
#guard bothAccept "[? {a: b}]\n"
#guard bothAccept "[a, ? ]\n"
#guard bothAccept "[[? ]]\n"

/-! ## §3  A break is separation too

`s-separate-lines(n)` is not just `s-white+`, so the follower test admits a line
break — `isBlankBool` covers both. -/

#guard bothAccept "[?\n a]\n"
#guard bothAccept "[?\n]\n"
#guard bothAccept "{?\n a: b}\n"
#guard bothAccept "[? #z\n a]\n"                  -- separation across a comment

/-! ## §4  What the rule does not touch

A `?` that never reaches the `?` arm — because it starts a plain scalar or sits
inside one — is unaffected, and so is every `?` in block context. -/

#guard bothAccept "[??]\n"                        -- ONE plain scalar `??`
#guard bothAccept "[?x]\n"                        -- ONE plain scalar `?x`
#guard bothAccept "[a ? b]\n"                     -- ONE plain scalar `a ? b`
#guard bothAccept "[? ?x]\n"                      -- key is the plain scalar `?x`
#guard bothAccept "?\n"                           -- block: `?` at end of input
#guard bothAccept "? a\n: b\n"
#guard bothAccept "? [a, b]\n: c\n"
-- the compact `?`'s break-crossed key content, one column past the `?` (its
-- equal-column twin `- ?⏎  a` refuses at item 177's floor, not at the `?`)
#guard bothAccept "- ?\n   a\n"

end Tests.Guards.ScannerFlowKeyFollower

end Blanket
