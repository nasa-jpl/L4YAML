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

/-! # Node properties must be delimited (DOCS item 9f)

`[161] ns-flow-node(n,c)` reads `c-ns-properties(n,c)` followed by EITHER
`s-separate(n,c)` and `ns-flow-content(n,c)` OR nothing at all (`e-scalar`), and
`[104] c-ns-alias-node` is a whole node.  There is no third arm, so the character
directly after a property or alias token is separation, an entry or collection
boundary, or end of input — never the first character of content.

The scanner enforced nothing: `[&a[b]]`, `[&a{b: c}]`, `[!t"x"]`, `[!t[b]]` and
`[*x[b]]` all scanned clean in both pipelines.  §1 pins the rejections.

**What does NOT reach this test, and why the two property forms differ so much.**
`[102] ns-anchor-char` is `ns-char - c-flow-indicator`, so an anchor name absorbs
everything except `,[]{}` — `&a"x"` is ONE anchor named `a"x"`, `&a*x` one named
`a*x`, `&a&b` one named `a&b`, `&a:b` one named `a:b`, and `&a!t` one named
`a!t`.  §3 pins those as accepted, because reading them as two tokens is the
mistake this guard is one character away from making.  `[153] ns-tag-char`
additionally subtracts everything outside `ns-uri-char`, so a tag really does
stop at `"` — which is why `[!t"x"]` needed the test and `[&a"x"]` did not.

**Why this one is not gated on `s.inFlow`** (item 9e's three tests are).  It
looks only FORWARD, at the character the token's own walk stopped on, so nothing
token-less can sit between the two: the block-context counterexample that forced
9e's gate (Reflection 615) cannot arise here.  §4 pins the block-context
documents that confirms it.
-/

namespace Tests.Guards.ScannerNodePropertyDelimiter

open L4YAML
open L4YAML.Scanner

/-- Legacy and indexed verdicts as a comparable pair: `none` on success,
    `some e` on rejection.  Equal pairs mean the two pipelines agree. -/
private def verdicts (input : String) : Option ScanError × Option ScanError :=
  ( (match scan input with | .ok _ => none | .error e => some e)
  , (match Indexed.ScannerStateIx.scanIx input with | .ok _ => none | .error e => some e) )

/-- Both pipelines reject `input` with the same `invalidNodeProperties`
    indicator and position. -/
private def rejects9f (input : String) (i : Char) (line col : Nat) : Bool :=
  verdicts input == (some (.invalidNodeProperties i line col),
                     some (.invalidNodeProperties i line col))

/-- Both pipelines accept `input`. -/
private def bothAccept (input : String) : Bool := verdicts input == (none, none)

/-! ## §1  A property directly against content

The position reported is the property's own indicator, not the follower. -/

#guard rejects9f "[&a[b]]\n" '&' 0 1              -- anchor, then a nested seq
#guard rejects9f "[&a{b: c}]\n" '&' 0 1           -- anchor, then a nested map
#guard rejects9f "{k: &a[b]}\n" '&' 0 4
#guard rejects9f "[!t[b]]\n" '!' 0 1              -- tag, then a nested seq
#guard rejects9f "[!t{a: b}]\n" '!' 0 1
#guard rejects9f "[!t\"x\"]\n" '!' 0 1            -- tag, then a double-quoted scalar
-- `'` is `[39] ns-uri-char` hence `[40] ns-tag-char`: `!t'x'` is ONE primary tag
-- (N1b: `scanNamedTag` collects the full `ns-tag-char+` suffix, not just word chars).
#guard bothAccept "[!t'x']\n"
#guard bothAccept "[!t.x]\n"                        -- `.` and `/` are ns-tag-chars too:
#guard bothAccept "[!t/x a]\n"                      -- one tag `!t/x`, then plain `a`
#guard rejects9f "[*x[b]]\n" '*' 0 1              -- §7.5 [104]: an alias is a whole node
#guard rejects9f "[*x{a: b}]\n" '*' 0 1

/-! ## §2  Legal property runs — a real separation is present

One space, a line break, or a comment line all give `s-separate`. -/

#guard bothAccept "[&a [b]]\n"
#guard bothAccept "[&a {b: c}]\n"
#guard bothAccept "[!t [b]]\n"
#guard bothAccept "[!t \"x\"]\n"
#guard bothAccept "[!t 'x']\n"
#guard bothAccept "[&a b]\n"
#guard bothAccept "[&a !t b]\n"
#guard bothAccept "[&a\n b]\n"                    -- separation across a line break
#guard bothAccept "[&a #c\n b]\n"                 -- separation across a comment

/-! ## §3  The node ends at the property (`e-scalar`), or the name absorbs the
character — both are legal and must stay accepted -/

#guard bothAccept "[&a]\n"                        -- properties + e-scalar
#guard bothAccept "[&a, b]\n"                     -- `,` ends the entry
#guard bothAccept "{&a: b}\n"
#guard bothAccept "{k: &a}\n"
#guard bothAccept "[!t]\n"
#guard bothAccept "[!t, b]\n"
#guard bothAccept "[&a\"x\"]\n"                   -- ONE anchor named `a"x"` ([102])
#guard bothAccept "[&a'x']\n"                     -- ONE anchor named `a'x'`
#guard bothAccept "[&a*x]\n"                      -- ONE anchor named `a*x`
#guard bothAccept "[&a&b]\n"                      -- ONE anchor named `a&b`
#guard bothAccept "[&a:b]\n"                      -- ONE anchor named `a:b`
#guard bothAccept "[&a!t b]\n"                    -- ONE anchor named `a!t`
#guard bothAccept "[&ab]\n"

/-! ## §4  Block context is unaffected

The test looks only forward, so it needs no `s.inFlow` gate — but the suite
documents that forced item 9e's gate are pinned here too, because they are the
ones a forward/backward mix-up would break first. -/

#guard bothAccept "&a\nb: c\n"
#guard bothAccept "k: &a\n"
#guard bothAccept "- &a\n- &b\n"
#guard bothAccept "!t v\n"
#guard bothAccept "!!str v\n"
#guard bothAccept "&a !t b\n"
#guard bothAccept "&a\n"                          -- property at end of input
#guard bothAccept "!t\n"
#guard bothAccept "!<u> v\n"
#guard bothAccept "---\n&mapping\n&key [ &item a, b, c ]: value\n"
#guard bothAccept "k: &alias1 v\ntop3: &node3 \n  *alias1 : scalar3\n"

/-! ## §5  Aliases still resolve, and the pre-existing checks still fire first -/

#guard bothAccept "[&x, *x]\n"
#guard bothAccept "{k1: &x 1, k2: *x}\n"
#guard bothAccept "[&x, *x, *x]\n"

end Tests.Guards.ScannerNodePropertyDelimiter

end Blanket
