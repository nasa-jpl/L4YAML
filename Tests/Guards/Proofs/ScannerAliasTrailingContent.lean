module

public import L4YAML.Scanner.Scanner

public meta import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch

public meta import L4YAML.Scanner.IndexedDispatch
public meta import L4YAML.Token.Token
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # An alias node ends its node (DOCS item 9h)

`[104] c-ns-alias-node ::= "*" ns-anchor-name` is a whole node — an
`ns-flow-node` [161], and through `s-l+block-node` [196] a whole block node.  So
in BLOCK context whatever follows it on the same line would have to be a SECOND
node in a slot that admits exactly one.

Every other block-context node terminator already says so, and they all share
one allow-list — a line break, a `#` comment, or the `:` that makes the node an
implicit key:

* quoted scalars ([109]/[120]) call `validateTrailingContent`;
* a `]`/`}` returning to block context ([137]/[140]) calls `validateFlowClose`.

The alias arm had neither.  §1 pins the nine followers that scanned clean in
BOTH pipelines before `validateAliasClose`; the parser rejected them a layer
later (`bareDocumentContent`), so this was never a shipped over-acceptance — but
`accum_flow_open_depth0` could not refute them, which is how it was found.

**Why the guard is gated on `!inFlow`.**  Inside a flow collection the same job
is already done one dispatcher earlier: `.alias` is in
`YamlToken.completesFlowValue`, so `scanNextToken_checkFlowAdjacency` (item 9b)
rejects `[*a *b]` before content dispatch runs.  §3 pins that.

**Why the plain, block-scalar, anchor and tag arms need nothing.**  A plain
scalar in block context ABSORBS what follows — `ns-plain-safe-out` is `ns-char`,
so `k: foo [a]` is the ONE scalar `foo [a]`, not two nodes; a block scalar runs
to the end of its lines; and `&a`/`!t` are `c-ns-properties` [96], which are
*supposed* to be followed by content on the same line.  §4 pins all three, and
`&a [b]` in particular: it is the legal inhabitant of the very accumulation arm
this item was found under, so a guard that rejected it would be wrong.
-/

namespace Tests.Guards.ScannerAliasTrailingContent

open L4YAML
open L4YAML.Scanner

/-- Legacy and indexed verdicts as a comparable pair: `none` on success,
    `some e` on rejection.  Equal pairs mean the two pipelines agree. -/
private def verdicts (input : String) : Option ScanError × Option ScanError :=
  ( (match scan input with | .ok _ => none | .error e => some e)
  , (match Indexed.ScannerStateIx.scanIx input with | .ok _ => none | .error e => some e) )

/-- Both pipelines reject `input` with `trailingContent` at the same position. -/
private def rejects9h (input : String) (line col : Nat) : Bool :=
  verdicts input == (some (.trailingContent line col), some (.trailingContent line col))

/-- Both pipelines accept `input`. -/
private def bothAccept (input : String) : Bool := verdicts input == (none, none)

/-! ## §1  A second node after an alias, in block context

The anchor has to be defined for the alias to reach content dispatch at all, so
every input carries a `k1: &a v` line first.  The rejection is at the follower,
column 7 on line 1 — the character after `k2: *a `. -/

#guard rejects9h "k1: &a v\nk2: *a [b]\n" 1 7        -- flow sequence
#guard rejects9h "k1: &a v\nk2: *a {b: c}\n" 1 7     -- flow mapping
#guard rejects9h "k1: &a v\nk2: *a \"x\"\n" 1 7      -- double-quoted
#guard rejects9h "k1: &a v\nk2: *a 'x'\n" 1 7        -- single-quoted
#guard rejects9h "k1: &a v\nk2: *a *a\n" 1 7         -- another alias
#guard rejects9h "k1: &a v\nk2: *a plain\n" 1 7      -- plain scalar
#guard rejects9h "k1: &a v\nk2: *a &b x\n" 1 7       -- an anchor
#guard rejects9h "k1: &a v\nk2: *a !t x\n" 1 7       -- a tag
#guard rejects9h "k1: &a v\nk2: *a |\n  x\n" 1 7     -- a block scalar header

/-! ## §2  The three followers that DO end the node

Exactly `validateTrailingContent`'s allow-list, and nothing else is added:
end of line (or of input), a comment, and the `:` that turns the alias into an
implicit key. -/

#guard bothAccept "k1: &a v\nk2: *a\n"               -- line break
#guard bothAccept "k1: &a v\nk2: *a"                 -- end of input, no newline
#guard bothAccept "k1: &a v\nk2: *a   \n"            -- trailing `s-white` only
#guard bothAccept "k1: &a v\nk2: *a # c\n"           -- a comment
#guard bothAccept "k1: &a v\n*a : x\n"               -- the alias AS an implicit key
#guard bothAccept "k1: &a v\n? *a\n: b\n"            -- …and as an explicit one
-- …and a sequence entry, whose `-` has to open a sequence somewhere legal:
-- at the mapping's OWN column with the entry complete it is §9.2's third
-- dangler, refused since item 134 (`scanBlockEntryValidate`), which is a
-- statement about the `-` and not about the alias behind it.
#guard bothAccept "k1: &a v\nk2:\n- *a\n"             -- a sequence entry

/-! ## §3  Flow context is untouched

`.alias` completes a flow value, so item 9b's adjacency check already rejects a
node after one — with its OWN error, which is what these pin: a `trailingContent`
here would mean the new guard had leaked past its `!inFlow` gate. -/

#guard bothAccept "k1: &a v\nk2: [*a, *a]\n"
#guard bothAccept "k1: &a v\nk2: {x: *a}\n"
#guard bothAccept "k1: &a v\nk2: [*a]\n"
#guard verdicts "k1: &a v\nk2: [*a *a]\n"
    == (some (.invalidFlowEntry 1 8), some (.invalidFlowEntry 1 8))

/-! ## §4  The sibling arms that must NOT get this test

A plain scalar absorbs its follower, a block scalar ends at its own line, and a
property run is *supposed* to be followed by content.  `&a [b]` is the one to
watch: it is a legal inhabitant of `accum_flow_open_depth0`'s open arm — the
same arm whose illegal inhabitants item 9h removes — so it must keep scanning
AND keep parsing to `["b"]`. -/

#guard bothAccept "foo [a]\n"                        -- ONE plain scalar `foo [a]`
#guard bothAccept "k: foo [a]\n"                     -- ONE plain scalar `foo [a]`
#guard bothAccept "&a [b]\n"                         -- anchor + flow sequence
#guard bothAccept "!!seq [b]\n"                      -- tag + flow sequence
#guard bothAccept "&a !!seq [b]\n"                   -- both properties
#guard bothAccept "!t {a: b}\n"
#guard bothAccept "k: &a [b]\n"
#guard bothAccept "- &a [b]\n"
#guard bothAccept "--- &a [b]\n"
#guard bothAccept "k: |\n  x\n"
#guard bothAccept "k: \"v\"\n"

/-! ## §5  A pre-existing pipeline difference this item does NOT introduce

The indexed `*` arm has no `definedAnchors` check (filed separately), so on an
UNDEFINED alias the two pipelines pick different errors: legacy reports
`undefinedAlias` from its pre-scan check, indexed reaches the alias scan and
then §1's `trailingContent`.  Both still reject; pinned here so the difference
is not later read as an item-9h regression. -/

#guard verdicts "&a x\n--- *a [b]\n"
    == (some (.undefinedAlias "a" 1 4), some (.trailingContent 1 7))

end Tests.Guards.ScannerAliasTrailingContent

end Blanket
