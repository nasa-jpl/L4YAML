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

/-! # Node-property runs inside flow collections (DOCS item 9e)

`[96] c-ns-properties` is one optional `[101] c-ns-anchor-property` and one
optional `[97] c-ns-tag-property`, in either order — so a node carries **at most
one of each**, and a property run is at most two tokens long.  And `[104]
c-ns-alias-node` is a whole node, offered by `[161] ns-flow-node` as an
*alternative* to the properties-bearing form, never as its content.

The scanner enforced neither.  `[&a &b]`, `[!t !u]`, `[&a !t &b c]` and
`[&a *x]` all scanned clean in both pipelines — strings with no derivation, which
`accum_step_content`'s flow-interior arm would have had to produce grammar
evidence for.  (`duplicateAnchor` caught *some* of them, but only in the parser,
which the scanner-strictness capstone cannot use; duplicate **tags** were caught
nowhere — `[!t !u]` parsed successfully.)

Item 9e rejects them at content dispatch with `invalidNodeProperties`.

**Why the check is gated on `inFlow`.**  Token adjacency means "same property
run" only where nothing token-less can intervene.  Inside a flow that holds:
`[137]`/`[140]` admit `ns-flow-node` only, so no block collection can open
between two tokens.  In block context it fails — a block collection opens with a
*virtual* indent and no token of its own, so two adjacent property tokens can
belong to different nodes:

```yaml
&mapping
&key [ &item a, b, c ]: value    # &mapping is on the MAPPING, &key on the seq
top3: &node3
  *alias1 : scalar3              # &node3 is on the nested mapping, not on *alias1
```

Both are valid, both are in the yaml-test-suite (26DV and the anchor-on-mapping
case), and both were rejected by the first, ungated version of this guard — which
is how the gap in the reasoning was found.  §4 pins them.  The block-context half
of §6.9 strictness needs the indent machinery and stays open (DOCS, β.5).
-/

namespace Tests.Guards.ScannerFlowPropertyRun

open L4YAML
open L4YAML.Scanner

/-- Legacy and indexed verdicts as a comparable pair: `none` on success,
    `some e` on rejection.  Equal pairs mean the two pipelines agree. -/
private def verdicts (input : String) : Option ScanError × Option ScanError :=
  ( (match scan input with | .ok _ => none | .error e => some e)
  , (match Indexed.ScannerStateIx.scanIx input with | .ok _ => none | .error e => some e) )

/-- Both pipelines reject `input` with the same `invalidNodeProperties`
    indicator and position. -/
private def rejects9e (input : String) (i : Char) (line col : Nat) : Bool :=
  verdicts input == (some (.invalidNodeProperties i line col),
                     some (.invalidNodeProperties i line col))

/-- Both pipelines accept `input`. -/
private def bothAccept (input : String) : Bool := verdicts input == (none, none)

/-- Both pipelines reject `input` — without pinning *which* error.  Used where a
    second, unrelated defect also fires. -/
private def bothReject (input : String) : Bool :=
  (verdicts input).1.isSome && (verdicts input).2.isSome

/-! ## §1  A repeated property of the same kind

Position is pinned at the offending indicator, not at the run's start. -/

#guard rejects9e "[&a &b]\n" '&' 0 4            -- two anchors
#guard rejects9e "[!t !u]\n" '!' 0 4            -- two tags
#guard rejects9e "{&a &b}\n" '&' 0 4            -- flow-mapping twins
#guard rejects9e "{!t !u}\n" '!' 0 4
#guard rejects9e "[&a &b c]\n" '&' 0 4          -- with content following
#guard rejects9e "[!t !u c]\n" '!' 0 4

/-! ## §2  The distance-2 case: a legal pair, then a third property

`&a !t` is a legal run, so the second lookback is what rejects the third
property.  This is why the run is read two tokens deep and not one. -/

#guard rejects9e "[&a !t &b c]\n" '&' 0 7       -- anchor, tag, anchor
#guard rejects9e "[!t &a !u c]\n" '!' 0 7       -- tag, anchor, tag
#guard rejects9e "[&a !t !u c]\n" '!' 0 7       -- adjacent repeat after a pair
#guard rejects9e "[!t &a &b c]\n" '&' 0 7
#guard rejects9e "[&a !t &b !u c]\n" '&' 0 7    -- 4-run: first offender reported

/-! ## §3  A property before an alias

`[161] ns-flow-node` offers `c-ns-alias-node` only *without* properties. -/

#guard rejects9e "[&x, &a *x]\n" '*' 0 8
#guard rejects9e "[&x, !t *x]\n" '*' 0 8
#guard rejects9e "{k: &x 1, &a *x}\n" '*' 0 13
#guard bothReject "[&a *x]\n"                   -- also an undefined alias (legacy)

/-! ## §4  Block context is untouched — the suite cases that forced the gate

Adjacent property tokens in block context can belong to different nodes, because
the block collection between them opens with a virtual indent and emits no token
of its own.  The ungated guard rejected all four of these. -/

#guard bothAccept "---\n&mapping\n&key [ &item a, b, c ]: value\n"
#guard bothAccept "k: &alias1 v\ntop3: &node3 \n  *alias1 : scalar3\n"
#guard bothAccept "&a\nb: c\n"
#guard bothAccept "- &a\n- &b\n"
#guard bothAccept "a: &x\nb: &y\n"
#guard bothAccept "&a !t b\n"                   -- a legal block-context run
#guard bothAccept "!t &a b\n"

/-! ## §5  Legal flow property runs still pass

One anchor, one tag, either order; properties separated by a `,`, a `:` or a
`?`; properties on a nested collection. -/

#guard bothAccept "[&a !t b]\n"
#guard bothAccept "[!t &a b]\n"
#guard bothAccept "[&a b]\n"
#guard bothAccept "[!t b]\n"
#guard bothAccept "[&a]\n"                      -- properties + e-scalar
#guard bothAccept "[!t]\n"
#guard bothAccept "[&a, &b]\n"                  -- `,` separates the runs
#guard bothAccept "[!t, !u]\n"
#guard bothAccept "{&a k: &b v}\n"              -- `:` separates the runs
#guard bothAccept "{&a : &b}\n"
#guard bothAccept "[? &a k]\n"                  -- `?` separates
#guard bothAccept "[&a [&b c]]\n"               -- `[` separates
#guard bothAccept "[&a {&b: c}]\n"
#guard bothAccept "[&a \"b\"]\n"
#guard bothAccept "[!t 'b']\n"
#guard bothAccept "[&a: b]\n"
#guard bothAccept "[&x, *x]\n"                  -- alias after a `,` is fine
#guard bothAccept "{k1: &x 1, k2: *x}\n"        -- alias after a `:` is fine

/-! ## §6  Flow basics, unchanged -/

#guard bothAccept "[a, b]\n"
#guard bothAccept "{a: 1, b: 2}\n"
#guard bothAccept "[]\n"
#guard bothAccept "[[a, [b, {c: [d]}]]]\n"

end Tests.Guards.ScannerFlowPropertyRun

end Blanket
