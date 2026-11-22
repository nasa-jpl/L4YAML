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

/-! # The indented entry's landed value composes (DOCS item 52)

`k:⏎  -⏎    a` — the entry's value on its OWN line — is `[196]
s-l+block-node`'s flow-in-block reading whose separator is
`[70] s-separate-lines(n)`: the crossed break plus the fresh line's
`s-indent(n)`.  The break-free reading is index-UNIVERSAL (the index never
occurs, item 23), which is why only the inline arms composed; the landing's
separator CONSUMES the index, so the reading exists at exactly the pending's
own `n` — `preprocess_some_separate_at_anyCol` (item 45) had built it at any
`n`, and item 52 is its first indented consumer.  ZERO runtime edits: every
pin here is an ACCEPT pin, and what moves is the derivation (the two
indented content arms' landing case parks arm 1's pending with the
fixed-index separator instead of deferring).

Pinned: the sequence-entry landing at both widths, quoted, with a sibling
snoc, with a nested mapping value; the empty-key and explicit-key mapping
twins, with a sibling entry.  The landed props/block-scalar/fold shapes stay
deferred (their own classes) but accepted — pinned as plain accepts. -/

namespace L4YAML.Tests.Guards.ScannerLandedValueCompose

open L4YAML

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok _, .ok _ => true
  | _, _ => false

-- The indented `-`'s landed value, at the floor width and above it.
#guard emits "k:\n  -\n    a\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :a", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  -\n   a\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :a", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  -\n    \"q\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL \"q", "-SEQ", "-MAP",
   "-DOC", "-STR"]
-- The entry-level snoc survives the landing: a sibling `-` extends.
#guard emits "k:\n  -\n    a\n  - b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ",
   "-MAP", "-DOC", "-STR"]
-- The landed content as a KEY: the nested mapping fills the entry.
#guard emits "k:\n  -\n    a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+MAP", "=VAL :a", "=VAL :1",
   "-MAP", "-SEQ", "-MAP", "-DOC", "-STR"]

-- The mapping twins: `[189]`'s empty key and `[187]`'s explicit key.
#guard emits "k:\n  :\n    v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :v", "-MAP",
   "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  ? a\n  :\n    v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :v", "-MAP",
   "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  :\n    v\n  a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :v",
   "=VAL :a", "=VAL :1", "-MAP", "-MAP", "-DOC", "-STR"]

-- The landed shapes whose classes stay deferred — accepted, unmoved.
#guard accepts "k:\n  -\n    &p a\n"
#guard accepts "k:\n  -\n    |\n     t\n"
#guard accepts "k:\n  -\n    a\n     b\n"

end L4YAML.Tests.Guards.ScannerLandedValueCompose

end Blanket
