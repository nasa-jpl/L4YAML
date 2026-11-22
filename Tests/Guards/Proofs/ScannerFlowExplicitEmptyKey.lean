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

/-! # `'?' s-separate ':'` — the explicit entry with an EMPTY key (DOCS item 9n)

Item 9l added `[143] ns-flow-map-explicit-entry`'s `( e-node e-node )` arm
(`[? ]`, `{? }`) and `[146] c-ns-flow-map-empty-key-entry` on the sequence side
(`[: a]`, `[:]`), and deliberately stopped short of their COMPOSITION:

    [150] ns-flow-pair(n,c) ::= ( "?" s-separate ns-flow-map-explicit-entry(n,c) )
                              | ns-flow-pair-entry(n,c)

reaches `[146]` through `[143]`'s implicit alternative, so `? : a` and `? :` are
an explicit entry whose key is an `e-node`.  Those two shapes have parsed
correctly since before any of this work, and until item 9n the grammar had no
derivation for them — the same accepts-correct-but-underivable gap Reflection
625 names, deferred on purpose because a constructor with no producer is
inhabitation debt and its only producer is the `:` dispatch.

Item 9n supplies the producer (`FlowOpenStack.receiveColonQuestion`), so the two
constructors land with it.  Nothing about the scanner changed: every `#guard`
below passes before and after, and they exist to pin the shapes the new
`SFlowSeqEntry.explicitEmptyKeyValue` / `.explicitEmptyKeyEmpty` and their
mapping twins derive — the corpus half of the check that the grammar addition
matches the shipped behaviour rather than inventing it.

§3 pins the OTHER tail item 9n closes, `.sep`: a `:` opening an entry with no
key at all.  Its grammar (`emptyKeyValue`/`emptyKeyEmpty`) is 9l's; what is new
is that `FlowOpenStack.receiveColonSep` is TOTAL on that tail — `betweenEmpty`
and `betweenHeld` are its only two frames and a `:` is legal after both.
-/

namespace Tests.Guards.ScannerFlowExplicitEmptyKey

open L4YAML
open L4YAML.Events

/-- Legacy and indexed event streams as a comparable pair; `none` on rejection.
    Equal pairs mean the two pipelines agree. -/
private def bothEvents (input : String) : Option String × Option String :=
  ( (match streamToEvents input with | .ok s => some s | .error _ => none)
  , (match streamToEventsIx input with | .ok s => some s | .error _ => none) )

/-- Both pipelines accept `input` and emit exactly `expected`. -/
private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  bothEvents input == (e, e)

/-! ## §1  `'?' s-separate ':'` in a flow SEQUENCE

`[150]`'s explicit arm with `[146]` inside it: the entry is a single-pair
mapping whose key is empty. -/

-- `[? : a]` — empty key, value `a`.
#guard emits "[? : a]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :", "=VAL :a", "-MAP",
   "-SEQ", "-DOC", "-STR"]

-- `[? :]` — empty key, empty value: `[148] c-ns-flow-map-separate-value`'s
-- `e-node` branch.
#guard emits "[? :]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :", "=VAL :", "-MAP",
   "-SEQ", "-DOC", "-STR"]

-- …with the value slot spelled out as trailing space rather than absent.
#guard emits "[? : ]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :", "=VAL :", "-MAP",
   "-SEQ", "-DOC", "-STR"]

-- Followed by a `,`: the entry closes at the comma, which is the
-- `SeqFrame.midQuestionEmptyColon` case of `holdComma`.
#guard emits "[? :, a]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :", "=VAL :", "-MAP",
   "=VAL :a", "-SEQ", "-DOC", "-STR"]

-- Preceded by an entry: the frame reaches `.question` from `betweenHeld`, not
-- only from `betweenEmpty`.
#guard emits "[a, ? : b]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :a", "+MAP {}", "=VAL :", "=VAL :b",
   "-MAP", "-SEQ", "-DOC", "-STR"]

-- Two of them in a row.
#guard emits "[? : a, ? : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :", "=VAL :a", "-MAP",
   "+MAP {}", "=VAL :", "=VAL :b", "-MAP", "-SEQ", "-DOC", "-STR"]

/-! ## §2  The same shapes in a flow MAPPING

`[142]`'s explicit entry rather than `[150]`'s pair, so the pair is emitted
directly into the enclosing mapping. -/

#guard emits "{? : a}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :", "=VAL :a", "-MAP", "-DOC", "-STR"]

#guard emits "{? :}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :", "=VAL :", "-MAP", "-DOC", "-STR"]

#guard emits "{? :, a: b}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :", "=VAL :", "=VAL :a", "=VAL :b",
   "-MAP", "-DOC", "-STR"]

/-! ## §3  The `.sep` tail: a `:` with no `?` and no key

Item 9l's `[146]` constructors, re-pinned here because item 9n's
`receiveColonSep` is the transition that reaches them — from `betweenEmpty`
(right after the bracket) and from `betweenHeld` (right after a `,`), the two
frames that tail class has. -/

#guard emits "[: a]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :", "=VAL :a", "-MAP",
   "-SEQ", "-DOC", "-STR"]

#guard emits "[:]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :", "=VAL :", "-MAP",
   "-SEQ", "-DOC", "-STR"]

#guard emits "[a, : b]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :a", "+MAP {}", "=VAL :", "=VAL :b",
   "-MAP", "-SEQ", "-DOC", "-STR"]

#guard emits "{: a}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :", "=VAL :a", "-MAP", "-DOC", "-STR"]

#guard emits "{a: b, : c}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :a", "=VAL :b", "=VAL :", "=VAL :c",
   "-MAP", "-DOC", "-STR"]

/-! ## §4  The `.question` tail's OTHER consumers, unchanged

`[? ]` and `[? , a]` are 9l's `( e-node e-node )` shapes: the same
`midQuestion` frame, closed or comma'd instead of colon'd.  Re-pinned so that
adding a second exit from that frame is visible as additive. -/

#guard emits "[? ]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :", "=VAL :", "-MAP",
   "-SEQ", "-DOC", "-STR"]

#guard emits "[? , a]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :", "=VAL :", "-MAP",
   "=VAL :a", "-SEQ", "-DOC", "-STR"]

#guard emits "{? }\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :", "=VAL :", "-MAP", "-DOC", "-STR"]

-- `? key : value` — the explicit entry WITH a key, which has had its
-- constructors since long before 9l and is the shape the new ones sit beside.
#guard emits "[? a : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :a", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]

end Tests.Guards.ScannerFlowExplicitEmptyKey

end Blanket
