module

public import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch
public meta import L4YAML.Scanner.IndexedDispatch
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
public meta import L4YAML.Token.Token
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The col-0 `:` opens an empty-key block mapping (DOCS item 13)

`[189] c-l-block-map-implicit-value` admits an `e-node` key: a `:` at
column 0 is a complete mapping entry whose key is null.  Item 13 built the
accumulation's first BLOCK-MAPPING state for it — `PendingNode.pendingMapValue`,
the mapping twin of `pendingBlock` — so `: v`, `:`, `: [a]`, `: |` and
`: &a v` stopped escaping through `block_dispatch_deferred`'s `pendingFlow`.

The event streams below pin the shapes those derivations cover, on BOTH
pipelines (the pass is proof-only: no scanner or emitter changed).  A
mapping with a null key is unusual YAML but fully legal, and it is the one
`:` dispatch whose entry needs NO held key — which is what made it the
block-mapping campaign's first completable arm.

**What stays escaped** (and still scans clean): the same-line `:` after
content — `a: b`, the implicit key, needs the parked content re-read in
`.blockKey` context — and the `?` explicit key.  Deliberately not pinned:
over-acceptances are not fixtures (Reflection 622).
-/

namespace Tests.Guards.ScannerEmptyKeyMapping

open L4YAML

/-- Legacy and indexed event streams as a comparable pair; `none` on rejection. -/
private def bothEvents (input : String) : Option String × Option String :=
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )

/-- Both pipelines accept `input` and emit exactly `expected`. -/
private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  bothEvents input == (e, e)

/-! ## §1  The entry the producer composes

`s-indent(0)` + `':'` + value.  The value node arrives through the same
consumers `pendingBlock` already had — content, flow open, block scalar —
so each shape below is one consumer arm's composition. -/

-- Scalar values — `SBlockNode.flowInBlock` through `pendingContent`.
#guard emits ": v\n" ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits ":  v\n" ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits ": 'q'\n" ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL 'q", "-MAP", "-DOC", "-STR"]
#guard emits ": \"q\"\n" ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL \"q", "-MAP", "-DOC", "-STR"]

-- No value at all — `[189]`'s `( e-node s-l-comments )`, the
-- `close_with_ssl` arm (`SBlockNode.emptyNode`).
#guard emits ":\n" ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :", "-MAP", "-DOC", "-STR"]
#guard emits ":" ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :", "-MAP", "-DOC", "-STR"]

-- The value on its own line — the separator crosses the break.
#guard emits ":\n  v\n" ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :v", "-MAP", "-DOC", "-STR"]

-- A flow collection as the value — the flow-open arm rides `h_close`.
#guard emits ": [a]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "+SEQ []", "=VAL :a", "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits ": {a: b}\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "+MAP {}", "=VAL :a", "=VAL :b", "-MAP", "-MAP", "-DOC", "-STR"]

-- A block scalar as the value.
#guard emits ": |\n text\n" ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL |text\\n", "-MAP", "-DOC", "-STR"]

-- A held `[96]` run decorating the VALUE — `pendingProps` with the map's
-- value closure as its route.
#guard emits ": &a v\n" ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL &a :v", "-MAP", "-DOC", "-STR"]

/-! ## §2  The producer's predecessors

Every closable pending closes at the line start first; the entry opens on
the position the close reached. -/

-- After an explicit document start / a document suffix.
#guard emits "---\n: v\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "x\n...\n: v\n"
  ["+STR", "+DOC", "=VAL :x", "-DOC ...", "+DOC", "+MAP", "=VAL :", "=VAL :v", "-MAP", "-DOC", "-STR"]

-- After a held property run: the props decorate the MAP itself in the
-- shipped parse; the accumulation's derivation closes the run as a
-- props-only document and continues — either way the input is in the
-- language, which is what the forward theorem asserts.
#guard emits "&a\n: v\n"
  ["+STR", "+DOC", "+MAP &a", "=VAL :", "=VAL :v", "-MAP", "-DOC", "-STR"]

-- Sibling entries: each `:` closes the previous entry's map state and
-- re-opens — `[211]`'s continuation admits the chain.
#guard emits ": a\n: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :a", "=VAL :", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits ": v\n:\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :v", "=VAL :", "=VAL :", "-MAP", "-DOC", "-STR"]

-- The map closed by a document suffix.
#guard emits ": v\n...\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :v", "-MAP", "-DOC ...", "-STR"]

/-! ## §3  What the arm does NOT accept

The scanner's own strictures around the shape — pinned so the composed arm
is not read as a loosening. -/

/-- Legacy and indexed verdicts as a comparable pair: `none` on success. -/
private def verdicts (input : String) : Option ScanError × Option ScanError :=
  ( (match Scanner.scan input with | .ok _ => none | .error e => some e)
  , (match Scanner.Indexed.ScannerStateIx.scanIx input with | .ok _ => none | .error e => some e) )

-- `- a` then a col-0 `:` dies in BOTH scanners before any dispatch:
-- the unwind sees trailing content at the sequence's own indent.
#guard verdicts "- a\n: v\n" == (some (.trailingContent 1 0), some (.trailingContent 1 0))

-- `:x` is not a value indicator at all — `isValueCandidate` wants a blank
-- after — it is a plain scalar.
#guard emits ":x\n" ["+STR", "+DOC", "=VAL ::x", "-DOC", "-STR"]

-- Nested empty keys on one line: `[194]`'s value slot has no same-line
-- mapping, so the second `:` is refused (item 48's `nestedMappingOnLine`).
#guard verdicts ": : v\n" == (some (.nestedMappingOnLine 0 2), some (.nestedMappingOnLine 0 2))

end Tests.Guards.ScannerEmptyKeyMapping

end Blanket
