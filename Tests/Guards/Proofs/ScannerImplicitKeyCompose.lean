module

public import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch
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

/-! # The col-0 plain implicit key composes (DOCS item 15)

`a: b` — a top-level plain scalar at column 0 whose same-line `:` resolves
the saved simple key — now accumulates as GRAMMAR instead of riding the
`scannerDrop` deferral: `[193] ns-s-block-map-implicit-key`'s YAML arm
(`ns-plain(0, block-key)` = the one-line reading), `[66]`'s optional
in-line separation, `GLit ':'`, and `pendingMapValue` awaiting the value
(item 13's mapping machinery, re-anchored at the key).

The coupling that fires the arm rides `PendingNode`'s scanner-state
parameter (item 12's design): the saved key is possible AND rests on the
current line — exactly the §7.4 pass `scanValueValidate` demands — iff the
parked plain scalar crossed no break, which is what lets a `.flowOut`
multi-line production re-read at `.blockKey`.  The witness chain is line
arithmetic: `saveSimpleKey` stamps `pos := currentPos` at the content
START, the scan only ever advances the line, and the fold arms advance it
STRICTLY (`collectPlainScalarLoop_line_le` + the one-line conjunct of
`collectPlainScalarLoop_prod`).

The pins below fix the composed shapes and the neighbours that stay put:
the punted pack (indented keys) still accepts through the deferral, and the
multiline shapes the coupling refutes still reject at the same place in
BOTH pipelines.  (The other heads followed: quoted keys in item 16, alias
and property-prefixed keys in item 17; and item 19 gave the break-crossed
`:` its own arm — where the pack is spent, the landing composes `[189]`'s
empty-key entry instead.)
-/

namespace Tests.Guards.ScannerImplicitKeyCompose

open L4YAML

/-- Legacy and indexed event streams as a comparable pair; `none` on rejection. -/
private def bothEvents (input : String) : Option String × Option String :=
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )

/-- Both pipelines accept `input` and emit exactly `expected`. -/
private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  bothEvents input == (e, e)

/-- Legacy and indexed end-to-end verdicts as a comparable pair: `none` on
    success (scan errors and parse errors share `ScanError`). -/
private def verdicts (input : String) : Option ScanError × Option ScanError :=
  ( (match Events.streamToEvents input with | .ok _ => none | .error e => some e)
  , (match Events.streamToEventsIx input with | .ok _ => none | .error e => some e) )

/-! ## §1  The composed shapes — col-0 plain keys, same-line `:`

Each is now covered by `colon_open_map_implicit`'s grammar derivation:
key production + `:` + value through `pendingMapValue`. -/

#guard emits "a: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
-- In-line separation before the `:` ([66], the key pack's trailing whites).
#guard emits "a : b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
-- Empty value: `[189]`'s `( e-node s-l-comments )` arm via the pending's close.
#guard emits "a:\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :", "-MAP", "-DOC", "-STR"]
-- Sibling chains ride `[211]`'s admitted bare-document continuation (item 13).
#guard emits "a: b\nc: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "=VAL :c", "=VAL :d",
   "-MAP", "-DOC", "-STR"]
-- A multi-word plain key: the in-line entries' `s-white*` slots.
#guard emits "a b: c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a b", "=VAL :c", "-MAP", "-DOC", "-STR"]
-- Flow and block-scalar values land through `pendingMapValue`'s consumers.
#guard emits "a: [x, y]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ []", "=VAL :x", "=VAL :y",
   "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "a: |\n x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL |x\\n", "-MAP", "-DOC", "-STR"]

/-! ## §2  Punted packs — accepted through the deferral, recorded in row 12

This pass packs only PLAIN content at column 0; the indented key accepts
unchanged and stays with the campaign's remaining arms.  (`[188]`'s JSON
arm followed: the quoted keys in item 16, `ScannerQuotedKeyCompose.lean`;
the alias and property-prefixed keys in item 17,
`ScannerPropsAliasKeyCompose.lean`.) -/

-- Indented mapping: a col≠0 key punts (the indent machinery's arm).
#guard emits " a: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]

/-! ## §3  The refuted neighbours — must NOT move, identical in BOTH pipelines

The multiline shapes the §7.4 coupling excludes keep their rejections. -/

-- A col-0 continuation line is ABSORBED by the plain scalar (`x a` gains),
-- so the `:` meets a stale cross-line key — the scan rejects (item 14's
-- refutation, unchanged).
#guard verdicts "x\na: b\n" == (some (.invalidImplicitKey 1), some (.invalidImplicitKey 1))
-- A value cannot itself become an implicit key on the same line — the
-- scanner refuses the second `:` (item 48's `nestedMappingOnLine`).
#guard verdicts "a: b: c\n" == (some (.nestedMappingOnLine 0 4), some (.nestedMappingOnLine 0 4))
-- A completed quoted document refuses a following bare mapping — the
-- accumulation's over-approximation admits the SCAN, the parser rejects.
#guard verdicts "\"x\"\na: b\n" ==
  (some (.invalidBareDocument 1 0), some (.invalidBareDocument 1 0))

end Tests.Guards.ScannerImplicitKeyCompose

end Blanket
