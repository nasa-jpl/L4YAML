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

/-! # The plain-scalar no-gain rewind, restored in the indexed walk (DOCS item 14)

A block- or flow-context plain-scalar continuation probe that collects
nothing beyond the fold itself rewinds to the PRE-fold cursor — legacy
`collectPlainScalarLoop`'s `result.content.length ≤ prevLen` branch.  The
indexed `collectPlainScalarLoopIx` dropped that rewind at the cursor
cutover (while its docstring still promised it), which made the two
pipelines' walks REST in different places after a failed probe, with two
symptom families across a 5,460-input differential sweep (580 divergent):

* **Family A (354)** — verdict-equal, stage-different: `x⏎: v` died at the
  indexed SCAN (`invalidImplicitKey` — the stale saved key survived to the
  `:` because no skip-time break crossing re-allowed a fresh one) but at
  the legacy PARSE (`invalidBareDocument` — the rewind let the skip cross,
  a fresh empty key resolved, and the parser refused the bare-document
  continuation).  Matrix-invisible: both reject.
* **Family B (226)** — content-different on ACCEPTED inputs: `x⏎⏎` kept
  the fold's `\n` in the indexed scalar (`=VAL :x\n` vs legacy `=VAL :x`),
  against `[131] ns-plain`, which has no trailing-break production.
  Invisible to matrix AND suites: no corpus case puts a bare top-level
  plain scalar before a trailing blank line.

`backtrackIfNoGain` (`Scanner/IndexedScanner.lean`) restores the rewind on
both fold arms; the sweep is clean.  The pins below fix each family's
representatives on BOTH pipelines, plus the neighbours that must NOT move
— including `x⏎y: v`, the §7.4 scan rejection the future implicit-key arm
(`a: b`, DOCS row 12) reads as its multiline-key refutation.
-/

namespace Tests.Guards.ScannerPlainNoGainRewind

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

/-! ## §1  Family B — the rewound fold no longer pollutes accepted content

A trailing blank line after a plain scalar is a no-gain probe: the scalar
is `x`, never `x\n`. -/

#guard emits "x\n\n" ["+STR", "+DOC", "=VAL :x", "-DOC", "-STR"]
#guard emits "x\n\n\n" ["+STR", "+DOC", "=VAL :x", "-DOC", "-STR"]
#guard emits "x\n \n" ["+STR", "+DOC", "=VAL :x", "-DOC", "-STR"]
#guard emits "x \n\n" ["+STR", "+DOC", "=VAL :x", "-DOC", "-STR"]
#guard emits "  x\n\n" ["+STR", "+DOC", "=VAL :x", "-DOC", "-STR"]

-- The flow twin: the same rewind guards the flow fold arm.
#guard emits "[x\n\n]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :x", "-SEQ", "-DOC", "-STR"]
#guard emits "{a: x\n\n}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :a", "=VAL :x", "-MAP", "-DOC", "-STR"]

-- A GAINING probe still folds: multiline plain scalars are untouched.
#guard emits "x\ny\n" ["+STR", "+DOC", "=VAL :x y", "-DOC", "-STR"]
#guard emits "x\n\ny\n" ["+STR", "+DOC", "=VAL :x\\ny", "-DOC", "-STR"]

/-! ## §2  Family A — the error family now dies identically

With the rewind, the skip crosses the probed break in both pipelines, a
fresh empty key resolves at the col-0 `:`, and the PARSER refuses the
bare-document continuation — the same `ScanError` value end to end. -/

#guard verdicts "x\n: v\n" == (some (.invalidBareDocument 1 0), some (.invalidBareDocument 1 0))
#guard verdicts "x\n:\n" == (some (.invalidBareDocument 1 0), some (.invalidBareDocument 1 0))
#guard verdicts "&a x\n: v\n" == (some (.invalidBareDocument 1 0), some (.invalidBareDocument 1 0))

-- The nested-gain shape: the DEEPEST probe rewinds even when an outer
-- probe gained a line.
#guard verdicts "x\ny\n: v\n" == (some (.invalidBareDocument 2 0), some (.invalidBareDocument 2 0))

-- The indented representative (the `x⏎: v` shape one level down).
#guard verdicts "a:\n  x\n  : v\n" ==
  (some (.invalidBareDocument 2 2), some (.invalidBareDocument 2 2))

/-! ## §3  The neighbours that must NOT move

The refutation the implicit-key arm (DOCS row 12) will consume, and the
accepted shapes on the family's boundary. -/

-- A plain scalar that GAINS a line and then meets a same-line `: ` is a
-- multiline implicit key — rejected at SCAN by §7.4 in BOTH pipelines
-- (the stale saved key, `simpleKey.pos.line ≠ line`, no rewind involved).
#guard verdicts "x\ny: v\n" == (some (.invalidImplicitKey 1), some (.invalidImplicitKey 1))

-- The single-line key with an inner space stays a plain implicit key.
#guard emits "x y: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :x y", "=VAL :v", "-MAP", "-DOC", "-STR"]

-- Sibling chains through a resolved value stay accepted: the value's
-- probe floor (`contentIndent = 1`) never touches the col-0 `:` line.
#guard emits "a: b\n: c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "=VAL :", "=VAL :c", "-MAP", "-DOC", "-STR"]

-- Explicit-key shapes: the `?` pushes a mapping indent, so the key
-- content's probe floor clears the `:` line — no probe, no staleness.
#guard emits "? x\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :x", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "?\n  x\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :x", "=VAL :v", "-MAP", "-DOC", "-STR"]

-- A comment line after the scalar terminates PRE-break in both walks
-- (the `#`-after-fold arm, untouched by the rewind).
#guard emits "x\n# c\n" ["+STR", "+DOC", "=VAL :x", "-DOC", "-STR"]

end Tests.Guards.ScannerPlainNoGainRewind

end Blanket
