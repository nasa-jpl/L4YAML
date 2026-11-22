module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The dangling run a FLOW COLLECTION carries (DOCS item 159)

Item 158 measured a family the scanner accepted and the parser refused:
`a: 1⏎&p [b]` scans clean and is `invalidBareDocument 1 0` one layer down.  It
named two mechanisms that miss it — §9.2's end-of-input check, which reads
`trailingNodeRun?` and finds a `]` there, and §8.1's floor, which measures the
BRACKET's column that the property run has moved right — and left the remedy as
a choice between giving the accumulation's flow arm the opaque resume and
"closing the hole in the scanner".

**The open is not the hole.**  A flow collection can head an implicit KEY, so a
`[` on the run's own line ends nothing: `a: 1⏎&p [b]: c` PARSES, and so does
`k:⏎␣␣m:⏎␣␣␣␣- a⏎␣␣&p [1]: b`, which `FlowFrameResumeRider` has witnessed since
item 114.  A check fired at the open refuses both — §2 is that measurement.

What was wrong is the READING.  `[161] ns-flow-node` is
`c-ns-properties? ns-flow-content`, and `ns-flow-content` is a flow collection
as readily as a scalar; a collection is simply not ONE token, so a run whose
body is one ends the array in a `]` and the first two arms of
`trailingNodeRun?` report no run at all.  The third arm reads the close back to
its own open (`flowOpenIdx?`) and continues the `[96]` walk-back from there, so
the run it reports starts where the parser reports: at the property.  The
terminator is untouched — the break, or end of input. -/

namespace L4YAML.Tests.Guards.FlowRunDanglingClosed

open L4YAML L4YAML.Scanner L4YAML.Proofs.EmitterScannability

private def posStr : Option YamlPos → String
  | some p => s!"{p.line},{p.col}"
  | none => "none"

private def scanOk (input : String) : String :=
  match scan input with
  | .ok _ => "SCAN-OK"
  | .error e => s!"SCAN-ERR {repr e}"

private def parseOk (input : String) : String :=
  match Events.streamToEvents input with
  | .ok _ => "PARSE-OK"
  | .error e => s!"PARSE-ERR {repr e}"

/-- The state `scanLoop`'s final validations run at: step until
    `scanNextToken` reports end of input. -/
private def finalState (s : ScannerState) : Nat → Option ScannerState
  | 0 => none
  | f + 1 =>
    match scanNextToken s with
    | .ok (some s') => finalState s' f
    | .ok none => some s
    | .error _ => none

/-- The run reading there — the kind of token the run starts with, where it
    sits, and the reading `scanLoop_checkDanglingNode` takes off it. -/
private def endRun (input : String) : String :=
  match finalState ((ScannerState.mk' input).emit .streamStart) 4000 with
  | none => "no-state"
  | some s =>
    match trailingNodeRun? s.tokens with
    | none => "run=none"
    | some (st, _) =>
      let t := s.tokens[st]!
      let k := if t.val.isNodeProperty then "prop"
               else if t.val.isNodeBody then "body"
               else if t.val.isFlowOpen then "open" else "other"
      s!"run={k}@{t.pos.line},{t.pos.col} park={posStr (danglingNodePos? s)}"

/-! ## §1  The family, refused where the parser already refused it

Every witness item 158 listed under "scans clean" is a scanner error now, at the
RUN's start — which is the position the parser had been reporting alone. -/

#guard ["a: 1\n&p [b]\n", "a: 1\n&p {b: 1}\n", "a: 1\n!t [b]\n",
        "- a\n&p [b]\n", "a: 1\n&p !t [b]\n"].map scanOk
  == ["SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"]

#guard ["a: 1\n&p [b]\n", "a: 1\n&p {b: 1}\n", "a: 1\n!t [b]\n",
        "- a\n&p [b]\n", "a: 1\n&p !t [b]\n"].map parseOk
  == ["PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 0"]

-- …at an indented landing and at a dedenting one, both at the run's own column
-- and both where the parser reported.
#guard ["k:\n  a: 1\n  &p [b]\n", "k:\n  a: 1\n&p [b]\n",
        "a: 1\n&p [b]\nc: 2\n"].map scanOk
  == ["SCAN-ERR L4YAML.ScanError.invalidBareDocument 2 2",
      "SCAN-ERR L4YAML.ScanError.invalidBareDocument 2 0",
      "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"]

/-! ## §2  Why the OPEN could not be the trigger

The obvious cheap fix — refuse at a `[`/`{` whose landing already reads a
dangling run — is wrong, and the repo's own guards say so.  A flow collection is
a node like any other, so it can be an implicit KEY, and the `:` that resolves
the run comes AFTER the close.  The reading at the props park is revocable
through a collection exactly as item 141 measured it through a scalar. -/

#guard ["a: 1\n&p [b]: c\n", "k:\n  m:\n    - a\n  &p [1]: b\n",
        "?\n  &p [1]: b\n: - w\n"].map scanOk
  == ["SCAN-OK", "SCAN-OK", "SCAN-OK"]

#guard ["a: 1\n&p [b]: c\n", "k:\n  m:\n    - a\n  &p [1]: b\n",
        "?\n  &p [1]: b\n: - w\n"].map parseOk
  == ["PARSE-OK", "PARSE-OK", "PARSE-OK"]

-- The discriminating pair, at one character of difference: the same park, the
-- same reading, and the `:` after the close is the whole of it.
#guard endRun "a: 1\n&p [b]: c\n" == "run=body@1,8 park=none"
#guard scanOk "a: 1\n&p [b]\n" == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"

/-! ## §3  The legal neighbours the widened reading leaves alone

A run is dangling when its predecessor offers it no slot AND its start names an
open level.  Reading through the close changes which token the START is; it
changes neither condition, so every shape whose collection has a slot or whose
column names no level reads `none` exactly as before. -/

#guard ["[1, 2]\n", "&p [1, 2]\n", "k: &p [1, 2]\n", "k:\n  &p [1, 2]\n",
        "- &p [1, 2]\n", "k: [1, 2]\nm: 3\n", "a:\n- &p [b]\n",
        "[&p [1], {a: 2}]\n", "a: 1\n---\n&p [b]\n"].map scanOk
  == ["SCAN-OK", "SCAN-OK", "SCAN-OK", "SCAN-OK", "SCAN-OK", "SCAN-OK",
      "SCAN-OK", "SCAN-OK", "SCAN-OK"]

-- The run START the third arm reports, on the two sides of the distinction:
-- the collection's own open where nothing decorates it, the property where one
-- does — and the predecessor is what settles the verdict either way.
#guard endRun "k: [1, 2]\nm: 3\n" == "run=body@1,3 park=none"
#guard endRun "&p [1, 2]\n" == "run=prop@0,0 park=none"
#guard endRun "- &p [1, 2]\n" == "run=prop@0,2 park=none"

-- Nesting: the walk counts brackets, so an inner collection does not stop it.
#guard endRun "&p [[1], {a: 2}]\n" == "run=prop@0,0 park=none"
#guard scanOk "a: 1\n&p [[1], {a: 2}]\n"
  == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"

/-! ## §4  What the reading costs the emitter side

`trailingNodeRun?_push_none` used to be free at a flow close — the close was
neither a body nor a property, so the array ended in no run.  It is not free
now, and the two emitter-scannability sites that spent it there
(`scanNextToken_flow_close_seq_outermost` and its mapping twin) pay the indent
stack instead: the emitter's own output stands on the sentinel alone, where no
column can match. -/

example (ts : Array (Positioned YamlToken)) (p : Positioned YamlToken)
    (hb : p.val.isNodeBody = false) (hp : p.val.isNodeProperty = false)
    (hc : p.val.isFlowClose = false)
    (hph : (p.val == YamlToken.placeholder) = false) :
    trailingNodeRun? (ts.push p) = none :=
  trailingNodeRun?_push_none ts p hb hp hc hph

-- The premise the close cannot supply…
example : YamlToken.isFlowClose .flowSequenceEnd = true := rfl
example : YamlToken.isFlowClose .flowMappingEnd = true := rfl
example : YamlToken.isFlowClose .blockEnd = false := rfl
example : YamlToken.isFlowOpen .flowSequenceStart = true := rfl
example : YamlToken.isFlowOpen .flowMappingStart = true := rfl

-- …and what replaces it: at the sentinel alone every column is negative and a
-- token's column is a `Nat`, so no run can be dangling BY COLUMN however it
-- is read — item 180's crossed-block clause reads no column, so its own
-- `none` rides as a second premise.
example (s : ScannerState)
    (h : s.indents = #[{ column := -1, isSequence := false }])
    (hx : crossedPropsExcessIdx? s.tokens = none) :
    scanLoop_checkDanglingNode s = .ok () :=
  scanLoop_checkDanglingNode_ok_of_sentinel_stack s h hx

/-! ## §5  What the next item needs

Item 158 recorded the property lane as three pieces.  This item closed the
third, and by the route that leaves `scannerDrop`'s domain alone (R1 is closed;
re-widening the opaque resume would reopen it).  Two remain, and the first is
still the blocker:

1. a premise shape for `pendingProps.h_route` that relays through a PROPERTY
   push — `danglingNodePos? sc = none` does not, because the run's start moves
   on the third property (`PropsParkDangling` §4), and what does has to see the
   run's two properties as being on different LINES;
2. `pendingBlockContent.h_closable` guarded as `pendingContent.h_closable`
   already is, since the run's ride into an ENTRY parks there.

What the flow arm (`accum_flow_open_depth0`) needed is no longer a decision:
the input it could not pay for is out of the accumulation's domain now, because
a dangling run that rides into a collection is refused at the next break or at
end of input. -/

end L4YAML.Tests.Guards.FlowRunDanglingClosed

end Blanket
