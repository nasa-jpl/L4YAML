module

public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx
public meta import L4YAML.Output.EventsIx
public import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch

public meta import L4YAML.Scanner.IndexedDispatch
public meta import L4YAML.Token.Token
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # A `:` with a `[96] c-ns-properties` run held before it (DOCS item 9o)

Item 9n split the `:` step by the frame TAIL.  This file is about the SECOND
index on the same step — the interior gap, which is either empty or holds a
scanned-but-unattached property run — and about what crossing the two indices
does to the pricing (Reflection 629).

The property run turns out to decorate the entry's KEY, whose content is empty:

    [161] ns-flow-node(n,c) ::= c-ns-alias-node
                              | ns-flow-content(n,c)
                              | ( c-ns-properties(n,c)
                                  ( ( s-separate(n,c) ns-flow-content(n,c) )
                                  | e-scalar ) )

so `[&a : b]` is `SFlowSeqEntry.pairValue` with `SFlowNode.propsEmpty` as its
key — the same node `receivePropsEmpty` builds when a `,` or a close decides the
run, one dispatch later.  §1 and §2 pin those shapes on the two tail classes that
are TOTAL there (`.sep` and `.question`), which is what
`FlowOpenStack.receiveColonPropsSep` / `.receiveColonPropsQuestion` construct.

§3 is the crossing's payoff.  `InteriorGap.props` carries `tl ≠ .value` as a
*field*, so the props × `.value` cell is not a case anybody has to write — it is
not a state.  The shapes that would reach it are rejected by item 9b's
`scanNextToken_checkFlowAdjacency`, which shipped nine items earlier: a property
may not stand directly after a completed flow value.  On the white row the same
tail is the MIXED class, the one cell nothing closes for free.

§4 pins the T833 strictening (DOCS items 9r + 11): a `:` at an
already-complete entry is rejected at BOTH scanners with the identical
`ScanError`.  The section pinned each intermediate state on the way — first the
parser-only rejection, then the legacy-only scanner rejection — so each landing
was measured against recorded behaviour rather than against a diff.
-/

namespace Tests.Guards.ScannerFlowPropsColon

open L4YAML
open L4YAML.Events
open L4YAML.Scanner

/-- Legacy and indexed event streams as a comparable pair; `none` on rejection.
    Equal pairs mean the two pipelines agree. -/
private def bothEvents (input : String) : Option String × Option String :=
  ( (match streamToEvents input with | .ok s => some s | .error _ => none)
  , (match streamToEventsIx input with | .ok s => some s | .error _ => none) )

/-- Both pipelines accept `input` and emit exactly `expected`. -/
private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  bothEvents input == (e, e)

/-- Legacy and indexed SCANNER verdicts as a comparable pair. -/
private def scanVerdicts (input : String) : Option ScanError × Option ScanError :=
  ( (match scan input with | .ok _ => none | .error e => some e)
  , (match Indexed.ScannerStateIx.scanIx input with | .ok _ => none | .error e => some e) )

/-- Both pipelines reject `input` in the SCANNER, with the same error. -/
private def rejectsInScanner (input : String) (e : ScanError) : Bool :=
  scanVerdicts input == (some e, some e)

/-- Both pipelines SCAN `input` clean but reject it downstream (no events).
    The shape of a gap that only the parser closes. -/
private def scansCleanButRejected (input : String) : Bool :=
  scanVerdicts input == (none, none) && bothEvents input == (none, none)

/-! ## §1  The `.sep` tail with a run held — `receiveColonPropsSep`

`betweenEmpty` (right after the bracket) and `betweenHeld` (right after a `,`)
are the only two frames that index admits, and a properties-only key is an
`ns-flow-node` after both. -/

-- `[&a : b]` — the anchor is on the entry's KEY, not on the entry.
#guard emits "[&a : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL &a :", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]

-- …with an empty value too (`[148]`'s `e-node` branch).
#guard emits "[&a :]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL &a :", "=VAL :", "-MAP",
   "-SEQ", "-DOC", "-STR"]

-- The tag half of `[96]` alone.
#guard emits "[!t : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL <!t> :", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]

-- Both halves, in either order — `PropsRun`'s `anchorThenTag` / `tagThenAnchor`.
#guard emits "[&a !t : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL &a <!t> :", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]

#guard emits "[!t &a : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL &a <!t> :", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]

-- The `betweenHeld` frame: the run opens the entry AFTER a `,`.
#guard emits "[a, &x : b]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :a", "+MAP {}", "=VAL &x :", "=VAL :b",
   "-MAP", "-SEQ", "-DOC", "-STR"]

#guard emits "[&a : b, &c : d]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL &a :", "=VAL :b", "-MAP",
   "+MAP {}", "=VAL &c :", "=VAL :d", "-MAP", "-SEQ", "-DOC", "-STR"]

-- The mapping twin of both frames.
#guard emits "{&a : b}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL &a :", "=VAL :b", "-MAP", "-DOC", "-STR"]

#guard emits "{!t : b}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL <!t> :", "=VAL :b", "-MAP", "-DOC", "-STR"]

#guard emits "{a: b, &c : d}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :a", "=VAL :b", "=VAL &c :", "=VAL :d",
   "-MAP", "-DOC", "-STR"]

/-! ## §2  The `.question` tail with a run held — `receiveColonPropsQuestion`

Here the run decorates the EXPLICIT key, so the frame lands in
`midExplicitColon` rather than `midQuestionEmptyColon`: `? &a :` is the `? `
shape whose key is a real `ns-flow-node` after all, just an empty one. -/

#guard emits "[? &a : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL &a :", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]

#guard emits "[? !t : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL <!t> :", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]

#guard emits "[? &a :]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL &a :", "=VAL :", "-MAP",
   "-SEQ", "-DOC", "-STR"]

#guard emits "{? &a : b}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL &a :", "=VAL :b", "-MAP", "-DOC", "-STR"]

/-! ## §3  The props × `.value` cell is NOT A STATE (item 9b, item 9o)

A property run may not stand directly after a completed flow value, so the cell
that is MIXED on the white row is empty on this one.  `InteriorGap.props` records
that as its `tl ≠ .value` field; the scanner records it as `invalidFlowEntry`,
one dispatcher before block-indicator dispatch is even reached. -/

#guard rejectsInScanner "[\"a\" &x : b]\n" (.invalidFlowEntry 0 5)
#guard rejectsInScanner "[\"a\" !t : b]\n" (.invalidFlowEntry 0 5)
#guard rejectsInScanner "[[a] &x : b]\n" (.invalidFlowEntry 0 5)
#guard rejectsInScanner "[[a] !t : b]\n" (.invalidFlowEntry 0 5)
#guard rejectsInScanner "[{a: b} &x : c]\n" (.invalidFlowEntry 0 8)

/-! ## §4  A SECOND `:` in one entry — rejected at BOTH scanners (item 9r,
Ix landing: DOCS item 11)

Three cells, one obligation, discharged on BOTH sides: the
`scanValueValidate` / `scanValueValidateIx` strictening rejects all seven
shapes at the SCANNER, because the pending simple key it reads was reserved at
the `:` itself when the gap is empty and BEFORE the run when it is not, and the
slot below that reservation is a `.value` exactly in the illegal shapes.

The legacy landing (item 9r) deliberately deferred the indexed twin — this
section pinned the divergence (legacy scanner rejects, indexed scanner scans
clean, parser refuses) until the Ix saved-key substrate landed: the five
scenario-lemma layout exposures, the conditional layout conjunct on
`EmitScansInFlowIx`, and the four assembler call sites (DOCS item 11).  With
that in, the guards below assert BOTH scanners reject with the IDENTICAL
`ScanError`, same as §1–§3. -/

-- White row, `.colon` cell.
#guard rejectsInScanner "[a: : b]\n" (.invalidFlowEntry 0 4)
#guard rejectsInScanner "[: :]\n" (.invalidFlowEntry 0 3)
#guard rejectsInScanner "{a: : b}\n" (.invalidFlowEntry 0 4)
#guard rejectsInScanner "[? : : a]\n" (.invalidFlowEntry 0 5)

-- White row, `.value` cell (the mixed one): the entry is already complete.
#guard rejectsInScanner "[a: b: c]\n" (.invalidFlowEntry 0 5)

-- Props row, `.colon` cell: the run sits between the two `:`s and changes
-- nothing, because the reservation slot is older than the run.
#guard rejectsInScanner "[a: &x : b]\n" (.invalidFlowEntry 0 7)
#guard rejectsInScanner "[a: !t : b]\n" (.invalidFlowEntry 0 7)

/-! ## §5  The run's other decisions, unchanged

`receivePropsEmpty`'s own shapes, re-pinned so that adding a `:` exit from a
held run is visible as additive. -/

#guard emits "[&a]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL &a :", "-SEQ", "-DOC", "-STR"]

#guard emits "[&a, b]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL &a :", "=VAL :b", "-SEQ", "-DOC", "-STR"]

-- …and `receivePropsContent`'s: the run decorates the node that follows.
#guard emits "[&a b]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL &a :b", "-SEQ", "-DOC", "-STR"]

end Tests.Guards.ScannerFlowPropsColon

end Blanket
