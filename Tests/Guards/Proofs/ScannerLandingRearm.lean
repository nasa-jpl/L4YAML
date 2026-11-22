module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The landing's own re-arm reaches the accumulator (DOCS item 76)

Item 74 measured the `:`'s floor and found the premise is not about the
indicator at all: `scanValuePrepare` pushes at the column of the key it
RESOLVES, so what a producer has to know is whether preprocessing re-SAVED.
Outside a flow `saveSimpleKey` declines for exactly one reason — the flag is
down — so a park that carries `simpleKeyAllowed` knows the answer, and the four
parks that do not carried `True` instead.

Item 76 gives those parks the OTHER funder.  `skipToContentLoop` re-arms the
flag on every break outside a flow (§7.4.2 suppresses it inside one), so a park
that is not at a line start reaches a column-0 landing only across a break, and
the walk itself says the save is fresh.  That fact now rides the landed arm of
`preprocess_some_ssl_comments_anyCol` / `_landing`, is spent by
`landing_save_or`, and lands on `indicator_floor_colon_at_col_of_save`.

The examples below are the compile-time witnesses of the two funders: the same
`IndentFloor`, with no `∨ True`, from the park's flag (item 74) and from the
landing's break (item 76).  They are `example`s over hypotheses rather than
`#guard`s because item 76 edits no runtime file — §3's inputs are pinned so a
later runtime change cannot move them silently, and §4 pins the MEASUREMENT the
remaining half is owed.
-/

namespace Tests.Guards.ScannerLandingRearm

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.PreprocessIndentStable

/-! ## §1  The landing's break funds the floor

The landed arm's payload is `sp_scan.col ≠ 0 → s_prep.inFlow = false → …`: a
park off a line start, outside a flow, reached a column-0 landing, so the walk
crossed a break and re-armed.  Nothing about the PARK's own flag is used. -/

example {sc s_prep s' : ScannerState} {sp_prep sp_scan : SurfPos} {k : Nat}
    (hcol_prep : sp_prep.col = k)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (h_noflow_disp : (if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep).inFlow = false)
    (h_noflow : s_prep.inFlow = false)
    (h_col : sp_scan.col ≠ 0)
    (h_arm : sp_scan.col ≠ 0 → s_prep.inFlow = false →
      s_prep.simpleKey.possible = true ∧ s_prep.simpleKey.pos.col = s_prep.col)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, ':')))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) ':' = .ok (some s')) :
    -- Item 179: at the SHIFTED index.
    IndentFloor s' (k + 1) :=
  indicator_floor_colon_at_col_of_save hcol_prep hcorr_prep h_noflow_disp
    (h_arm h_col h_noflow).2 h_preprocess h_dispatch

/-! ## §2  …and the park's own flag funds the same one

Item 74's route, unchanged: the flag rides the walk (`skipToContent` only ever
raises it), so a park that scanned `-`/`?`/`:` measures without a landing. -/

example {sc s_prep s' : ScannerState} {sp_prep : SurfPos} {k : Nat}
    (hcol_prep : sp_prep.col = k)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (h_noflow_disp : (if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep).inFlow = false)
    (h_sk : sc.simpleKeyAllowed = true)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, ':')))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) ':' = .ok (some s')) :
    -- Item 179: at the SHIFTED index.
    IndentFloor s' (k + 1) :=
  indicator_floor_colon_at_col hcol_prep hcorr_prep h_noflow_disp h_sk
    h_preprocess h_dispatch

/-! ## §3  The inputs the two funders cover, held fixed

`a: b⏎: w` and `k:⏎  a: b⏎  : w` are the mid-line parks §1 serves — the `:`
lands at column 0 from a park inside the previous entry's value; `: v` and
`# c⏎: v` are the line-start park `noPending` now carries a flag for; `? a⏎: v`
and `? a⏎: - w` are the explicit VALUE line, which measures on the same
datum. -/

private def bothEvents (input : String) : Option String × Option String :=
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  bothEvents input == (e, e)

#guard emits "a: b\n: w\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "=VAL :", "=VAL :w", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  a: b\n  : w\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :b", "=VAL :", "=VAL :w",
   "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits ": v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "# c\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "? a\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "? a\n: - w\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]

/-! ## §4  The half item 76 does NOT fund, measured

A park AT a line start crosses no break, so §1's payload is vacuous there and
the datum has to be the park's own flag.  `noPending` now carries one; the two
CONTENT parks do not, and what stands in the way is a column: `[170]`'s block
scalar is the one content scan that parks at column 0, and it re-arms
(`scanBlockScalar` ends `simpleKeyAllowed := true`), while the plain and quoted
walks leave the flag down and — measured, not proven — never park there.

The predicate below is that measurement, machine-checked on the shapes that
reach column 0: no block-context park sits at a line start with the save down. -/

private def parkOk (s : ScannerState) : Bool :=
  !(s.col == 0 && !s.simpleKeyAllowed && s.flowLevel == 0)

private def parksArmedLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    match scanNextToken s with
    | .error _ => true
    | .ok none => true
    | .ok (some s') => parkOk s' && parksArmedLoop s' fuel'

/-- Every park the scan reaches is either off a line start, armed, or in a flow. -/
private def parksArmed (input : String) : Bool :=
  parksArmedLoop ((ScannerState.mk' input).emit .streamStart) (input.utf8ByteSize + 1)

private def col0ParkSeenLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match scanNextToken s with
    | .error _ => false
    | .ok none => false
    | .ok (some s') =>
      (s'.col == 0 && s'.flowLevel == 0) || col0ParkSeenLoop s' fuel'

/-- …and the block-context line-start park is REACHED, so `parksArmed` above is
    not vacuous on the shape it is there to measure. -/
private def col0ParkSeen (input : String) : Bool :=
  col0ParkSeenLoop ((ScannerState.mk' input).emit .streamStart) (input.utf8ByteSize + 1)

-- The block scalar, which DOES park at column 0 (and re-arms there).
#guard col0ParkSeen "a: |\n  x\nd: 1\n"
#guard parksArmed "a: |\n  x\nd: 1\n"
#guard parksArmed "a: |\n  x\n: 1\n"
#guard parksArmed "a: >\n  x\n- 1\n"
-- The plain and quoted walks, which stop before the break.
#guard parksArmed "a: b\n  c\nd: 1\n"
#guard parksArmed "a\nb\n---\nc\n"
#guard parksArmed "\"a\"\n: 1\n"
#guard parksArmed "a: b\n...\n"
-- …and the flow parks, where the disjunct is the flow level itself.
#guard parksArmed "[1, 2]\n"
#guard parksArmed "{a: b}\n"

end Tests.Guards.ScannerLandingRearm

end Blanket
