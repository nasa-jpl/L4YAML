module

public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
public meta import L4YAML.Scanner.State
public meta import L4YAML.Scanner.TokenQueries
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # A flow open below the pending's index is refused at the gate (DOCS items 66, 172)

Item 46 left one deferral at the depth-0 flow open: the landing that under-runs
`s-indent(n)` on the OPEN itself, which no `[70] s-separate-lines(n)` derives.
Item 66 refused it at the open; item 172 moved §8.1's floor to the CLOSE
(a flow open at a level's column may be the level's next implicit KEY, so
key-vs-value is only decidable there), and the under-run family now refuses at
the break/EOF gate, by whichever of the two gate readings owns the landing:

* §1 **at a level whose slot still OFFERS a node** — the `-`'s own column, a
  props park's floor, the root value slot — the deferred floor refuses as
  `underIndentedFlowContent` at the OPEN's position: the collection stood in
  the awaited slot and no `:` resolved it (`underIndentedFlowValuePos?`,
  `[96]`-transparent through the run in front of the open).
* §1' **where the landing DEDENTS past the awaiting level**, preprocessing's
  unwind closes it (`blockEnd`), the slot holder no longer offers, and the
  same landing is §9.2's dangling node — `invalidBareDocument` at the open's
  position, the constructor the scalar twin gets.
* §2 **the landing that matches no open level never gets that far**:
  preprocessing's own trailing-content check refuses it while unwinding.  So
  the readings together cover every column below the index.
* §3 **the TAB half is §6.1's** (item 64's `LandingTabFacts`): a tab in the
  landing's indent run is `tabInIndentation`, at every column at or left of
  the floor. -/

namespace L4YAML.Tests.Guards.ScannerFlowOpenUnderRun

open L4YAML

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def errAt (input : String) : Option (Nat × Nat) :=
  match Events.streamToEvents input with
  | .error (.underIndentedFlowContent l c) => some (l, c)
  | _ => none

private def bareAt (input : String) : Option (Nat × Nat) :=
  match Events.streamToEvents input with
  | .error (.invalidBareDocument l c) => some (l, c)
  | _ => none

private def trailingAt (input : String) : Option (Nat × Nat) :=
  match Events.streamToEvents input with
  | .error (.trailingContent l c) => some (l, c)
  | _ => none

-- §1/§1'/§2 A SEQUENCE entry pending at index 2 (`k:⏎  -`).  Every column
-- below the index is refused, and the refusals alternate with the levels:
-- 0 dedents past the sequence (§1', the unwind's `blockEnd` de-offers the
-- slot), 1 lands between two levels (§2), 2 is the sequence's own — the
-- offered slot, the deferred floor's reading at the open's position (§1).
#guard bareAt "k:\n  -\n[1]\n" == some (2, 0)
#guard trailingAt "k:\n  -\n [1]\n" == some (2, 1)
#guard errAt "k:\n  -\n  [1]\n" == some (2, 2)
#guard emits "k:\n  -\n   [1]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+SEQ []", "=VAL :1", "-SEQ",
   "-SEQ", "-MAP", "-DOC", "-STR"]

-- …and one level deeper, where the alternation runs four columns: 0 and 2
-- dedent past the sequence (§1'), 1 and 3 land between levels (§2), 4 is the
-- sequence's own offered slot (§1).
#guard bareAt "a:\n  b:\n    -\n[1]\n" == some (3, 0)
#guard trailingAt "a:\n  b:\n    -\n [1]\n" == some (3, 1)
#guard bareAt "a:\n  b:\n    -\n  [1]\n" == some (3, 2)
#guard trailingAt "a:\n  b:\n    -\n   [1]\n" == some (3, 3)
#guard errAt "a:\n  b:\n    -\n    [1]\n" == some (3, 4)
#guard refuses "a:\n  b:\n    -\n[1]\n"

-- The same for a mapping VALUE pending (`k:⏎  a:`) and for a held property
-- run (`k:⏎  b:⏎    &x`) — the other two parks that open the stack at their
-- own index.  The dedent past the value's level is §1'; the props park met at
-- the enclosing level is §1, the run read `[96]`-transparently to the offer.
#guard bareAt "k:\n  a:\n[1]\n" == some (2, 0)
#guard trailingAt "k:\n  a:\n [1]\n" == some (2, 1)
#guard errAt "k:\n  b:\n    &x\n  [1]\n" == some (3, 2)

-- §1's boundary at the root, where the floor is the document's own: a `[` at
-- column 0 in the root value slot is refused at the gate, one column past it
-- reads.  (The KEY half of the same landing — `k:⏎[1]: b` — is the sibling
-- entry now; `StreamFlipRemainderMap` §5 pins it.)
#guard errAt "k:\n[1]\n" == some (1, 0)
#guard emits "k:\n [1]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ []", "=VAL :1", "-SEQ", "-MAP",
   "-DOC", "-STR"]

-- §3 The TAB half, at every column the floor admits.
#guard refuses "k:\n  -\n\t[1]\n"
#guard refuses "k:\n  -\n \t[1]\n"
#guard refuses "k:\n  a:\n\t[1]\n"
#guard refuses "a:\n  b:\n    -\n  \t[1]\n"


/-! ## §4 The same family SWEPT, and the branch it prices (DOCS item 264)

The columns above are hand-typed, and a hand-typed knob chooses the answer (§9).
This section walks the landing column instead and lets the machine name the
**turnover** — the least column the scanner accepts — at every combination of
three enclosing contexts, four park kinds, both flow-open characters and four
park indents.

**Why it is worth sweeping a family already pinned.**  `accum_flow_open_depth0`
spends β.5's `dropClose` at exactly one place, `have drop_ride`, and three LIVE
arms take it — `pendingProps`, `pendingBlock` and `pendingMapValue`, one each,
all on the run-end half of this under-run:

    rcases h_ur with ⟨j, sx, hj, h_ind, _h_ws2, h_end | h_tab⟩
    · exact drop_ride                              -- §4's subject
    · exact (flowOpen_underRunTab_refuted …).elim  -- §3's half, already REFUTED

So this family is not an audit of the scanner — it is the price of the one
library proof β.5 breaks that is neither a dead branch nor the escape.  The
source says of those three rides that "no accepted scan ever consults" them; §4
is that sentence measured instead of asserted, and what it measures is that the
run-end half is refutable exactly where the tab half already is.

**The props park is why a sweep was needed and not another column.**  Its
turnover does not track its own column: an anchor at column 3 takes a flow open
at column 1.  `pendingProps.h_floor : IndentFloor sc n` carries the floor of the
context the run stands IN, not the anchor's, so the boundary sits at 1 from
indent 1 rightwards — and a grid varying only the park's own column would have
read that as an under-run being accepted. -/

private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok a, .ok b => a == b
  | _, _ => false

private def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- A park of the given kind at indent `p`, a break, then `q` spaces and a
    depth-0 flow open.  `outer` supplies the indent when `p` is nonzero, and it
    is varied because a boundary that moved with the enclosing construct would
    be a fact about that construct rather than about the floor. -/
private def mk (outer kind : String) (p q : Nat) (op : String) : String :=
  let pre := match outer, p with
    | _, 0 => ""
    | "map", _ => "w:\n"
    | "seq", _ => "-\n"
    | _, _ => "? w\n: v\nz:\n"
  let body := match kind with
    | "mapValue" => spaces p ++ "k:"
    | "block" => spaces p ++ "-"
    | "qmark" => spaces p ++ "?"
    | _ => spaces p ++ "&a"
  pre ++ body ++ "\n" ++ spaces q ++ op ++ "\n"

private def outers : List String := ["map", "seq", "doc"]
private def kinds : List String := ["mapValue", "block", "qmark", "props"]
private def opens : List String := ["[1]", "{a: b}"]
private def indents : List Nat := [0, 1, 2, 3]
private def columns : List Nat := [0, 1, 2, 3, 4, 5]

/-- **The park's floor, as a model of this grid.**  Three of the four kinds ARE
    the level they stand at, so their floor is one past their own column.  The
    props run is not: it carries the floor of the context it stands in, which
    this grid nests at 1.  Pinning the turnover against a MODEL rather than
    against a list of numbers is what makes the reading a law — and a wrong
    model fails the census rather than sliding it. -/
private def floorOf (kind : String) (p : Nat) : Nat :=
  if kind == "props" then min p 1 else p + 1

/-- One walk of the grid: `(cells, rows with a single boundary, turnover = the
    floor, accepted BELOW the floor, accepted AT the floor)`.

    The third and fourth are the same reading taken two ways, so neither can
    pass vacuously: the fourth counts accepted cells left of the floor directly
    and must be **zero**, and the fifth counts the floor cells themselves and
    must be all of them — a zero over a grid that never reached the boundary
    would be a coverage report (§9). -/
private def sweep : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut cells := 0
  let mut clean := 0
  let mut atFloorTurn := 0
  let mut belowOk := 0
  let mut atFloorOk := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          cells := cells + 1
          let n := floorOf kind p
          let row := columns.map (fun q => accepts (mk outer kind p q op))
          -- monotone in `q` with ONE boundary: a row that accepts, refuses and
          -- accepts again has no turnover to speak of.
          if !((row.dropWhile (· == false)).any (· == false)) then
            clean := clean + 1
          if (columns.zip row |>.filter (·.2) |>.map (·.1)).head? == some n then
            atFloorTurn := atFloorTurn + 1
          for (q, ok) in columns.zip row do
            if ok && q < n then belowOk := belowOk + 1
            if ok && q == n then atFloorOk := atFloorOk + 1
  return (cells, clean, atFloorTurn, belowOk, atFloorOk)

/- **Ninety-six cells, every one with a single boundary, and the boundary is
    the floor.**  No accepted scan in the grid lands a depth-0 flow open
    strictly left of the park's floor — which is the branch `drop_ride` is
    spent on — and all ninety-six floor cells are accepted, so the grid
    straddles the boundary rather than sitting to one side of it. -/
#guard sweep == (96, 96, 96, 0, 96)

/- The props cell the hand-typed columns above do not reach: the anchor stands
    at column 3 and the open it takes is at column 1, two columns to its LEFT
    and accepted, because the floor the park carries is the enclosing
    mapping's. -/
#guard emits (mk "map" "props" 3 1 "[1]")
  ["+STR", "+DOC", "+MAP", "=VAL :w", "+SEQ [] &a", "=VAL :1", "-SEQ", "-MAP",
   "-DOC", "-STR"]

/- …and one column further left is the under-run, refused at the EOF gate —
    the "deferred floor" reading, §1's. -/
#guard errAt (mk "map" "props" 3 0 "[1]") == some (2, 0)



/-! ## §5 Where each refusal actually happens, and what that costs (DOCS item 265)

§4 measured that no accepted scan lands the open below the park's floor.  That
is a statement about the SCANNER; the proof obligation it was measured for is
`accum_flow_open_depth0`'s, and there the question is sharper: *is the refusal
available at the step the arm is proving?*  A branch the runtime refuses five
steps downstream is still a branch the step lemma has to build.

So this section walks the same grid one reading further in.  For every landing
column strictly below the park's floor it drives `scanNextToken` itself and
records two things: whether the flow OPEN is ever dispatched, and — when it is
— how far past that dispatch the scan dies and at which gate.

What it reads splits the family in two, and only one part is the arm's to
refute:

* **54 columns never reach the lemma.**  `scanNextToken_preprocess` refuses
  them while unwinding, so `h_preprocess : … = .ok (some (s_prep, c))` is
  already a contradiction and no arm is entered.
* **144 columns dispatch the open** and die three or five steps later, at one
  of the two gates that guard a landing: §8.1's floor read on a closed
  collection (90) and §9.2's dangling run (54).  Both gates also run at the
  open's own step — on a state where the collection is not yet closed, so both
  say `.ok` there.  `h_dn` and `h_bare` are those readings AT THE OPEN, which
  is why carrying them buys nothing here: they are the right checks at the
  wrong state.

`deathShape` then reads what the gate is looking at when it fires, because that
is the fact a carrier would have to deliver from the open: at every one of the
144 the collection has closed, the last real token is its flow close, and the
open's column is still on the indent stack.  One carried fact, not two — the
two gates partition the 144 by `offersNodeSlot` alone, with no overlap and no
remainder. -/

private def start (input : String) : Scanner.ScannerState :=
  let s := Scanner.ScannerState.mk' input
  let s := s.emit .streamStart
  match s.peek? with
  | some '﻿' => s.consumeBOM
  | _ => s

/-- `(open dispatched?, steps from the open to the death, the gate that fired)`
    for one input, driving `scanNextToken` directly. -/
private def walk (input : String) : Bool × Nat × String := Id.run do
  let mut s := start input
  let mut i : Nat := 0
  let mut openStep : Option Nat := none
  let mut fuel := input.utf8ByteSize * 4 + 8
  while fuel > 0 do
    fuel := fuel - 1
    let d := i - openStep.getD i
    match Scanner.scanNextToken s with
    | .error _ =>
      -- inside the step: preprocessing is the only gate that can refuse
      -- before the open is dispatched
      match Scanner.scanNextToken_preprocess s with
      | .error _ => return (openStep.isSome, d, "step:preprocess")
      | _ => return (openStep.isSome, d, "step:later")
    | .ok none =>
      if s.flowLevel > 0 then return (openStep.isSome, d, "eof:unterminated")
      match Scanner.scanLoop_checkDanglingNode s with
      | .error _ => return (openStep.isSome, d, "eof:dangling")
      | .ok _ =>
        match Scanner.scanLoop_checkFlowValueIndent s with
        | .error _ => return (openStep.isSome, d, "eof:floor")
        | .ok _ => return (openStep.isSome, d, "ACCEPT")
    | .ok (some s') =>
      if s.flowLevel == 0 && s'.flowLevel == 1 && openStep.isNone then
        openStep := some i
      s := s'
      i := i + 1
  return (openStep.isSome, 0, "FUEL")

/-- `(columns below a floor, never dispatched, of those refused by
    PREPROCESSING, dispatched, dispatched dying at §8.1's floor, dispatched
    dying at §9.2's dangling run)`.

    The second and third are the same count taken two ways: a column that
    never dispatches the open must be refused by the one gate that runs before
    the dispatch, and if it were refused anywhere else the arm's
    `h_preprocess` would not reach it. -/
private def dispatchSweep : Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut cols := 0
  let mut nd := 0
  let mut ndPre := 0
  let mut disp := 0
  let mut floorDeaths := 0
  let mut danglingDeaths := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            cols := cols + 1
            let (d, _, w) := walk (mk outer kind p q op)
            if d then
              disp := disp + 1
              if w == "eof:floor" then floorDeaths := floorDeaths + 1
              if w == "eof:dangling" then danglingDeaths := danglingDeaths + 1
            else
              nd := nd + 1
              if w == "step:preprocess" then ndPre := ndPre + 1
  return (cols, nd, ndPre, disp, floorDeaths, danglingDeaths)

#guard dispatchSweep == (198, 54, 54, 144, 90, 54)

/-- The distinct distances, in scanner steps, from the open's dispatch to the
    death.  Neither is zero, which is the whole finding: there is no column at
    which the open's OWN step refuses. -/
private def distances : List Nat := Id.run do
  let mut ds : List Nat := []
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            let (d, n, _) := walk (mk outer kind p q op)
            if d && !ds.contains n then ds := ds ++ [n]
  return ds.mergeSort (· ≤ ·)

#guard distances == [3, 5]

/-- The state the gate is reading when it fires, over the 144 that dispatch:
    `(rows, collection closed, last real token is its flow close, the open's
    column still on the indent stack, exactly one of the two readings fires)`.
    All five must agree, and the fifth is what says the two gates partition
    the family rather than merely covering it. -/
private def deathState (input : String) : Option Scanner.ScannerState := Id.run do
  let mut s := start input
  let mut fuel := input.utf8ByteSize * 4 + 8
  while fuel > 0 do
    fuel := fuel - 1
    match Scanner.scanNextToken s with
    | .error _ => return some s
    | .ok none => return some s
    | .ok (some s') => s := s'
  return none

private def deathShape : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut closed := 0
  let mut lastClose := 0
  let mut colIn := 0
  let mut oneReading := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            let inp := mk outer kind p q op
            let (d, _, _) := walk inp
            if !d then continue
            match deathState inp with
            | none => pure ()
            | some s =>
              rows := rows + 1
              if s.flowLevel == 0 then closed := closed + 1
              match Scanner.prevRealIdx? s.tokens s.tokens.size with
              | some i => if s.tokens[i]!.val.isFlowClose then lastClose := lastClose + 1
              | none => pure ()
              if s.indents.any (fun e => e.column == (q : Int)) then colIn := colIn + 1
              let uf := (Scanner.underIndentedFlowValuePos? s).isSome
              let dn := (Scanner.danglingNodePos? s).isSome
              if (uf && !dn) || (!uf && dn) then oneReading := oneReading + 1
  return (rows, closed, lastClose, colIn, oneReading)

#guard deathShape == (144, 144, 144, 144, 144)

/-- **The grid ends at the open, and that is itself a knob** (§9).  With a
    sibling line after the open's, the same columns refuse in the same two
    classes and nothing is accepted that was not accepted before.
    `(columns, accepted, never dispatched, dispatched, deaths at a MID-STREAM
    gate)`.

    The fifth count is what makes this a second reading rather than a copy of
    `dispatchSweep`: without the sibling line every death is at an end-of-input
    gate and it reads zero, so a pin that omitted it would hold whether or not
    a tail was ever appended. -/
private def tailSweep : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut cols := 0
  let mut acc := 0
  let mut nd := 0
  let mut disp := 0
  let mut mid := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            cols := cols + 1
            let (d, _, w) := walk (mk outer kind p q op ++ "zz: 9\n")
            if w == "ACCEPT" then acc := acc + 1
            if w == "step:later" then mid := mid + 1
            if d then disp := disp + 1 else nd := nd + 1
  return (cols, acc, nd, disp, mid)

#guard tailSweep == (198, 0, 54, 144, 144)


/-! ## §6 What the carrier costs, and who pays it (DOCS item 266)

§5 showed the run-end half is FALSE and not LOCALLY false: the gates that kill
the input run three to five steps past the open, so no hypothesis of
`accum_flow_open_depth0` can refute the branch and what it costs is a CARRIER.
§10 prices a missing carrier by the PRODUCERS it touches, and this section is
the half of that price the runtime decides.  The other half —
`passenger=7 heavy=7 prop=8 consumer=1 gate=1`, pinned below — is
`lake run price -- carrier`.

**The transport already exists.**  `ParkAnchor sc0 s d` runs a fact from a
depth-0 flow OPEN to its CLOSE and is spent there by `ParkAnchor.dangling_eq`,
whose premises are §5's `deathShape` component for component: prefix agreement,
`s_cl.indents = s_bc.indents`, `s_cl.inFlow = false`, the last real token at the
base open's index, and that token a flow close.  So the question is not what to
build but what the existing transport refuses to carry.

Three readings answer it.

* **The park is forced.**  `carrierCore` evaluates the anchor's four transport
  fields at the death state against each candidate park.  Against
  preprocessing's state all four hold at all 144; against the state the step
  began from the hold NEVER resolves, because preprocessing's own pushes sit
  between the two arrays.  There is one park, and it is not the one the
  existing anchor uses.
* **At that park the carrier is a PASSENGER.**  `carrierPark`: preprocessing's
  cursor column IS the open's column, at all 144 — so "the open's column stands
  on the indent stack" is a fact about the park ALONE, with no reference to the
  state it is transported to, and every transport lemma carries it for free.
  At the other park the same membership holds but the column is not the park's,
  which is the difference between a passenger and a premise.
* **What blocks the existing anchor is one field.**  `anchorProp`: `parkProp`
  ("the park's last real token is a node property") holds at 18 of the 144, and
  it is a pure passenger in every transport lemma — read by the genesis and by
  the spend, by nothing in between.

And `preLaw` names the carrier's source.  Over all 198 columns, preprocessing
accepts a landing out of flow exactly when its column stands on the indent
stack: the 54 it refuses are the 54 whose column stands nowhere, and the 144 it
accepts all have it.  The datum is preprocessing's own law, one production over
from `FlowIndentStable.preprocess_indents_of_inFlow` — not a field threaded
through the pending-state invariant. -/

private def openTriple (input : String) :
    Option (Scanner.ScannerState × Scanner.ScannerState × Scanner.ScannerState) := Id.run do
  let mut s := start input
  let mut fuel := input.utf8ByteSize * 4 + 8
  while fuel > 0 do
    fuel := fuel - 1
    match Scanner.scanNextToken s with
    | .error _ => return none
    | .ok none => return none
    | .ok (some s') =>
      if s.flowLevel == 0 && s'.flowLevel == 1 then
        match Scanner.scanNextToken_preprocess s with
        | .ok (some (sp, _)) => return some (s, sp, s')
        | _ => return none
      s := s'
  return none

/-- The column of the bracket the open pushed, read back off the array. -/
private def openColOf (s' : Scanner.ScannerState) : Option Nat :=
  match Scanner.prevRealIdx? s'.tokens s'.tokens.size with
  | some i => if s'.tokens[i]!.val.isFlowOpen then some s'.tokens[i]!.pos.col else none
  | none => none

private def hasCol (s : Scanner.ScannerState) (c : Nat) : Bool :=
  s.indents.any (fun e => e.column == (c : Int))

/-- `(rows, the open's column is the STEP state's cursor column, it stands on
    that state's indent stack, it is PREPROCESSING's cursor column, it stands on
    preprocessing's stack)`.

    The second must be zero and the fourth all of them: that is what says the
    carrier is a passenger at one park and not at the other, rather than a
    membership fact that happens to hold at both. -/
private def carrierPark : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut scCol := 0
  let mut scMem := 0
  let mut spCol := 0
  let mut spMem := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            match openTriple (mk outer kind p q op) with
            | none => pure ()
            | some (sc, sp, s') =>
              match openColOf s' with
              | none => pure ()
              | some c =>
                rows := rows + 1
                if sc.col == c then scCol := scCol + 1
                if hasCol sc c then scMem := scMem + 1
                if sp.col == c then spCol := spCol + 1
                if hasCol sp c then spMem := spMem + 1
  return (rows, scCol, scMem, spCol, spMem)

#guard carrierPark == (144, 0, 144, 144, 144)

/-- `ParkAnchor`'s four transport fields at the death state, against BOTH
    candidate parks: `(rows, below, held, ind, parkFlow — all at preprocessing's
    state; the rows where `parkProp` holds THERE too; then held and ind at the
    step's state)`.

    The last two are the discrimination: an anchor parked where the existing one
    parks never holds its open, so the park is forced by the runtime and not
    chosen.  A sixth count for "all four at once" would read 144 whatever the
    scanner did, since each of the four already does — so the sixth is the
    overlap with the EXISTING anchor instead, which is the only reading of this
    family that is not implied by the five beside it. -/
private def carrierCore : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut below := 0
  let mut held := 0
  let mut ind := 0
  let mut pflow := 0
  let mut alsoProp := 0
  let mut heldSc := 0
  let mut indSc := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            let inp := mk outer kind p q op
            match openTriple inp, deathState inp with
            | some (sc, sp, _), some s =>
              rows := rows + 1
              let lastOpen : Nat → Bool := fun n =>
                match Scanner.prevRealIdx? s.tokens s.tokens.size with
                | some i => Scanner.flowOpenIdx? s.tokens i == some n
                | none => false
              let b := (List.range sp.tokens.size).all (fun j => s.tokens[j]! == sp.tokens[j]!)
              let h := lastOpen sp.tokens.size
              let i2 := s.indents == sp.indents
              let prop := match Scanner.prevRealIdx? sp.tokens sp.tokens.size with
                | some k => sp.tokens[k]!.val.isNodeProperty
                | none => false
              if b then below := below + 1
              if h then held := held + 1
              if i2 then ind := ind + 1
              if sp.inFlow == false then pflow := pflow + 1
              if b && h && i2 && sp.inFlow == false && prop then alsoProp := alsoProp + 1
              if lastOpen sc.tokens.size then heldSc := heldSc + 1
              if s.indents == sc.indents then indSc := indSc + 1
            | _, _ => pure ()
  return (rows, below, held, ind, pflow, alsoProp, heldSc, indSc)

#guard carrierCore == (144, 144, 144, 144, 144, 18, 0, 90)

/-- `(rows, the park's last real token is a node PROPERTY, the step's array is
    preprocessing's, the step's indent stack is preprocessing's)`.

    The second is what `ParkAnchor.parkProp` asks and it is 18 of 144 — the
    props cells alone.  The third is zero at every landing: preprocessing always
    writes, which is the same fact `carrierCore`'s hold reads from the other
    side.  The fourth is the unwind, and it is exactly the 90 that §8.1 kills. -/
private def anchorProp : Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut prop := 0
  let mut tokEq := 0
  let mut indEq := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            match openTriple (mk outer kind p q op) with
            | none => pure ()
            | some (sc, sp, _) =>
              rows := rows + 1
              match Scanner.prevRealIdx? sp.tokens sp.tokens.size with
              | some k => if sp.tokens[k]!.val.isNodeProperty then prop := prop + 1
              | none => pure ()
              if sc.tokens.size == sp.tokens.size then tokEq := tokEq + 1
              if sc.indents == sp.indents then indEq := indEq + 1
  return (rows, prop, tokEq, indEq)

#guard anchorProp == (144, 18, 0, 90)

/-- `offersNodeSlot` read exactly as `underIndentedFlowValuePos?` reads it, at
    the death state.

    The close test cannot refuse a cell of this grid — §5's `deathShape` pins
    the last real token as the flow close at all 144 — so it is here because the
    definition MIRRORS the gate, not because it discriminates.  Deleting it
    moves no count, which the perturbation harness asserts rather than
    discovers. -/
private def offersAtDeath (s : Scanner.ScannerState) : Bool :=
  match Scanner.prevRealIdx? s.tokens s.tokens.size with
  | none => false
  | some i =>
    if !(s.tokens[i]!.val.isFlowClose) then false
    else
      match Scanner.flowOpenIdx? s.tokens i with
      | none => false
      | some o =>
        match Scanner.prevRealIdx? s.tokens (Scanner.propsRunStart s.tokens o) with
        | some j => s.tokens[j]!.val.offersNodeSlot
        | none => false

/-- `(rows, the slot OFFERS, BOTH gates fire, offers ∧ §8.1 fires, ¬offers ∧
    §9.2 fires, the hold resolves to preprocessing's array end)`.

    §5 read the 90/54 split off the gate that fired; this reads it off the token
    array instead, and the two agree cell for cell — which is what says
    `offersNodeSlot` IS the partition and not a correlate of it.  The third
    count is the half §5 could not state: its `oneReading` counts an exclusive
    or, which a cell firing NEITHER gate would also fail, so the overlap is
    counted here directly and must be zero. -/
private def slotSplit : Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut off := 0
  let mut both := 0
  let mut offFloor := 0
  let mut noffDang := 0
  let mut openIdx := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            let inp := mk outer kind p q op
            match openTriple inp, deathState inp with
            | some (_, sp, _), some s =>
              rows := rows + 1
              let o := offersAtDeath s
              if o then off := off + 1
              if (Scanner.underIndentedFlowValuePos? s).isSome
                  && (Scanner.danglingNodePos? s).isSome then both := both + 1
              if o && (Scanner.underIndentedFlowValuePos? s).isSome then
                offFloor := offFloor + 1
              if !o && (Scanner.danglingNodePos? s).isSome then
                noffDang := noffDang + 1
              match Scanner.prevRealIdx? s.tokens s.tokens.size with
              | some i =>
                if Scanner.flowOpenIdx? s.tokens i == some sp.tokens.size then
                  openIdx := openIdx + 1
              | none => pure ()
            | _, _ => pure ()
  return (rows, off, both, offFloor, noffDang, openIdx)

#guard slotSplit == (144, 90, 0, 90, 54, 144)

/-- The state the landing step begins from, and whether preprocessing accepts
    it — the one reading that has to be taken on the columns the scan REFUSES,
    where no later state exists. -/
private def landingStep (input : String) : Option (Scanner.ScannerState × Bool) := Id.run do
  let mut s := start input
  let mut fuel := input.utf8ByteSize * 4 + 8
  while fuel > 0 do
    fuel := fuel - 1
    match Scanner.scanNextToken s with
    | .error _ =>
      match Scanner.scanNextToken_preprocess s with
      | .error _ => return some (s, false)
      | _ => return some (s, true)
    | .ok none => return none
    | .ok (some s') =>
      if s.flowLevel == 0 && s'.flowLevel == 1 then return some (s, true)
      s := s'
  return none

/-- **The carrier's SOURCE, over all 198 columns**: `(columns, preprocess
    refuses, of those the landing's column stands on NO level, preprocess
    accepts, of those it stands on one)`.

    Both directions, because one of them alone is a coverage report: the refused
    columns are refused BECAUSE the column matches no level, and every accepted
    one matches.

    `columns = refuses + accepts` is a READING here, not an identity: a cell
    whose scan runs to the end of the stream without reaching the landing at all
    is counted in the first and in neither of the other two.  What `198 = 54 +
    144` says is that no cell of this grid does that. -/
private def preLaw : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut cols := 0
  let mut bad := 0
  let mut badOut := 0
  let mut good := 0
  let mut goodIn := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            cols := cols + 1
            match landingStep (mk outer kind p q op) with
            | none => pure ()
            | some (s, ok) =>
              if ok then
                good := good + 1
                if hasCol s q then goodIn := goodIn + 1
              else
                bad := bad + 1
                if !hasCol s q then badOut := badOut + 1
  return (cols, bad, badOut, good, goodIn)

#guard preLaw == (198, 54, 54, 144, 144)

/-- What `lake run price -- carrier` reads by editing `StreamAccum.lean` and
    counting the declarations each edit breaks.

    Five probes, five rings, aimed at the BUILT carrier (item 267).  `core` and
    `slot` add a required field to the transport core and to the carrier's own
    payload; each is seven declarations, and the two sevens are not the same
    seven — `rewriteKey` builds its core out of `congrKind` and `pushInert` and
    so survives a field on `ParkCore`, while it builds its `ParkSlot` directly
    and does not.  `prop` RENAMES `parkProp` out from under its readers, which
    is the edit that prices a payload the split left in place; its eight are the
    seven wrappers and the spend, and `ofOpen` is not among them because it
    takes the property as a parameter rather than reading the field.
    `consumer` and `gate` are the two rings below, and each is a single
    declaration. -/
def expectedCarrierPrice : String :=
  "core=7 slot=7 prop=8 consumer=1 gate=1"



/-! ## §7 What the built carrier reads, at both ends (DOCS item 267)

§6 priced the carrier and named its source.  This section is the three readings
the BUILD rests on — one per design decision that could have gone the other way.

* **One carrier, two gates.**  `runStart` reads where §9.2's run begins on the
  cells that fire it.  It begins AT the open, at all 54, and no cell of the
  family puts a property in front of it — so the position §9.2 reports and the
  position §8.1 reports are the same token's, and one payload serves both
  spends.  A props-headed run would have needed a second reading.
* **What is a park fact and what is not.**  `parkFacts` reads
  `offersNodeSlot` at the death state and again at the park's own array, and
  they agree cell for cell: which gate owns a landing is fixed before the open
  is written, so the spends can take the slot as a hypothesis about the park
  rather than as a transported field.  Its last count is the genesis's own
  premise — the open token's column IS the park's cursor column.
* **Why the carrier is a payload and not a core field.**  `acceptedParks`
  walks the cells the scanner ACCEPTS.  The open's column stands on neither
  candidate park's indent stack at any of them, so a `ParkCore` that demanded
  the carrier could not be built where the `[96]` park builds one today.  The
  same walk is the membership law's control: its conclusion holds at none of
  the 378 and its hypothesis at none of them either, which is what says
  `preprocess_landing_on_stack`'s `h_below` decides the law rather than
  decorating it. -/

/-- `(rows, §9.2 fires, its run starts AT the open, the run start's column is
    the open's, that column stands on the stack, the run is props-headed)`.

    The last is the discrimination and it must be **zero**: a run headed by a
    property starts left of the bracket, and its refusal would be reported at a
    column the carrier does not name. -/
private def runStart : Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut dang := 0
  let mut atOpen := 0
  let mut colEqOpen := 0
  let mut onStack := 0
  let mut propsHead := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            let inp := mk outer kind p q op
            match openTriple inp, deathState inp with
            | some (_, sp, _), some s =>
              rows := rows + 1
              if (Scanner.danglingNodePos? s).isSome then
                dang := dang + 1
                match Scanner.trailingNodeRun? s.tokens with
                | none => pure ()
                | some (st, _) =>
                  if st == sp.tokens.size then atOpen := atOpen + 1
                  if s.tokens[st]!.pos.col == s.tokens[sp.tokens.size]!.pos.col then
                    colEqOpen := colEqOpen + 1
                  if hasCol s s.tokens[st]!.pos.col then onStack := onStack + 1
                  if st < sp.tokens.size then propsHead := propsHead + 1
            | _, _ => pure ()
  return (rows, dang, atOpen, colEqOpen, onStack, propsHead)

#guard runStart == (144, 54, 54, 54, 54, 0)

/-- The same slot reading `offersAtDeath` takes, read on the PARK's own array —
    the walk-back starts at the array's end, which is where the bracket lands. -/
private def offersAtPark (sp : Scanner.ScannerState) : Bool :=
  match Scanner.prevRealIdx? sp.tokens (Scanner.propsRunStart sp.tokens sp.tokens.size) with
  | some j => sp.tokens[j]!.val.offersNodeSlot
  | none => false

/-- `(rows, the slot offers at the death state, it offers at the PARK, the two
    agree, the open token's column is the park's cursor column)`. -/
private def parkFacts : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut offD := 0
  let mut offP := 0
  let mut agree := 0
  let mut colEq := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            let inp := mk outer kind p q op
            match openTriple inp, deathState inp with
            | some (_, sp, s'), some s =>
              rows := rows + 1
              let a := offersAtDeath s
              let b := offersAtPark sp
              if a then offD := offD + 1
              if b then offP := offP + 1
              if a == b then agree := agree + 1
              match Scanner.prevRealIdx? s'.tokens s'.tokens.size with
              | some i => if s'.tokens[i]!.pos.col == sp.col then colEq := colEq + 1
              | none => pure ()
            | _, _ => pure ()
  return (rows, offD, offP, agree, colEq)

#guard parkFacts == (144, 90, 90, 144, 144)

/-- The cells the scanner ACCEPTS, read at the same open: `(rows, the open's
    column stands on the STEP state's stack, on PREPROCESSING's stack, the
    landing's own column stands on preprocessing's stack, the landing is
    strictly DEEPER than the step state's floor)`.

    The first three must be zero and the fourth all of them.  Three zeros beside
    each other would be a coverage report; the fourth is what says the walk
    reached a landing at every cell and found the law's hypothesis false there,
    which is the same boundary §4's turnover names from the other side. -/
private def acceptedParks : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut scMem := 0
  let mut spMem := 0
  let mut landMem := 0
  let mut deeper := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in columns do
            if q < floorOf kind p then continue
            let inp := mk outer kind p q op
            if !accepts inp then continue
            match openTriple inp with
            | none => pure ()
            | some (sc, sp, s') =>
              match Scanner.prevRealIdx? s'.tokens s'.tokens.size with
              | none => pure ()
              | some i =>
                rows := rows + 1
                if hasCol sc s'.tokens[i]!.pos.col then scMem := scMem + 1
                if hasCol sp s'.tokens[i]!.pos.col then spMem := spMem + 1
                if hasCol sp sp.col then landMem := landMem + 1
                if (sp.col : Int) > sc.currentIndent then deeper := deeper + 1
  return (rows, scMem, spMem, landMem, deeper)

#guard acceptedParks == (378, 0, 0, 0, 378)


/-! ## §8 Which check kills, and whether the carrier's source can reach it
       (DOCS item 268)

§7 built the carrier and left it unconsumed: `accum_flow_open_depth0` hands
`h_kpkg none`, so the frame the under-run's open pushes is UNGATED, its node
reading is unconditional, and only `dropClose` can supply one.  What it costs to
gate that frame is the question here, and it has three parts — which check the
144 actually die at, whether anything on the proof side HOLDS that check, and
whether the carrier's source can be applied where the arm stands.

**There are four checks, not two.**  §5 read the deaths with no tail and found
them at the END-OF-INPUT gates; `tailSweep` read the same 144 dying at a
MID-STREAM gate with a sibling line after the open.  Both gates exist at both
depths, so the population splits over four checks — and §1 below reads the same
`offersNodeSlot` partition, 90 and 54, at each of them.  One carrier serves all
four; two consumers does not describe the surface.

**The two halves are not the same bill.**  Resolved in the environment rather
than grepped, §9.2's mid-stream check is held as a hypothesis by twenty-one
declarations of the accumulation and its end-of-input twin by five; §8.1's
checks are held by NONE, at either depth.  §8.1's success is derived once, at
`scanNextToken_accum_step`, and discarded on the next line while its twin
`h_dn` is threaded into twenty-one signatures.  So the 54 that die at §9.2 have
a rail that already reaches the arm, and the 90 that die at §8.1 — the majority
— have no holder to reach at all.  The census is
`Tests/Guards/Proofs/ParkBill.lean` §5.

**And the carrier's source cannot be applied at the arm.**  §2 reads the
hypotheses of `preprocess_landing_on_stack` at the state the open's step begins
with.  `needIndentCheck` is false at every one of the 144 and true at every one
after `skipToContent`: the break this family crosses is crossed INSIDE the open's
own step, so a premise stated on the incoming state names a flag the consumer
never has.  The conclusion holds at all 144 regardless, which is what says the
lemma is true and unusable rather than wrong. -/

/-- Drive `scanNextToken`, and when a step refuses, re-run that step's own two
    mid-stream gates against the state the step began with — the two states
    `scanNextToken` reads them on, the RUN before preprocessing's unwind and the
    LAND after it.  That names WHICH of the four checks the refusal is. -/
private def walkGate (input : String) : Bool × String := Id.run do
  let mut s := start input
  let mut opened := false
  let mut fuel := input.utf8ByteSize * 4 + 8
  while fuel > 0 do
    fuel := fuel - 1
    match Scanner.scanNextToken s with
    | .error _ =>
      match Scanner.scanNextToken_preprocess s with
      | .error _ => return (opened, "step:preprocess")
      | .ok none => return (opened, "step:pre-none")
      | .ok (some (s_prep, _)) =>
        match Scanner.scanNextToken_checkDanglingNode s s_prep with
        | .error _ => return (opened, "mid:dangling")
        | .ok _ =>
          match Scanner.scanNextToken_checkFlowValueIndent s s_prep with
          | .error _ => return (opened, "mid:floor")
          | .ok _ => return (opened, "mid:other")
    | .ok none =>
      if s.flowLevel > 0 then return (opened, "eof:unterminated")
      match Scanner.scanLoop_checkDanglingNode s with
      | .error _ => return (opened, "eof:dangling")
      | .ok _ =>
        match Scanner.scanLoop_checkFlowValueIndent s with
        | .error _ => return (opened, "eof:floor")
        | .ok _ => return (opened, "ACCEPT")
    | .ok (some s') =>
      if s.flowLevel == 0 && s'.flowLevel == 1 then opened := true
      s := s'
  return (opened, "FUEL")

/-- **§1 The four checks, over the same 144.**  `(dispatched, dying at §8.1's
    END-OF-INPUT floor, at §9.2's end-of-input run, at §8.1's MID-STREAM floor,
    at §9.2's mid-stream run)` — the last two with a sibling line appended.

    The four are read by name rather than by error constructor, so a reading
    cannot drift onto the twin at the other depth; and the two pairs must sum to
    the same 144 and split it the same way, which is what says the tail moves
    the DEPTH of the refusal and nothing else. -/
private def killSite : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut disp := 0
  let mut eofFloor := 0
  let mut eofDang := 0
  let mut midFloor := 0
  let mut midDang := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            let inp := mk outer kind p q op
            let (d, w) := walkGate inp
            if !d then continue
            disp := disp + 1
            if w == "eof:floor" then eofFloor := eofFloor + 1
            if w == "eof:dangling" then eofDang := eofDang + 1
            let (_, w2) := walkGate (inp ++ "zz: 9\n")
            if w2 == "mid:floor" then midFloor := midFloor + 1
            if w2 == "mid:dangling" then midDang := midDang + 1
  return (disp, eofFloor, eofDang, midFloor, midDang)

#guard killSite == (144, 90, 54, 90, 54)

/-- The state the OPEN's own step begins with and the state preprocessing hands
    that step, for one input of the family. -/
private def openPair (input : String) :
    Option (Scanner.ScannerState × Scanner.ScannerState) := Id.run do
  let mut s := start input
  let mut fuel := input.utf8ByteSize * 4 + 8
  while fuel > 0 do
    fuel := fuel - 1
    match Scanner.scanNextToken s with
    | .error _ => return none
    | .ok none => return none
    | .ok (some s') =>
      if s.flowLevel == 0 && s'.flowLevel == 1 then
        match Scanner.scanNextToken_preprocess s with
        | .ok (some (sp, _)) => return some (s, sp)
        | _ => return none
      s := s'
  return none

/-- **§2 The carrier's source, read at its consumer.**  `(rows, the flag on the
    incoming state, the flag one function later, out of flow, the landing below
    the incoming floor, the membership the carrier names, the indent stack
    unmoved, the stack popped)`.

    Of `preprocess_landing_on_stack`'s premises this reads one — the landing
    at or left of the floor the step began with — together with its
    conclusion; the flag and the flow are what `scanNextToken_preprocess`
    consults on the way, not what the lemma asks for.  The second and third
    are the same flag at the two states preprocessing reads it on, which is
    the whole finding: this family crosses its break INSIDE the open's own
    step, so the flag is false on the state the arm holds and true on the
    state the unwind consults.  The fifth and the eighth are the same dedent
    counted two ways — the premise `preprocess_pops_of_below` takes and the
    conclusion it draws — so neither can pass vacuously, and the seventh is
    their complement. -/
private def sourceFacts : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut nic := 0
  let mut nicSkip := 0
  let mut noflow := 0
  let mut below := 0
  let mut mem := 0
  let mut same := 0
  let mut popped := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            match openPair (mk outer kind p q op) with
            | none => pure ()
            | some (sc, sp) =>
              rows := rows + 1
              if sc.needIndentCheck then nic := nic + 1
              match Scanner.skipToContent sc with
              | .ok sk => if sk.needIndentCheck then nicSkip := nicSkip + 1
              | _ => pure ()
              if !sc.inFlow then noflow := noflow + 1
              if (sp.col : Int) < sc.currentIndent then below := below + 1
              if sp.indents.any (fun e => e.column == (sp.col : Int)) then
                mem := mem + 1
              if sp.indents == sc.indents then same := same + 1
              if sp.indents != sc.indents then popped := popped + 1
  return (rows, nic, nicSkip, noflow, below, mem, same, popped)

#guard sourceFacts == (144, 0, 144, 144, 54, 144, 90, 54)

/-- **§3 What the wiring costs, by producers** (`lake run price -- wire`).

    Four probes, four rings.  `gate` widens `GateOf`'s arity — who READS the
    frame's gate; `anchor` adds the carrier as a third conjunct of
    `FlowBaseAnchor` — who BUILDS a gated frame; `route` adds a hypothesis to
    `FlowBaseRoutes.value` — who supplies and who applies the node reading;
    `eof` adds one to `scanNextToken_none_stream` — who drives the end-of-input
    consumer.

    The asymmetry is the reading: putting the carrier on the anchor costs TWO
    declarations, a single transport funnel and a single producer, while
    widening the gate that reads it costs FORTY-NINE.  A carrier-aware verdict
    therefore belongs on the route, not on `GateOf`. -/
def expectedWirePrice : String := "gate=49 anchor=2 route=3 eof=1"

/-- **§10a What each `drop_ride` arm HOLDS** (`lake run price -- arm`).

    Twenty-four cells: eight readings against the three arms that spend the
    ride, each taken by ELABORATION at the spend site — `assumption` for the
    six that ask whether a type is inhabited in the local context, and a
    reference for the two that ask whether a NAME is bound there.  A cell is
    `P` when the arm already holds the reading and `O` when it does not; a
    derivation is a different bill from a binder, and this table is about
    binders.

    **The three arms read identically on every row but one.**  They hold
    preprocessing's equation, the sentinel base and the landing's out-of-flow
    fact, and they hold none of `preprocess_floor_eq`'s two floor premises nor
    the guard item 147's floor sits behind.  §10 reads all four of those as TRUE
    at every one of the 144 the branch admits, so the ride owes a coordinate and
    not a fact.

    The one row that discriminates is `gate_gp`, and it is the reason this table
    is taken at the arm rather than at the declaration: `propsPark_open_gate` is
    called once in the module, on the path into the FIRST arm, which obtains its
    `gp` and then discards it by handing `h_kpkg none`.  The other two never see
    it.  An environment census of that gate's callers resolves to one
    declaration and cannot say this, because all three arms live inside it. -/
def expectedArmTable : String :=
  "cells=24 paid=10 owed=14 hok=PPP base=PPP le=OOO floor=OOO \
noflow_prep=PPP park_col_ne0=OOO gate_gp=POO sibling_floor_prep=OOO"

/-- **§11 What the coordinate costs** (`scripts/coordinate_price.py`).

    Four probes, all by elaboration at the three sites that spend the ride.

    `ident` is the 3x3 matrix that fixes the arm NAMES: each of the three
    constructors declares a binder the other two do not, so a probe that merely
    REFERS to one elaborates at its own site and nowhere else.  The matrix is
    diagonal, which is how item 270's third label — `pendingContent`, an arm of
    the same `cases` that spends no ride — was caught.

    `le`, `park_col_ne0` and `floor` each ask twice: once with `assumption`,
    which is item 270's question, and once with a NAMED derivation.  `P` is what
    the arm holds, `B` what it can derive from what it holds, `O` neither.
    Reading `BBB BBB BBB`: none of the three is a fact the arm is handed and
    all three are derivations it can write.  The first two are bridges off the
    under-run's own location and off a constructor field; the third is the
    conjunct `preprocess_some_separate_at_floor` carries (item 272), spent
    against the park-column bridge above it and item 270's `noflow_prep`.

    `lib` is the arity flip on that splitter: its under-run disjunct gains a
    component that is true everywhere and is supplied in the splitter's own
    proof, so the census counts sites that must now WRITE something, not sites
    where the fact is hard.  ONE library declaration, three sites, all inside
    `accum_flow_open_depth0` — which is why item 270's table had to be taken at
    the ARM and why this census cannot read three declarations.  Compare item
    268's `gate=49`.

    The tree census is held out of this pin and out of the battery: it rebuilds
    every module that imports the patched one.  `coordinate_price.py wide`
    re-derives it. -/
def expectedCoordPrice : String :=
  "arms=pendingProps,pendingBlock,pendingMapValue ident=diagonal le=BBB \
park_col_ne0=BBB floor=BBB lib=1"

/-! ## §9 The rail that is not worth building, and the source that is
    (DOCS item 269)

Item 268 measured that §8.1's check is held as a hypothesis by no declaration of
the accumulation and left one instruction: thread it from
`scanNextToken_accum_step` the way §9.2's is threaded.  §5 above already
answered that, in prose, three items earlier — *both gates also run at the
open's own step, on a state where the collection is not yet closed, so both say
`.ok` there* — and §9.1 makes the answer a number.  The rail would deliver a
reading that is true at every landing in the family for a reason that has
nothing to do with the family, so it is not built.

What IS built is the carrier's source, restated.  §9.2 reads the landing's own
floor and finds it AT the landing's column at every one of the 144, which turns
the membership into a projection of the state the arm is handed, against the
control §9.2a supplies; §9.3 reads the indent-check flag on the two states
preprocessing consults, beside a same-line control that holds the other
answer. -/

private def lastRealIsFlowClose (s : Scanner.ScannerState) : Bool :=
  match Scanner.prevRealIdx? s.tokens s.tokens.size with
  | none => false
  | some i => s.tokens[i]!.val.isFlowClose

/-- **§9.1 What a rail from the open would carry.**  `(rows, §8.1's check
    succeeds at the OPEN, its position reading is `none` there, the landing is
    ARMED there, the run's last real token is a flow close there, the position
    reading is `some` at the state the scan died at, the last real token is a
    flow close there, §9.2's position reading is `some` there)`.

    The fourth component is what stops the third from passing vacuously:
    `scanNextToken_checkFlowValueIndent` answers `.ok` outright when the landing
    is not armed, and the landing is armed at every one of the 144 — so the
    check LOOKS, and finds nothing.  The fifth says why it finds nothing, and it
    is the whole reading: `underIndentedFlowValuePos?` reports only on a run
    whose last real token is a flow CLOSE, and at the open the collection has
    not been opened.  Three to five steps later the same function answers `some`
    at exactly the ninety.

    So a rail from `scanNextToken_accum_step` to the open's arm would carry a
    true statement that discriminates nothing, and the datum the ninety die on
    is not yet a fact when the rail's head runs.  A carrier is the only
    transport that crosses those steps. -/
private def railPayload : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut fvOk := 0
  let mut posNone := 0
  let mut armed := 0
  let mut fcOpen := 0
  let mut posSomeD := 0
  let mut fcD := 0
  let mut dnSomeD := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            let inp := mk outer kind p q op
            match openTriple inp, deathState inp with
            | some (sc, sp, _), some sD =>
              rows := rows + 1
              match Scanner.scanNextToken_checkFlowValueIndent sc sp with
              | .ok _ => fvOk := fvOk + 1
              | _ => pure ()
              if (Scanner.underIndentedFlowValuePos? sc).isNone then
                posNone := posNone + 1
              if sp.simpleKeyAllowed then armed := armed + 1
              if lastRealIsFlowClose sc then fcOpen := fcOpen + 1
              if (Scanner.underIndentedFlowValuePos? sD).isSome then
                posSomeD := posSomeD + 1
              if lastRealIsFlowClose sD then fcD := fcD + 1
              if (Scanner.danglingNodePos? sD).isSome then dnSomeD := dnSomeD + 1
            | _, _ => pure ()
  return (rows, fvOk, posNone, armed, fcOpen, posSomeD, fcD, dnSomeD)

#guard railPayload == (144, 144, 144, 144, 0, 90, 144, 54)

/-- **§9.2 The landing's own floor.**  `(rows, the floor preprocessing leaves
    EQUALS the landing's column, it is left of the column, it is right of the
    column, the resulting stack has at most one entry, the landing is below the
    floor the step BEGAN with, it is at that floor, it is above it)`.

    The second is what `preprocess_floor_eq` concludes.  The third and fourth
    complete the trichotomy and are therefore arithmetic and not evidence: with
    the second at every row they cannot read anything else, and a grid that
    never produces the other answer reports its own coverage.  `floorControl` is
    the reading that carries the evidence.  The fifth refutes the sentinel
    escape — `preprocess_landing_at_level`'s disjunct — at every row, so the
    equality is read off a stack with a real top, and it is not forced by the
    second.

    The last three partition the same 144 by the floor the step BEGAN with: 54
    land below it and 90 land exactly at it.  One premise spans both, because it
    reads the floor the landing RESTS at rather than the floor it started from,
    and `landing_on_stack_of_floor_eq` needs no scanner run to spend it. -/
private def floorFacts : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut eq := 0
  let mut lt := 0
  let mut gt := 0
  let mut small := 0
  let mut below := 0
  let mut atFloor := 0
  let mut above := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            match openTriple (mk outer kind p q op) with
            | none => pure ()
            | some (sc, sp, _) =>
              rows := rows + 1
              let c : Int := (sp.col : Int)
              if sp.currentIndent == c then eq := eq + 1
              if sp.currentIndent < c then lt := lt + 1
              if sp.currentIndent > c then gt := gt + 1
              if sp.indents.size <= 1 then small := small + 1
              if c < sc.currentIndent then below := below + 1
              if c == sc.currentIndent then atFloor := atFloor + 1
              if c > sc.currentIndent then above := above + 1
  return (rows, eq, lt, gt, small, below, atFloor, above)

#guard floorFacts == (144, 144, 0, 0, 0, 54, 90, 0)

/-- The same grid with the open on the park's OWN line, which is the control
    §9.3 reads its flag against. -/
private def mkSame (outer kind : String) (p : Nat) (op : String) : String :=
  let pre := match outer, p with
    | _, 0 => ""
    | "map", _ => "w:\n"
    | "seq", _ => "-\n"
    | _, _ => "? w\n: v\nz:\n"
  let body := match kind with
    | "mapValue" => spaces p ++ "k:"
    | "block" => spaces p ++ "-"
    | "qmark" => spaces p ++ "?"
    | _ => spaces p ++ "&a"
  pre ++ body ++ " " ++ op ++ "\n"

/-- **§9.2a The control for §9.2.**  The same grid with the open on the park's
    own line — a family that reaches the same dispatch with no break to cross,
    so the unwind does not run.  `(rows, the resting floor equals the landing's
    column, it is left of the column, it is right of the column, the landing is
    at or left of the floor the step began with)`.

    The second is the answer §9.2 reads at all 144, and the control reads it at
    NONE of its 96; the third is its opposite at every one.  So §9.2's equality
    discriminates between two families rather than reporting a constant.  The
    fifth is `preprocess_floor_eq`'s own premise `h_le`, and no control row
    satisfies it: the line that separates the two answers is exactly the line
    the premise draws, which is what makes it load-bearing and not
    decoration. -/
private def floorControl : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut eq := 0
  let mut lt := 0
  let mut gt := 0
  let mut inDom := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          match openTriple (mkSame outer kind p op) with
          | none => pure ()
          | some (sc, sp, _) =>
            rows := rows + 1
            let c : Int := (sp.col : Int)
            if sp.currentIndent == c then eq := eq + 1
            if sp.currentIndent < c then lt := lt + 1
            if sp.currentIndent > c then gt := gt + 1
            if c <= sc.currentIndent then inDom := inDom + 1
  return (rows, eq, lt, gt, inDom)

#guard floorControl == (96, 0, 96, 0, 0)

/-- **§9.3 The flag, on the state the unwind consults, against a control.**
    `(rows, the line moves from the incoming state to the landing, the flag is
    UP on the state `skipToContent` hands preprocessing, the flag is DOWN on the
    landing, CONTROL rows, the control's line moves, the control's flag is up)`.

    Read on the INCOMING state the flag stands at zero of the 144, which is
    item 268's count.  These three say where it is instead: this
    family crosses its break inside the open's own step, so the flag is raised
    by the skip and cleared again by the unwind, and neither state the arm holds
    shows it.  The control is the same grid with the open on the park's own
    line — a family that reaches the same dispatch with no break to cross — and
    it holds the opposite answer at every row, so the reading is a
    discrimination and not a constant. -/
private def lineSource : Nat × Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut moved := 0
  let mut flag := 0
  let mut spDown := 0
  let mut crows := 0
  let mut cmoved := 0
  let mut cflag := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            match openTriple (mk outer kind p q op) with
            | none => pure ()
            | some (sc, sp, _) =>
              rows := rows + 1
              if sc.line != sp.line then moved := moved + 1
              match Scanner.skipToContent sc with
              | .ok sk => if sk.needIndentCheck then flag := flag + 1
              | _ => pure ()
              if sp.needIndentCheck == false then spDown := spDown + 1
          match openTriple (mkSame outer kind p op) with
          | none => pure ()
          | some (sc, sp, _) =>
            crows := crows + 1
            if sc.line != sp.line then cmoved := cmoved + 1
            match Scanner.skipToContent sc with
            | .ok sk => if sk.needIndentCheck then cflag := cflag + 1
            | _ => pure ()
  return (rows, moved, flag, spDown, crows, cmoved, cflag)

#guard lineSource == (144, 144, 144, 144, 96, 0, 0)

/-- **§10 The genesis disjunct, refuted rather than read.**  `(rows, the flag is
    DOWN on the state the step begins with, the line MOVES from that state to
    the landing, the landing is out of flow, the park's own cursor column is
    nonzero, the indent stack is unmoved, the landing rests at or right of its
    own floor)`.

    `preprocess_some_ssl_comments_anyCol` asserts BOTH of its arms exist, so no
    single predicate says which one a landing takes.  The stale arm carries its
    own refutation instead: under `sc.needIndentCheck = false` it concludes
    `s_prep.line = sc.line` and `s_prep.indents = sc.indents`.  The second
    component reads that guard SATISFIED and the third reads the line MOVED, so
    at every row where both hold the stale arm's conclusion is false and the
    landed arm is the one in hand — measured at the arm's own statement rather
    than inferred from the shape of the proof that reaches it.

    Both refutations fire, with different reach: the line conclusion is false at
    all 144 and the indent conclusion at the 54 that pop, which is why the sixth
    component is read beside the third rather than in place of it — a single
    refuting reading would not say whether the arm fails everywhere or only
    where the stack moves.

    The fourth and fifth are the two guards item 147's floor sits behind in that
    landed arm, `s_prep.inFlow = false` and `sp.col ≠ 0`, the second read at the
    park's own cursor; the seventh is the floor itself.  All three hold at every
    row, and `floorFacts`'s own last three say the remaining premise does too —
    54 below the incoming floor, 90 at it, 0 above.  So every premise
    `preprocess_floor_eq` asks for is TRUE at every input this branch admits,
    and `lake run price -- arm` reads none of them as nameable inside the arm:
    what the ride owes is a COORDINATE, not a fact. -/
private def genesisFacts : Nat × Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut nic0 := 0
  let mut moved := 0
  let mut noflow := 0
  let mut colNe0 := 0
  let mut same := 0
  let mut floor := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            match openTriple (mk outer kind p q op) with
            | none => pure ()
            | some (sc, sp, _) =>
              rows := rows + 1
              if sc.needIndentCheck == false then nic0 := nic0 + 1
              if sc.line != sp.line then moved := moved + 1
              if sp.inFlow == false then noflow := noflow + 1
              if sc.col != 0 then colNe0 := colNe0 + 1
              if sp.indents == sc.indents then same := same + 1
              if sp.currentIndent <= (sp.col : Int) then floor := floor + 1
  return (rows, nic0, moved, noflow, colNe0, same, floor)

#guard genesisFacts == (144, 144, 144, 144, 144, 90, 144)

/-! ## §11 What the coordinate costs (DOCS item 271)

§10 read every premise `preprocess_floor_eq` asks for as TRUE at every one of
the 144 and none of them as nameable inside the arm, and called what the ride
owes a coordinate.  A coordinate has a price.  Item 268 measured one — `anchor=2`
against `gate=49` — but over a different datum, so the number does not transfer
without being re-read.

Re-read, two of the three premises cost **nothing**, because neither is a
carriage.  The under-run the three arms split on is LOCATED:
`WhiteRunUnderRun n sp_mid sp_prep` is `j < n` spaces off a column-0 line start,
and on the RUN-END half those spaces ARE the landing.  So the landing's column
is `j`, the index it under-ran bounds it, and each arm's own `IndentFloor`
bounds that index by the floor the step began with
(`underRunEnd_col_le_currentIndent`).  The park-column guard is one step from a
field each of the three constructors declares — `h_col0 : 0 < sp_scan.col` at
`pendingProps` and `pendingMapValue`, `h_col : sp_scan.col = n + 1` at
`pendingBlock`.

This section reads that derivation's premises and its conclusion at the runtime,
on the family and on a control the family's own boundary supplies. -/

/-- `(rows, preprocessing lands at the built column, the park's index is at most
    the incoming floor plus one, the landing is at or left of the incoming
    floor, the incoming floor is not the sentinel)`.

    The second and third are `underRunEnd_col_le_currentIndent`'s two premises
    read where the proof cannot see them — `sp_prep.col = j` after the
    column-0 line start, and `n ≤ minContentIndentOf sc` off the arm's own
    `IndentFloor` — and the fourth is its conclusion.  The fifth says the
    conclusion is not carried by the vacuous branch: a stack at its base floors
    the index at zero, where `j < n` is the under-run's own refutation, so a
    family that sat there would prove the lemma without exercising it. -/
private def bridgeFacts : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut landed := 0
  let mut idxFloored := 0
  let mut concl := 0
  let mut nonneg := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            match openTriple (mk outer kind p q op) with
            | none => pure ()
            | some (sc, sp, _) =>
              rows := rows + 1
              if sp.col == q then landed := landed + 1
              if ((floorOf kind p : Nat) : Int) ≤ sc.currentIndent + 1 then
                idxFloored := idxFloored + 1
              if (sp.col : Int) ≤ sc.currentIndent then concl := concl + 1
              if sc.currentIndent ≥ 0 then nonneg := nonneg + 1
  return (rows, landed, idxFloored, concl, nonneg)

#guard bridgeFacts == (144, 144, 144, 144, 144)

/-- The same five readings one column to the RIGHT — at the park's floor rather
    than below it, which is §4's accepted boundary and not this branch.

    This is the control that says the conclusion is not an arithmetic
    consequence of how the family is built.  Both premises still read all
    ninety-six: preprocessing still lands at the built column and the park's
    index is still floored by the incoming state, because neither is a fact
    about the landing being UNDER-run.  The conclusion reads zero.  What
    separates the two families is the one premise the runtime cannot show
    directly — `j < n` — and the control is how that is established without
    asking the count to be its own evidence.

    The fifth reading is **90**, and the six cells it misses are the props park
    at indent 0 across both opens and all three outers, which build the same
    input.  Those are the grid's only sentinel floors, and they are exactly the
    cells the family above cannot reach: `floorOf "props" 0` is 0, so the
    under-run row is empty there.  The lemma's vacuous branch and the family's
    empty rows are the same six cells, which is why `bridgeFacts` reads 144 on
    a component the control cannot. -/
private def bridgeControl : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut landed := 0
  let mut idxFloored := 0
  let mut concl := 0
  let mut nonneg := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          let q := floorOf kind p
          match openTriple (mk outer kind p q op) with
          | none => pure ()
          | some (sc, sp, _) =>
            rows := rows + 1
            if sp.col == q then landed := landed + 1
            if ((floorOf kind p : Nat) : Int) ≤ sc.currentIndent + 1 then
              idxFloored := idxFloored + 1
            if (sp.col : Int) ≤ sc.currentIndent then concl := concl + 1
            if sc.currentIndent ≥ 0 then nonneg := nonneg + 1
  return (rows, landed, idxFloored, concl, nonneg)

#guard bridgeControl == (96, 96, 96, 0, 90)


/-! ## §12 What the APPLIED source still owes (DOCS item 272)

§11 priced the coordinate and item 272 landed it:
`preprocess_some_separate_at_floor`'s under-run disjunct carries item 147's
floor, so all three premises of `preprocess_landing_on_stack` are readable at
the arm and `underRunEnd_landing_on_stack` returns its conclusion there.

What that conclusion is, exactly, is a membership on the LANDING — the column
preprocessing came to rest at, standing on the stack it came to rest with.
What `ParkSlot.ofOpen` asks for is the same membership over the OPEN TOKEN's
column, because both gates read the token's own position and not the park's
cursor (§7).  The two are the same number at every cell of this family and the
equation between them is carried by nothing: item 165's `h_optok` names the
push and the token's kind and says nothing about its position.

This section reads the two shapes, the equation between them and the gate a
frame parked at the landing would carry, at the runtime, on the family and on
the accepted boundary the family's own §4 supplies. -/

/-- `(rows, the applied source's conclusion, the genesis's premise, the two are
    the same column, §9.2's verdict at the LANDING's park, §9.2's verdict at
    the state the step began with)`.

    The second is what `underRunEnd_landing_on_stack` returns; the third is
    what `ParkSlot.ofOpen` takes; the fourth is the equation between them, and
    it is the one datum the arm cannot name.  The last two are read at the
    OPEN's own step, three to five steps before the refusal (§5's
    `distances`): a frame parked at the landing carries `GateOf (some s_prep)`
    and its producer owes the verdict at `sc`.

    The third and fourth are `carrierPark`'s own readings (§6), taken again
    here rather than cited: the point of this tuple is that the two the arm can
    derive and the one it cannot are read on ONE grid, against ONE control, so
    which of them splits is a comparison and not a cross-reference. -/
private def transportFacts : Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut srcConcl := 0
  let mut genesis := 0
  let mut posEq := 0
  let mut gateLanding := 0
  let mut gateStep := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            match openTriple (mk outer kind p q op) with
            | none => pure ()
            | some (sc, sp, s') =>
              match openColOf s' with
              | none => pure ()
              | some c =>
                rows := rows + 1
                if hasCol sp sp.col then srcConcl := srcConcl + 1
                if hasCol sp c then genesis := genesis + 1
                if sp.col == c then posEq := posEq + 1
                if (Scanner.danglingNodePos? sp).isNone then
                  gateLanding := gateLanding + 1
                if (Scanner.danglingNodePos? sc).isNone then
                  gateStep := gateStep + 1
  return (rows, srcConcl, genesis, posEq, gateLanding, gateStep)

#guard transportFacts == (144, 144, 144, 144, 144, 144)

/-- The same six one column to the RIGHT — at the park's floor, which §4
    measures as the scanner's turnover and this branch never reaches.

    **The two readings the arm can derive are the two that split, and the one
    it cannot name is the one that does not.**  The membership reads 144 on the
    family and ZERO here, in both shapes: §7's `acceptedParks` reads the open's
    column standing on neither candidate park's stack at all 378 accepted
    cells, and this is that reading at the boundary.  The position equation
    reads all ninety-six — the bracket is written at preprocessing's cursor
    whatever the landing did — so it is a fact about the dispatch and not about
    this branch, which is exactly why no hypothesis of the branch carries it.

    And the gate reads all ninety-six on both states in both families, which
    says what gating the frame at the landing buys at THIS step: nothing.  The
    verdict the close spends has to come from the slot. -/
private def transportControl : Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut srcConcl := 0
  let mut genesis := 0
  let mut posEq := 0
  let mut gateLanding := 0
  let mut gateStep := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          let q := floorOf kind p
          match openTriple (mk outer kind p q op) with
          | none => pure ()
          | some (sc, sp, s') =>
            match openColOf s' with
            | none => pure ()
            | some c =>
              rows := rows + 1
              if hasCol sp sp.col then srcConcl := srcConcl + 1
              if hasCol sp c then genesis := genesis + 1
              if sp.col == c then posEq := posEq + 1
              if (Scanner.danglingNodePos? sp).isNone then
                gateLanding := gateLanding + 1
              if (Scanner.danglingNodePos? sc).isNone then
                gateStep := gateStep + 1
  return (rows, srcConcl, genesis, posEq, gateLanding, gateStep)

#guard transportControl == (96, 0, 0, 96, 96, 96)

/-! ### §12a What the applied source still owes, priced

`scripts/transport_price.py`, battery stage 22c.  Six probes, read by
elaboration at the three arms that spend `drop_ride`:

* `source` — the membership `underRunEnd_landing_on_stack` returns, at the arm.
* `hcol` — the same membership in the shape `ParkSlot.ofOpen` names it, over
  the OPEN TOKEN's column, with the source offered as the derivation.  It is
  refused at all three, and the elaborator's message is a type mismatch on the
  column and nothing else.
* `genesis` — `ParkSlot s_prep s' 0` at the arm GIVEN the position equation.
  `B` says that equation is the only premise missing: the push, the token's
  kind, the indent equality and the park's flow are all bound already.
* `optok` — the ring.  Adding a conjunct to item 165's `h_optok` breaks THREE
  sites in two declarations: the two call sites in `accum_step_flow` and the
  props arm's own destructuring.  Against item 268's four rings — `gate=49
  anchor=2 route=3 eof=1` — the ring an APPLIED source needs is none of them.
* `pay` — the same ring PAID, with the two call sites supplying the column from
  the lemma they already rewrite with (`scanFlow…Start_tokens` writes the token
  at `currentPos`; the `allowDirectives` update preserves it).  `B` at all
  three says the carrier's genesis is then available with no hypothesis and no
  hole.
* `frames` / `ride` — the second ring.  The declaration builds ~~SEVEN~~ EIGHT
  frames since item 285, and the one the under-run's open pushes is built by
  ~~`drop_ride`~~ `slot_ride`, a single `have` that precedes `cases h_pending`:
  none of the three arms' own binders is in scope there, while a hypothesis of
  the declaration is.  A `have` has no
  arity, so no flip in this repo can see that ring.
* `genesis` / `pay` read `BBB` since item 284: `ParkSlot.ofOpen`'s `hrun` is
  `slotRun_of_dn` at the props arm and `slotRun_of_offer` at the indicator arms
  (the probes' `HRUN`), so the carrier's genesis needs nothing but the `optok`
  ring the `pay` row simulates.  Every other column read as before.
* Item 285 LANDS the ring and spends the slot, and one column moves: `frames`
  7 → 8, `slot_ride`'s frame, the gated one the three arms take.  `optok`
  re-reads 3 on the ringed `h_optok` — the two call sites and one site in
  `accum_flow_open_depth0` — and `pay` reads the module as it is.  `ride` stays
  0/3: `slot_ride` is a `have` beside `drop_ride` and takes the arms' three data
  as PARAMETERS, so the ring is paid at the spend rather than in scope. -/

def expectedTransportPrice : String :=
  "source=BBB hcol=OOO genesis=BBB optok=3 pay=BBB frames=8 ride=0/3"

/-! ## §13 What the ride can carry, and what the frame will receive
    (DOCS item 273)

§12 measured the ring an applied source needs and recorded an order for this
section: build the ride per arm, then pay `optok`.  That order was written from
what each ring BUYS.  This section reads what RECEIVES the carrier.

A ride that takes a `ParkSlot` has exactly one place to put it — the frame's
own `FlowBaseAnchor g s' 0` argument, which is what `FlowStackK` carries from
the open to the close (`FlowBaseAnchor.gate`).  That definition's `some` arm
names `ParkAnchor`: the same `ParkCore`, one field apart.  `ParkAnchor` asks
that the park's last real token be a node property; `ParkSlot` asks that the
open's column stand on the park's indent stack.

The two are not two ways of naming one fact, and the difference is not a
nameability gap of the kind §10 measured.  One of them is FALSE at most of this
family. -/

/-- `(rows, `ParkAnchor`'s own field at the landing's park, `ParkSlot`'s own
    field at the same park, cells where the slot holds and the anchor does not,
    cells where the anchor holds and the slot does not, `ParkFloor`'s own
    field)`.

    The second is what `FlowBaseAnchor`'s `some` arm asks of this family; the
    third is what the family can supply.  §6's `anchorProp` read the second
    already and this tuple takes it again beside the other four rather than
    citing it, for §12's reason: a comparison between two censuses is not a
    comparison.

    The fourth and fifth are the two directions of that comparison and neither
    can pass vacuously — the fifth must be ZERO, or replacing the anchor with
    the slot would lose a cell the anchor holds, and a tuple that reported a
    strictly weaker ask without checking the other direction would be reporting
    an assumption.  The sixth is the frame's other half, which costs nothing at
    depth 0: the open clears the pending key and the stacked range is empty. -/
private def carrierChoice : Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut anch := 0
  let mut slot := 0
  let mut slotOnly := 0
  let mut anchOnly := 0
  let mut floorF := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            match openTriple (mk outer kind p q op) with
            | none => pure ()
            | some (_, sp, s') =>
              match openColOf s' with
              | none => pure ()
              | some c =>
                rows := rows + 1
                let a := match Scanner.prevRealIdx? sp.tokens sp.tokens.size with
                  | some k => sp.tokens[k]!.val.isNodeProperty
                  | none => false
                let sl := hasCol sp c
                if a then anch := anch + 1
                if sl then slot := slot + 1
                if sl && !a then slotOnly := slotOnly + 1
                if a && !sl then anchOnly := anchOnly + 1
                if s'.simpleKey.possible == false then floorF := floorF + 1
  return (rows, anch, slot, slotOnly, anchOnly, floorF)

#guard carrierChoice == (144, 18, 144, 126, 0, 144)

/-- The same six at the park's floor — §4's turnover, which this branch never
    reaches, and where the two fields' relationship INVERTS.

    On the family the slot holds at every cell and the anchor at eighteen, and
    no cell holds the anchor without the slot.  Here the slot holds at NONE
    (§7's `acceptedParks` read the open's column standing on neither candidate
    park's stack at all 378 accepted cells) and the anchor at twenty-four, so
    every cell that holds one holds only the anchor.  The comparison the family
    reports is therefore about this branch and not about the two definitions:
    a control that merely zeroed would have left that open. -/
private def carrierChoiceControl : Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut anch := 0
  let mut slot := 0
  let mut slotOnly := 0
  let mut anchOnly := 0
  let mut floorF := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          let q := floorOf kind p
          match openTriple (mk outer kind p q op) with
          | none => pure ()
          | some (_, sp, s') =>
            match openColOf s' with
            | none => pure ()
            | some c =>
              rows := rows + 1
              let a := match Scanner.prevRealIdx? sp.tokens sp.tokens.size with
                | some k => sp.tokens[k]!.val.isNodeProperty
                | none => false
              let sl := hasCol sp c
              if a then anch := anch + 1
              if sl then slot := slot + 1
              if sl && !a then slotOnly := slotOnly + 1
              if a && !sl then anchOnly := anchOnly + 1
              if s'.simpleKey.possible == false then floorF := floorF + 1
  return (rows, anch, slot, slotOnly, anchOnly, floorF)

#guard carrierChoiceControl == (96, 24, 0, 0, 24, 96)

/-! ### §13a What the ride can carry, priced

`scripts/ride_price.py`, battery stage 22d.  Five rows read by elaboration at
the three arms that spend `drop_ride`, on a module with item 272's ring PAID —
the payment is applied and the probes carry no hypothesis and no hole — and
four censuses taken by arity flip:

* `slot` / `floor` — `ParkSlot s_prep s' 0` and `ParkFloor s_prep s' 0`, the
  two halves a carrier-holding frame would need.  Both are `B` at all three:
  with the ring paid the genesis is available outright, and the floor costs
  nothing at depth 0.
* `prop_sc` / `prop` — `ParkAnchor`'s own remaining field, at the state the
  step began with and at the landing's park.  `BOO` against `OOO`: the props
  arm can name the property, and only at `sc`, which is the park this family
  cannot open over — preprocessing's pushes sit between the two arrays, so
  `ParkCore.ofOpen`'s push equation holds at `s_prep` and fails at `sc`.
* `gated` — `FlowBaseAnchor (some s_prep) s' 0`, the frame argument itself.
  ~~`OOO` follows from `prop`.~~  Since item 285 it is asked as `slot_ride`
  builds it, the slot on `ParkChoice`'s right beside the floor: the `ParkAnchor`
  route on the left is `prop`'s question, and asked that way the column read
  `OOO` once more on the item-285 tree, `prop`'s refusal again.
* `ride` — the arity flip on `have drop_ride`: ~~FOUR terms spend the ride, all
  inside one declaration.  Three are the live arms' run-end halves and the
  fourth is~~ ONE term spends the ride since item 285, `opaque_resume`, which
  `pendingFlow` takes and which has no under-run to read a membership from.  The
  live arms' run-end halves take `slot_ride`.
* `add` / `swap` / `anchor` — three reshapes of `FlowBaseAnchor`'s `some` arm.
  Item 276 PAID the `choice` reshape, so each flip now prices UN-paying it:
  `add` puts the slot beside the anchor, `swap` the slot alone, `anchor`
  restores item 162's anchor-only arm — and each costs the same three
  declarations, `FlowBaseAnchor.gate`, `FlowBaseAnchor.transport`,
  `propsPark_open_gate` ~~(`add` reaches `gate` at two sites)~~ — `add` reaches
  `propsPark_open_gate` at two sites and `gate` at one, in the item-284 run and in
  item 285's.  Since item 285 each reshape also breaks `accum_flow_open_depth0`
  (`add` at two sites): `slot_ride` writes the `some` arm's term itself, where the
  props arm's gated frame calls `propsPark_open_gate`.
  ~~`slot=OOO` since item 276: `ParkSlot.ofOpen` takes `hrun`, which no arm holds
  (§15).~~  `slot=BBB` since item 284: the parks carry the slot face (§18), and
  `slotRun_of_dn` / `slotRun_of_offer` are `hrun` at all three arms.
* `transport` — the arity flip on `FlowBaseAnchor.transport`, the funnel every
  other carrier lemma is routed through.  Nine sites in seven declarations:
  that is the second wave any of the three reshapes pays, and it is the number
  the `anchor=2` of item 268 was taken without. -/

def expectedRidePrice : String :=
  "slot=BBB floor=BBB prop_sc=BOO prop=OOO gated=BBB ride=1/1 add=6/4 \
   swap=4/4 anchor=4/4 transport=9/7"

/-! ## §14 What the CLOSE can pay for a reshaped carrier (DOCS item 274)

§13 read what receives the carrier and recorded the next step: reshape
`FlowBaseAnchor`'s `some` arm, because the close is where the shape is decided.
The reshape's price is a count of declarations and §13 took it.  What it did
not take is the question this section is: **what the slot branch of
`FlowBaseAnchor.gate` can be closed with.**

`GateOf (some sc0)` is `danglingNodePos? sc0 = none` — a reading on the PARK's
state, which an anchor-carried frame relays from the close by an EQUATION
(`ParkAnchor.dangling_eq`).  A slot-carried frame has no equation to relay: its
two spends make a verdict FIRE, and which one fires is the `offersNodeSlot`
partition §6 measured.  Where §9.2 fires, the verdict the slot returns is the
one `GateOf` reads and it CONTRADICTS the close's own `h_closable`, so the gate
is discharged by ex falso.  Where §8.1 fires, the verdict the slot returns is
the other one, and nothing connects it to the goal.

So the reshape's real price is arithmetical, and these are the two numbers it
turns on. -/

/-- The two states of the depth-0 CLOSE — the step that takes the flow level
    from one back to zero — which are `FlowBaseAnchor.gate`'s own `s_bc` and
    `s_cl`.  Every cell of the family reaches one (§5's `deathShape`: the
    collection has closed at all 144 and dies three to five steps later). -/
private def closePair (input : String) :
    Option (Scanner.ScannerState × Scanner.ScannerState) := Id.run do
  let mut s := start input
  let mut fuel := input.utf8ByteSize * 4 + 8
  while fuel > 0 do
    fuel := fuel - 1
    match Scanner.scanNextToken s with
    | .error _ => return none
    | .ok none => return none
    | .ok (some s') =>
      if s.flowLevel == 1 && s'.flowLevel == 0 then return some (s, s')
      s := s'
  return none

/-- `(rows, §9.2 SILENT at the close, §9.2 FIRES there, §8.1 fires there, the
    gate's own verdict at the park, the slot spend's run-start premise, the
    anchor's field at the same park, the anchor's field where §8.1 fires)`.

    The second and third are the halves of the reshape.  On the third the slot
    branch closes by ex falso — `ParkSlot.dangling_fires` returns
    `danglingNodePos? s_cl = some …` against the close's `h_closable`, which
    says `none` — and on the second it does not, because the verdict that fires
    there is the fourth column's and `GateOf` does not read it.  The second and
    the fourth are the same cells counted two ways, which is what says the
    split is the `offersNodeSlot` one and not an artifact of where the walk
    stopped.

    The fifth is `GateOf (some s_prep)` itself, read at the park a gated ride
    would open over.  It is the column that decides whether gating the ride
    RETIRES the drop or merely moves it: a premise that holds at every cell of
    the family is satisfied rather than vacuous, and a route stated against it
    still has to produce the stream.

    The last two are the slot spend's own missing premise and the anchor's
    field, and they must sum to the rows: `propsRunStart` walks back exactly
    when the token in front of the open is a node property, so
    `hst : propsRunStart s_cl.tokens sc0.tokens.size = sc0.tokens.size` is the
    NEGATION of `ParkAnchor.parkProp`.  The two carriers of a `choice`
    disjunction are therefore complementary on the very premise the slot's
    spend needs.

    The eighth is the containment those two leave open: the cells the slot's
    §9.2 spend cannot reach for want of the run-start premise are exactly cells
    its §8.1 spend does reach, so ONE carrier still covers the family — but
    `propsRunStart` walks back at most two, so "props-headed implies offering"
    is a fact about this family and not a law, and the coverage is measured
    here rather than proved. -/
private def closeGate : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut silent := 0
  let mut dang := 0
  let mut floorFires := 0
  let mut gatePark := 0
  let mut runAt := 0
  let mut propAt := 0
  let mut propOffer := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            let inp := mk outer kind p q op
            match openTriple inp, closePair inp with
            | some (_, sp, _), some (_, scl) =>
              rows := rows + 1
              if (Scanner.danglingNodePos? scl).isNone then silent := silent + 1
              if (Scanner.danglingNodePos? scl).isSome then dang := dang + 1
              if (Scanner.underIndentedFlowValuePos? scl).isSome then
                floorFires := floorFires + 1
              if (Scanner.danglingNodePos? sp).isNone then
                gatePark := gatePark + 1
              if Scanner.propsRunStart scl.tokens sp.tokens.size
                  == sp.tokens.size then
                runAt := runAt + 1
              match Scanner.prevRealIdx? sp.tokens sp.tokens.size with
              | some k =>
                if sp.tokens[k]!.val.isNodeProperty then
                  propAt := propAt + 1
                  if (Scanner.underIndentedFlowValuePos? scl).isSome then
                    propOffer := propOffer + 1
              | none => pure ()
            | _, _ => pure ()
  return (rows, silent, dang, floorFires, gatePark, runAt, propAt,
    propOffer)

#guard closeGate == (144, 90, 54, 90, 144, 126, 18, 18)

/-- The same seven at the park's floor — §4's turnover, one column right, where
    the scanner ACCEPTS.

    Both verdicts are silent at every cell, which is what an accepted close
    looks like and what says columns two through four above report this
    family's deaths rather than the readings' defaults.  The last two split the
    other way from the family's: the anchor's field holds at twenty-four here
    and at eighteen there, and the slot spend's premise is its complement at
    both. -/
private def closeGateControl : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
    Id.run do
  let mut rows := 0
  let mut silent := 0
  let mut dang := 0
  let mut floorFires := 0
  let mut gatePark := 0
  let mut runAt := 0
  let mut propAt := 0
  let mut propOffer := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          let q := floorOf kind p
          let inp := mk outer kind p q op
          match openTriple inp, closePair inp with
          | some (_, sp, _), some (_, scl) =>
            rows := rows + 1
            if (Scanner.danglingNodePos? scl).isNone then silent := silent + 1
            if (Scanner.danglingNodePos? scl).isSome then dang := dang + 1
            if (Scanner.underIndentedFlowValuePos? scl).isSome then
              floorFires := floorFires + 1
            if (Scanner.danglingNodePos? sp).isNone then
              gatePark := gatePark + 1
            if Scanner.propsRunStart scl.tokens sp.tokens.size
                == sp.tokens.size then
              runAt := runAt + 1
            match Scanner.prevRealIdx? sp.tokens sp.tokens.size with
            | some k =>
              if sp.tokens[k]!.val.isNodeProperty then
                propAt := propAt + 1
                if (Scanner.underIndentedFlowValuePos? scl).isSome then
                  propOffer := propOffer + 1
            | none => pure ()
          | _, _ => pure ()
  return (rows, silent, dang, floorFires, gatePark, runAt, propAt,
    propOffer)

#guard closeGateControl == (96, 96, 0, 0, 96, 72, 24, 0)

/-! ### §14a What the close can pay, priced

`scripts/close_price.py`, battery stage 22e.  Five rows read by elaboration —
each a standalone probe of what `FlowBaseAnchor.gate`'s slot branch could be
closed with, all five in ONE insertion and one elaboration, each carrying a
null twin that must FAIL — and five censuses taken by flip:

* `anchor` — the control: `gate`'s existing proof restated over `ParkAnchor`.
  It must read `B`, or the four rows below are measuring the scaffolding.
* `bare` — the slot branch from the premises `gate` has today: `O`.  Neither
  slot spend applies without its offer premise and neither returns an equation,
  so there is nothing to relay the close's verdict to the park's.
* `nonoffer` — with §9.2's own two premises supplied: `B`, by ex falso.
  `ParkSlot.dangling_fires` returns `danglingNodePos? s_cl = some …` and the
  close's `h_closable` says `none`.
* `offer` — with §8.1's premise instead: `O`.  The verdict that fires there is
  the one `GateOf` does not read.
* `floor` — `offer` plus the close's own §8.1 reading: `B`, again by ex falso.
  So the missing datum is ONE reading on the close's own state, and item 268
  found no declaration holding it at either depth.

* `name` — the premise the slot branch needs, written over `sc0`, on `gate`
  and on `gate_of_close`: `OO`.  Neither declaration binds the park — both
  quantify `g : Option ScannerState` — so the premise cannot be STATED where
  the spend is written, let alone where it is applied.
* `wrap` — the same premise written over `g` (`∀ sc0, g = some sc0 → …`):
  `BB`, which is the payable phrasing.
* `gate` / `close` — who must WRITE one: `1/1` and `4/1`.  The premise on
  `gate` reaches `gate_of_close` alone; on `gate_of_close` it reaches
  `accum_step_flow` at four locations.
* `apps` — the same declaration renamed rather than re-arited, which breaks
  each application exactly once: `2`.  An arity census counts error LOCATIONS,
  so the four above are the TWO base closes reported twice each — the flow
  sequence end and the flow mapping end.
* `closable` — a second verdict added where the first one lands,
  `PendingNode.pendingContent`'s `h_closable`: **20 sites in 5 declarations**
  (`content_dispatch_routed`, `accum_content_on_pendingMapValue_indented`,
  `accum_content_pending`, `accum_step_flow`, `PendingNode.close_with_ssl`).
  That is the route's bill arriving from the consumer's side, and it is item
  268's `route=3` the way `3 + 7` was item 268's `anchor=2`. -/

def expectedClosePrice : String :=
  "anchor=B bare=O nonoffer=B offer=O floor=B name=OO wrap=BB gate=1/1 \
   close=4/1 closable=20/5 apps=2"


/-! ## §15 What the reshape paid, and what the slot owes (DOCS item 276)

Item 276 PAID the `choice` reshape: `FlowBaseAnchor`'s `some` arm names
`ParkChoice sc0 s d ∧ ParkFloor sc0 s d`, `GateOf (some sc0)` carries the
park's own `simpleKeyAllowed = false` beside §9.2's verdict, and `ParkSlot`
grew `slotRun` — the cell item 274's `closeGate` never enumerated, a park whose
`[96]` run is offered no slot, at which BOTH verdicts are silent at the close.
Three pins below re-read against the paid tree:

* `RIDE-PRICE`: `slot=OOO` — `ParkSlot.ofOpen` now takes `hrun`, and no arm
  holds it (`by assumption` stands where it would go, so the refusal names the
  datum) — and §16 measures that no arm CAN hold it, because the fact is false
  on accepted input; `gated=OOO` for the same reason plus `parkSka`; the three flips now
  price UN-paying the reshape (`anchor` restores item 162's arm) and
  `transport` re-reads the funnel over `ParkChoice`.
* `TRANSPORT-PRICE`: `genesis=OOO pay=OOO` — the same `hrun` at the same arms.
* `CLOSE-PRICE`: `anchor=B` — the control returns the pair now. -/

/-! ## §16 Why the slot the arms were told to supply was false, and what fixed it
    (DOCS items 277, 278)

Item 276 recorded a NEXT — *supply `slotRun` at the three arms* — and a supply
question: price a `PendingNode` field against an `accum_flow_open_depth0`
hypothesis.  Item 277 measured the fact instead of pricing a carrier for it,
and found it FALSE at the arms: `slotRun` asks that the `[96]` run in front of
the park's cursor be absent or *offered a node slot*, and `offersNodeSlot` then
counted only the three block indicators `:`, `?`, `-`.  A document root is
exactly where a run can stand with nothing but the start in front of it, so
`&x⏎[1]` — accepted, and correctly, since the property and its node may sit on
separate lines — read `slotRun = false`.  No carrier supplies a false fact.

Item 278 settled which of the two readings was wrong, by the measurement item
277 §5 named rather than by argument.  `offersNodeSlot` was under-approximating
its own criterion: `[185] l-bare-document` is `s-l+block-node(-1, block-in)`
just as `[186]` is the block entry's, so the stream and document starts offer
the following node a slot in the same sense the three indicators do.  Extending
it moves **no verdict** — censused over 1420 inputs of this family (700 with the
run behind a start, 720 with a block level on the indent stack so §8.1's second
conjunct can hold), the 402-case suite (869 passed / 0 failed / 151 skipped,
unchanged) and the whole Lean battery (21 suites, zero failures) — and it
breaks **no proof**.  The structural reason the reading moves and no verdict
does: §8.1's floor needs the open's column on the indent stack as well, and
nothing has opened a block level at the point where a run can sit behind a
start, so the two conditions are mutually exclusive.

The rows below are therefore the arms' supply, pinned at the open — and each
pins the PREDECESSOR beside the verdict, so a revert of `offersNodeSlot` breaks
them with the reason attached rather than with a bare `false`.

**The enumeration above is a floor and §17 is the set** (item 281): the
argument from the second root node does not reach a document SUFFIX, so
`documentEnd` was a non-offer standing in front of an accepted depth-0 open,
and the supply was unpaid again until it joined the three indicators and the
two starts. -/

/-- The index of the first depth-0 flow open, or `none`. -/
private def depth0OpenIdx (tokens : Array (Positioned YamlToken)) : Option Nat :=
  let rec go (i d : Nat) : Option Nat :=
    if i >= tokens.size then none
    else
      let t := tokens[i]!.val
      if t.isFlowOpen then (if d == 0 then some i else go (i + 1) (d + 1))
      else if t.isFlowClose then go (i + 1) (d - 1)
      else go (i + 1) d
  go 0 0

/-- `ParkSlot.slotRun` read at the depth-0 open of a scanned input, paired with
    the token the run stands behind.  The park is the state just before the open
    is pushed, so the park's cursor IS that index, and both the walk-back and the
    offer test read only below it. -/
private def slotRunAtOpen (input : String) : Option (Bool × String) :=
  match L4YAML.Scanner.scanFiltered input with
  | .error _ => none
  | .ok tokens =>
    match depth0OpenIdx tokens with
    | none => none
    | some o =>
      let st := L4YAML.Scanner.propsRunStart tokens o
      let pred := match L4YAML.Scanner.prevRealIdx? tokens st with
        | some j => toString (repr tokens[j]!.val)
        | none => "<none>"
      some (st == o || (match L4YAML.Scanner.prevRealIdx? tokens st with
        | some j => tokens[j]!.val.offersNodeSlot
        | none => false), pred)

-- the run stands behind a START, which is an offer since item 278
#guard slotRunAtOpen "&x\n[1]\n" == some (true, "L4YAML.YamlToken.streamStart")
#guard slotRunAtOpen "&x\n[1, 2]\n" == some (true, "L4YAML.YamlToken.streamStart")
#guard slotRunAtOpen "--- &x\n[1]\n" == some (true, "L4YAML.YamlToken.documentStart")
#guard slotRunAtOpen "---\n&x\n[1]\n" == some (true, "L4YAML.YamlToken.documentStart")
#guard slotRunAtOpen "---\n&x !t\n[1]\n" == some (true, "L4YAML.YamlToken.documentStart")
#guard slotRunAtOpen "---\na\n...\n---\n&x\n[1]\n"
  == some (true, "L4YAML.YamlToken.documentStart")

-- the three block indicators, which offered one all along
#guard slotRunAtOpen "k: &x [1]\n" == some (true, "L4YAML.YamlToken.value")
#guard slotRunAtOpen "- &x [1]\n" == some (true, "L4YAML.YamlToken.blockEntry")
#guard slotRunAtOpen "? &x [1]\n" == some (true, "L4YAML.YamlToken.key")

-- a park with no run at all holds it by the LEFT disjunct, whatever stands there
#guard slotRunAtOpen "[1]\n" == some (true, "L4YAML.YamlToken.streamStart")
#guard slotRunAtOpen "k: [1]\n" == some (true, "L4YAML.YamlToken.value")

-- and every OTHER shape that would put a non-offer in front of the run is a
-- second root node in one document, which §9.2 refuses — with the document
-- SUFFIX the one exception, which does not continue a document but ENDS one
-- (item 281, §17: the kinds are censused there rather than argued from here)
#guard slotRunAtOpen "---\nk:\n  j: a\n&x\n[1]\n" == none
#guard slotRunAtOpen "---\n- a\n&x\n[1]\n" == none
#guard slotRunAtOpen "---\nk: a\n&x\n[1]\n" == none
#guard slotRunAtOpen "---\n[a]\n&x\n[1]\n" == none
#guard slotRunAtOpen "k:\n  b:\n    &x\n  [1]\n" == none
#guard slotRunAtOpen "k:\n  -\n[1]\n" == none

/-! ## §17 The offer set censused, and the carrier question answered by the
    states (DOCS item 281)

§16 extended `offersNodeSlot` with the two STARTS and enumerated the rest from
one refusal: every other non-offering predecessor is a second root node in one
document, which §9.2 refuses.  **That argument does not reach the document
SUFFIX.**  A `...` does not continue a document, it ENDS one, so what stands
after it is a fresh `[185] l-bare-document` and a `[96]` run in front of a
depth-0 open there is that document's root-node properties — the same slot
`---` offers, by the same production.

So `a⏎...⏎&x⏎[1]` was accepted with `slotRun = false`, in seven shapes, and the
supply item 278 paid was unpaid again.  Item 278's enumeration was a FLOOR, for
the same reason a one-round flip census is.

The rows below are the census that argument should have been: one `YamlToken`
kind per row, each naming either an accepted witness whose first depth-0 open
carries that kind as its run's predecessor, or the refusal that makes the kind
unreachable in that position.  Six of the 23 kinds cannot be the predecessor at
all and are named here rather than left to a blank: `placeholder` is what
`prevRealIdx?` walks past by construction, `comment` is what `scanFiltered`
filters, `streamEnd` has nothing after it, and `flowEntry` /
`flowSequenceStart` / `flowMappingStart` stand only inside a collection, where
the open they precede is at depth ≥ 1 and this reading does not apply.  Two
more REDUCE to an offer rather than being reachable: `blockSequenceStart` and
`blockMappingStart` are emitted before the indicator that opens the entry, so
the predecessor a run sees is that indicator, and their rows pin the reduction.

**`dispatchedSlot` is the supply itself**, and it is the reading to re-take
before any future carrier is priced: over the same corpus it counts the inputs
that DISPATCH a depth-0 open and, of those, the ones whose park reads
`slotRun = false`.  The third number is what items 277 and 281 each found
non-zero.

**`carrierStates` answers the question item 279 left open** — a `PendingNode`
field against an `accum_flow_open_depth0` hypothesis — by reading the states
each candidate would have to hold at, which is cheaper than pricing either:

* a LOOP INVARIANT is false.  The fact would have to be re-established at every
  scanner step, the way `scanLoop_grammar_prod`'s induction re-establishes
  `h_kbc`, `h_base` and `h_mono` through their own `scanNextToken_preserves_*`.
  The second column counts states where the predicate is false, the next step
  SUCCEEDS, and the input is accepted — `[a, &x b]` is one — so no
  unconditional preservation lemma exists.  The third counts the same at depth
  0, so guarding it on `flowLevel = 0` as `h_pending` itself is guarded does
  not save it either.
* a `PendingNode` FIELD is false at a park its own producer must admit.  The
  fourth column counts parks reading `slotRun = false` whose step's own §9.2
  and §8.1 readings are both SILENT and whose step succeeds — exactly the
  hypotheses a producer holds (items 157 and 275 threaded both) — so the
  field's obligation covers a state no producer can pay at.
* a HYPOTHESIS has no supplier but the loop.  Its ring chain is
  `accum_step_flow` (2 applications) → `scanNextToken_accum_step` (1) →
  `scanLoop_grammar_prod` (1), and the last is the induction that would need
  the invariant the first bullet refutes.

What that leaves is not a carrier.  The fact is true exactly where the open is
DISPATCHED, and what decides dispatch is §9.2's and §8.1's readings at that
step — `h_dn` and `h_fv`, hypotheses of the arm since items 157 and 275.  Where
the predicate fails and an open follows, `h_dn` FIRES: `---⏎k: a⏎&x⏎[1]` never
reaches the arm at all, and the last two rows of `parkFace` pin that against
the silent park beside it. -/

/-- `ParkSlot.slotRun` read at index `i` of a token array: the `[96]` run in
    front of `i` is absent, or the real token behind that run offers a node
    slot.  §16's `slotRunAtOpen` is this at the open; the sweeps below need it
    at an arbitrary cursor. -/
private def slotRunAtIdx (tokens : Array (Positioned YamlToken)) (i : Nat) : Bool :=
  let st := Scanner.propsRunStart tokens i
  st == i || (match Scanner.prevRealIdx? tokens st with
              | some j => tokens[j]!.val.offersNodeSlot
              | none => false)

/-- One witness per kind: the input, and the kind it is meant to put in front
    of the run.  A row whose reading names a different kind is a REDUCTION and
    §17's prose says which; a row that reads `none` is a refusal. -/
private def kindWitness : List (String × String) :=
  [ ("streamStart",        "&x\n[1]\n"),
    ("documentStart",      "---\n&x\n[1]\n"),
    ("documentEnd",        "a\n...\n&x\n[1]\n"),
    ("value",              "k: &x [1]\n"),
    ("key",                "? &x [1]\n"),
    ("blockEntry",         "- &x [1]\n"),
    ("blockSequenceStart", "- &x [1]\n"),
    ("blockMappingStart",  "k: &x [1]\n"),
    ("scalar",             "---\nk: a\n&x\n[1]\n"),
    ("alias",              "&p q\n---\n*p\n&x\n[1]\n"),
    ("blockEnd",           "---\nk:\n  v\n&x\n[1]\n"),
    ("flowSequenceEnd",    "[a]\n&x\n[1]\n"),
    ("flowMappingEnd",     "{a: b}\n&x\n[1]\n"),
    ("versionDirective",   "%YAML 1.2\n&x\n[1]\n"),
    ("tagDirective",       "%TAG !e! tag:x\n&x\n[1]\n"),
    ("anchor",             "&a !t &b\n[1]\n"),
    ("tag",                "!t1 !t2 &a\n[1]\n") ]

/-- `(kinds probed, kinds reaching an accepted depth-0 open, of those whose
    predecessor OFFERS a slot)`.

    The second and third must agree, and that agreement IS the arms' supply: a
    kind that reaches the position and offers nothing is a `slotRun` no carrier
    can deliver, which is what items 277 and 281 each found one of. -/
private def kindCensus : Nat × Nat × Nat := Id.run do
  let mut n := 0
  let mut reach := 0
  let mut offered := 0
  for (_, input) in kindWitness do
    n := n + 1
    match slotRunAtOpen input with
    | none => pure ()
    | some (sr, _) =>
      reach := reach + 1
      if sr then offered := offered + 1
  return (n, reach, offered)

#guard kindCensus == (17, 8, 8)

-- the suffix: item 281's hole, now an offer, in the seven shapes that read it
#guard slotRunAtOpen "a\n...\n&x\n[1]\n" == some (true, "L4YAML.YamlToken.documentEnd")
#guard slotRunAtOpen "a\n...\n  &x\n  [1]\n" == some (true, "L4YAML.YamlToken.documentEnd")
#guard slotRunAtOpen "a\n...\n...\n&x\n[1]\n" == some (true, "L4YAML.YamlToken.documentEnd")
#guard slotRunAtOpen "a\n...\n# c\n&x\n[1]\n" == some (true, "L4YAML.YamlToken.documentEnd")
#guard slotRunAtOpen "a\n...\n!t &x\n[1]\n" == some (true, "L4YAML.YamlToken.documentEnd")
#guard slotRunAtOpen "k: v\n...\n&x\n{p: q}\n" == some (true, "L4YAML.YamlToken.documentEnd")
#guard slotRunAtOpen "- a\n...\n&x\n[1]\n" == some (true, "L4YAML.YamlToken.documentEnd")

-- the two REDUCTIONS: a collection's own start is never the predecessor
#guard slotRunAtOpen "- &x [1]\n" == some (true, "L4YAML.YamlToken.blockEntry")
#guard slotRunAtOpen "k: &x [1]\n" == some (true, "L4YAML.YamlToken.value")

-- the nine kinds the position does not reach, each by the refusal that stops it
#guard slotRunAtOpen "---\nk: a\n&x\n[1]\n" == none
#guard slotRunAtOpen "&p q\n---\n*p\n&x\n[1]\n" == none
#guard slotRunAtOpen "---\nk:\n  v\n&x\n[1]\n" == none
#guard slotRunAtOpen "[a]\n&x\n[1]\n" == none
#guard slotRunAtOpen "{a: b}\n&x\n[1]\n" == none
#guard slotRunAtOpen "%YAML 1.2\n&x\n[1]\n" == none
#guard slotRunAtOpen "%TAG !e! tag:x\n&x\n[1]\n" == none
#guard slotRunAtOpen "&a !t &b\n[1]\n" == none
#guard slotRunAtOpen "!t1 !t2 &a\n[1]\n" == none

/-- The corpus the three readings below share: the eight kinds that reach the
    position, the nine that do not, the three indicators' own under-indented
    landings, and four runs that are absent rather than unoffered. -/
private def slotCorpus : List String :=
  [ "&x\n[1]\n", "---\n&x\n[1]\n", "k: &x [1]\n", "- &x [1]\n", "? &x [1]\n",
    "a\n...\n&x\n[1]\n", "a\n...\n  &x\n  [1]\n", "a\n...\n...\n&x\n[1]\n",
    "a\n...\n# c\n&x\n[1]\n", "a\n...\n!t &x\n[1]\n", "k: v\n...\n&x\n{p: q}\n",
    "- a\n...\n&x\n[1]\n", "---\nk: a\n&x\n[1]\n", "&p q\n---\n*p\n&x\n[1]\n",
    "---\nk:\n  v\n&x\n[1]\n", "[a]\n&x\n[1]\n", "{a: b}\n&x\n[1]\n",
    "%YAML 1.2\n&x\n[1]\n", "&a !t &b\n[1]\n", "!t1 !t2 &a\n[1]\n",
    "k:\n  &x\n  [1]\n", "- \n  &x\n  [1]\n", "?\n  &x\n  [1]\n",
    "[1]\n", "k: [1]\n", "a\n...\n[1]\n", "a\n...\n{p: q}\n" ]

/-- `(inputs, inputs that DISPATCH a depth-0 flow open, of those: parks reading
    `slotRun = false`)`.

    The park is the state the open is dispatched from, after preprocessing —
    the array `accum_flow_open_depth0`'s arm reads is `s_prep.tokens` — so this
    is the arms' supply at the one place it has to hold.  The third number must
    be ZERO; items 277 and 281 each read it non-zero, and each time the repair
    was the predicate rather than a carrier for it. -/
private def dispatchedSlot : Nat × Nat × Nat := Id.run do
  let mut n := 0
  let mut disp := 0
  let mut bad := 0
  for input in slotCorpus do
    n := n + 1
    let mut s := start input
    let mut fuel := input.utf8ByteSize * 4 + 8
    let mut seen := false
    let mut sawBad := false
    while fuel > 0 && !seen do
      fuel := fuel - 1
      match Scanner.scanNextToken s with
      | .error _ => seen := true
      | .ok none => seen := true
      | .ok (some s') =>
        if s.flowLevel == 0 && s'.flowLevel == 1 then
          seen := true
          disp := disp + 1
          match Scanner.scanNextToken_preprocess s with
          | .ok (some (s_prep, _)) =>
            if !slotRunAtIdx s_prep.tokens s_prep.tokens.size then sawBad := true
          | _ => if !slotRunAtIdx s.tokens s.tokens.size then sawBad := true
        else s := s'
    if sawBad then bad := bad + 1
  return (n, disp, bad)

#guard dispatchedSlot == (27, 21, 0)

/-- The shapes a carrier would have to hold at: a props run inside a flow
    collection, and one standing after a completed block node at depth 0. -/
private def carrierCorpus : List String :=
  [ "[a, &x b]\n", "{a: b, &x c}\n", "[a, &x b, c]\n", "[[a], &x b]\n",
    "k: [a, &x b]\n", "- [a, &x b]\n", "[a, &x !t b]\n",
    "---\nk: a\n&x b\n", "---\nk:\n  v\n&x b\n", "---\n- a\n&x b\n",
    "a\n...\n&x b\n", "&x\n[1]\n", "k: &x [1]\n" ]

/-- `(inputs, false-then-step at depth ≥ 1 on an ACCEPTED input, false-then-step
    at depth 0, parks reading false whose step's own §9.2 AND §8.1 readings are
    both silent and whose step succeeds)`.

    Columns two and three refute a loop invariant — unguarded and
    `flowLevel = 0`-guarded — and column four refutes a `PendingNode` field,
    because those are exactly the hypotheses a producer of the park holds. -/
private def carrierStates : Nat × Nat × Nat × Nat := Id.run do
  let mut n := 0
  let mut deep := 0
  let mut flat := 0
  let mut silent := 0
  for input in carrierCorpus do
    n := n + 1
    let mut s := start input
    let mut fuel := input.utf8ByteSize * 4 + 8
    let mut sawDeep := false
    let mut sawFlat := false
    let mut sawSilent := false
    let mut ok := false
    while fuel > 0 do
      fuel := fuel - 1
      let isBad := !slotRunAtIdx s.tokens s.tokens.size
      let isFlat := s.flowLevel == 0
      match Scanner.scanNextToken s with
      | .error _ => fuel := 0
      | .ok none =>
        ok := s.flowLevel == 0
          && (Scanner.scanLoop_checkDanglingNode s).isOk
          && (Scanner.scanLoop_checkFlowValueIndent s).isOk
        fuel := 0
      | .ok (some s') =>
        if isBad then
          if isFlat then sawFlat := true else sawDeep := true
          match Scanner.scanNextToken_preprocess s with
          | .ok (some (s_prep, _)) =>
            if isFlat
                && (Scanner.scanNextToken_checkDanglingNode s s_prep).isOk
                && (Scanner.scanNextToken_checkFlowValueIndent s s_prep).isOk then
              sawSilent := true
          | _ => pure ()
        s := s'
    if sawDeep && ok then deep := deep + 1
    if sawFlat then flat := flat + 1
    if sawSilent then silent := silent + 1
  return (n, deep, flat, silent)

#guard carrierStates == (13, 7, 3, 3)

/-- `(step, the park's last real token, `slotRun`, §9.2 at that step, §8.1 at
    that step, the step succeeded)` — the producer's own face at one park.

    The first row is the park a `PendingNode` field cannot be paid at, and the
    second is why no carrier is owed for it: one token later, with an open
    following instead of a scalar, §9.2 FIRES and the arm is never reached. -/
private def parkFace (input : String) (upto : Nat) :
    Nat × String × Bool × String × String × Bool := Id.run do
  let mut s := start input
  let mut i : Nat := 0
  while i < upto do
    match Scanner.scanNextToken s with
    | .ok (some s') => s := s'; i := i + 1
    | _ => i := upto
  let lastTok := match Scanner.prevRealIdx? s.tokens s.tokens.size with
    | some j => toString (repr s.tokens[j]!.val)
    | none => "<none>"
  let (dn, fv) := match Scanner.scanNextToken_preprocess s with
    | .ok (some (s_prep, _)) =>
      ((match Scanner.scanNextToken_checkDanglingNode s s_prep with
        | .ok _ => "silent"
        | .error _ => "FIRES"),
       (match Scanner.scanNextToken_checkFlowValueIndent s s_prep with
        | .ok _ => "silent"
        | .error _ => "FIRES"))
    | _ => ("no-preprocess", "no-preprocess")
  let stepped := match Scanner.scanNextToken s with
    | .ok (some _) => true
    | _ => false
  return (i, lastTok, slotRunAtIdx s.tokens s.tokens.size, dn, fv, stepped)

#guard parkFace "---\nk: a\n&x b\n" 5
  == (5, "L4YAML.YamlToken.anchor \"x\"", false, "silent", "silent", true)
#guard parkFace "---\nk: a\n&x\n[1]\n" 5
  == (5, "L4YAML.YamlToken.anchor \"x\"", false, "FIRES", "silent", false)
#guard parkFace "a\n...\n&x\n[1]\n" 3
  == (3, "L4YAML.YamlToken.anchor \"x\"", true, "silent", "silent", true)

/-! ## §18 The bridge item 281 ordered, measured before it is written (DOCS item 283)

Item 281 §7 ordered ONE lemma: `slotRun_of_dn`, from `scanNextToken_checkDanglingNode
sc s_prep = .ok ()` plus the park's own facts to `ParkSlot`'s payload at `s_prep`,
and said to price it "against §9.2's own reading, not as a carrier".  §10's rule
is that a NEXT naming a construction carries a consumer probe before anything is
spent on it, so this section is that probe, and it refutes the construction as
named while confirming the fact it was meant to deliver.

**The counter-model.**  `slotCounterModel` scans `k: a⏎&x⏎[1]` to the park after
`&x` and then deletes the mapping's level from the indent stack, leaving the
sentinel alone.  Every TOKEN-side hypothesis `accum_flow_open_depth0`'s props arm
holds is unchanged by that edit — the trailing run, `simpleKeyAllowed = false`,
`needIndentCheck = false`, `LastTokenReal`, `IndentFloor` at index 0, the
sentinel base — and the edited state preprocesses to the same landing, where §9.2,
§8.1 and the bare-document check are all SILENT and `slotRun` is FALSE, at the
park and at `s_prep` alike.  So no lemma over those hypotheses derives the
payload: the datum that excluded a scalar predecessor was the indent stack, and
it was consumed one step EARLIER, by `scanNextToken_checkBareDocument` at the
run's own landing (`k: a⏎&x`: the run at the mapping's column is a sibling and
scans; `a⏎&x`, with no level at 0, is refused there).  What is left to the arm
are the GRAMMAR-side fields — `h_route`, `h_key`, `h_sep`, `h_run`, `h_kslot` —
and spending one of those on a token fact is the transport this row does not
pay.

**The census.**  `slotSupply` walks 4 752 generated inputs (31 prefixes × 6 runs ×
6 separators × 3 opens, with the §17 corpora's shapes among them) and reads
three things at every depth-0 props park: whether the gated face
`danglingNodePos? s = none → slotRun s` holds — it does at all 5 562, with the
predecessor OFFERING at 3 078 and the run's column standing on an open level at
the other 2 484, and no park paid by the excess clause or by nothing — and, at
every depth-0 open dispatched from such a park across a break, whether
`slotRun` holds at `s_prep`: it does at all 1 068.  Of those, 108 land at or
below the park's incoming floor (the half the three rides are taken on); 12 emit
a `blockEnd`, which makes the payload's first disjunct free, and the other 96
have a predecessor that offers — `-`, `?` or `:` — and nothing else.

**So the fact is true where it is needed and the arm cannot see why.**  The price
is a FIELD on `pendingProps`, GATED exactly as `h_route` is:
`danglingNodePos? sc = none → sc.indents.size ≤ 1 ∨ slotRun sc`.  It is not the
field item 281 §5 refuted (`slotRun` unconditionally, false at `---⏎k: a⏎&x b`),
because the gate is false there; the `size ≤ 1` escape is for the stream-start
run, where no level exists and the arm's own under-run is vacuous
(`IndentFloor` at the base floors the index at 0 and `j < 0` is the refutation).
Every producer can pay it from a fact it already holds or from the last real
token it just pushed, and the per-producer bill is DOCS item 283's. -/

/-- `k: a⏎&x⏎[1]` at the park after `&x`, read twice: as scanned, and with the
    mapping's level deleted from the stack.  Per reading: `(danglingNodePos?` is
    `none`, `slotRun`, the predecessor)`; for the edited state also the three
    checks at the next landing and `slotRun` at `s_prep`. -/
private def slotCounterModel :
    (Bool × Bool × String) × (Bool × Bool × String × Bool × Bool × Bool × Bool) := Id.run do
  let mut s := start "k: a\n&x\n[1]\n"
  for _ in [0:6] do
    match Scanner.scanNextToken s with
    | .ok (some s') => s := s'
    | _ => pure ()
  let pred (st : Scanner.ScannerState) : String :=
    match Scanner.prevRealIdx? st.tokens (Scanner.propsRunStart st.tokens st.tokens.size) with
    | some j => toString (repr st.tokens[j]!.val)
    | none => "<none>"
  let face (st : Scanner.ScannerState) : Bool × Bool × String :=
    ((Scanner.danglingNodePos? st).isNone, slotRunAtIdx st.tokens st.tokens.size, pred st)
  let t := { s with indents := #[{ column := -1, isSequence := false }] }
  let checks := match Scanner.scanNextToken_preprocess t with
    | .ok (some (tp, _)) =>
      ((Scanner.scanNextToken_checkDanglingNode t tp).isOk,
       (Scanner.scanNextToken_checkFlowValueIndent t tp).isOk,
       (Scanner.scanNextToken_checkBareDocument tp).isOk,
       slotRunAtIdx tp.tokens tp.tokens.size)
    | _ => (false, false, false, false)
  let (a, b, c) := face t
  return (face s, (a, b, c, checks.1, checks.2.1, checks.2.2.1, checks.2.2.2))

-- as scanned: §9.2 reads the run at the mapping's column (`some`), slotRun false
-- edited: §9.2 reads nothing, slotRun false, and at the landing all three checks
-- are silent with slotRun still false — the arm's token-side view, exactly
#guard slotCounterModel ==
  ((false, false, "L4YAML.YamlToken.scalar \"a\" (L4YAML.ScalarStyle.plain)"),
   (true, false, "L4YAML.YamlToken.scalar \"a\" (L4YAML.ScalarStyle.plain)",
    true, true, true, false))

private def supplyPrefixes : List String :=
  [ "", "---\n", "a\n...\n", "a\n...\n---\n", "k:\n  ", "k: v\n", "k: v\n  ", "-\n  ", "- a\n",
    "- a\n  ", "k:\n  j:\n    v\n", "k:\n  j:\n    v\n  ", "k:\n  j: a\n  ", "? \n  ", "? a\n: ",
    "[a]\n", "{a: b}\n", "%YAML 1.2\n", "%YAML 1.2\n---\n", "k: ", "- ", "? ", "--- ",
    "k:\n  - ", "k:\n  - a\n  ", "k:\n  - a\n", "a: 1\nb: 2\n", "a: 1\n", "- - a\n  ", "- - a\n",
    "\"a\" ", "[a] ", "{a: b} ", "&p q\n---\n*p ", "&p q\n---\n*p\n", "k: \"v\" ", "k: [v] ", "- [v] ",
    "k:\n  j: a\n", "k:\n  j:\n    v\n", "? a\n", "? a\n: b\n", "--- a\n...\n", "a\n...\n...\n" ]
private def supplyRuns : List String := ["&x", "!t", "&x !t", "!t &x", "&a !t &b", "&x\n!t"]
private def supplySeps : List String := [" ", "\n", "\n ", "\n  ", "\n   ", "\n    "]
private def supplyOpens : List String := ["[1]", "{p: q}", "[1, 2]"]

private def supplyCorpus : List String := Id.run do
  let mut out := []
  for p in supplyPrefixes do
    for r in supplyRuns do
      for sp in supplySeps do
        for o in supplyOpens do
          out := (p ++ r ++ sp ++ o ++ "\n") :: out
  return out

/-- the park has a trailing `[96]` run -/
private def hasRun (s : Scanner.ScannerState) : Bool :=
  match Scanner.prevRealIdx? s.tokens s.tokens.size with
  | some i => s.tokens[i]!.val.isNodeProperty
  | none => false

/-- the run's START column stands on the indent stack — §9.2's first clause -/
private def runColOnStack (s : Scanner.ScannerState) : Bool :=
  let st := Scanner.propsRunStart s.tokens s.tokens.size
  s.indents.any (fun e => e.column == (s.tokens[st]!.pos.col : Int))

/-- `(inputs, accepted, depth-0 props parks, parks where the gated face FAILS,
    parks paid by an OFFER, parks paid by the run's column on the stack, parks
    paid by the excess clause, depth-0 opens dispatched from a props park across a
    break, of those with `slotRun` FALSE at `s_prep`, of those landing at or
    below the incoming floor, of THOSE with no `blockEnd` emitted, and the
    predecessor kinds seen there)`. -/
private def slotSupply :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × List String := Id.run do
  let mut inputs := 0; let mut accepted := 0; let mut parks := 0; let mut fails := 0
  let mut byOffer := 0; let mut byStack := 0; let mut byExcess := 0
  let mut dispatched := 0; let mut viol := 0; let mut atOrBelow := 0; let mut noPop := 0
  let mut preds : List String := []
  for input in supplyCorpus do
    inputs := inputs + 1
    let mut s := start input
    let mut fuel := input.utf8ByteSize * 4 + 8
    let mut ok := false
    while fuel > 0 do
      fuel := fuel - 1
      let park := s.flowLevel == 0 && hasRun s
      if park then
        parks := parks + 1
        let offer := slotRunAtIdx s.tokens s.tokens.size
        let onStack := runColOnStack s
        let exc := (Scanner.crossedPropsExcessIdx? s.tokens).isSome
        -- the gated face: §9.2 silent at the park → the slot is offered
        if (Scanner.danglingNodePos? s).isNone && !offer then fails := fails + 1
        if offer then byOffer := byOffer + 1
        else if onStack then byStack := byStack + 1
        else if exc then byExcess := byExcess + 1
      match Scanner.scanNextToken s with
      | .error _ => fuel := 0
      | .ok none =>
        ok := s.flowLevel == 0 && (Scanner.scanLoop_checkDanglingNode s).isOk
          && (Scanner.scanLoop_checkFlowValueIndent s).isOk
        fuel := 0
      | .ok (some s') =>
        if park && s'.flowLevel == 1 then
          match Scanner.scanNextToken_preprocess s with
          | .ok (some (sp, _)) =>
            if sp.simpleKeyAllowed then
              dispatched := dispatched + 1
              if !slotRunAtIdx sp.tokens sp.tokens.size then viol := viol + 1
              if (sp.col : Int) ≤ s.currentIndent then
                atOrBelow := atOrBelow + 1
                let pop := (sp.tokens.extract s.tokens.size sp.tokens.size).any
                  (fun q => q.val == .blockEnd)
                if !pop then
                  noPop := noPop + 1
                  let pk := match Scanner.prevRealIdx? s.tokens
                      (Scanner.propsRunStart s.tokens s.tokens.size) with
                    | some j => toString (repr s.tokens[j]!.val)
                    | none => "<none>"
                  if !preds.contains pk then preds := preds ++ [pk]
          | _ => pure ()
        s := s'
    if ok then accepted := accepted + 1
  return (inputs, accepted, parks, fails, byOffer, byStack, byExcess,
          dispatched, viol, atOrBelow, noPop, preds)

#guard slotSupply ==
  (4752, 1276, 5562, 0, 3078, 2484, 0, 1068, 0, 108, 96,
   ["L4YAML.YamlToken.blockEntry", "L4YAML.YamlToken.key", "L4YAML.YamlToken.value"])

end L4YAML.Tests.Guards.ScannerFlowOpenUnderRun

end Blanket
