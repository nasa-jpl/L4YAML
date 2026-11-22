import L4YAML.Scanner.Scanner

/-!
# Is a DECLINE ever REACHED?  (item 219)

[Item 218](../DOCS.md) cut the runtime question behind the `∨ True` idiom from
99 splits to **nineteen named lemmas** — `RelaySupplyCensus.expectedDeclineWriters`,
the lemmas whose proof terms actually WRITE a `Or.inr trivial` into a park's
optional field — and recorded the instrument the remainder wants:

> the candidate predicate evaluated at every state the scan visits over the 402
> `in.yaml` leaves, as an over-approximation, run before the runtime is touched.

This module is that instrument, and a second one beside it, because the first
alone cannot answer the question it was asked.

## What a candidate predicate is here

For each of the nineteen, the conjunction of its OWN hypotheses that are
decidable at the scanner state — evaluated by calling the runtime expressions
the hypothesis list already names (`scanNextToken_preprocess`,
`scanNextToken_dispatch*`, `scanNextToken_checkBareDocument`,
`scanNextToken_checkDanglingNode`, `sc.simpleKeyAllowed`, `sc.allowDirectives`,
`sc.needIndentCheck`, `sc.explicitKeyLine`, `sc.currentIndent`,
`sc.simpleKey.*`, `trailingPropertyRunOnLine`, `lastRealToken?`), never a
paraphrase of them.  `ScannerSurfCorr.col_eq` (`sp.col = sc.col`) is what lets a
`sp_scan.col` hypothesis be read at the runtime state, so `sp_scan.col = n + 1`
fixes a park's index at `sc.col - 1`.

Each row is restricted further by the union of its CALLERS' park classes, the
call graph having been read out of the environment rather than out of a grep.

The conjunction is NECESSARY for the lemma's site to be entered, so a predicate
that never fires says the site is unreached, and one that fires says nothing.
`Tests/Guards/Proofs/DeclineReachCorpus.lean` PROVES that necessity for seven of
the nine park classes; the two it cannot are named there.

## What the two censuses say

* **The corpus** (402 `in.yaml` leaves, `run`): every one of the nineteen is
  reached, each on at least two leaves the scanner ACCEPTS.  The corpus retires
  nothing.
* **The domain** (50 653 machine-enumerated three-line programs, `domainCensus`):
  the same nineteen, all reached, all on accepted programs.

And the reason both are here: the ONE park class the corpus reads as empty at a
block dispatch — `pendingDocEnd`, visited eleven times over ten leaves and never
handed a `-`/`?`/`:` — is reached **1 633** times over the domain, and by the
four-step accepted input `a⏎...⏎- b` (`controls`).  **A corpus zero is a
coverage report, not a refutation**: 402 files are a sample of the language, and
an arm they miss is not an arm nothing reaches.  The instrument that can retire
an arm is the enumerated domain (item 204's shape), not the corpus (item 182's).

## Running it

```
lake exe declinereach                      # controls + domain census
lake exe declinereach <yaml-test-suite>/data   # + the corpus census
```
Exits 1 on any disagreement with the pins below.
-/

namespace Tests.DeclineReachCensus

open L4YAML
open L4YAML.Scanner

/-! ## The decidable readings of the park constructors' `sc` fields -/

/-- `IndentFloor sc n` (`Proofs/Scanner/PreprocessIndentStable.lean`). -/
def floorB (sc : ScannerState) (n : Nat) : Bool :=
  !sc.needIndentCheck && n ≤ (max 0 (sc.currentIndent + 1)).toNat

/-- `LastTokenReal sc.tokens` (`Proofs/Scanner/FlowAdjacency.lean`). -/
def lastRealB (ts : Array (Positioned YamlToken)) : Bool :=
  0 < ts.size && ts[ts.size - 1]!.val != YamlToken.placeholder

/-- The three stamp wrappers' shared premise, negated — `colon_open_map.h_src`
    and `compact_open_map.h_src`'s consequent, read at the DISPATCH state.  The
    positive form is `CompactRouteCensus.stampSrcUndecided`. -/
def srcDecided (s : ScannerState) : Bool :=
  s.explicitKeyLine == none ||
  (scanValueClearKey s).simpleKey.possible == true ||
  (s.col : Int) != s.explicitKeyCol

/-- `noPending`: `h_col`, `h_arm`, `h_noek`, `h_ntop`. -/
def pNoPending (sc : ScannerState) : Bool :=
  (sc.col == 0 || sc.inFlow) && (sc.simpleKeyAllowed || sc.inFlow) &&
  (sc.inFlow || sc.explicitKeyLine == none) && (sc.inFlow || sc.currentIndent < 0)

/-- `pendingContent` AND `pendingBlockContent`: `h_arm`, `h_nodir`, `h_nic0`.
    The two constructors have the same `sc` footprint, so no state-level census
    can separate them, and the two rows below are equal by construction. -/
def pContentish (sc : ScannerState) : Bool :=
  ((sc.simpleKeyAllowed && !sc.simpleKey.possible) || 0 < sc.col) &&
  !sc.allowDirectives && (sc.col != 0 || sc.needIndentCheck)

/-- `pendingProps`: `h_nic`, `h_real`, `h_ska`, `h_nodir`, and the run.
    **Incomplete, found at item 220**: the constructor also carries
    `h_col0 : 0 < sp_scan.col`, which `ScannerSurfCorr.col_eq` delivers at the
    runtime state and this reading drops.  Adding it moves no count (4 550
    either way, none at column 0) and turns two measured containments into
    theorems — see `Tests.DeclineArmCensus.pPropsT`.  The reading is left as it
    stands so item 219's pins keep meaning what they meant.  The run —
    `h_run : PropsRun n .flowOut ha ht sp_p sp_scan` carries at least one
    property, so `h_anchor`/`h_tag` make the trailing run on `sc.line` non-empty.
    **The run conjunct is a READING** (`PropsRun → ha = true ∨ ht = true` is not
    in the library); the other four are proved in `DeclineReachCorpus`. -/
def pProps (sc : ScannerState) : Bool :=
  !sc.needIndentCheck && lastRealB sc.tokens && !sc.simpleKeyAllowed &&
  !sc.allowDirectives && !(trailingPropertyRunOnLine sc.tokens sc.line).isEmpty

/-- `pendingDocEnd`: `h_arm`, `h_nic0`, and `h_marker : SCDocumentEnd sp_block
    sp_scan` — the `...` stands immediately behind the park, so the last real
    token is the marker, on the park's own line.  **The marker conjunct is a
    READING**, and it is the one asymmetry this census found: `pendingDocStart`
    carries its token-level witness as a field (`h_marker_tail`) and
    `pendingDocEnd` carries only the surface-grammar one, so the twin park
    bridges and this one does not. -/
def pDocEnd (sc : ScannerState) : Bool :=
  (sc.simpleKeyAllowed || 0 < sc.col) && (sc.col != 0 || sc.needIndentCheck) &&
  (match lastRealToken? sc.tokens with
   | some t => t.val == YamlToken.documentEnd && t.pos.line == sc.line
   | none => false)

/-- `pendingDocStart`: `h_nic`, `h_real`, `h_marker_tail`, `h_arm`, `h_nodir`,
    `h_nic0`. -/
def pDocStart (sc : ScannerState) : Bool :=
  !sc.needIndentCheck && lastRealB sc.tokens &&
  (match lastRealToken? sc.tokens with
   | some t => t.val == YamlToken.documentStart && t.pos.line == sc.line
   | none => false) &&
  (sc.simpleKeyAllowed || 0 < sc.col) && !sc.allowDirectives &&
  (sc.col != 0 || sc.needIndentCheck)

/-- `pendingFlow` — β.5's own escape park: `h_arm`, `h_nodir`, `h_nic0`, which
    item 77's comment already calls "the ONE scanner fact every park has".  It
    holds at exactly the states `pContentish` holds at, measured both ways
    (`DIFF … = 0` in both censuses), so the escape has no state of its own.

    **Item 222 made that definitional.**  `h_arm` now carries item 80's cleared
    key beside the flag, so the escape's footprint IS `pContentish`'s expression
    — `Tests.Guards.ArmStrengthLadder.pFlowParkT_eq_pContentish` is `rfl`.  This
    reading is left at item 219's strength so that items 219–221 keep meaning
    what they meant; the tightened twin lives beside item 220's `pPropsT` and
    item 221's `pMapValueT`. -/
def pFlowPark (sc : ScannerState) : Bool :=
  (sc.simpleKeyAllowed || 0 < sc.col) && !sc.allowDirectives &&
  (sc.col != 0 || sc.needIndentCheck)

/-- `pendingBlock`: `h_sk`, `h_nodir`, `h_floor`, `h_col`, `h_park_top`. -/
def pBlock (sc : ScannerState) : Bool :=
  sc.simpleKeyAllowed && !sc.allowDirectives && 1 ≤ sc.col &&
  floorB sc sc.col && sc.currentIndent ≤ ((sc.col - 1 : Nat) : Int)

/-- `pendingMapValue`: `h_nic`, `h_real`, `h_sk`, `h_nodir`. -/
def pMapValue (sc : ScannerState) : Bool :=
  !sc.needIndentCheck && lastRealB sc.tokens && sc.simpleKeyAllowed && !sc.allowDirectives

/-! ## One step of the scan, classified by the dispatch it takes -/

inductive Disp where
  | struct | flow | block | content | err
  deriving BEq, Repr, Inhabited

structure StepInfo where
  disp   : Disp
  sPrep  : ScannerState
  c      : Char
  sDis   : ScannerState
  sPost  : Option ScannerState
  bareOk : Bool
  dnOk   : Bool

/-- `scanNextToken`'s own dispatch chain (`Scanner.lean:1153`), re-run to say
    WHICH branch this step takes.  The two checks the block lemmas carry as
    hypotheses (`h_bare`, `h_dn`) ride along. -/
def classify (sc : ScannerState) : Option StepInfo :=
  match scanNextToken_preprocess sc with
  | .ok (some (sPrep, c)) =>
    let dnOk := (scanNextToken_checkDanglingNode sc sPrep).toOption.isSome
    let bareOk := (scanNextToken_checkBareDocument sPrep).toOption.isSome
    let sDis := if sPrep.allowDirectives then
        { sPrep with allowDirectives := false, documentEverStarted := true } else sPrep
    match scanNextToken_dispatchStructural sPrep c with
    | .ok (some s') => some ⟨.struct, sPrep, c, sDis, some s', bareOk, dnOk⟩
    | .ok .none =>
      match scanNextToken_dispatchFlowIndicators sDis c with
      | .ok (some s') => some ⟨.flow, sPrep, c, sDis, some s', bareOk, dnOk⟩
      | .ok .none =>
        match scanNextToken_dispatchBlockIndicators sDis c with
        | .ok (some s') => some ⟨.block, sPrep, c, sDis, some s', bareOk, dnOk⟩
        | .ok .none =>
          match scanNextToken_dispatchContent sDis c with
          | .ok s' => some ⟨.content, sPrep, c, sDis, some s', bareOk, dnOk⟩
          | .error _ => some ⟨.err, sPrep, c, sDis, none, bareOk, dnOk⟩
        | .error _ => some ⟨.err, sPrep, c, sDis, none, bareOk, dnOk⟩
      | .error _ => some ⟨.err, sPrep, c, sDis, none, bareOk, dnOk⟩
    | .error _ => some ⟨.err, sPrep, c, sDis, none, bareOk, dnOk⟩
  | _ => none

/-! ## The nineteen rows -/

/-- `RelaySupplyCensus.expectedDeclineWriters` in full, plus
    `indicator_open_map` in parentheses — not a decline writer, but
    `colon_open_map`'s and `question_open_map`'s only caller, so the two cannot
    be restricted without it. -/
def names : Array String :=
  #["accum_block_pending", "accum_block_on_noPending", "accum_block_on_closeThenBlock",
    "accum_block_on_pendingBlock", "accum_block_on_pendingBlockContent",
    "accum_block_on_pendingContent", "accum_content_pending",
    "accum_content_on_pendingBlock_indented", "accum_content_on_pendingMapValue_indented",
    "content_dispatch_routed", "accum_step_flow", "colon_open_map",
    "colon_open_map_explicit", "colon_open_map_implicit", "colon_open_map_props",
    "compact_open_map", "question_open_map", "colon_fires_implicit_key",
    "colon_fires_props_key", "(indicator_open_map)"]

/-- The caller graph, read out of the environment (`ConstantInfo.value?` with
    `allowOpaque := true`, the whole nineteen plus `indicator_open_map`), which
    is what each row's park restriction below is taken from:

    ```
    accum_block_pending        -> on_noPending, on_closeThenBlock, on_pendingBlock,
                                  on_pendingBlockContent, on_pendingContent,
                                  colon_fires_props_key
    on_noPending               -> indicator_open_map
    on_closeThenBlock          -> colon_open_map_explicit, compact_open_map,
                                  indicator_open_map
    on_pendingBlock            -> on_closeThenBlock, colon_open_map_explicit,
                                  compact_open_map, indicator_open_map
    on_pendingBlockContent     -> on_closeThenBlock, colon_open_map_explicit,
                                  colon_fires_implicit_key, indicator_open_map
    on_pendingContent          -> on_closeThenBlock, colon_fires_implicit_key
    accum_content_pending      -> on_pendingBlock_indented,
                                  on_pendingMapValue_indented, content_dispatch_routed
    colon_fires_implicit_key   -> colon_open_map_implicit
    colon_fires_props_key      -> colon_open_map_props
    indicator_open_map         -> colon_open_map, question_open_map
    ```

    `on_closeThenBlock` is called from SIX places spanning most park classes,
    which is why its row is nearly the parent's and not a defect of the
    predicate. -/
def fire (sc : ScannerState) (st : StepInfo) : Array Bool :=
  let blockD := st.disp == Disp.block && !st.sPrep.inFlow && st.bareOk && st.dnOk
  let contD  := st.disp == Disp.content && !st.sPrep.inFlow
  let colon  := blockD && st.c == ':'
  let src    := srcDecided st.sDis
  let sPost  := st.sPost.getD st.sDis
  let noP    := pNoPending sc
  let cont   := pContentish sc
  let blk    := pBlock sc
  let props  := pProps sc
  let dEnd   := pDocEnd sc
  let dStart := pDocStart sc
  let flowP  := pFlowPark sc
  let closeP := dEnd || dStart || props || flowP || blk || cont
  let r01 := blockD
  let r02 := blockD && noP
  let r03 := blockD && closeP
  let r04 := blockD && blk
  let r05 := blockD && cont
  let r06 := blockD && cont
  let r07 := contD
  let r08 := contD && blk
  let r09 := contD && pMapValue sc
  let r10 := contD && !st.sPrep.needIndentCheck
  let r11 := st.disp == Disp.flow && st.bareOk && st.dnOk
  let r19 := colon && props
  let r15 := r19 && sc.simpleKey.possible
  let r18 := colon && cont &&
             ((sc.simpleKeyAllowed && !sc.simpleKey.possible) || 0 < sc.col)
  let r14 := r18 && st.sPrep.simpleKey.possible &&
             st.sPrep.simpleKey.pos.line == st.sPrep.line &&
             st.sPrep.simpleKey.pos.offset != st.sPrep.offset &&
             floorB sPost (st.sPrep.simpleKey.pos.col + 1)
  let r13 := colon && closeP && st.sDis.explicitKeyLine != none
  let r16 := blockD && (dEnd || dStart || props || flowP || blk) &&
             sc.simpleKeyAllowed && (st.c != ':' || src)
  let r20 := blockD && (noP || closeP)
  let r12 := r20 && st.c == ':' && src
  let r17 := r20 && st.c == '?'
  #[r01, r02, r03, r04, r05, r06, r07, r08, r09, r10,
    r11, r12, r13, r14, r15, r16, r17, r18, r19, r20]

/-! ## The walk -/

structure Acc where
  steps     : Nat := 0
  byDisp    : Array Nat := Array.replicate 5 0
  hits      : Array Nat := Array.replicate 20 0
  seen      : Array Bool := Array.replicate 20 false
  /-- the seven classes at a BLOCK dispatch, then `onlyFlowPark`, then the
      same `docEnd` count with `h_bare`/`h_dn` dropped. -/
  park      : Array Nat := Array.replicate 9 0
  /-- the seven classes at EVERY visited state — the positive control for a
      class that reads zero at a block dispatch. -/
  parkAll   : Array Nat := Array.replicate 7 0
  /-- `flowPark ∧ ¬contentish` and `contentish ∧ ¬flowPark`: equal COUNTS are a
      hypothesis, a zero here is the containment. -/
  diff      : Array Nat := Array.replicate 2 0
  sawDocEnd : Bool := false
  deriving Inhabited

/-- Walk one input along `scanNextToken`'s own path — `scan`'s seed, BOM
    included, and `scanLoop`'s own four end-of-stream checks — evaluating every
    predicate at every state it visits.  Returns the accumulator and whether the
    walk accepted, which `run` cross-checks against `scan` itself. -/
partial def walk (input : String) : Acc × Bool :=
  let rec go (s : ScannerState) (fuel : Nat) (a : Acc) : Acc × Bool :=
    match fuel with
    | 0 => (a, false)
    | fuel' + 1 =>
      let a : Acc := Id.run do
        match classify s with
        | none => return a
        | some st =>
          let di := match st.disp with
            | .struct => 0 | .flow => 1 | .block => 2 | .content => 3 | .err => 4
          let f := fire s st
          let mut hits := a.hits
          let mut sn := a.seen
          for i in [0:20] do
            if f[i]! then
              hits := hits.set! i (hits[i]! + 1)
              sn := sn.set! i true
          let fl := #[pNoPending s, pDocEnd s, pDocStart s, pProps s,
                      pFlowPark s, pBlock s, pContentish s]
          let mut pa := a.parkAll
          for k in [0:7] do
            if fl[k]! then pa := pa.set! k (pa[k]! + 1)
          let mut df := a.diff
          if fl[4]! && !fl[6]! then df := df.set! 0 (df[0]! + 1)
          if fl[6]! && !fl[4]! then df := df.set! 1 (df[1]! + 1)
          let mut pk := a.park
          if st.disp == Disp.block && fl[1]! then pk := pk.set! 8 (pk[8]! + 1)
          if st.disp == Disp.block && !st.sPrep.inFlow && st.bareOk && st.dnOk then
            for k in [0:7] do
              if fl[k]! then pk := pk.set! k (pk[k]! + 1)
            if fl[4]! && !(fl[0]! || fl[1]! || fl[2]! || fl[3]! || fl[5]! || fl[6]!) then
              pk := pk.set! 7 (pk[7]! + 1)
          return { steps := a.steps + 1, byDisp := a.byDisp.set! di (a.byDisp[di]! + 1),
                   hits := hits, seen := sn, park := pk, parkAll := pa, diff := df,
                   sawDocEnd := a.sawDocEnd || fl[1]! }
      match scanNextToken s with
      | .ok (some s') => go s' fuel' a
      | .ok none =>
        if s.flowLevel > 0 || s.directivesPresent then (a, false)
        else match scanLoop_checkDanglingNode s with
          | .error _ => (a, false)
          | .ok _ => match scanLoop_checkFlowValueIndent s with
            | .error _ => (a, false)
            | .ok _ => (a, true)
      | .error _ => (a, false)
  let s0 := (ScannerState.mk' input).emit .streamStart
  let s0 := match s0.peek? with | some '﻿' => s0.consumeBOM | _ => s0
  go s0 20000 {}

/-! ## The positive controls -/

/-- Seven hand-built inputs, one per park class.  A class reading zero over a
    domain is a refusal only if the class can fire at all, and the first row is
    the one that matters: `a⏎...⏎- b` reaches a `pendingDocEnd` park AT A BLOCK
    DISPATCH in four steps, and the scanner accepts it. -/
def controls : List (String × String) :=
  [ ("docEnd-then-block", "a\n...\n- b\n")
  , ("docEnd-plain",      "a\n...\n")
  , ("docStart",          "---\n- a\n")
  , ("props-key",         "!!str : v\n")
  , ("block-entry",       "- a: 1\n")
  , ("flow",              "[1, 2]\n")
  , ("mapping",           "a: 1\n") ]

/-- `(label, accepted, steps, parkAll vector, park-at-block vector)`. -/
def controlCensus : List (String × Bool × Nat × Array Nat × Array Nat) :=
  controls.map fun (lbl, txt) =>
    let (a, ok) := walk txt
    (lbl, ok, a.steps, a.parkAll, a.park.extract 0 7)

/-! ## The enumerated domain -/

/-- Item 204's 33-fragment line alphabet, plus the two document markers and the
    two property heads — without the markers no program can stand at a
    `pendingDocEnd` park at all, which is the class the corpus reads empty. -/
def frags : List String :=
  [ "a: 1", "b: 2", "k:", "- a", "- b", "-",
    "? a", "? b", "?", ": a", ": b", ":",
    "- ? a", "- : a", "- - a", "- ? b", "- : b",
    "  a: 1", "  - a", "  ? a", "  : a", "  ?", "  :",
    "    ? a", "    : a", "    - a",
    "[1]", "{a: b}", "- [1]", "? [1]", ": [1]",
    "#c", "", "...", "---", "&x", "!!str" ]

def programs : List String :=
  frags.flatMap fun a => frags.flatMap fun b => frags.map fun c =>
    a ++ "\n" ++ b ++ "\n" ++ c ++ "\n"

structure Census where
  units      : Nat := 0
  steps      : Nat := 0
  accepted   : Nat := 0
  byDisp     : Array Nat := Array.replicate 5 0
  hits       : Array Nat := Array.replicate 20 0
  unitHits   : Array Nat := Array.replicate 20 0
  accUnitHits : Array Nat := Array.replicate 20 0
  park       : Array Nat := Array.replicate 9 0
  parkAll    : Array Nat := Array.replicate 7 0
  diff       : Array Nat := Array.replicate 2 0
  deriving Inhabited

def Census.add (c : Census) (a : Acc) (ok : Bool) : Census := Id.run do
  let mut c := { c with units := c.units + 1, steps := c.steps + a.steps,
                        accepted := c.accepted + (if ok then 1 else 0) }
  let mut bd := c.byDisp; let mut hs := c.hits; let mut uh := c.unitHits
  let mut ah := c.accUnitHits; let mut pk := c.park; let mut pa := c.parkAll
  let mut df := c.diff
  for i in [0:5] do bd := bd.set! i (bd[i]! + a.byDisp[i]!)
  for i in [0:9] do pk := pk.set! i (pk[i]! + a.park[i]!)
  for i in [0:7] do pa := pa.set! i (pa[i]! + a.parkAll[i]!)
  for i in [0:2] do df := df.set! i (df[i]! + a.diff[i]!)
  for i in [0:20] do
    hs := hs.set! i (hs[i]! + a.hits[i]!)
    if a.seen[i]! then
      uh := uh.set! i (uh[i]! + 1)
      if ok then ah := ah.set! i (ah[i]! + 1)
  return { c with byDisp := bd, hits := hs, unitHits := uh, accUnitHits := ah,
                  park := pk, parkAll := pa, diff := df }

def domainCensus : Census := Id.run do
  let mut c : Census := {}
  for p in programs do
    let (a, ok) := walk p
    c := c.add a ok
  return c

/-! ## The pins -/

/-- The domain census, 50 653 three-line programs.  `unreached` is the count of
    the twenty rows no program reaches; `unreachedOnAccepted` the count no
    ACCEPTED program reaches.  Both are ZERO: the enumerated domain retires
    nothing either, and every row has an accepted witness. -/
def expectedDomain : String :=
  "programs=50653 steps=216114 accepted=14084 unreached=0 unreachedOnAccepted=0 \
diffFlowNotCont=0 diffContNotFlow=0"

/-- The domain's park census at a block dispatch.  `docEnd=1633` against the
    corpus's `0` is this item's finding, and `ONLYflowPark=0` is the escape's:
    `pendingFlow` never stands at a state no other park class covers. -/
def expectedDomainPark : String :=
  "noPending=36175 docEnd=1633 docStart=1633 props=2200 flowPark=42242 \
block=16256 contentish=42242 ONLYflowPark=0 docEndUNGATED=1633"

/-- The corpus census over the 402 `in.yaml` leaves.  `DIVERGENT` is the control
    that the walk follows the scanner's own path: acceptance is read off `scan`
    itself, and the two verdicts agree on all 402. -/
def expectedCorpus : String :=
  "leaves=402 steps=2946 accepted=309 tokens=7252 divergent=0 unreached=0 \
minAcceptedLeaves=2"

/-- The corpus's park census at a block dispatch.  `docEnd=0` — and eleven
    `pendingDocEnd` states ARE visited, on ten named leaves (`expectedDocEndLeaves`);
    not one of them is handed a `-`/`?`/`:`.  The same predicate reads 1 633 on
    the enumerated domain, which is what says the zero belongs to the corpus. -/
def expectedCorpusPark : String :=
  "noPending=69 docEnd=0 docStart=17 props=24 flowPark=662 block=33 \
contentish=662 ONLYflowPark=0 docEndUNGATED=0"

/-- The ten leaves at which a `pendingDocEnd` park is visited at all. -/
def expectedDocEndLeaves : List String :=
  ["5TYM", "6WLZ", "6ZKB", "7Z25", "9DXL", "9WXW", "M7A3", "U9NS", "UT92", "W4TN"]

/-- The corpus rows, `name :: hits leaves acceptedLeaves`.  The narrowest pair is
    the props-key route: `colon_fires_props_key` and `colon_open_map_props` rest
    on TWO leaves, `FH7J` and `PW8X`, and a later item that moves them has
    exactly those two witnesses. -/
def expectedCorpusRows : List String :=
  ["accum_block_pending :: 731 245 187",
   "accum_block_on_noPending :: 69 69 58",
   "accum_block_on_closeThenBlock :: 662 228 175",
   "accum_block_on_pendingBlock :: 33 18 16",
   "accum_block_on_pendingBlockContent :: 662 228 175",
   "accum_block_on_pendingContent :: 662 228 175",
   "accum_content_pending :: 1175 306 247",
   "accum_content_on_pendingBlock_indented :: 237 89 80",
   "accum_content_on_pendingMapValue_indented :: 689 247 201",
   "content_dispatch_routed :: 1175 306 247",
   "accum_step_flow :: 370 87 67",
   "colon_open_map :: 418 181 134",
   "colon_open_map_explicit :: 29 22 21",
   "colon_open_map_implicit :: 408 175 128",
   "colon_open_map_props :: 5 2 2",
   "compact_open_map :: 92 55 48",
   "question_open_map :: 36 24 22",
   "colon_fires_implicit_key :: 437 187 140",
   "colon_fires_props_key :: 5 2 2",
   "(indicator_open_map) :: 731 245 187"]

/-- The domain rows, `name :: hits programs acceptedPrograms`. -/
def expectedDomainRows : List String :=
  ["accum_block_pending :: 80050 47241 13732",
   "accum_block_on_noPending :: 36175 36175 8835",
   "accum_block_on_closeThenBlock :: 43875 27482 12802",
   "accum_block_on_pendingBlock :: 16256 13479 6490",
   "accum_block_on_pendingBlockContent :: 42242 26521 12290",
   "accum_block_on_pendingContent :: 42242 26521 12290",
   "accum_content_pending :: 64591 41287 12943",
   "accum_content_on_pendingBlock_indented :: 40382 34023 11018",
   "accum_content_on_pendingMapValue_indented :: 48275 38765 12250",
   "content_dispatch_routed :: 64591 41287 12943",
   "accum_step_flow :: 26134 12274 2989",
   "colon_open_map :: 29062 23709 8738",
   "colon_open_map_explicit :: 3232 3222 2358",
   "colon_open_map_implicit :: 9519 8694 4106",
   "colon_open_map_props :: 616 616 322",
   "compact_open_map :: 20578 16470 8404",
   "question_open_map :: 21253 18724 7141",
   "colon_fires_implicit_key :: 20015 16562 8177",
   "colon_fires_props_key :: 616 616 322",
   "(indicator_open_map) :: 80050 47241 13732"]

/-! ## Rendering, shared by the guards and the executable -/

def parkStr (p : Array Nat) : String :=
  s!"noPending={p[0]!} docEnd={p[1]!} docStart={p[2]!} props={p[3]!} \
flowPark={p[4]!} block={p[5]!} contentish={p[6]!} ONLYflowPark={p[7]!} \
docEndUNGATED={p[8]!}"

def rowsStr (c : Census) : List String :=
  (List.range 20).map fun i =>
    s!"{names[i]!} :: {c.hits[i]!} {c.unitHits[i]!} {c.accUnitHits[i]!}"

def unreachedOf (c : Census) : Nat × Nat := Id.run do
  let mut a := 0
  let mut b := 0
  for i in [0:20] do
    if c.hits[i]! == 0 then a := a + 1
    if c.accUnitHits[i]! == 0 then b := b + 1
  return (a, b)

def domainStr : String :=
  let c := domainCensus
  let (u, ua) := unreachedOf c
  s!"programs={c.units} steps={c.steps} accepted={c.accepted} unreached={u} \
unreachedOnAccepted={ua} diffFlowNotCont={c.diff[0]!} diffContNotFlow={c.diff[1]!}"

/-! ## The corpus half (IO) -/

partial def leafPaths (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in (← root.readDir) do
    if e.fileName == "tags" || e.fileName == "name" then continue
    if (← e.path.isDir) then out := out ++ (← leafPaths e.path)
    else if e.fileName == "in.yaml" then out := out.push e.path
  return out

/-- `(census, tokens, divergent, minAcceptedUnits, docEnd leaves)`. -/
def corpusCensus (dataDir : String) : IO (Census × Nat × Nat × Nat × Array String) := do
  let ps := (← leafPaths dataDir).qsort (fun a b => a.toString < b.toString)
  let mut c : Census := {}
  let mut tokens := 0
  let mut divergent := 0
  let mut docEndLeaves : Array String := #[]
  for p in ps do
    let txt ← IO.FS.readFile p
    let (a, walkOk) := walk txt
    let res := scan txt
    let ok := res.toOption.isSome
    if walkOk != ok then divergent := divergent + 1
    tokens := tokens + (match res with | .ok ts => ts.size | .error _ => 0)
    if a.sawDocEnd then
      docEndLeaves := docEndLeaves.push
        (((p.toString.splitOn "/data/").getLast!).replace "/in.yaml" "")
    c := c.add a ok
  let mut minAcc := 1000000
  for i in [0:20] do
    if c.accUnitHits[i]! < minAcc then minAcc := c.accUnitHits[i]!
  return (c, tokens, divergent, minAcc, docEndLeaves)

def check (label expected got : String) : IO Bool := do
  if expected == got then
    IO.println s!"OK   {label}"
    return true
  else
    IO.println s!"FAIL {label}\n  expected: {expected}\n  got:      {got}"
    return false

def checkList (label : String) (expected got : List String) : IO Bool := do
  if expected == got then
    IO.println s!"OK   {label} ({got.length} rows)"
    return true
  else
    IO.println s!"FAIL {label}"
    for (e, g) in expected.zip got do
      if e != g then IO.println s!"  expected: {e}\n  got:      {g}"
    if expected.length != got.length then
      IO.println s!"  length {expected.length} vs {got.length}"
    return false

def main (args : List String) : IO UInt32 := do
  let mut ok := true
  IO.println "── controls ─────────────────────────────────────────────"
  for (lbl, acc, steps, pa, pb) in controlCensus do
    IO.println s!"  {lbl} accepted={acc} steps={steps} \
all=[noP={pa[0]!} docEnd={pa[1]!} docStart={pa[2]!} props={pa[3]!} flowPark={pa[4]!} \
block={pa[5]!} cont={pa[6]!}] atBlock=[noP={pb[0]!} docEnd={pb[1]!} docStart={pb[2]!} \
props={pb[3]!} block={pb[5]!} cont={pb[6]!}]"
  IO.println "── domain ───────────────────────────────────────────────"
  ok := (← check "domain" expectedDomain domainStr) && ok
  ok := (← check "domainPark" expectedDomainPark (parkStr domainCensus.park)) && ok
  ok := (← checkList "domainRows" expectedDomainRows (rowsStr domainCensus)) && ok
  match args with
  | [] =>
    IO.println "── corpus ───────────────────────────────────────────────"
    IO.println "  skipped (pass the yaml-test-suite data directory to run it)"
  | dataDir :: _ =>
    IO.println "── corpus ───────────────────────────────────────────────"
    let (c, tokens, divergent, minAcc, docEndLeaves) ← corpusCensus dataDir
    let (u, _) := unreachedOf c
    let got := s!"leaves={c.units} steps={c.steps} accepted={c.accepted} \
tokens={tokens} divergent={divergent} unreached={u} minAcceptedLeaves={minAcc}"
    ok := (← check "corpus" expectedCorpus got) && ok
    ok := (← check "corpusPark" expectedCorpusPark (parkStr c.park)) && ok
    ok := (← checkList "docEndLeaves" expectedDocEndLeaves docEndLeaves.toList) && ok
    ok := (← checkList "corpusRows" expectedCorpusRows (rowsStr c)) && ok
  if ok then
    IO.println "ALL PINS OK"
    return 0
  else
    IO.println "PINS DISAGREE"
    return 1

end Tests.DeclineReachCensus
