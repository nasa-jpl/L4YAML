import Tests.DeclineReachCensus

/-!
# Which ARM is reached, and what does a zero mean?  (item 220)

[Item 219](../DOCS.md) built the corpus census its own mandate asked for, found
**all nineteen decline writers reached**, and recorded the instrument the
remainder wants:

> a domain sweep whose alphabet is chosen per ROW rather than shared, because
> this item's 37 fragments are item 204's alphabet plus four, and a row that
> reads zero over them says nothing about a row whose shape the alphabet cannot
> spell.

That sweep is built and run here — five alphabets, one per surviving zero,
148 480 programs and 632 239 scanner steps beyond the shared domain — and **not
one zero moves**.  What moves them is a different instrument entirely, and it
costs 1.5 seconds: a sweep over synthetic STATES rather than over inputs.

## What item 219 measured, and where its zeros were not

219 counted **row totals** (twenty rows) and **park totals** (nine slots).  It
never took the CROSS.  But a row is nonzero as soon as ONE of its arms is:
`accum_block_on_closeThenBlock` is `blockD && (dEnd || dStart || props ||
flowP || blk || cont)`, six arms under one row.  The zeros live in the cross,
and this module prints it — 20 x 8 = **160 cells**, inclusive and EXCLUSIVE
(the states where exactly one park holds, item 219's `ONLYflowPark` generalized
to the whole family).

## The three instruments, and what each direction can say

1. **The input sweep** (219's, re-run here over the cross).  Over inputs it can
   only ever say REACHED — 219's own rule.
2. **The synthetic-state sweep**: 10 240 states, exhaustive over every field the
   nine park predicates read (five flags x four columns x four stack tops x two
   explicit-key settings x ten token shapes, `line` pinned at 0 so the shapes
   carry both on-line and off-line markers).  Over states it can only ever say
   SATISFIABLE — the exact dual.  And its **UNSAT is a proof obligation**: every
   containment it reads empty is stated and discharged in
   `Tests/Guards/Proofs/DeclineArmLattice.lean`.
3. **The per-zero alphabets**: the mandate, executed, with a park-coverage
   control on each so that a zero is a read zero and not an unread one.

Together they bracket each zero: reached (live), unsatisfiable (dead whatever
the alphabet), or satisfiable-but-unreached (a scanner INVARIANT nobody has
stated).  Twelve containment zeros split **7 / 5** — and the five that remain
are reachability facts, not coverage gaps.

## The abstraction the synthetic space makes, stated

`col` ranges over `0..3` and the stack top over `-1..2`.  The park predicates
compare `col` with `0`, with `1`, with `currentIndent + 1`, and `currentIndent`
with `col - 1`; every ordering among those is realized inside those ranges, so
a wider range adds order-isomorphic states and no new verdicts.  That is an
abstraction, and it is why the sweep's empties are turned into Lean lemmas
rather than quoted as proofs.

Run: `lake exe declinearm` (matrix + lattice + alphabets), and
`lake exe declinearm <yaml-test-suite-data-dir>` to add the 402-leaf corpus.
`--emit` prints the measured values instead of checking them.
Exits 1 on any disagreement with the pins below.
-/

namespace Tests.DeclineArmCensus

open L4YAML
open L4YAML.Scanner
open Tests.DeclineReachCensus

/-! ## The eight park classes, as one vector -/

def parkNames : Array String :=
  #["noPending", "docEnd", "docStart", "props", "flowPark", "block", "contentish", "mapValue"]

def parkVec (sc : ScannerState) : Array Bool :=
  #[pNoPending sc, pDocEnd sc, pDocStart sc, pProps sc,
    pFlowPark sc, pBlock sc, pContentish sc, pMapValue sc]

/-- Item 219's `pProps` TIGHTENED with the field the constructor already carries
    — `pendingProps.h_col0 : 0 < sp_scan.col`, which `ScannerSurfCorr.col_eq`
    reads at the runtime state.  The census reading dropped it.  Tightening
    moves **no reachable count** (4 550 either way) and moves **two** of the
    containment verdicts from MEASURED to ENTAILED: a dropped field costs
    nothing in the counts and everything in the classification. -/
def pPropsT (sc : ScannerState) : Bool := pProps sc && 0 < sc.col

def parkVecT (sc : ScannerState) : Array Bool :=
  #[pNoPending sc, pDocEnd sc, pDocStart sc, pPropsT sc,
    pFlowPark sc, pBlock sc, pContentish sc, pMapValue sc]

/-- The raw `sc` fields every park predicate reads, no paraphrase. -/
def fieldNames : Array String :=
  #["allowDirectives", "needIndentCheck", "simpleKeyAllowed", "simpleKey.possible",
    "col=0", "inFlow", "currentIndent<0", "lastRealB"]

def fieldVec (sc : ScannerState) : Array Bool :=
  #[sc.allowDirectives, sc.needIndentCheck, sc.simpleKeyAllowed, sc.simpleKey.possible,
    sc.col == 0, sc.inFlow, sc.currentIndent < 0, lastRealB sc.tokens]

/-! ## The visitor — item 219's walk, collecting the states instead of counting -/

partial def states (input : String) : Array (ScannerState × StepInfo) × Bool :=
  let rec go (s : ScannerState) (fuel : Nat) (acc : Array (ScannerState × StepInfo)) :
      Array (ScannerState × StepInfo) × Bool :=
    match fuel with
    | 0 => (acc, false)
    | fuel' + 1 =>
      let acc := match classify s with
        | none => acc
        | some st => acc.push (s, st)
      match scanNextToken s with
      | .ok (some s') => go s' fuel' acc
      | .ok none =>
        if s.flowLevel > 0 || s.directivesPresent then (acc, false)
        else match scanLoop_checkDanglingNode s with
          | .error _ => (acc, false)
          | .ok _ => match scanLoop_checkFlowValueIndent s with
            | .error _ => (acc, false)
            | .ok _ => (acc, true)
      | .error _ => (acc, false)
  let s0 := (ScannerState.mk' input).emit .streamStart
  let s0 := match s0.peek? with | some '﻿' => s0.consumeBOM | _ => s0
  go s0 20000 #[]

/-- Item 219's accumulator, rebuilt from the visited states.  **The control**:
    this visitor is a second authoring of the stepping, so every number below is
    readable only if it walks the same walk — `WALKAGREE` checks the whole
    accumulator, not just the step count. -/
def accOf (vs : Array (ScannerState × StepInfo)) : Acc := Id.run do
  let mut a : Acc := {}
  for sst in vs do
    let s : ScannerState := sst.1
    let st : StepInfo := sst.2
    let di := match st.disp with
      | .struct => 0 | .flow => 1 | .block => 2 | .content => 3 | .err => 4
    let f := fire s st
    let mut hits := a.hits; let mut sn := a.seen
    for i in [0:20] do
      if f[i]! = true then hits := hits.set! i (hits[i]! + 1); sn := sn.set! i true
    let fl := #[pNoPending s, pDocEnd s, pDocStart s, pProps s,
                pFlowPark s, pBlock s, pContentish s]
    let mut pa := a.parkAll
    for k in [0:7] do if fl[k]! = true then pa := pa.set! k (pa[k]! + 1)
    let mut df := a.diff
    if fl[4]! && !fl[6]! then df := df.set! 0 (df[0]! + 1)
    if fl[6]! && !fl[4]! then df := df.set! 1 (df[1]! + 1)
    let mut pk := a.park
    if st.disp == Disp.block && fl[1]! then pk := pk.set! 8 (pk[8]! + 1)
    if st.disp == Disp.block && !st.sPrep.inFlow && st.bareOk && st.dnOk then
      for k in [0:7] do if fl[k]! = true then pk := pk.set! k (pk[k]! + 1)
      if fl[4]! && !(fl[0]! || fl[1]! || fl[2]! || fl[3]! || fl[5]! || fl[6]!) then
        pk := pk.set! 7 (pk[7]! + 1)
    a := { steps := a.steps + 1, byDisp := a.byDisp.set! di (a.byDisp[di]! + 1),
           hits := hits, seen := sn, park := pk, parkAll := pa, diff := df,
           sawDocEnd := a.sawDocEnd || fl[1]! }
  return a

def accStr (a : Acc) (ok : Bool) : String :=
  s!"{a.steps}|{a.byDisp}|{a.hits}|{a.seen}|{a.park}|{a.parkAll}|{a.diff}|{a.sawDocEnd}|{ok}"

def agree (input : String) : Bool :=
  let r1 := walk input
  let r2 := states input
  accStr r1.1 r1.2 == accStr (accOf r2.1) r2.2

/-! ## The matrix -/

structure Mat where
  units : Nat := 0
  /-- row x park, at the same state. -/
  cells : Array Nat := Array.replicate 160 0
  /-- the same, restricted to states where EXACTLY ONE park holds. -/
  excl  : Array Nat := Array.replicate 160 0
  /-- `|{ park j and not park k }|` — zero says `j` is contained in `k` HERE. -/
  cont  : Array Nat := Array.replicate 64 0
  parks : Array Nat := Array.replicate 8 0
  /-- the raw fields at every state, then at `docEnd` states, then `docStart`. -/
  fAll  : Array Nat := Array.replicate 8 0
  fEnd  : Array Nat := Array.replicate 8 0
  fStart : Array Nat := Array.replicate 8 0
  nEnd  : Nat := 0
  nStart : Nat := 0
  steps : Nat := 0
  deriving Inhabited

def Mat.add (m : Mat) (vs : Array (ScannerState × StepInfo)) : Mat := Id.run do
  let mut c := m.cells; let mut e := m.excl; let mut ct := m.cont; let mut pk := m.parks
  let mut fa := m.fAll; let mut fe := m.fEnd; let mut fs := m.fStart
  let mut ne := m.nEnd; let mut ns := m.nStart; let mut steps := m.steps
  for sst in vs do
    let s : ScannerState := sst.1
    let st : StepInfo := sst.2
    let f := fire s st
    let pv := parkVec s
    let fv := fieldVec s
    steps := steps + 1
    for j in [0:8] do if fv[j]! = true then fa := fa.set! j (fa[j]! + 1)
    if pv[1]! = true then
      ne := ne + 1
      for j in [0:8] do if fv[j]! = true then fe := fe.set! j (fe[j]! + 1)
    if pv[2]! = true then
      ns := ns + 1
      for j in [0:8] do if fv[j]! = true then fs := fs.set! j (fs[j]! + 1)
    let mut nOn := 0
    for j in [0:8] do
      if pv[j]! = true then
        nOn := nOn + 1
        pk := pk.set! j (pk[j]! + 1)
      for k in [0:8] do
        if pv[j]! = true && pv[k]! = false then ct := ct.set! (j*8+k) (ct[j*8+k]! + 1)
    for i in [0:20] do
      if f[i]! = true then
        for j in [0:8] do
          if pv[j]! = true then
            c := c.set! (i*8+j) (c[i*8+j]! + 1)
            if nOn == 1 then e := e.set! (i*8+j) (e[i*8+j]! + 1)
  return { units := m.units + 1, cells := c, excl := e, cont := ct, parks := pk,
           fAll := fa, fEnd := fe, fStart := fs, nEnd := ne, nStart := ns, steps := steps }

def matRows (m : Mat) : List String :=
  (List.range 20).map fun i => Id.run do
    let mut row := s!"{names[i]!} ::"
    for j in [0:8] do
      let k := i*8+j
      row := row ++ s!" {parkNames[j]!}={m.cells[k]!}|{m.excl[k]!}"
    return row

def matZeros (m : Mat) : Nat × Nat × Nat := Id.run do
  let mut zi := 0; let mut ze := 0; let mut both := 0
  for k in [0:160] do
    if m.cells[k]! == 0 then zi := zi + 1
    if m.excl[k]! == 0 then ze := ze + 1
    if m.cells[k]! != 0 && m.excl[k]! == 0 then both := both + 1
  return (zi, ze, both)

/-- **Which cells are ARMS.**  Six of the twenty rows disjoin over parks in
    `fire`; for those, a cell says whether that arm of the caller is witnessed.
    For the other fourteen the row's own predicate pins the park, so their other
    cells measure park OVERLAP, which is a different question.  This table is a
    STRUCTURAL reading of six lines of `fire` — which disjuncts appear under
    each row — not a re-authoring of any predicate, and the counts below are
    derived from the matrix by machine:

    ```
    accum_block_on_closeThenBlock  blockD && (dEnd||dStart||props||flowP||blk||cont)
    colon_open_map                 r20 && ':' && src            (noP + the six)
    colon_open_map_explicit        ':' && closeP && ekLine       (the six)
    compact_open_map               blockD && (dEnd||dStart||props||flowP||blk)
    question_open_map              r20 && '?'                    (noP + the six)
    (indicator_open_map)           blockD && (noP || closeP)     (noP + the six)
    ```
    Park order: noPending, docEnd, docStart, props, flowPark, block, contentish,
    mapValue.  `mapValue` is never an arm — no row disjoins over it. -/
def armCells : List (Nat × List Nat) :=
  [ (2,  [1, 2, 3, 4, 5, 6])
  , (11, [0, 1, 2, 3, 4, 5, 6])
  , (12, [1, 2, 3, 4, 5, 6])
  , (15, [1, 2, 3, 4, 5])
  , (16, [0, 1, 2, 3, 4, 5, 6])
  , (19, [0, 1, 2, 3, 4, 5, 6]) ]

def armZeros (m : Mat) : String := Id.run do
  let mut total := 0
  let mut nZero := 0
  let mut names' : List String := []
  for (i, js) in armCells do
    for j in js do
      total := total + 1
      if m.cells[i*8+j]! == 0 then
        nZero := nZero + 1
        names' := names' ++ [s!"{names[i]!}/{parkNames[j]!}"]
  return s!"armCells={total} zero={nZero} :: {String.intercalate " " names'}"

def contRows (m : Mat) : List String :=
  (List.range 8).map fun j => Id.run do
    let mut row := s!"{parkNames[j]!} ::"
    for k in [0:8] do
      if j != k then row := row ++ s!" -{parkNames[k]!}={m.cont[j*8+k]!}"
    return row

def fieldRow (label : String) (n : Nat) (f : Array Nat) : String := Id.run do
  let mut row := s!"{label} n={n} ::"
  for j in [0:8] do row := row ++ s!" {fieldNames[j]!}={f[j]!}"
  return row

/-! ## The synthetic state space -/

def tokShapes : Array (Array (Positioned YamlToken) × String) :=
  #[(#[], "empty"),
    (#[{ pos := ⟨0,0,0⟩, val := .placeholder }], "placeholder"),
    (#[{ pos := ⟨0,0,0⟩, val := .scalar "a" .plain }], "scalar@0"),
    (#[{ pos := ⟨0,0,0⟩, val := .documentEnd }], "docEnd@0"),
    (#[{ pos := ⟨0,1,0⟩, val := .documentEnd }], "docEnd@1"),
    (#[{ pos := ⟨0,0,0⟩, val := .documentStart }], "docStart@0"),
    (#[{ pos := ⟨0,1,0⟩, val := .documentStart }], "docStart@1"),
    (#[{ pos := ⟨0,0,0⟩, val := .anchor "x" }], "anchor@0"),
    (#[{ pos := ⟨0,0,0⟩, val := .anchor "x" },
       { pos := ⟨0,0,0⟩, val := .tag "!" "s" }], "anchor,tag@0"),
    (#[{ pos := ⟨0,1,0⟩, val := .anchor "x" }], "anchor@1")]

def synthStates : Array (ScannerState × String) := Id.run do
  let base := ScannerState.mk' ""
  let mut out : Array (ScannerState × String) := #[]
  for ad in [false, true] do
    for nic in [false, true] do
      for ska in [false, true] do
        for skp in [false, true] do
          for fl in [0, 1] do
            for col in [0, 1, 2, 3] do
              for ci in [(-1 : Int), 0, 1, 2] do
                for ek in [none, (some 0 : Option Nat)] do
                  for ts in tokShapes do
                    let s : ScannerState :=
                      { base with allowDirectives := ad, needIndentCheck := nic,
                                  simpleKeyAllowed := ska,
                                  simpleKey := { base.simpleKey with possible := skp },
                                  flowLevel := fl, col := col, line := 0,
                                  indents := #[{ column := ci, isSequence := false }],
                                  explicitKeyLine := ek, tokens := ts.1 }
                    out := out.push (s, s!"ad={ad} nic={nic} ska={ska} skp={skp} \
flow={fl} col={col} ci={ci} ek={ek.isSome} tok={ts.2}")
  return out

/-- `(entailments, separations-with-a-witness)` over the synthetic space. -/
def lattice (tight : Bool) : List String × List String := Id.run do
  let ss := synthStates
  let mut cont : Array Nat := Array.replicate 64 0
  let mut wit : Array String := Array.replicate 64 ""
  for sn in ss do
    let s : ScannerState := sn.1
    let pv := if tight then parkVecT s else parkVec s
    for j in [0:8] do
      for k in [0:8] do
        if pv[j]! = true && pv[k]! = false then
          cont := cont.set! (j*8+k) (cont[j*8+k]! + 1)
          if wit[j*8+k]! == "" then wit := wit.set! (j*8+k) sn.2
  let mut ent : List String := []
  let mut sep : List String := []
  for j in [0:8] do
    for k in [0:8] do
      if j != k then
        if cont[j*8+k]! == 0 then
          ent := ent ++ [s!"{parkNames[j]!} -> {parkNames[k]!}"]
        else
          sep := sep ++ [s!"{parkNames[j]!} /-> {parkNames[k]!} n={cont[j*8+k]!} :: {wit[j*8+k]!}"]
  return (ent, sep)

/-- The separations that the DOMAIN nevertheless reads empty — the residue:
    satisfiable as a state, never reached by the scan.  Each is a scanner
    invariant nobody has stated. -/
def residual (m : Mat) (tight : Bool) : List String := Id.run do
  let ss := synthStates
  let mut cont : Array Nat := Array.replicate 64 0
  let mut wit : Array String := Array.replicate 64 ""
  for sn in ss do
    let s : ScannerState := sn.1
    let pv := if tight then parkVecT s else parkVec s
    for j in [0:8] do
      for k in [0:8] do
        if pv[j]! = true && pv[k]! = false then
          cont := cont.set! (j*8+k) (cont[j*8+k]! + 1)
          if wit[j*8+k]! == "" then wit := wit.set! (j*8+k) sn.2
  let mut out : List String := []
  for j in [0:8] do
    for k in [0:8] do
      if j != k && m.cont[j*8+k]! == 0 && cont[j*8+k]! != 0 then
        out := out ++ [s!"{parkNames[j]!} subseteq {parkNames[k]!} \
reachedSep=0 synthSep={cont[j*8+k]!} :: {wit[j*8+k]!}"]
  return out

/-! ## The mandate: an alphabet chosen PER ZERO, not shared -/

def targeted : List (String × List String × Nat) :=
  [ ("flowPark-not-contentish",
     ["a", "a:", "'a'", "\"a\"", "? a", ": a", "- a", "", "#c", "---", "...", "&x",
      "!!str", "[a]", "{a: b}", "a: b"], 4)
  , ("mapValue-not-contentish",
     ["a:", "a: b", ": b", ":", "? a", "- a", "a", "", "  b", "b:", "---", "..."], 4)
  , ("docStart-not-mapValue",
     ["---", "--- a", "--- - a", "--- ? a", "--- !!str x", "--- &x", "a", "", "...",
      "%YAML 1.2", "#c", "- a"], 4)
  , ("block-not-mapValue",
     ["- a", "-", "? a", "?", ":", ": a", "", "#c", "---", "...", "  - a", "a: 1"], 4)
  , ("docEnd-with-allowDirectives-false",
     ["...", "a", "- a", "? a", ": a", "%YAML 1.2", "---", "", "#c", "&x", "!!str",
      "  a"], 4)
  ]

def expand (frags : List String) (depth : Nat) : List String :=
  match depth with
  | 0 => [""]
  | d + 1 => (expand frags d).flatMap fun rest => frags.map fun f => f ++ "\n" ++ rest

/-- `(programs, steps, accepted, five targets, eight park totals)`.  The park
    totals are **the control**: a target reading zero over an alphabet that
    never visits the park is an unread zero, which is the mistake item 219
    caught one level up. -/
def sweepTargets (progs : List String) : Nat × Nat × Nat × Array Nat × Array Nat := Id.run do
  let mut steps := 0; let mut acc := 0
  let mut pk : Array Nat := Array.replicate 8 0
  let mut t : Array Nat := Array.replicate 5 0
  for p in progs do
    let r := states p
    if r.2 then acc := acc + 1
    for sst in r.1 do
      let s : ScannerState := sst.1
      steps := steps + 1
      let pv := parkVec s
      for j in [0:8] do if pv[j]! = true then pk := pk.set! j (pk[j]! + 1)
      if pFlowPark s && !pContentish s then t := t.set! 0 (t[0]! + 1)
      if pMapValue s && !pContentish s then t := t.set! 1 (t[1]! + 1)
      if pDocStart s && !pMapValue s then t := t.set! 2 (t[2]! + 1)
      if pBlock s && !pMapValue s then t := t.set! 3 (t[3]! + 1)
      if pDocEnd s && !s.allowDirectives then t := t.set! 4 (t[4]! + 1)
  return (progs.length, steps, acc, t, pk)

def targetedRows : List String :=
  (targeted.zipIdx).map fun (tg, i) => Id.run do
    let r := sweepTargets (expand tg.2.1 tg.2.2)
    let t := r.2.2.2.1
    let pk := r.2.2.2.2
    let mut ctl := ""
    for j in [0:8] do ctl := ctl ++ s!" {parkNames[j]!}={pk[j]!}"
    return s!"{tg.1} frags={tg.2.1.length} depth={tg.2.2} programs={r.1} \
steps={r.2.1} accepted={r.2.2.1} OWN={t[i]!} all=[{t[0]!},{t[1]!},{t[2]!},{t[3]!},{t[4]!}] \
control:{ctl}"

/-! ## The domain half -/

def domainMat : Mat := Id.run do
  let mut m : Mat := {}
  for p in programs do
    m := m.add (states p).1
  return m

/-! ## The pins -/

/-- **The control.** This module re-authors item 219's stepping in order to
    collect the states; the whole accumulator must agree on every control and
    every one of the 50 653 programs, or nothing below is readable. -/
def expectedWalkAgree : String :=
  "controls=true domainPrograms=50653 disagree=0"

/-- 160 cells; **47** read zero, and **143** are never reached at a state where
    their park is the only one holding. -/
def expectedDomainStats : String :=
  "units=50653 steps=216114 zeroIncl=47 zeroExcl=143 inclNonzeroExclZero=96 docEndStates=2345 \
docStartStates=2345"

def expectedDomainParks : String :=
  "noPending=82571 docEnd=2345 docStart=2345 props=4550 flowPark=163124 block=68307 \
contentish=163124 mapValue=93260"

/-- `|{ park j and not park k }|` over the domain.  **Twelve** entries read
    zero; the synthetic sweep below says which of them are entailments. -/
def expectedDomainCont : List String :=
  [ "noPending :: -docEnd=82571 -docStart=82571 -props=82571 -flowPark=50645 -block=80101 \
-contentish=50645 -mapValue=66608"
  , "docEnd :: -noPending=2345 -docStart=2345 -props=2345 -flowPark=2345 -block=2345 \
-contentish=2345 -mapValue=2345"
  , "docStart :: -noPending=2345 -docEnd=2345 -props=2345 -flowPark=0 -block=2345 -contentish=0 \
-mapValue=0"
  , "props :: -noPending=4550 -docEnd=4550 -docStart=4550 -flowPark=0 -block=4550 -contentish=0 \
-mapValue=4550"
  , "flowPark :: -noPending=131198 -docEnd=163124 -docStart=160779 -props=158574 -block=94817 \
-contentish=0 -mapValue=69864"
  , "block :: -noPending=65837 -docEnd=68307 -docStart=68307 -props=68307 -flowPark=0 \
-contentish=0 -mapValue=0"
  , "contentish :: -noPending=131198 -docEnd=163124 -docStart=160779 -props=158574 -flowPark=0 \
-block=94817 -mapValue=69864"
  , "mapValue :: -noPending=77297 -docEnd=93260 -docStart=90915 -props=93260 -flowPark=0 \
-block=24953 -contentish=0" ]

/-- `name :: park=inclusive|exclusive`, twenty rows.  The exclusive column is
    item 219's `ONLYflowPark` generalized: **only `noPending` and `docEnd`
    ever hold alone**, so every other park's arm is witnessed only in company. -/
def expectedDomainMatrix : List String :=
  [ "accum_block_pending :: noPending=36175|36175 docEnd=1633|1633 docStart=1633|0 props=2200|0 \
flowPark=42242|0 block=16256|0 contentish=42242|0 mapValue=19289|0"
  , "accum_block_on_noPending :: noPending=36175|36175 docEnd=0|0 docStart=0|0 props=0|0 \
flowPark=0|0 block=0|0 contentish=0|0 mapValue=0|0"
  , "accum_block_on_closeThenBlock :: noPending=0|0 docEnd=1633|1633 docStart=1633|0 \
props=2200|0 flowPark=42242|0 block=16256|0 contentish=42242|0 mapValue=19289|0"
  , "accum_block_on_pendingBlock :: noPending=0|0 docEnd=0|0 docStart=0|0 props=0|0 \
flowPark=16256|0 block=16256|0 contentish=16256|0 mapValue=16256|0"
  , "accum_block_on_pendingBlockContent :: noPending=0|0 docEnd=0|0 docStart=1633|0 props=2200|0 \
flowPark=42242|0 block=16256|0 contentish=42242|0 mapValue=19289|0"
  , "accum_block_on_pendingContent :: noPending=0|0 docEnd=0|0 docStart=1633|0 props=2200|0 \
flowPark=42242|0 block=16256|0 contentish=42242|0 mapValue=19289|0"
  , "accum_content_pending :: noPending=8682|8682 docEnd=402|402 docStart=402|0 props=780|0 \
flowPark=55507|0 block=40382|0 contentish=55507|0 mapValue=48275|0"
  , "accum_content_on_pendingBlock_indented :: noPending=0|0 docEnd=0|0 docStart=0|0 props=0|0 \
flowPark=40382|0 block=40382|0 contentish=40382|0 mapValue=40382|0"
  , "accum_content_on_pendingMapValue_indented :: noPending=0|0 docEnd=0|0 docStart=402|0 \
props=0|0 flowPark=48275|0 block=40382|0 contentish=48275|0 mapValue=48275|0"
  , "content_dispatch_routed :: noPending=8682|8682 docEnd=402|402 docStart=402|0 props=780|0 \
flowPark=55507|0 block=40382|0 contentish=55507|0 mapValue=48275|0"
  , "accum_step_flow :: noPending=15953|2894 docEnd=134|134 docStart=134|0 props=176|0 \
flowPark=23106|0 block=7623|0 contentish=23106|0 mapValue=7869|0"
  , "colon_open_map :: noPending=10129|10129 docEnd=427|427 docStart=427|0 props=616|0 \
flowPark=18506|0 block=5167|0 contentish=18506|0 mapValue=5986|0"
  , "colon_open_map_explicit :: noPending=0|0 docEnd=0|0 docStart=0|0 props=0|0 flowPark=3232|0 \
block=384|0 contentish=3232|0 mapValue=384|0"
  , "colon_open_map_implicit :: noPending=0|0 docEnd=0|0 docStart=0|0 props=0|0 flowPark=9519|0 \
block=0|0 contentish=9519|0 mapValue=0|0"
  , "colon_open_map_props :: noPending=0|0 docEnd=0|0 docStart=0|0 props=616|0 flowPark=616|0 \
block=0|0 contentish=616|0 mapValue=0|0"
  , "compact_open_map :: noPending=0|0 docEnd=1633|1633 docStart=1633|0 props=0|0 \
flowPark=18945|0 block=15912|0 contentish=18945|0 mapValue=18945|0"
  , "question_open_map :: noPending=10129|10129 docEnd=469|469 docStart=469|0 props=616|0 \
flowPark=10655|0 block=6142|0 contentish=10655|0 mapValue=7003|0"
  , "colon_fires_implicit_key :: noPending=0|0 docEnd=0|0 docStart=427|0 props=616|0 \
flowPark=20015|0 block=5511|0 contentish=20015|0 mapValue=6330|0"
  , "colon_fires_props_key :: noPending=0|0 docEnd=0|0 docStart=0|0 props=616|0 flowPark=616|0 \
block=0|0 contentish=616|0 mapValue=0|0"
  , "(indicator_open_map) :: noPending=36175|36175 docEnd=1633|1633 docStart=1633|0 props=2200|0 \
flowPark=42242|0 block=16256|0 contentish=42242|0 mapValue=19289|0" ]

/-- The raw fields at every visited state, then at the two marker parks.  The
    second and third rows are the single cause: `allowDirectives` is UP at
    **every** `docEnd` state and DOWN at **every** `docStart` state, and six of
    the seven other park predicates require it down. -/
def expectedFieldsAll : String :=
  "all n=216114 :: allowDirectives=52990 needIndentCheck=50645 simpleKeyAllowed=146250 \
simpleKey.possible=97665 col=0=50645 inFlow=31926 currentIndent<0=78325 lastRealB=216114"

def expectedFieldsEnd : String :=
  "docEnd n=2345 :: allowDirectives=2345 needIndentCheck=0 simpleKeyAllowed=2345 \
simpleKey.possible=0 col=0=0 inFlow=0 currentIndent<0=2345 lastRealB=2345"

def expectedFieldsStart : String :=
  "docStart n=2345 :: allowDirectives=0 needIndentCheck=0 simpleKeyAllowed=2345 \
simpleKey.possible=0 col=0=0 inFlow=0 currentIndent<0=2345 lastRealB=2345"

/-- Containments that hold at **every** synthetic state — candidates for proof,
    discharged in `Tests/Guards/Proofs/DeclineArmLattice.lean`. -/
def expectedEntailLoose : List String :=
  [ "docStart -> flowPark"
  , "docStart -> contentish"
  , "block -> flowPark"
  , "block -> contentish"
  , "contentish -> flowPark" ]

/-- The same with `pProps` tightened by the field the constructor carries.
    **Two more entailments, and not one reachable count moves.** -/
def expectedEntailTight : List String :=
  [ "docStart -> flowPark"
  , "docStart -> contentish"
  , "props -> flowPark"
  , "props -> contentish"
  , "block -> flowPark"
  , "block -> contentish"
  , "contentish -> flowPark" ]

/-- The residue: containments the scan never separates but a state CAN.  Each
    is a scanner invariant nobody has stated, and each carries the synthetic
    state that separates it.  Four of the five touch `mapValue` — the park
    whose reading has no column — and the fifth is the escape's own corner. -/
def expectedResidual : List String :=
  [ "docStart subseteq mapValue reachedSep=0 synthSep=96 :: ad=false nic=false ska=false \
skp=false flow=0 col=1 ci=-1 ek=false tok=docStart@0"
  , "flowPark subseteq contentish reachedSep=0 synthSep=160 :: ad=false nic=true ska=true \
skp=true flow=0 col=0 ci=-1 ek=false tok=empty"
  , "block subseteq mapValue reachedSep=0 synthSep=48 :: ad=false nic=false ska=true skp=false \
flow=0 col=1 ci=0 ek=false tok=empty"
  , "mapValue subseteq flowPark reachedSep=0 synthSep=256 :: ad=false nic=false ska=true \
skp=false flow=0 col=0 ci=-1 ek=false tok=scalar@0"
  , "mapValue subseteq contentish reachedSep=0 synthSep=256 :: ad=false nic=false ska=true \
skp=false flow=0 col=0 ci=-1 ek=false tok=scalar@0" ]

/-- **The mandate, executed.**  One alphabet per residual zero, 148 480
    programs and 632 239 steps beyond the shared domain.  `OWN` is the zero the
    alphabet was built to spell; `control:` is how often it visited each park,
    so that a zero is a READ zero.  Every `OWN` is 0. -/
def expectedTargeted : List String :=
  [ "flowPark-not-contentish frags=16 depth=4 programs=65536 steps=297472 accepted=16321 OWN=0 \
all=[0,0,0,0,0] control: noPending=124476 docEnd=10360 docStart=10360 props=16856 \
flowPark=221592 block=32347 contentish=221592 mapValue=83960"
  , "mapValue-not-contentish frags=12 depth=4 programs=20736 steps=100329 accepted=12052 OWN=0 \
all=[0,0,0,0,0] control: noPending=20735 docEnd=4741 docStart=4741 props=0 flowPark=74853 \
block=18553 contentish=74853 mapValue=36616"
  , "docStart-not-mapValue frags=12 depth=4 programs=20736 steps=82015 accepted=7756 OWN=0 \
all=[0,0,0,0,0] control: noPending=20720 docEnd=3850 docStart=29655 props=9163 flowPark=55155 \
block=3568 contentish=55155 mapValue=33223"
  , "block-not-mapValue frags=12 depth=4 programs=20736 steps=86705 accepted=12047 OWN=0 \
all=[0,0,0,0,0] control: noPending=20720 docEnd=4380 docStart=4380 props=0 flowPark=61605 \
block=30485 contentish=61605 mapValue=40004"
  , "docEnd-with-allowDirectives-false frags=12 depth=4 programs=20736 steps=65718 accepted=9513 \
OWN=0 all=[0,0,0,0,0] control: noPending=20720 docEnd=4330 docStart=4520 props=7500 \
flowPark=38358 block=12333 contentish=38358 mapValue=16853" ]

/-- **The arms.**  Of the thirty-eight cells that are genuine arms, four are
    empty over the domain — and all four are one row's, `colon_open_map_explicit`,
    plus `compact_open_map`'s props arm. -/
def expectedDomainArms : String :=
  "armCells=38 zero=4 :: colon_open_map_explicit/docEnd colon_open_map_explicit/docStart \
colon_open_map_explicit/props compact_open_map/props"

/-- Eight over the corpus, and the four extra are all `/docEnd`. -/
def expectedCorpusArms : String :=
  "armCells=38 zero=8 :: accum_block_on_closeThenBlock/docEnd colon_open_map/docEnd \
colon_open_map_explicit/docEnd colon_open_map_explicit/docStart compact_open_map/docEnd \
compact_open_map/props question_open_map/docEnd (indicator_open_map)/docEnd"

/-- The 402 leaves: **52** zero cells, five more than the domain, all in the
    `docEnd` column — item 219's finding at cell resolution. -/
def expectedCorpusStats : String :=
  "units=402 steps=2946 zeroIncl=52 zeroExcl=150 inclNonzeroExclZero=98 docEndStates=11 \
docStartStates=154"

def expectedCorpusParks : String :=
  "noPending=1059 docEnd=11 docStart=154 props=178 flowPark=2507 block=319 contentish=2507 \
mapValue=1205"

/-- And the corpus is **not** a subset of the domain: `props` and `noPending`
    hold together at six corpus states and at none of the 216 114 domain ones.
    Each sample misses something the other has. -/
def expectedCorpusCont : List String :=
  [ "noPending :: -docEnd=1059 -docStart=1059 -props=1053 -flowPark=399 -block=1059 \
-contentish=399 -mapValue=732"
  , "docEnd :: -noPending=11 -docStart=11 -props=11 -flowPark=11 -block=11 -contentish=11 \
-mapValue=11"
  , "docStart :: -noPending=154 -docEnd=154 -props=154 -flowPark=0 -block=154 -contentish=0 \
-mapValue=0"
  , "props :: -noPending=172 -docEnd=178 -docStart=178 -flowPark=0 -block=178 -contentish=0 \
-mapValue=178"
  , "flowPark :: -noPending=1847 -docEnd=2507 -docStart=2353 -props=2329 -block=2188 \
-contentish=0 -mapValue=1302"
  , "block :: -noPending=319 -docEnd=319 -docStart=319 -props=319 -flowPark=0 -contentish=0 \
-mapValue=0"
  , "contentish :: -noPending=1847 -docEnd=2507 -docStart=2353 -props=2329 -flowPark=0 \
-block=2188 -mapValue=1302"
  , "mapValue :: -noPending=878 -docEnd=1205 -docStart=1051 -props=1205 -flowPark=0 -block=886 \
-contentish=0" ]

def expectedCorpusMatrix : List String :=
  [ "accum_block_pending :: noPending=69|69 docEnd=0|0 docStart=17|0 props=24|0 flowPark=662|0 \
block=33|0 contentish=662|0 mapValue=77|0"
  , "accum_block_on_noPending :: noPending=69|69 docEnd=0|0 docStart=0|0 props=0|0 flowPark=0|0 \
block=0|0 contentish=0|0 mapValue=0|0"
  , "accum_block_on_closeThenBlock :: noPending=0|0 docEnd=0|0 docStart=17|0 props=24|0 \
flowPark=662|0 block=33|0 contentish=662|0 mapValue=77|0"
  , "accum_block_on_pendingBlock :: noPending=0|0 docEnd=0|0 docStart=0|0 props=0|0 \
flowPark=33|0 block=33|0 contentish=33|0 mapValue=33|0"
  , "accum_block_on_pendingBlockContent :: noPending=0|0 docEnd=0|0 docStart=17|0 props=24|0 \
flowPark=662|0 block=33|0 contentish=662|0 mapValue=77|0"
  , "accum_block_on_pendingContent :: noPending=0|0 docEnd=0|0 docStart=17|0 props=24|0 \
flowPark=662|0 block=33|0 contentish=662|0 mapValue=77|0"
  , "accum_content_pending :: noPending=160|160 docEnd=2|2 docStart=105|0 props=138|0 \
flowPark=1013|0 block=237|0 contentish=1013|0 mapValue=689|0"
  , "accum_content_on_pendingBlock_indented :: noPending=0|0 docEnd=0|0 docStart=0|0 props=0|0 \
flowPark=237|0 block=237|0 contentish=237|0 mapValue=237|0"
  , "accum_content_on_pendingMapValue_indented :: noPending=0|0 docEnd=0|0 docStart=105|0 \
props=0|0 flowPark=689|0 block=237|0 contentish=689|0 mapValue=689|0"
  , "content_dispatch_routed :: noPending=160|160 docEnd=2|2 docStart=105|0 props=138|0 \
flowPark=1013|0 block=237|0 contentish=1013|0 mapValue=689|0"
  , "accum_step_flow :: noPending=286|30 docEnd=0|0 docStart=19|0 props=7|0 flowPark=340|0 \
block=44|0 contentish=340|0 mapValue=126|0"
  , "colon_open_map :: noPending=3|3 docEnd=0|0 docStart=1|0 props=4|0 flowPark=415|0 block=2|0 \
contentish=415|0 mapValue=3|0"
  , "colon_open_map_explicit :: noPending=0|0 docEnd=0|0 docStart=0|0 props=1|0 flowPark=29|0 \
block=1|0 contentish=29|0 mapValue=1|0"
  , "colon_open_map_implicit :: noPending=0|0 docEnd=0|0 docStart=0|0 props=4|0 flowPark=408|0 \
block=0|0 contentish=408|0 mapValue=0|0"
  , "colon_open_map_props :: noPending=0|0 docEnd=0|0 docStart=0|0 props=5|0 flowPark=5|0 \
block=0|0 contentish=5|0 mapValue=0|0"
  , "compact_open_map :: noPending=0|0 docEnd=0|0 docStart=17|0 props=0|0 flowPark=92|0 \
block=33|0 contentish=92|0 mapValue=77|0"
  , "question_open_map :: noPending=11|11 docEnd=0|0 docStart=2|0 props=2|0 flowPark=25|0 \
block=4|0 contentish=25|0 mapValue=12|0"
  , "colon_fires_implicit_key :: noPending=0|0 docEnd=0|0 docStart=1|0 props=5|0 flowPark=437|0 \
block=2|0 contentish=437|0 mapValue=3|0"
  , "colon_fires_props_key :: noPending=0|0 docEnd=0|0 docStart=0|0 props=5|0 flowPark=5|0 \
block=0|0 contentish=5|0 mapValue=0|0"
  , "(indicator_open_map) :: noPending=69|69 docEnd=0|0 docStart=17|0 props=24|0 flowPark=662|0 \
block=33|0 contentish=662|0 mapValue=77|0" ]

/-! ## Reporting -/

def parksStr (m : Mat) : String := Id.run do
  let mut s := ""
  for j in [0:8] do
    if j != 0 then s := s ++ " "
    s := s ++ s!"{parkNames[j]!}={m.parks[j]!}"
  return s

def statsStr (m : Mat) : String :=
  let (zi, ze, both) := matZeros m
  s!"units={m.units} steps={m.steps} zeroIncl={zi} zeroExcl={ze} inclNonzeroExclZero={both} \
docEndStates={m.nEnd} docStartStates={m.nStart}"

def corpusMat (dataDir : String) : IO Mat := do
  let ps := (← leafPaths dataDir).qsort (fun a b => a.toString < b.toString)
  let mut m : Mat := {}
  for p in ps do
    let txt ← IO.FS.readFile p
    m := m.add (states txt).1
  return m

def main (args : List String) : IO UInt32 := do
  let emit := args.contains "--emit"
  let dirs := args.filter (fun a => a != "--emit")
  let mut ok := true
  let chk (label expected got : String) : IO Bool := do
    if emit then IO.println s!"{label} := {got}"; return true
    else check label expected got
  let chkL (label : String) (expected got : List String) : IO Bool := do
    if emit then
      IO.println s!"{label} :="
      for g in got do IO.println s!"  {g}"
      return true
    else checkList label expected got
  IO.println "── control: the visitor walks item 219's walk ───────────"
  let ctl := (controls.map (fun (p : String × String) => p.2)).all agree
  let mut bad := 0
  for p in programs do
    if !agree p then bad := bad + 1
  ok := (← chk "walkAgree" expectedWalkAgree
          s!"controls={ctl} domainPrograms={programs.length} disagree={bad}") && ok
  IO.println "── the matrix over the shared 37-fragment domain ────────"
  let m := domainMat
  ok := (← chk "domainStats" expectedDomainStats (statsStr m)) && ok
  ok := (← chk "domainParks" expectedDomainParks (parksStr m)) && ok
  ok := (← chkL "domainCont" expectedDomainCont (contRows m)) && ok
  ok := (← chkL "domainMatrix" expectedDomainMatrix (matRows m)) && ok
  ok := (← chk "domainArms" expectedDomainArms (armZeros m)) && ok
  ok := (← chk "fieldsAll" expectedFieldsAll (fieldRow "all" m.steps m.fAll)) && ok
  ok := (← chk "fieldsEnd" expectedFieldsEnd (fieldRow "docEnd" m.nEnd m.fEnd)) && ok
  ok := (← chk "fieldsStart" expectedFieldsStart (fieldRow "docStart" m.nStart m.fStart)) && ok
  IO.println "── the synthetic state space ───────────────────────────"
  IO.println s!"  states={synthStates.size}"
  let (entL, _) := lattice false
  let (entT, _) := lattice true
  ok := (← chkL "entailLoose" expectedEntailLoose entL) && ok
  ok := (← chkL "entailTight" expectedEntailTight entT) && ok
  ok := (← chkL "residual" expectedResidual (residual m true)) && ok
  IO.println "── the mandate: an alphabet per zero ───────────────────"
  ok := (← chkL "targeted" expectedTargeted targetedRows) && ok
  match dirs with
  | [] =>
    IO.println "── corpus ──────────────────────────────────────────────"
    IO.println "  skipped (pass the yaml-test-suite data directory to run it)"
  | dataDir :: _ =>
    IO.println "── corpus ──────────────────────────────────────────────"
    let cm ← corpusMat dataDir
    ok := (← chk "corpusStats" expectedCorpusStats (statsStr cm)) && ok
    ok := (← chk "corpusParks" expectedCorpusParks (parksStr cm)) && ok
    ok := (← chk "corpusArms" expectedCorpusArms (armZeros cm)) && ok
    ok := (← chkL "corpusCont" expectedCorpusCont (contRows cm)) && ok
    ok := (← chkL "corpusMatrix" expectedCorpusMatrix (matRows cm)) && ok
  if emit then
    IO.println "EMITTED"
    return 0
  else if ok then
    IO.println "ALL PINS OK"
    return 0
  else
    IO.println "PINS DISAGREE"
    return 1

end Tests.DeclineArmCensus
