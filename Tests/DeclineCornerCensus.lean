import Tests.DeclineArmCensus

/-!
# Which literal carries a zero (item 221)

Item 220 read five containments empty over its two input samples and separated
by the synthetic state space, and named them invariants nobody has stated.  A
five-literal conjunction that reads 0 does not say **which** literal carries the
zero, and the literal that carries it is the lemma to prove.  So this module
asks the smaller question.

## The instrument

Every park predicate in `Tests.DeclineReachCensus` is a Boolean expression over
seven atoms — the directive flag, the indent check, the two simple-key bits, "at
column 0", "the last token is real", and "the last real token is a `---` on this
line".  Each visited state therefore has a **seven-bit profile**, and one
128-bucket histogram over the walk is the whole measurement.  Everything below is arithmetic on that histogram:

* a containment's SEPARATOR PROFILE — which atoms are pinned, and to what, at
  every synthetic state where the containment fails — is read off the exhaustive
  synthetic space, and each one is restated and PROVED in
  `Tests/Guards/Proofs/DeclineArmInvariants.lean`, so it is not a sweep result;
* every sub-conjunction of a profile has its count summed out of the histogram
  in 128 additions, and the count is monotone in the subset, so the **minimal
  zero** — a conjunction that reads 0 and none of whose one-atom weakenings
  does — is well defined and is what the search returns.

**The minimal zero is the cheapest lemma.**  Item 220 proved the corner's full
five-literal profile as an iff and had to prove nothing about the scanner; the
minimal zero says how much of that iff a scanner argument actually has to kill.

## The state a park stands at

Items 219 and 220 read the park predicates at each step's LOOP-ENTRY state.
The park's own `sc` is the state after the dispatch: every `pendingFlow` site
pays `h_nic0` with `deferred_nic0_of_dispatch` or `content_park_nic_any`, and
both conclude about `s'` (`StreamAccum.lean:1737-1748`).  The two sets differ
only by the seed and the last step, so the reading should not move — but that
is a source reading, and §1 says a source reading is a hypothesis.  This census
therefore walks BOTH and pins the difference.
-/

namespace Tests.DeclineCornerCensus

open L4YAML L4YAML.Scanner
open Tests.DeclineReachCensus Tests.DeclineArmCensus

/-! ## §1  The seven atoms -/

/-- The seven Boolean atoms.  `dir` is `allowDirectives`, `real` is `lastRealB`
    — the census's Bool reading of `FlowAdjacency.LastTokenReal` — and `dsTok`
    is `pDocStart`'s marker conjunct, the atom the six-atom version of this
    search could not see. -/
def atomNames : Array String :=
  #["dir", "nic", "ska", "skp", "col0", "real", "dsTok"]

def nAtoms : Nat := 7

/-- **The atom set is a PROJECTION, and that is the whole of its honesty.**
    It carries every field `pContentish`, `pFlowPark`, `pMapValue` and
    `pDocStart` read, and it does NOT carry `pBlock`'s indent floor or stack
    top, `pNoPending`'s flow level and explicit-key line, `pProps`'s trailing
    run, or `pDocEnd`'s marker.  A separator profile read through the projection
    is therefore NECESSARY and may not be sufficient — so a sub-conjunction the
    search returns is always a genuine zero over the sample, and an EMPTY return
    means the projection cannot see the separator at all.  It never lies; it
    declines. -/
def atomVec (sc : ScannerState) : Array Bool :=
  #[sc.allowDirectives, sc.needIndentCheck, sc.simpleKeyAllowed,
    sc.simpleKey.possible, sc.col == 0, lastRealB sc.tokens,
    (match lastRealToken? sc.tokens with
     | some t => t.val == YamlToken.documentStart && t.pos.line == sc.line
     | none => false)]

/-- The state's seven-bit profile, atom `j` in bit `j`. -/
def atomMask (sc : ScannerState) : Nat := Id.run do
  let v := atomVec sc
  let mut m := 0
  for j in [0:nAtoms] do
    if v[j]! = true then m := m + (1 <<< j)
  return m

def bitOf (m j : Nat) : Bool := (m >>> j) % 2 == 1

/-- Item 219's `pMapValue` TIGHTENED with `pendingMapValue.h_col0 : 0 < sp_scan.col`,
    which `ScannerSurfCorr.col_eq` delivers at the runtime state and the reading
    drops — the same omission item 220 found on `pProps`, on the park item 220's
    own instrument debt named ("`pendingMapValue`'s reading has no column, which
    is why four of the five residual zeros touch it").  **The field was there all
    along.**  Adding it moves no reachable count and turns two of item 220's
    five "invariants" into theorems. -/
def pMapValueT (sc : ScannerState) : Bool := pMapValue sc && 0 < sc.col

/-! ## §2  The five containments item 220 left without a proof -/

def resNames : Array String :=
  #["docStart<=mapValue", "flowPark<=contentish", "block<=mapValue",
    "mapValue<=flowPark", "mapValue<=contentish"]

def resPair : Array ((ScannerState → Bool) × (ScannerState → Bool)) :=
  #[(pDocStart, pMapValue), (pFlowPark, pContentish), (pBlock, pMapValue),
    (pMapValue, pFlowPark), (pMapValue, pContentish)]

/-- `A` holds and `B` does not — the containment's separator. -/
def sepAt (i : Nat) (sc : ScannerState) : Bool :=
  let p := resPair[i]!
  p.1 sc && !p.2 sc

/-! ## §3  The histogram — the one measurement -/

structure Cen where
  units : Nat := 0
  nE : Nat := 0
  nP : Nat := 0
  hE : Array Nat := Array.replicate 128 0
  hP : Array Nat := Array.replicate 128 0
  sepE : Array Nat := Array.replicate 5 0
  sepP : Array Nat := Array.replicate 5 0
  parkE : Array Nat := Array.replicate 8 0
  parkP : Array Nat := Array.replicate 8 0
  /-- Entry states with the indent check armed that are NOT their program's
      seed — the number that says whether the entry reading's `nic` column is
      the stream seed and nothing else. -/
  nicNonSeed : Nat := 0
  col0NonSeed : Nat := 0
  /-- `pMapValue` and `pMapValueT` at the park state, and the two containments
      the tightening closes, measured under it. -/
  nMV : Nat := 0
  nMVT : Nat := 0
  sepT : Array Nat := Array.replicate 2 0
  deriving Inhabited

def Cen.merge (a b : Cen) : Cen := Id.run do
  let mut hE := a.hE; let mut hP := a.hP
  for m in [0:128] do
    hE := hE.set! m (hE[m]! + b.hE[m]!)
    hP := hP.set! m (hP[m]! + b.hP[m]!)
  let mut sepE := a.sepE; let mut sepP := a.sepP
  for i in [0:5] do
    sepE := sepE.set! i (sepE[i]! + b.sepE[i]!)
    sepP := sepP.set! i (sepP[i]! + b.sepP[i]!)
  let mut parkE := a.parkE; let mut parkP := a.parkP
  for j in [0:8] do
    parkE := parkE.set! j (parkE[j]! + b.parkE[j]!)
    parkP := parkP.set! j (parkP[j]! + b.parkP[j]!)
  return { units := a.units + b.units, nE := a.nE + b.nE, nP := a.nP + b.nP,
           hE := hE, hP := hP, sepE := sepE, sepP := sepP,
           parkE := parkE, parkP := parkP,
           nicNonSeed := a.nicNonSeed + b.nicNonSeed,
           col0NonSeed := a.col0NonSeed + b.col0NonSeed,
           nMV := a.nMV + b.nMV, nMVT := a.nMVT + b.nMVT,
           sepT := #[a.sepT[0]! + b.sepT[0]!, a.sepT[1]! + b.sepT[1]!] }

def Cen.add (c0 : Cen) (vs : Array (ScannerState × StepInfo)) : Cen := Id.run do
  let mut c := if vs.isEmpty then c0 else { c0 with units := c0.units + 1 }
  for sstIdx in vs.zipIdx do
    let sst : ScannerState × StepInfo := sstIdx.1
    let k : Nat := sstIdx.2
    let s : ScannerState := sst.1
    let m := atomMask s
    if k != 0 then
      if s.needIndentCheck then c := { c with nicNonSeed := c.nicNonSeed + 1 }
      if s.col == 0 then c := { c with col0NonSeed := c.col0NonSeed + 1 }
    let pv := parkVec s
    let hE := c.hE.set! m (c.hE[m]! + 1)
    let mut sepE := c.sepE
    for i in [0:5] do if sepAt i s then sepE := sepE.set! i (sepE[i]! + 1)
    let mut parkE := c.parkE
    for j in [0:8] do if pv[j]! = true then parkE := parkE.set! j (parkE[j]! + 1)
    c := { c with nE := c.nE + 1, hE := hE, sepE := sepE, parkE := parkE }
    match sst.2.sPost with
    | none => pure ()
    | some s' =>
      let m' := atomMask s'
      let pv' := parkVec s'
      let hP := c.hP.set! m' (c.hP[m']! + 1)
      let mut sepP := c.sepP
      for i in [0:5] do if sepAt i s' then sepP := sepP.set! i (sepP[i]! + 1)
      let mut parkP := c.parkP
      for j in [0:8] do if pv'[j]! = true then parkP := parkP.set! j (parkP[j]! + 1)
      let mut sepT := c.sepT
      if pMapValueT s' && !pFlowPark s' then sepT := sepT.set! 0 (sepT[0]! + 1)
      if pMapValueT s' && !pContentish s' then sepT := sepT.set! 1 (sepT[1]! + 1)
      c := { c with nP := c.nP + 1, hP := hP, sepP := sepP, parkP := parkP,
                    nMV := c.nMV + (if pMapValue s' then 1 else 0),
                    nMVT := c.nMVT + (if pMapValueT s' then 1 else 0),
                    sepT := sepT }
  return c

/-- The histogram itself, nonzero buckets only — the datum every count below is
    summed out of. -/
def histStr (h : Array Nat) : String := Id.run do
  let mut parts : List String := []
  for m in [0:128] do
    if h[m]! != 0 then
      let mut nm := ""
      for j in [0:nAtoms] do
        if bitOf m j then nm := nm ++ (if nm.isEmpty then "" else "+") ++ atomNames[j]!
      let label := if nm.isEmpty then "-" else nm
      parts := parts ++ [s!"{label}={h[m]!}"]
  return String.intercalate " " parts

/-! ## §4  The separator profile, read off the exhaustive synthetic space -/

/-- Which atoms are constant at every synthetic state that separates
    containment `i`, and to what value.  Each profile is restated and proved in
    `Tests.Guards.DeclineArmInvariants`; this is the reading that FOUND it. -/
def sepProfile (i : Nat) : Array (Option Bool) := Id.run do
  let mut prof : Array (Option Bool) := Array.replicate nAtoms none
  let mut seen := false
  for sn in synthStates do
    let s : ScannerState := sn.1
    if sepAt i s then
      let v := atomVec s
      if !seen then
        prof := v.map some
        seen := true
      else
        for j in [0:nAtoms] do
          if prof[j]! == some (!v[j]!) then prof := prof.set! j none
  return prof

def profStr (prof : Array (Option Bool)) : String := Id.run do
  let mut parts : List String := []
  for j in [0:nAtoms] do
    match prof[j]! with
    | some b => parts := parts ++ [s!"{atomNames[j]!}={if b then 1 else 0}"]
    | none => pure ()
  return if parts.isEmpty then "(none)" else String.intercalate "," parts

def sepSynth (i : Nat) : Nat := Id.run do
  let mut n := 0
  for sn in synthStates do
    if sepAt i sn.1 then n := n + 1
  return n

/-! ## §5  Sub-conjunction counts — arithmetic on the histogram -/

/-- The number of visited states whose profile agrees with `prof` on every atom
    in `sub`.  Summed out of the 64 buckets; no state is visited again. -/
def subCount (h : Array Nat) (prof : Array (Option Bool)) (sub : Nat) : Nat := Id.run do
  let mut n := 0
  for m in [0:128] do
    if h[m]! != 0 then
      let mut hit := true
      for j in [0:nAtoms] do
        if bitOf sub j then
          match prof[j]! with
          | some w => if bitOf m j != w then hit := false
          | none => hit := false
      if hit then n := n + h[m]!
  return n

def subStr (prof : Array (Option Bool)) (sub : Nat) : String := Id.run do
  let mut parts : List String := []
  for j in [0:nAtoms] do
    if bitOf sub j then
      match prof[j]! with
      | some b => parts := parts ++ [s!"{atomNames[j]!}={if b then 1 else 0}"]
      | none => parts := parts ++ [s!"{atomNames[j]!}=?"]
  return if parts.isEmpty then "(empty)" else String.intercalate "^" parts

def popCount (n : Nat) : Nat := Id.run do
  let mut k := 0
  for j in [0:nAtoms] do if bitOf n j then k := k + 1
  return k

/-- The subsets of `prof`'s pinned atoms that read 0 and whose every one-atom
    weakening reads more than 0.  The count is monotone in the subset, so these
    are exactly the minimal zeros — and each is a lemma that closes the
    containment. -/
def minimalZeros (h : Array Nat) (prof : Array (Option Bool)) : List String := Id.run do
  let mut pinned := 0
  for j in [0:nAtoms] do
    if prof[j]!.isSome then pinned := pinned + (1 <<< j)
  let mut out : List String := []
  for sub in [1:128] do
    if sub &&& pinned == sub && subCount h prof sub == 0 then
      let mut minimal := true
      for j in [0:nAtoms] do
        if bitOf sub j then
          if subCount h prof (sub - (1 <<< j)) == 0 then minimal := false
      if minimal then out := out ++ [s!"{subStr prof sub}(k={popCount sub})"]
  return out

/-- One row per containment: what the separator pins, how many synthetic states
    separate it, how many walked states reach the separator at the loop-entry
    state and at the park's own state, and the minimal zeros. -/
def resRows (c : Cen) : List String :=
  (List.range 5).map fun i =>
    let prof := sepProfile i
    let mz := minimalZeros c.hP prof
    s!"{resNames[i]!} pins={profStr prof} synthSep={sepSynth i} \
entry={c.sepE[i]!} park={c.sepP[i]!} minimal=[{String.intercalate " " mz}]"

/-- The singleton counts, which is what says a minimal zero is READ and not an
    artifact of an atom the walk never sets. -/
def atomRow (h : Array Nat) (n : Nat) : String := Id.run do
  let mut parts : List String := []
  for j in [0:nAtoms] do
    let mut t := 0
    for m in [0:128] do
      if bitOf m j then t := t + h[m]!
    parts := parts ++ [s!"{atomNames[j]!}={t}"]
  return s!"n={n} :: " ++ String.intercalate " " parts

def parkAgree (c : Cen) : String := Id.run do
  let mut parts : List String := []
  for j in [0:8] do
    parts := parts ++ [s!"{parkNames[j]!}={c.parkE[j]!}/{c.parkP[j]!}"]
  return s!"entry={c.nE} park={c.nP} :: " ++ String.intercalate " " parts

/-! ## §6  The samples

The shared domain is item 204's 37 fragments, cubed.  **Those 37 fragments
contain no `|` and no `>`** — `blockScalarFrags` below counts them and the count
is pinned — and a block scalar is the one content scan that ends at a line
start with the indent check armed (`StreamAccum.lean:1745`, item 154's
`content_park_nic`).  So the shared domain cannot spell the only shape that
puts a park at column 0, and a zero it reads in the `nic` or `col0` column is
an unread zero.

This is the case item 220's rule does not cover.  Item 220 widened the alphabet
five times on a hunch and moved nothing, and concluded that widening the
alphabet is the expensive way to read a zero.  It is — **when the missing shape
cannot be named.**  Here it can: the shape is `|`, the predicate that reads it
is `col0`, and one sixteen-fragment alphabet settles it in a second. -/

/-- How many of an alphabet's fragments carry a block-scalar head. -/
def blockScalarFrags (fs : List String) : Nat :=
  (fs.filter (fun f => f.any (fun ch => ch == '|' || ch == '>'))).length

/-- Sixteen fragments chosen to put a block scalar's park at column 0: a head,
    a content line that clears the floor, and the ordinary surroundings so the
    park lands in every context the domain's own fragments open. -/
def bsFrags : List String :=
  [ "a: |", "a: >", "- |", "- >", "|", ">", "|-", ">+",
    "  x", "  y", "b: 2", "- c", "", "---", "...", "? k" ]

def bsPrograms : List String :=
  bsFrags.flatMap fun a => bsFrags.flatMap fun b => bsFrags.map fun c =>
    a ++ "\n" ++ b ++ "\n" ++ c ++ "\n"

def cenOf (progs : List String) : Cen := Id.run do
  let mut c : Cen := {}
  for p in progs do
    c := c.add (states p).1
  return c

def domainCen : Cen := cenOf programs
def bsCen : Cen := cenOf bsPrograms

def corpusCen (dataDir : String) : IO Cen := do
  let ps := (← leafPaths dataDir).qsort (fun a b => a.toString < b.toString)
  let mut c : Cen := {}
  for p in ps do
    let txt ← IO.FS.readFile p
    c := c.add (states txt).1
  return c

/-- The seed/terminal accounting.  Items 219 and 220 read the park predicates at
    each step's LOOP-ENTRY state, which is the park a decline writer BRANCHES
    ON.  This census reads them at the post-dispatch state as well, which is the
    park a producer CREATES — the `sc` every `h_nic0` term concludes about.  The
    two populations are not the same, and this row is how much they differ. -/
def acctRow (c : Cen) : String :=
  s!"units={c.units} entry={c.nE} park={c.nP} seeds={c.units} \
entryNonSeed={c.nE - c.units} terminalParks={c.nP + c.units - c.nE} \
nicNonSeed={c.nicNonSeed} col0NonSeed={c.col0NonSeed}"

def sampleRows (c : Cen) : List String :=
  [ s!"entryAtoms {atomRow c.hE c.nE}"
  , s!"parkAtoms  {atomRow c.hP c.nP}"
  , s!"parkHist   {histStr c.hP}"
  , s!"acct       {acctRow c}"
  , s!"tighten    mapValue={c.nMV} mapValueT={c.nMVT} \
mapValueT<=flowPark={c.sepT[0]!} mapValueT<=contentish={c.sepT[1]!}" ]
  ++ resRows c

/-! ## §7  The pins -/

/-- The named gap: not one of item 204's 37 fragments carries a block-scalar
    head, and the block scalar is the only content scan that parks at a line
    start. -/
def expectedAlphabet : String :=
  "domainFrags=37 domainBlockScalarFrags=0 bsFrags=16 bsBlockScalarFrags=8 \
domainPrograms=50653 bsPrograms=4096"

/-- **Every `nic` and every `col0` reads 0 at a park state here — and both are
    coverage artifacts.**  The alphabet cannot spell `|`, so the corner's
    minimal zeros come back at k=1 and neither of them is a theorem. -/
def expectedDomain : List String :=
  [ "entryAtoms n=216114 :: dir=52990 nic=50645 ska=146250 skp=97665 col0=50645 real=216114 \
dsTok=2345"
  , "parkAtoms  n=202372 :: dir=3076 nic=0 ska=108759 skp=123738 col0=0 real=202372 dsTok=3076"
  , "parkHist   ska+real=72482 dir+ska+real=3076 skp+real=93613 ska+skp+real=30125 \
ska+real+dsTok=3076"
  , "acct       units=50645 entry=216114 park=202372 seeds=50645 entryNonSeed=165469 \
terminalParks=36903 nicNonSeed=0 col0NonSeed=0"
  , "tighten    mapValue=105683 mapValueT=105683 mapValueT<=flowPark=0 mapValueT<=contentish=0"
  , "docStart<=mapValue pins=dir=0,nic=0,ska=0,col0=0,real=1,dsTok=1 synthSep=96 entry=0 \
park=0 minimal=[ska=0^dsTok=1(k=2)]"
  , "flowPark<=contentish pins=dir=0,nic=1,ska=1,skp=1,col0=1 synthSep=160 entry=0 park=0 \
minimal=[nic=1(k=1) col0=1(k=1)]"
  , "block<=mapValue pins=dir=0,nic=0,ska=1,col0=0,real=0,dsTok=0 synthSep=48 entry=0 park=0 \
minimal=[real=0(k=1)]"
  , "mapValue<=flowPark pins=dir=0,nic=0,ska=1,col0=1,real=1 synthSep=256 entry=0 park=0 \
minimal=[col0=1(k=1)]"
  , "mapValue<=contentish pins=dir=0,nic=0,ska=1,col0=1,real=1 synthSep=256 entry=0 park=0 \
minimal=[col0=1(k=1)]"
  ]

/-- Sixteen fragments and 4 096 programs move `nic` at a park state from 0 to
    **3 930** and the corner's minimal zeros from k=1 to k=2. -/
def expectedBlockScalar : List String :=
  [ "entryAtoms n=12996 :: dir=4590 nic=6137 ska=10141 skp=4097 col0=6137 real=12996 dsTok=495"
  , "parkAtoms  n=12144 :: dir=738 nic=3930 ska=8504 skp=4942 col0=3930 real=12144 dsTok=738"
  , "parkHist   ska+real=1796 dir+ska+real=738 skp+real=3640 ska+skp+real=1302 \
nic+ska+col0+real=3930 ska+real+dsTok=738"
  , "acct       units=4095 entry=12996 park=12144 seeds=4095 entryNonSeed=8901 \
terminalParks=3243 nicNonSeed=2042 col0NonSeed=2042"
  , "tighten    mapValue=3836 mapValueT=3836 mapValueT<=flowPark=0 mapValueT<=contentish=0"
  , "docStart<=mapValue pins=dir=0,nic=0,ska=0,col0=0,real=1,dsTok=1 synthSep=96 entry=0 \
park=0 minimal=[ska=0^dsTok=1(k=2)]"
  , "flowPark<=contentish pins=dir=0,nic=1,ska=1,skp=1,col0=1 synthSep=160 entry=0 park=0 \
minimal=[nic=1^skp=1(k=2) skp=1^col0=1(k=2)]"
  , "block<=mapValue pins=dir=0,nic=0,ska=1,col0=0,real=0,dsTok=0 synthSep=48 entry=0 park=0 \
minimal=[real=0(k=1)]"
  , "mapValue<=flowPark pins=dir=0,nic=0,ska=1,col0=1,real=1 synthSep=256 entry=0 park=0 \
minimal=[nic=0^col0=1(k=2)]"
  , "mapValue<=contentish pins=dir=0,nic=0,ska=1,col0=1,real=1 synthSep=256 entry=0 park=0 \
minimal=[nic=0^col0=1(k=2)]"
  ]

def expectedUnion : List String :=
  [ "entryAtoms n=229110 :: dir=57580 nic=56782 ska=156391 skp=101762 col0=56782 real=229110 \
dsTok=2840"
  , "parkAtoms  n=214516 :: dir=3814 nic=3930 ska=117263 skp=128680 col0=3930 real=214516 \
dsTok=3814"
  , "parkHist   ska+real=74278 dir+ska+real=3814 skp+real=97253 ska+skp+real=31427 \
nic+ska+col0+real=3930 ska+real+dsTok=3814"
  , "acct       units=54740 entry=229110 park=214516 seeds=54740 entryNonSeed=174370 \
terminalParks=40146 nicNonSeed=2042 col0NonSeed=2042"
  , "tighten    mapValue=109519 mapValueT=109519 mapValueT<=flowPark=0 mapValueT<=contentish=0"
  , "docStart<=mapValue pins=dir=0,nic=0,ska=0,col0=0,real=1,dsTok=1 synthSep=96 entry=0 \
park=0 minimal=[ska=0^dsTok=1(k=2)]"
  , "flowPark<=contentish pins=dir=0,nic=1,ska=1,skp=1,col0=1 synthSep=160 entry=0 park=0 \
minimal=[nic=1^skp=1(k=2) skp=1^col0=1(k=2)]"
  , "block<=mapValue pins=dir=0,nic=0,ska=1,col0=0,real=0,dsTok=0 synthSep=48 entry=0 park=0 \
minimal=[real=0(k=1)]"
  , "mapValue<=flowPark pins=dir=0,nic=0,ska=1,col0=1,real=1 synthSep=256 entry=0 park=0 \
minimal=[nic=0^col0=1(k=2)]"
  , "mapValue<=contentish pins=dir=0,nic=0,ska=1,col0=1,real=1 synthSep=256 entry=0 park=0 \
minimal=[nic=0^col0=1(k=2)]"
  ]

/-- The corpus knocks out one more: `nic=1^skp=1` is REACHED here (four states),
    so the corner's minimal zero rises to k=3 on that branch. -/
def expectedCorpus : List String :=
  [ "entryAtoms n=2946 :: dir=439 nic=460 ska=1701 skp=1525 col0=438 real=2942 dsTok=154"
  , "parkAtoms  n=2877 :: dir=52 nic=107 ska=1380 skp=1781 col0=82 real=2873 dsTok=162"
  , "parkHist   dir+ska+skp=4 real=3 ska+real=806 dir+ska+real=22 nic+ska+real=21 \
skp+real=1490 nic+skp+real=4 ska+skp+real=257 dir+ska+skp+real=26 nic+ska+col0+real=82 \
ska+real+dsTok=162"
  , "acct       units=399 entry=2946 park=2877 seeds=399 entryNonSeed=2547 terminalParks=330 \
nicNonSeed=61 col0NonSeed=39"
  , "tighten    mapValue=1225 mapValueT=1225 mapValueT<=flowPark=0 mapValueT<=contentish=0"
  , "docStart<=mapValue pins=dir=0,nic=0,ska=0,col0=0,real=1,dsTok=1 synthSep=96 entry=0 \
park=0 minimal=[ska=0^dsTok=1(k=2)]"
  , "flowPark<=contentish pins=dir=0,nic=1,ska=1,skp=1,col0=1 synthSep=160 entry=0 park=0 \
minimal=[nic=1^ska=1^skp=1(k=3) skp=1^col0=1(k=2)]"
  , "block<=mapValue pins=dir=0,nic=0,ska=1,col0=0,real=0,dsTok=0 synthSep=48 entry=0 park=0 \
minimal=[dir=0^real=0(k=2)]"
  , "mapValue<=flowPark pins=dir=0,nic=0,ska=1,col0=1,real=1 synthSep=256 entry=0 park=0 \
minimal=[nic=0^col0=1(k=2)]"
  , "mapValue<=contentish pins=dir=0,nic=0,ska=1,col0=1,real=1 synthSep=256 entry=0 park=0 \
minimal=[nic=0^col0=1(k=2)]"
  ]

/-- **The decisive row.**  One candidate survives all three samples for the
    corner — `skp=1^col0=1` — and it is exactly what
    `dispatchContent_arm_or_col_any` has proved since item 77. -/
def expectedAllThree : List String :=
  [ "entryAtoms n=232056 :: dir=58019 nic=57242 ska=158092 skp=103287 col0=57220 real=232052 \
dsTok=2994"
  , "parkAtoms  n=217393 :: dir=3866 nic=4037 ska=118643 skp=130461 col0=4012 real=217389 \
dsTok=3976"
  , "parkHist   dir+ska+skp=4 real=3 ska+real=75084 dir+ska+real=3836 nic+ska+real=21 \
skp+real=98743 nic+skp+real=4 ska+skp+real=31684 dir+ska+skp+real=26 \
nic+ska+col0+real=4012 ska+real+dsTok=3976"
  , "acct       units=55139 entry=232056 park=217393 seeds=55139 entryNonSeed=176917 \
terminalParks=40476 nicNonSeed=2103 col0NonSeed=2081"
  , "tighten    mapValue=110744 mapValueT=110744 mapValueT<=flowPark=0 mapValueT<=contentish=0"
  , "docStart<=mapValue pins=dir=0,nic=0,ska=0,col0=0,real=1,dsTok=1 synthSep=96 entry=0 \
park=0 minimal=[ska=0^dsTok=1(k=2)]"
  , "flowPark<=contentish pins=dir=0,nic=1,ska=1,skp=1,col0=1 synthSep=160 entry=0 park=0 \
minimal=[nic=1^ska=1^skp=1(k=3) skp=1^col0=1(k=2)]"
  , "block<=mapValue pins=dir=0,nic=0,ska=1,col0=0,real=0,dsTok=0 synthSep=48 entry=0 park=0 \
minimal=[dir=0^real=0(k=2)]"
  , "mapValue<=flowPark pins=dir=0,nic=0,ska=1,col0=1,real=1 synthSep=256 entry=0 park=0 \
minimal=[nic=0^col0=1(k=2)]"
  , "mapValue<=contentish pins=dir=0,nic=0,ska=1,col0=1,real=1 synthSep=256 entry=0 park=0 \
minimal=[nic=0^col0=1(k=2)]"
  ]

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
  IO.println "── the named gap in the shared alphabet ────────────────"
  ok := (← chk "alphabet" expectedAlphabet
          s!"domainFrags={frags.length} domainBlockScalarFrags={blockScalarFrags frags} \
bsFrags={bsFrags.length} bsBlockScalarFrags={blockScalarFrags bsFrags} \
domainPrograms={programs.length} bsPrograms={bsPrograms.length}") && ok
  IO.println "── the shared 37-fragment domain ───────────────────────"
  let cd := domainCen
  ok := (← chkL "domain" expectedDomain (sampleRows cd)) && ok
  IO.println "── the block-scalar alphabet ───────────────────────────"
  let cb := bsCen
  ok := (← chkL "blockScalar" expectedBlockScalar (sampleRows cb)) && ok
  IO.println "── both together ──────────────────────────────────────"
  ok := (← chkL "union" expectedUnion (sampleRows (Cen.merge cd cb))) && ok
  match dirs with
  | [] =>
    IO.println "── corpus ──────────────────────────────────────────────"
    IO.println "  skipped (pass the yaml-test-suite data directory to run it)"
  | dataDir :: _ =>
    IO.println "── corpus ──────────────────────────────────────────────"
    let cc ← corpusCen dataDir
    ok := (← chkL "corpus" expectedCorpus (sampleRows cc)) && ok
    IO.println "── all three samples ───────────────────────────────────"
    ok := (← chkL "allThree" expectedAllThree
            (sampleRows (Cen.merge (Cen.merge cd cb) cc))) && ok
  if emit then
    IO.println "EMITTED"
    return 0
  else if ok then
    IO.println "ALL PINS OK"
    return 0
  else
    IO.println "PINS DISAGREE"
    return 1

end Tests.DeclineCornerCensus
