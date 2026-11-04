module

public import Scripts.Price.Env
public import Scripts.Price.ParkTop
public import Scripts.Price.VslotTop
public import Scripts.Price.MvSlotTop
public import Scripts.Price.OpenMap
public import Scripts.Price.ParkNic0
public import Scripts.Price.LandingNic0
public import Scripts.Price.Carrier
public import Scripts.Price.Wire
public import Scripts.Price.Arm
public import Scripts.Price.Ride
public import Scripts.Lean.DeclRanges
public import Scripts.Price.Close
public import Scripts.Price.InlineClass
public import Scripts.Price.Ride

/-!
# `lake run price -- SCRIPT [MODE…]` — the six `*_price.py` of items 205–210 in Lean

Rule 9 phase 3.3: `park_top_price.py`, `vslot_top_price.py`, `mv_slot_top_price.py`,
`open_map_price.py`, `park_nic0_price.py` and `landing_nic0_price.py` as sub-commands of
one exe.  Each patches a probe into `L4YAML/Proofs/Production/StreamAccum.lean`, runs
`lake env lean` on it, restores the bytes (digests on stderr) and prints the Python's
report, line for line (`Scripts.Price.*` are the pure readings).  Never run one beside a
`lake build`.

exit status: 0 report printed; 1 an anchor is not where the probe expects it (the Python's
`AssertionError` / `KeyError`), or the file was not restored; 2 usage.
-/

namespace Scripts.MainPrice

open Scripts.Price.Attribute (errorLines sortedNat)

def target : String := Scripts.Punt.Price.target

def version : String := "scripts-price 1.0 (Rule 9 phase 3.3)"

def usage : String := s!"usage: lake run price -- SCRIPT [MODE…] [-C ROOT]

  park-top     [ring1|all|<park>]          park_top_price.py (item 205): the park-TOP carrier by rings
  vslot-top                                vslot_top_price.py (item 208): the SLOT-TOP conjunct's payers
  mv-slot-top                              mv_slot_top_price.py (item 209): the slot's own stack top
  open-map     [LEMMA…]                    open_map_price.py (item 209): the dispatch-floor ring
  park-nic0    [{Scripts.Price.ParkNic0.usageModes}]
                                           park_nic0_price.py (items 206/207): the armed-at-column-zero carrier
  landing-nic0 [<lemma>|all|payers|drop]   landing_nic0_price.py (item 210): item 154's flag at the block landing
  carrier      [core|slot|prop|consumer|gate|all]   carrier_price.py (items 266/267): the built carrier by producers
  wire         [gate|anchor|route|eof|all] [--wide] wire_price.py (item 268): the carrier's wiring (`--wide`: lake build)
  arm                                      arm_price.py (item 270): what each arm holds, premise by premise (24 runs)
  coordinate   [bridge|ident|split|all|wide] coordinate_price.py (item 271): the bridge, the arms' identity, the arity flip
  transport    [arms|optok|frames|pay|ride|all|wide] transport_price.py (item 272): the open token's position through the arms
  ride         [arm|ride|carrier|transport|all|wide] ride_price.py (item 273): the arms with the ring paid; ride/carrier/transport flips
  close        [probe|name|flip|all|wide] close_price.py (item 274): what the frame's CLOSE can pay for a reshaped carrier
  inline-class [feeders|arms|census]       inline_class_price.py (items 286/287): the escape's INLINE class (pins in BlockDeferralClasses.lean)
  -C, --root ROOT  repository root (default: the current directory)
  -h, --help / -V, --version

`all` of carrier/wire/coordinate/transport/ride and `arm` end by comparing their line with the pin in
Tests/Guards/Proofs/ScannerFlowOpenUnderRun.lean (`expectedCarrierPrice`, `expectedWirePrice`,
`expectedArmTable`, `expectedCoordPrice`, `expectedTransportPrice`, `expectedRidePrice`); exit 1 when it
disagrees or is absent.  The `wide` mode of coordinate/transport/ride runs `lake build` on the patched tree.  Each mode but `payers` patches {target} in place, runs `lake env lean` on it and restores
it (digests on stderr); never run one beside a `lake build`."

def die (msg : String) (code : UInt32 := 1) : IO UInt32 := do
  IO.eprintln msg; pure code

def printAll (ls : Array String) : IO Unit := do
  let out ← IO.getStdout
  for l in ls do out.putStrLn l

def readLines (text : String) : Array String := (text.splitOn "\n").toArray

/-- One probe: print the headline (the Python prints it before the run), run, report. -/
def probeRun (root : System.FilePath) (suffix original : String) (headline : String)
    (patched : Except String (Array String)) (report : Array String → String → Array String) : IO UInt32 := do
  match patched with
  | .error e => die e
  | .ok patched =>
    IO.println headline
    match ← Scripts.Price.Env.leanOn root target suffix original patched with
    | .error e => die e
    | .ok (_, body) => printAll (report patched body); pure 0

def parkTop (root : System.FilePath) (original : String) (lines : Array String) (pos : List String) : IO UInt32 := do
  let which := pos.headD "ring1"
  if !Scripts.Price.ParkTop.modes.contains which then
    return ← die s!"usage: park_top_price.py [{Scripts.Price.ParkTop.usageModes}]"
  let names := (Scripts.Price.ParkTop.applyProbe lines which).toOption.map (·.2) |>.getD #[]
  probeRun root ".parktop-bak" original s!"probe: {which} -> {", ".intercalate names.toList}"
    ((Scripts.Price.ParkTop.applyProbe lines which).map (·.1))
    (fun patched body => Scripts.Price.ParkTop.report patched names body)

def vslotTop (root : System.FilePath) (original : String) (lines : Array String) : IO UInt32 :=
  probeRun root ".vslot-bak" original Scripts.Price.VslotTop.headline
    (Scripts.Price.VslotTop.applyProbe lines) Scripts.Price.VslotTop.report

def mvSlotTop (root : System.FilePath) (original : String) (lines : Array String) : IO UInt32 :=
  probeRun root ".mvslot-bak" original Scripts.Price.MvSlotTop.headline
    (Scripts.Price.MvSlotTop.applyProbe lines) Scripts.Price.MvSlotTop.report

def openMap (root : System.FilePath) (original : String) (lines : Array String) (pos : List String) : IO UInt32 := do
  let names := if pos.isEmpty then Scripts.Price.OpenMap.lemmas else pos
  let bad := names.filter fun n => !Scripts.Price.OpenMap.lemmas.contains n
  if !bad.isEmpty then
    return ← die s!"unknown lemma(s) {bad}; known: {", ".intercalate Scripts.Price.OpenMap.lemmas}"
  probeRun root ".openmap-bak" original (Scripts.Price.OpenMap.headline names)
    (Scripts.Price.OpenMap.applyProbe lines names)
    (fun patched body => Scripts.Price.OpenMap.report patched names body)

def parkNic0 (root : System.FilePath) (original : String) (lines : Array String) (pos : List String) : IO UInt32 := do
  let which := pos.headD "pendingFlow"
  if which == "payers" then printAll (Scripts.Price.ParkNic0.payersReport lines); return 0
  if !Scripts.Price.ParkNic0.modes.contains which then
    return ← die s!"usage: park_nic0_price.py [{Scripts.Price.ParkNic0.usageModes}]"
  let names := (Scripts.Price.ParkNic0.applyProbe lines which).toOption.map (·.2) |>.getD #[]
  probeRun root ".nic0-bak" original (Scripts.Price.ParkNic0.headline which names)
    ((Scripts.Price.ParkNic0.applyProbe lines which).map (·.1))
    (fun patched body => Scripts.Price.ParkNic0.report patched which names body)

def landingNic0 (root : System.FilePath) (original : String) (lines : Array String) (pos : List String) : IO UInt32 := do
  let which := pos.headD "all"
  if which == "payers" then printAll (Scripts.Price.LandingNic0.payersReport lines); return 0
  if which == "drop" then
    match Scripts.Price.LandingNic0.carriers lines with
    | .error e => return ← die e
    | .ok cs =>
      IO.println (Scripts.Price.LandingNic0.carriersLine cs); IO.println ""
      for n in cs do
        match Scripts.Price.LandingNic0.applyDrop lines n with
        | .error e => return ← die e
        | .ok (patched, _) =>
          match ← Scripts.Price.Env.leanOn root target ".landing-bak" original patched with
          | .error e => return ← die e
          | .ok (_, body) => printAll (Scripts.Price.LandingNic0.dropLines n (sortedNat (errorLines body)))
      return 0
  if !Scripts.Price.LandingNic0.modes.contains which then
    return ← die s!"usage: landing_nic0_price.py [{Scripts.Price.LandingNic0.usageModes}]"
  let names := (Scripts.Price.LandingNic0.applyProbe lines which).toOption.map (·.2) |>.getD #[]
  probeRun root ".landing-bak" original (Scripts.Price.LandingNic0.headline which names)
    ((Scripts.Price.LandingNic0.applyProbe lines which).map (·.1))
    (fun patched body => Scripts.Price.LandingNic0.report patched names body)

/-- `line ↦ declaration` for a patched copy of the target, off the module's declaration ranges
    (`Scripts.Lean.DeclRanges`); `run` has `lake build` the pristine module first, so the ranges
    describe the source the probe read.  A missing `.olean` is a failure, not a reading. -/
def declOwner (root : System.FilePath) (pristine patched : Array String) : IO (Except String (Nat → String)) := do
  let olean := root / ".lake" / "build" / "lib" / "lean" / "L4YAML" / "Proofs" / "Production" / "StreamAccum.olean"
  if !(← olean.pathExists) then
    return .error s!"{olean} is missing -- build the library first (the declaration census reads the module's declaration ranges from it)"
  try
    let ds := Scripts.Lean.DeclRanges.decls (← Scripts.Lean.DeclRanges.readRanges olean)
    if ds.isEmpty then return .error s!"{olean}: no declaration ranges -- build the library first"
    let m := Scripts.Lean.DeclRanges.lineMap pristine patched
    return .ok fun l => Scripts.Lean.DeclRanges.ownerOf ds (m.getD (l - 1) l)
  catch e => return .error s!"reading the declaration ranges of {olean}: {e}"

def readPin (root : System.FilePath) : IO (Option String) := do
  let p := root / Scripts.Price.Pin.pin
  if ← p.pathExists then return some (← IO.FS.readFile p) else return none

def carrier (root : System.FilePath) (original : String) (lines : Array String) (pos : List String) : IO UInt32 := do
  let which := pos.headD "core"
  let one (p : String) : IO (Except String (Array Nat × Array (String × Array Nat))) := do
    match Scripts.Price.Carrier.applyProbe lines p with
    | .error e => return .error e
    | .ok patched =>
      match ← Scripts.Price.Env.leanOn root target ".carrier-price-bak" original patched with
      | .error e => return .error e
      | .ok (_, out) =>
        match ← declOwner root lines patched with
        | .error e => return .error e
        | .ok owner => return Scripts.Price.Carrier.reading p owner out
  if which == "all" then
    let mut got : Array String := #[]
    for p in Scripts.Price.Carrier.probes do
      match ← one p with
      | .error e => return ← die e
      | .ok (raw, decls) =>
        IO.println (Scripts.Price.Carrier.allRow p raw.size decls.size (Scripts.Price.Carrier.names decls))
        got := got.push s!"{p}={decls.size}"
    let gotS := " ".intercalate got.toList
    IO.println ""; IO.println s!"CARRIER-PRICE {gotS}"
    let want := (← readPin root).bind (Scripts.Price.Pin.expectedLiteral? · "expectedCarrierPrice")
    let (ls, rc) := Scripts.Price.Pin.pinVerdict "CARRIER" want gotS
    printAll ls; return rc
  if !Scripts.Price.Carrier.probes.contains which then return ← die Scripts.Price.Carrier.usage
  match ← one which with
  | .error e => die e
  | .ok (raw, decls) => printAll (Scripts.Price.Carrier.verboseLines which raw decls); return 0

def wire (root : System.FilePath) (original : String) (lines : Array String) (pos : List String) : IO UInt32 := do
  let wide := pos.contains "--wide"
  let pos := pos.filter (· != "--wide")
  let which := pos.headD "gate"
  let one (p : String) : IO (Except String (Array Nat × Array (String × Array Nat) × Array String)) := do
    match Scripts.Price.Wire.applyProbe lines p with
    | .error e => return .error e
    | .ok patched =>
      match ← Scripts.Price.Env.leanOn root target ".wire-price-bak" original patched (wide := wide) with
      | .error e => return .error e
      | .ok (_, out) =>
        match ← declOwner root lines patched with
        | .error e => return .error e
        | .ok owner => return Scripts.Price.Wire.reading p owner out
  if which == "all" then
    let mut got : Array String := #[]
    for p in Scripts.Price.Wire.probes do
      match ← one p with
      | .error e => return ← die e
      | .ok (raw, decls, away) =>
        IO.println (Scripts.Price.Wire.allRow p raw.size decls.size (Scripts.Price.Wire.names decls) away)
        got := got.push s!"{p}={decls.size}"
    let gotS := " ".intercalate got.toList
    IO.println ""; IO.println s!"WIRE-PRICE {gotS}"
    let want := (← readPin root).bind (Scripts.Price.Pin.expectedLiteral? · "expectedWirePrice")
    let (ls, rc) := Scripts.Price.Pin.pinVerdict "WIRE" want gotS
    printAll ls; return rc
  if !Scripts.Price.Wire.probes.contains which then return ← die Scripts.Price.Wire.usage
  match ← one which with
  | .error e => die e
  | .ok (raw, decls, away) => printAll (Scripts.Price.Wire.verboseLines which raw decls away); return 0

def arm (root : System.FilePath) (original : String) (lines : Array String) : IO UInt32 := do
  let idxs := Scripts.Price.Arm.spendLines lines
  if idxs.size != Scripts.Price.Arm.arms.length then
    return ← die s!"expected {Scripts.Price.Arm.arms.length} spends of `{Scripts.Price.Arm.spend}`, found {idxs.size} -- the arm population moved and this table is not about it"
  let path := root / target
  let before := Scripts.Lean.Md5.md5 (← IO.FS.readBinFile path)
  let mut rows : Array (String × String × Bool) := #[]
  for (armName, li) in Scripts.Price.Arm.arms.zip idxs.toList do
    for (name, ty, tac) in Scripts.Price.Arm.premises do
      let patched := Scripts.Price.Arm.patched lines li ty tac
      match ← Scripts.Price.Env.leanOn root target ".arm-price-bak" original patched with
      | .error e => return ← die e
      | .ok (code, out) =>
        let paid := code == 0
        rows := rows.push (armName, name, paid)
        IO.println (Scripts.Price.Arm.rowLine paid armName name)
        if !paid then if let some d := Scripts.Price.Arm.firstDiag out then IO.println d
  let after := Scripts.Lean.Md5.md5 (← IO.FS.readBinFile path)
  IO.println ""; IO.println (Scripts.Price.Arm.md5Line (path.fileName.getD target) before after)
  let line := Scripts.Price.Arm.tableLine rows
  IO.println line
  let got := Scripts.Punt.Price.drop line "ARMTABLE ".length
  let want := (← readPin root).bind (Scripts.Price.Pin.expectedScanned? · "expectedArmTable")
  let (ls, rc) := Scripts.Price.Pin.pinVerdict "ARM" want got
  printAll ls
  return (if before != after then 1 else rc)

/-- One `have NAME : TY := by TAC` probe before the spend at `li`; `(elaborated?, log)`. -/
def probeAt (root : System.FilePath) (suffix original : String) (pristine : Array String) (li : Nat) (ty tac name : String) : IO (Except String (Bool × String)) := do
  let patched := Scripts.Price.Attribute.replaceLine pristine li (Scripts.Price.Arm.withProbe pristine[li]! ty (some tac) name)
  match ← Scripts.Price.Env.leanOn root target suffix original patched with
  | .error e => return .error e
  | .ok (code, out) => return .ok (code == 0, out)

/-- `  ARM/NAME refused: <first error line, 160 chars>`, sorted by `(arm, name)`. -/
def refusedLines (why : Array (String × String × String)) : Array String :=
  (why.qsort fun (a, n, _) (b, m, _) => a < b || (a == b && n < m)).map fun (a, n, out) =>
    let first := ((out.splitOn "\n").find? fun l => (l.splitOn ": error").length > 1).getD ""
    s!"  {a}/{n} refused: {Scripts.Punt.Price.take (Scripts.Price.Attribute.strip first) 160}"

def md5Of (root : System.FilePath) : IO String := do
  return Scripts.Lean.Md5.md5 (← IO.FS.readBinFile (root / target))

/-- The P/B/O cell: `assumption` first, then the named derivation. -/
def cellOf (root : System.FilePath) (suffix original : String) (pristine : Array String) (li : Nat) (ty : String) (named : Option String) (name : String)
    : IO (Except String (String × Option String)) := do
  match ← probeAt root suffix original pristine li ty "assumption" name with
  | .error e => return .error e
  | .ok (true, _) => return .ok ("P", none)
  | .ok (false, _) =>
    match named with
    | none => return .ok ("O", none)
    | some tac =>
      match ← probeAt root suffix original pristine li ty tac name with
      | .error e => return .error e
      | .ok (ok, out) => return .ok (if ok then "B" else "O", if ok then none else some out)

def tail (root : System.FilePath) (which : String) (before : String) : IO (Option UInt32) := do
  let after ← md5Of root
  IO.println ""; IO.println (Scripts.Price.Arm.md5Line ((root / target).fileName.getD target) before after)
  if before != after then return some 1
  if which != "all" then return some 0
  return none

def verdict (root : System.FilePath) (label pinName got : String) : IO UInt32 := do
  let want := (← readPin root).bind (Scripts.Price.Pin.expectedScanned? · pinName)
  let (ls, rc) := Scripts.Price.Pin.pinVerdict label want got
  printAll ls
  return rc

def coordModes : List String := ["bridge", "ident", "split", "all", "wide"]

open Scripts.Price.Coordinate in
def coordinate (root : System.FilePath) (original : String) (lines : Array String) (pos : List String) : IO UInt32 := do
  let which := pos.headD "all"
  if !coordModes.contains which then return ← die s!"coordinate: unknown mode '{which}' (one of {", ".intercalate coordModes})" 2
  let idxs := Scripts.Price.Arm.spendLines lines
  if idxs.size != arms.length then
    return ← die s!"expected {arms.length} spends of `{Scripts.Price.Arm.spend}`, found {idxs.size} -- the arm population moved and this table is not about it"
  let sfx := ".coordinate-price-bak"
  let before ← md5Of root
  let mut cells : Array (String × String × String) := #[]
  let mut grid : Array (String × String × Bool) := #[]
  let mut lib := 0
  let mut libnames : Array String := #[]
  if which == "bridge" || which == "all" then
    IO.println "-- bridge: null (assumption) against a named derivation"
    for (a, li) in arms.zip idxs.toList do
      for (n, ty, named) in bridgeRows a do
        match ← cellOf root sfx original lines li ty named probeName with
        | .error e => return ← die e
        | .ok (v, _) => cells := cells.push (a, n, v); IO.println (bridgeLine v a n)
  if which == "ident" || which == "all" then
    IO.println "-- ident: which arm each site is in"
    for (a, li) in arms.zip idxs.toList do
      for o in arms do
        match ← probeAt root sfx original lines li "True" (identTac o) probeName with
        | .error e => return ← die e
        | .ok (ok, _) => grid := grid.push (a, o, ok); IO.println (identLine ok a o)
  if which == "split" || which == "all" then
    IO.println "-- split: the arity flip, by declaration, in the module"
    match patchSplit lines with
    | .error e => return ← die e
    | .ok patched =>
      match ← Scripts.Price.Env.leanOn root target sfx original patched with
      | .error e => return ← die e
      | .ok (_, out) =>
        match ← declOwner root lines patched with
        | .error e => return ← die e
        | .ok owner =>
          match splitReading owner out with
          | .error e => return ← die e
          | .ok (rows, n, names) => printAll rows; lib := n; libnames := names
  if which == "wide" then
    IO.println "-- wide: the same flip over the tree, module repaired"
    match patchSplit lines (repair := true) with
    | .error e => return ← die e
    | .ok patched =>
      match ← Scripts.Price.Env.leanOn root target sfx original patched (wide := true) with
      | .error e => return ← die e
      | .ok (code, out) =>
        match wideReading code out with
        | .error e => return ← die e
        | .ok (rows, _, _) => printAll rows
  if let some rc ← tail root which before then return rc
  let got := gotLine grid cells lib
  IO.println ("COORD-PRICE " ++ got)
  IO.println s!"  library declarations broken: {", ".intercalate libnames.toList}"
  verdict root "COORD" "expectedCoordPrice" got

def transportModes : List String := ["arms", "optok", "frames", "pay", "ride", "all", "wide"]

open Scripts.Price.Coordinate in
open Scripts.Price.Transport in
def transport (root : System.FilePath) (original : String) (lines : Array String) (pos : List String) : IO UInt32 := do
  let which := pos.headD "all"
  if !transportModes.contains which then return ← die s!"transport: unknown mode '{which}' (one of {", ".intercalate transportModes})" 2
  let idxs := Scripts.Price.Arm.spendLines lines
  if idxs.size != arms.length then
    return ← die s!"expected {arms.length} spends, found {idxs.size} -- the arm population moved and this table is not about it"
  let sfx := ".transport-price-bak"
  let before ← md5Of root
  let mut cells : Array (String × String × String) := #[]
  let mut why : Array (String × String × String) := #[]
  let mut optokN := 0; let mut optokD : Array String := #[]
  let mut framesN := 0; let mut framesD : Array String := #[]
  let mut pay : Array (String × String) := #[]
  let mut ride := 0
  if which == "arms" || which == "all" then
    IO.println "-- arms: the applied source, the shape the genesis names, and the genesis"
    let r := ringed lines
    for (a, li) in arms.zip idxs.toList do
      for (n, ty, named) in rows a r do
        match ← cellOf root sfx original lines li ty (some named) Scripts.Price.Transport.probeName with
        | .error e => return ← die e
        | .ok (v, w) =>
          cells := cells.push (a, n, v); IO.println (cellLine v a n)
          if let some out := w then why := why.push (a, n, out)
  for (mode, heading) in [("optok", "-- optok: who must supply the open token's position"),
                          ("frames", "-- frames: how many frames the declaration builds")] do
    if which == mode || which == "all" then
      IO.println heading
      match patchFlip lines mode with
      | .error e => return ← die e
      | .ok patched =>
        match ← Scripts.Price.Env.leanOn root target sfx original patched with
        | .error e => return ← die e
        | .ok (_, out) =>
          match ← declOwner root lines patched with
          | .error e => return ← die e
          | .ok owner =>
            match flipReading mode owner out with
            | .error e => return ← die e
            | .ok (rs, n, names) =>
              printAll rs
              if mode == "optok" then
                optokN := n; optokD := names
              else
                framesN := n; framesD := names
  if which == "pay" || which == "all" then
    IO.println "-- pay: the genesis once the ring is paid"
    match patchPay lines with
    | .error e => return ← die e
    | .ok paid =>
      match ← Scripts.Price.Env.leanOn root target sfx original paid with
      | .error e => return ← die e
      | .ok (code, out) =>
        if code != 0 then return ← die (Scripts.Punt.Price.take ("pay: the paid module does not elaborate:\n" ++ "\n".intercalate ((out.splitOn "\n").filter fun l => (l.splitOn ": error").length > 1)) 2000)
        let paidText := "\n".intercalate paid.toList
        let pidx := Scripts.Price.Arm.spendLines paid
        for (a, li) in arms.zip pidx.toList do
          match ← probeAt root sfx original paid li payTy (payTac a) Scripts.Price.Transport.probeName with
          | .error e => return ← die e
          | .ok (okN, _) =>
            match ← probeAt root sfx original paid li payTy "assumption" Scripts.Price.Transport.probeName with
            | .error e => return ← die e
            | .ok (okA, _) =>
              let v := if okA then "P" else if okN then "B" else "O"
              pay := pay.push (a, v); IO.println (payLine v a)
        let _ := paidText
  if which == "ride" || which == "all" then
    IO.println "-- ride: what is in scope where `drop_ride` is built"
    match Scripts.Price.Pin.indexOf lines rideAnchor with
    | .error e => return ← die e
    | .ok li =>
      for a in arms do
        match ← probeAt root sfx original lines li "True" (rideTac (ident a)) Scripts.Price.Transport.probeName with
        | .error e => return ← die e
        | .ok (ok, _) =>
          IO.println (rideLine ok a)
          if ok then ride := ride + 1
      match ← probeAt root sfx original lines li "True" (rideTac "h_base") Scripts.Price.Transport.probeName with
      | .error e => return ← die e
      | .ok (ok, _) =>
        IO.println (rideControl ok)
        if !ok then return ← die rideControlErr
  if which == "wide" then
    IO.println "-- wide: the `optok` ring over the tree"
    match patchFlip lines "optok" with
    | .error e => return ← die e
    | .ok patched =>
      match ← Scripts.Price.Env.leanOn root target sfx original patched (wide := true) with
      | .error e => return ← die e
      | .ok (code, out) =>
        match wideReading "optok" code out with
        | .error e => return ← die e
        | .ok (rs, _, _) => printAll rs
  if let some rc ← tail root which before then return rc
  let got := gotLine cells optokN pay framesN ride
  IO.println ("TRANSPORT-PRICE " ++ got)
  IO.println s!"  optok sites in: {", ".intercalate optokD.toList}"
  IO.println s!"  frames sites in: {", ".intercalate framesD.toList}"
  printAll (refusedLines why)
  verdict root "TRANSPORT" "expectedTransportPrice" got

def rideModes : List String := ["arm", "ride", "carrier", "transport", "all", "wide"]

open Scripts.Price.Coordinate in
open Scripts.Price.Ride in
def rideCmd (root : System.FilePath) (original : String) (lines : Array String) (pos : List String) : IO UInt32 := do
  let which := pos.headD "all"
  if !rideModes.contains which then return ← die s!"ride: unknown mode '{which}' (one of {", ".intercalate rideModes})" 2
  let sfx := ".ride-price-bak"
  let before ← md5Of root
  let mut cells : Array (String × String × String) := #[]
  let mut why : Array (String × String × String) := #[]
  let mut rideR : Nat × Array String := (0, #[])
  let mut carrierR : Array (String × Nat × Array String) := #[]
  let mut trR : Nat × Array String := (0, #[])
  if which == "arm" || which == "all" then
    IO.println "-- arm: what each arm can build, with item 272's ring PAID"
    match Scripts.Price.Transport.patchPay lines with
    | .error e => return ← die e
    | .ok paid =>
      match ← Scripts.Price.Env.leanOn root target sfx original paid with
      | .error e => return ← die e
      | .ok (code, out) =>
        if code != 0 then return ← die (armErr out)
        let idxs := Scripts.Price.Arm.spendLines paid
        if idxs.size != arms.length then return ← die s!"expected {arms.length} spends, found {idxs.size}"
        for (a, li) in arms.zip idxs.toList do
          for (n, ty, named) in rows a do
            match ← cellOf root sfx original paid li ty named Scripts.Price.Ride.probeName with
            | .error e => return ← die e
            | .ok (v, w) =>
              cells := cells.push (a, n, v); IO.println (Scripts.Price.Transport.cellLine v a n)
              if let some o := w then why := why.push (a, n, o)
  let flip (mode : String) : IO (Except String (Nat × Array String)) := do
    match patchFlip lines mode with
    | .error e => return .error e
    | .ok patched =>
      match ← Scripts.Price.Env.leanOn root target sfx original patched with
      | .error e => return .error e
      | .ok (_, out) =>
        match ← declOwner root lines patched with
        | .error e => return .error e
        | .ok owner =>
          match Scripts.Price.Transport.flipReading mode owner out with
          | .error e => return .error e
          | .ok (rs, n, names) => printAll rs; return .ok (n, names)
  if which == "ride" || which == "all" then
    IO.println "-- ride: how many terms spend the ride"
    match ← flip "ride" with | .error e => return ← die e | .ok r => rideR := r
  if which == "carrier" || which == "all" then
    IO.println "-- carrier: three reshapes of the frame's `some` arm"
    for v in carriers do
      IO.println s!"   {v}:"
      match ← flip v with | .error e => return ← die e | .ok (n, names) => carrierR := carrierR.push (v, n, names)
  if which == "transport" || which == "all" then
    IO.println "-- transport: who goes through the carrier funnel"
    match ← flip "transport" with | .error e => return ← die e | .ok r => trR := r
  if which == "wide" then
    IO.println "-- wide: the `choice` reshape over the tree"
    match patchFlip lines "choice" with
    | .error e => return ← die e
    | .ok patched =>
      match ← Scripts.Price.Env.leanOn root target sfx original patched (wide := true) with
      | .error e => return ← die e
      | .ok (code, out) =>
        match Scripts.Price.Transport.wideReading "choice" code out with
        | .error e => return ← die e
        | .ok (rs, _, _) => printAll rs
  if let some rc ← tail root which before then return rc
  let got := gotLine cells (rideR.1, rideR.2.size) (carrierR.map fun (v, n, d) => (v, n, d.size)) (trR.1, trR.2.size)
  IO.println ("RIDE-PRICE " ++ got)
  IO.println s!"  ride sites in: {", ".intercalate rideR.2.toList}"
  for (v, _, d) in carrierR do IO.println s!"  {v} sites in: {", ".intercalate d.toList}"
  IO.println s!"  transport sites in: {", ".intercalate trR.2.toList}"
  printAll (refusedLines why)
  verdict root "RIDE" "expectedRidePrice" got

open Scripts.Price.Close in
def closeCmd (root : System.FilePath) (original : String) (lines : Array String) (pos : List String) : IO UInt32 := do
  let which := pos.headD "all"
  if !modes.contains which then return ← die s!"close: unknown mode '{which}' (one of {", ".intercalate modes})" 2
  let sfx := ".close-price-bak"
  let before ← md5Of root
  let mut cells : Array (String × String) := #[]
  let mut why : Array (String × String) := #[]
  let mut nameC : Array String := #[]
  let mut wrapC : Array String := #[]
  let mut flips : Array (String × Nat × Array String) := #[]
  let mut apps : Nat × Array String := (0, #[])
  if which == "probe" || which == "all" then
    IO.println "-- probe: what the slot branch of `gate` can be closed with"
    match patchProbe lines with
    | .error e => return ← die e
    | .ok (at_, patched) =>
      match ← Scripts.Price.Env.leanOn root target sfx original patched with
      | .error e => return ← die e
      | .ok (_, out) =>
        match ← declOwner root lines patched with
        | .error e => return ← die e
        | .ok owner =>
          let mut hit : Array (String × Array String) := #[]
          for l in out.splitOn "\n" do
            if let some (_, n) := Scripts.Price.Pin.errLoc? l then
              let d := (ownerInBlock at_ n).getD (owner n)
              hit := Scripts.Price.Attribute.addTo hit d (Scripts.Price.Attribute.strip l)
          let stray := ((hit.map (·.1)).filter fun d => !(d.startsWith "_probe274_" || d.startsWith "_null274_")).qsort (· < ·)
          if !stray.isEmpty then
            return ← die s!"probe: the insertion broke declarations of its own host: {", ".intercalate stray.toList}"
          for row in rowNames do
            let ok := (hit.find? (·.1 == s!"_probe274_{row}")).isNone
            if (hit.find? (·.1 == s!"_null274_{row}")).isNone then
              return ← die s!"probe/{row}: `by assumption` PROVED the goal -- the row reads a hypothesis, not a derivation."
            let cell := if ok then "B" else "O"
            cells := cells.push (row, cell)
            if !ok then why := why.push (row, ((hit.find? (·.1 == s!"_probe274_{row}")).map (·.2[0]!)).getD "")
            IO.println (cellLine cell row)
  if which == "name" || which == "all" then
    IO.println "-- name: can the premise be stated where the spend is?"
    for (prem, isWrap) in [(barePrem, false), (wrapPrem, true)] do
      for head in [gateHead, closeHead] do
        match patchPrem lines head prem with
        | .error e => return ← die e
        | .ok patched =>
          match ← Scripts.Price.Env.leanOn root target sfx original patched with
          | .error e => return ← die e
          | .ok (code, out) =>
            let errs := ((out.splitOn "\n").filter fun l => (Scripts.Price.Pin.errLoc? l).isSome).toArray.map Scripts.Price.Attribute.strip
            let named := errs.any isNamed
            IO.println (nameLine named head errs)
            if !named && code == 0 then
              return ← die s!"name/{headName head}: adding a premise broke NOTHING -- the census below would be vacuous and the edit did not apply."
            let c := if named then "O" else "B"
            if isWrap then wrapC := wrapC.push c else nameC := nameC.push c
  let flip (label : String) (patched : Array String) : IO (Except String (Nat × Array String)) := do
    match ← Scripts.Price.Env.leanOn root target sfx original patched with
    | .error e => return .error e
    | .ok (_, out) =>
      match ← declOwner root lines patched with
      | .error e => return .error e
      | .ok owner =>
        let raw := (Scripts.Price.Attribute.errorLines out).qsort (· < ·)
        if raw.isEmpty then return .error s!"{label}: the flip broke nothing -- it did not apply"
        let decls := Scripts.Price.Pin.byDeclLines owner raw
        printAll (flipRows decls)
        return .ok (raw.size, (decls.map (·.1)).qsort (· < ·))
  if which == "flip" || which == "all" then
    IO.println "-- flip: who must WRITE one, by declaration"
    for (tag, head) in [("gate", gateHead), ("close", closeHead)] do
      IO.println s!"   {tag}:"
      match patchPrem lines head wrapPrem with
      | .error e => return ← die e
      | .ok patched =>
        match ← flip tag patched with
        | .error e => return ← die e
        | .ok (n, ds) => flips := flips.push (tag, n, ds)
    IO.println "   apps:"
    match patchRename lines with
    | .error e => return ← die e
    | .ok patched =>
      match ← flip "apps" patched with
      | .error e => return ← die e
      | .ok r => apps := r
    IO.println "   closable:"
    match patchClosable lines with
    | .error e => return ← die e
    | .ok patched =>
      match ← flip "closable" patched with
      | .error e => return ← die e
      | .ok (n, ds) => flips := flips.push ("closable", n, ds)
  if which == "wide" then
    IO.println "-- wide: the wrapped premise on `gate_of_close`, over the tree"
    match patchPrem lines closeHead wrapPrem with
    | .error e => return ← die e
    | .ok patched =>
      match ← Scripts.Price.Env.leanOn root target sfx original patched (wide := true) with
      | .error e => return ← die e
      | .ok (code, out) =>
        match wideReading code out with
        | .error e => return ← die e
        | .ok (rs, _) => printAll rs
  if let some rc ← tail root which before then return rc
  let got := gotLine cells nameC wrapC flips apps.1
  IO.println ("CLOSE-PRICE " ++ got)
  for t in ["gate", "close", "closable"] do
    IO.println s!"  {t} sites in: {", ".intercalate (((flips.find? (·.1 == t)).map (·.2.2)).getD #[]).toList}"
  IO.println s!"  apps sites in: {", ".intercalate apps.2.toList}"
  for (row, out) in why.qsort (·.1 < ·.1) do IO.println s!"  {row} refused: {Scripts.Punt.Price.take out 170}"
  verdict root "CLOSE" "expectedClosePrice" got

open Scripts.Price.InlineClass in
def inlineClassCmd (root : System.FilePath) (original : String) (lines : Array String) (pos : List String) : IO UInt32 := do
  let which := pos.headD "feeders"
  if !["feeders", "arms", "census"].contains which then return ← die "usage: inline_class_price.py feeders|arms|census" 2
  let pinText ← do let p := root / pin; if ← p.pathExists then pure (some (← IO.FS.readFile p)) else pure none
  let check (name label line : String) : IO UInt32 := do
    let (ls, rc) := pinVerdict label (pinText.bind (Scripts.Price.Pin.expectedLiteral? · name)) line
    printAll ls; return rc
  -- one elaboration of a patched copy, timed, with the Python's own md5 line
  let run (patched : Array String) : IO (Except String String) := do
    let path := root / target
    let before := Scripts.Lean.Md5.md5 (← IO.FS.readBinFile path)
    let t0 ← IO.monoMsNow
    let r ← Scripts.Price.Env.leanOn root target ".inline-class-bak" original patched
    let after := Scripts.Lean.Md5.md5 (← IO.FS.readBinFile path)
    let secs := ((← IO.monoMsNow) - t0 + 500) / 1000
    IO.println s!"md5 StreamAccum.lean  before {before}  after {after}  {if before == after then "==" else "DIFFERS"}   ({secs}s)"
    match r with
    | .error e => return .error e
    | .ok (_, out) => return .ok out
  let olean := root / ".lake" / "build" / "lib" / "lean" / "L4YAML" / "Proofs" / "Production" / "StreamAccum.olean"
  if which == "feeders" then
    if !hasFallback lines then IO.println retiredLine; return 0
    let ds := Scripts.Lean.DeclRanges.decls (← Scripts.Lean.DeclRanges.readRanges olean)
    let start (d : String) : Option Nat := (ds.find? (·.name == d)).map (·.start - 1)
    match narrow lines start with
    | .error e => return ← die e
    | .ok patched =>
      match ← run patched with
      | .error e => return ← die e
      | .ok body =>
        match ← declOwner root lines patched with
        | .error e => return ← die e
        | .ok owner =>
          let declLine (d : String) : Nat := ((ds.find? (·.name == d)).map (·.start - 1)).getD 0
          let mut rows : Array (String × String × Nat × Nat × String × String) := #[]
          for l in body.splitOn "\n" do
            if let some (ln, col, msg) := errRow? l then
              let d := owner ln
              rows := rows.push (d, armOf patched (ln - 1) (declLine d), ln, col, msg, Scripts.Price.Attribute.strip patched[ln - 1]!)
          let mut groups : Array (String × Array (String × String × Nat × Nat × String × String)) := #[]
          for r in rows do groups := Scripts.Price.Attribute.addTo groups r.1 r
          IO.println ""; IO.println s!"=== feeders: {rows.size} errors / {groups.size} declarations ==="
          for (d, rs) in groups.qsort (fun a b => a.2[0]!.2.2.1 < b.2[0]!.2.2.1) do
            IO.println s!"  {Scripts.Punt.Price.padLeft (toString rs.size) 3}  {d}{if narrowed.contains d then " (NARROWED -- its own body)" else ""}"
            for (_, arm, ln, col, msg, text) in rs do
              IO.println s!"         L{ln}:{Scripts.Punt.Price.padRight (toString col) 4} arm {Scripts.Punt.Price.padRight arm 20} {Scripts.Punt.Price.take msg 60}"
              IO.println s!"                     {Scripts.Punt.Price.take text 90}"
          let arms := ((rows.filter fun r => !narrowed.contains r.1).map fun r => (r.1, r.2.1)).toList.eraseDups.toArray.qsort
            (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))
          let other := (body.splitOn "\n").filter fun l => (l.splitOn "error").length > 1 && (errRow? l).isNone
          if !other.isEmpty then
            IO.println s!"  (other error lines: {other.length} )"
            for l in other.take 10 do IO.println s!"    {Scripts.Punt.Price.take l 160}"
          let line := s!"errors={rows.size} decls={groups.size} feeders=" ++ ",".intercalate (arms.toList.map fun (d, a) => s!"{d}/{a}")
          IO.println ("INLINE-FEEDERS " ++ line)
          return ← check "expectedInlineFeeders" "INLINE-FEEDERS-PIN" line
  if which == "arms" then
    let ds := Scripts.Lean.DeclRanges.decls (← Scripts.Lean.DeclRanges.readRanges olean)
    let some w := ds.find? (·.name == wrapper) | return ← die s!"AssertionError: no declaration {wrapper} in the module"
    let a := w.start - 1
    let b := w.stop
    let patched := (lines.extract 0 a) ++ (Array.replicate (b - a) deletedMarker) ++ (lines.extract b lines.size)
    match ← run patched with
    | .error e => return ← die e
    | .ok body =>
      match ← declOwner root lines patched with
      | .error e => return ← die e
      | .ok owner =>
        let declLine (d : String) : Nat := ((ds.find? (·.name == d)).map (·.start - 1)).getD 0
        let mut rows : Array (String × String × Nat) := #[]
        let mut other : Array String := #[]
        for l in body.splitOn "\n" do
          if let some (ln, _, msg) := errRow? l then
            if (msg.splitOn wrapper).length ≤ 1 then other := other.push l
            else
              let d := owner ln
              rows := rows.push (d, armLabel lines (ln - 1) (declLine d), ln)
        let mut groups : Array (String × Array (String × Nat)) := #[]
        for (d, arm, ln) in rows do groups := Scripts.Price.Attribute.addTo groups d (arm, ln)
        IO.println ""; IO.println s!"=== arms: {rows.size} applications / {groups.size} declarations ==="
        for (d, rs) in groups.qsort (·.1 < ·.1) do
          IO.println s!"  {Scripts.Punt.Price.padLeft (toString rs.size) 3}  {d}"
          for (arm, ln) in rs do IO.println s!"         L{Scripts.Punt.Price.padRight (toString ln) 6} {arm}"
        if !other.isEmpty then
          IO.println s!"  ({other.size} other errors -- the deletion broke more than the applications)"
          for l in other.toList.take 10 do IO.println s!"    {Scripts.Punt.Price.take l 180}"
        let sorted := rows.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))
        let line := s!"apps={rows.size} decls={groups.size} arms=" ++ ",".intercalate (sorted.toList.map fun (d, arm, _) => s!"{d}/{arm}")
        IO.println ("INLINE-ARMS " ++ line)
        return ← check "expectedInlineArms" "INLINE-ARMS-PIN" line
  -- census
  let probe := root / probePath
  let dir := root / "Scratch"
  if ← probe.pathExists then return ← die s!"{probe} exists; refusing to overwrite it"
  let madeDir := !(← dir.pathExists)
  IO.FS.createDirAll dir
  IO.FS.writeFile probe program
  let t0 ← IO.monoMsNow
  let cleanup : IO Unit := do
    IO.FS.removeFile probe
    if madeDir then
      try IO.FS.removeDir dir catch _ => pure ()
  let r ← try
      IO.Process.output { cmd := "lake", args := #["env", "lean", probePath], cwd := some root }
    catch e => do
      cleanup
      throw e
  cleanup
  let body := r.stdout ++ r.stderr
  if r.exitCode != 0 then
    IO.println (Scripts.Punt.Price.take body 3000)
    return ← die s!"census probe failed ({r.exitCode})"
  let rows := (body.splitOn "\n").filterMap rowOf? |>.toArray
  let src := ((body.splitOn "\n").findSome? fun l => if l.startsWith "SOURCES " then (l.splitOn " ")[1]!.toNat? else none).getD 0
  let acc := rows.filter (·[2]! == "acc=true")
  let nokey := acc.filter (·[3]! == "live=false")
  let popped := acc.filter (·[4]! != "no-pop")
  let mut groups : Array (String × Nat) := #[]
  for r in popped do
    match groups.findIdx? (·.1 == r[4]!) with
    | some i => groups := groups.modify i fun (k, v) => (k, v + 1)
    | none => groups := groups.push (r[4]!, 1)
  let secs := ((← IO.monoMsNow) - t0 + 500) / 1000
  IO.println s!"sources {src}, candidates {candidates.length}  ({secs}s)"
  for kind in kinds do
    let ks := rows.filter (·[1]! == kind)
    let ka := ks.filter (·[2]! == "acc=true")
    IO.println s!"  {Scripts.Punt.Price.padRight kind 8} rows {Scripts.Punt.Price.padLeft (toString ks.size) 4}   accepted {Scripts.Punt.Price.padLeft (toString ka.size) 4}   refused {Scripts.Punt.Price.padLeft (toString (ks.size - ka.size)) 4}"
  IO.println s!"  accepted with no live key on the park's line: {nokey.size}"
  for r in nokey do IO.println s!"      {r[5]!} {Scripts.Punt.Price.take r[6]! 100}"
  let bySorted := groups.qsort (·.1 < ·.1)
  IO.println (s!"  accepted whose own landing popped: {popped.size}  " ++ "  ".intercalate (bySorted.toList.map fun (k, v) => s!"{k}={v}"))
  for r in popped do if r[4]! != "onto-map" then IO.println s!"      {r[4]!} {r[5]!} {Scripts.Punt.Price.take r[6]! 100}"
  let g (k : String) : Nat := ((groups.find? (·.1 == k)).map (·.2)).getD 0
  let line := s!"rows={rows.size} accepted={acc.size} nokey={nokey.size} popped={popped.size} onto-map={g "onto-map"} onto-seq={g "onto-seq"} off-level={g "off-level"}"
  IO.println ("INLINE-CENSUS " ++ line)
  check "expectedInlineCensus" "INLINE-CENSUS-PIN" line

def scripts : List String := ["park-top", "vslot-top", "mv-slot-top", "open-map", "park-nic0", "landing-nic0", "carrier", "wire", "arm", "coordinate", "transport", "ride", "close", "inline-class"]

def run (args : List String) : IO UInt32 := do
  if args.any (fun a => a == "-h" || a == "--help") then IO.println usage; return 0
  if args.any (fun a => a == "-V" || a == "--version") then IO.println version; return 0
  let args := if args.headD "" == "--" then args.drop 1 else args
  let rec opts : List String → System.FilePath → List String → Except String (System.FilePath × List String)
    | [], r, pos => .ok (r, pos.reverse)
    | "-C" :: v :: t, _, pos | "--root" :: v :: t, _, pos => opts t v pos
    | "--wide" :: t, r, pos => opts t r ("--wide" :: pos)
    | a :: t, r, pos => if a.startsWith "-" && a.length > 1 then .error s!"unknown option '{a}'" else opts t r (a :: pos)
  let (root, pos) ← match opts args "." [] with
    | .ok x => pure x
    | .error e => return ← die s!"{e}\n{usage}" 2
  let some script := pos.head? | return ← die usage 2
  if !scripts.contains script then return ← die s!"unknown script '{script}'\n{usage}" 2
  let pos := pos.drop 1
  if script != "wire" && pos.contains "--wide" then return ← die s!"--wide is a `wire` option\n{usage}" 2
  if script != "open-map" && (pos.filter (· != "--wide")).length > 1 then return ← die s!"one mode at a time\n{usage}" 2
  let root ← try IO.FS.realPath root catch e => return ← die s!"invalid root: {e}" 2
  let path := root / target
  if !(← path.pathExists) then return ← die s!"{path} not found (pass -C ROOT)" 2
  let original ← IO.FS.readFile path
  let lines := readLines original
  if ["carrier", "wire", "coordinate", "transport", "ride", "close", "inline-class"].contains script then
    if let .error e ← Scripts.Price.Env.ensureBuilt root target then return ← die e
  match script with
  | "park-top" => parkTop root original lines pos
  | "vslot-top" => vslotTop root original lines
  | "mv-slot-top" => mvSlotTop root original lines
  | "open-map" => openMap root original lines pos
  | "park-nic0" => parkNic0 root original lines pos
  | "landing-nic0" => landingNic0 root original lines pos
  | "carrier" => carrier root original lines pos
  | "wire" => wire root original lines pos
  | "coordinate" => coordinate root original lines pos
  | "transport" => transport root original lines pos
  | "ride" => rideCmd root original lines pos
  | "close" => closeCmd root original lines pos
  | "inline-class" => inlineClassCmd root original lines pos
  | _ => arm root original lines

end Scripts.MainPrice

public def main (args : List String) : IO UInt32 := Scripts.MainPrice.run args
