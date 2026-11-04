module

public import Scripts.Price.Env
public import Scripts.Price.ParkTop
public import Scripts.Price.VslotTop
public import Scripts.Price.MvSlotTop
public import Scripts.Price.OpenMap
public import Scripts.Price.ParkNic0
public import Scripts.Price.LandingNic0

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
  -C, --root ROOT  repository root (default: the current directory)
  -h, --help / -V, --version

Each mode but `payers` patches {target} in place, runs `lake env lean` on it and restores
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
    | .ok body => printAll (report patched body); pure 0

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
          | .ok body => printAll (Scripts.Price.LandingNic0.dropLines n (sortedNat (errorLines body)))
      return 0
  if !Scripts.Price.LandingNic0.modes.contains which then
    return ← die s!"usage: landing_nic0_price.py [{Scripts.Price.LandingNic0.usageModes}]"
  let names := (Scripts.Price.LandingNic0.applyProbe lines which).toOption.map (·.2) |>.getD #[]
  probeRun root ".landing-bak" original (Scripts.Price.LandingNic0.headline which names)
    ((Scripts.Price.LandingNic0.applyProbe lines which).map (·.1))
    (fun patched body => Scripts.Price.LandingNic0.report patched names body)

def scripts : List String := ["park-top", "vslot-top", "mv-slot-top", "open-map", "park-nic0", "landing-nic0"]

def run (args : List String) : IO UInt32 := do
  if args.any (fun a => a == "-h" || a == "--help") then IO.println usage; return 0
  if args.any (fun a => a == "-V" || a == "--version") then IO.println version; return 0
  let args := if args.headD "" == "--" then args.drop 1 else args
  let rec opts : List String → System.FilePath → List String → Except String (System.FilePath × List String)
    | [], r, pos => .ok (r, pos.reverse)
    | "-C" :: v :: t, _, pos | "--root" :: v :: t, _, pos => opts t v pos
    | a :: t, r, pos => if a.startsWith "-" && a.length > 1 then .error s!"unknown option '{a}'" else opts t r (a :: pos)
  let (root, pos) ← match opts args "." [] with
    | .ok x => pure x
    | .error e => return ← die s!"{e}\n{usage}" 2
  let some script := pos.head? | return ← die usage 2
  if !scripts.contains script then return ← die s!"unknown script '{script}'\n{usage}" 2
  let pos := pos.drop 1
  if script != "open-map" && pos.length > 1 then return ← die s!"one mode at a time\n{usage}" 2
  let root ← try IO.FS.realPath root catch e => return ← die s!"invalid root: {e}" 2
  let path := root / target
  if !(← path.pathExists) then return ← die s!"{path} not found (pass -C ROOT)" 2
  let original ← IO.FS.readFile path
  let lines := readLines original
  match script with
  | "park-top" => parkTop root original lines pos
  | "vslot-top" => vslotTop root original lines
  | "mv-slot-top" => mvSlotTop root original lines
  | "open-map" => openMap root original lines pos
  | "park-nic0" => parkNic0 root original lines pos
  | _ => landingNic0 root original lines pos

end Scripts.MainPrice

public def main (args : List String) : IO UInt32 := Scripts.MainPrice.run args
