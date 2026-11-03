module

public import Scripts.Punt.Price

/-!
# `lake run punt-price -- MODE` — the price of `KeyPackPunt`'s reasons (item 211)

The port of `scripts/punt_reason_price.py` (Rule 9 phase 3.2b).  The readings are
`Scripts.Punt.Price`; this is the IO: each mode patches a copy of
`L4YAML/Proofs/Production/StreamAccum.lean` in place (a constructor commented out, or
one `∨ True` made `∨ False`), runs `lake env lean` on it, restores the bytes and
reads the error locations.  Never run it beside a `lake build`.

exit status: 0 report printed; 1 an anchor or constructor is not where the mode
expects it (the lemma moved — re-aim), or the file was not restored; 2 usage.
-/

namespace Scripts.PuntPrice

open Scripts.Punt.Price

def version : String := "scripts-punt-price 1.0 (Rule 9 phase 3.2b)"

def usage : String := s!"usage: lake run punt-price -- [{usageModes}] [-C ROOT]

  <reason> | all   delete the constructor (commented out), `lake env lean`, errors by declaration
  split            productions vs consumer arms, from the source alone (no Lean run)
  phantom          both switches of `flowKeyPack_of_close` narrowed (`stamp`, `keyroute`), one run each
  reaches          each of `content_dispatch_routed`'s five contexts narrowed; which applications decline all five
  -C, --root ROOT  repository root (default: the current directory)
  -h, --help / -V, --version"

def die (msg : String) (code : UInt32 := 1) : IO UInt32 := do
  IO.eprintln msg; pure code

def readLines (text : String) : Array String := (text.splitOn "\n").toArray

/-- Write `patched` over the target, run `lake env lean` on it, restore the original bytes. -/
def leanOn (root : System.FilePath) (original : String) (patched : Array String) : IO (Except String String) := do
  let path := root / target
  let res ← try
    IO.FS.writeFile path ("\n".intercalate patched.toList)
    let r ← IO.Process.output { cmd := "lake", args := #["env", "lean", target], cwd := some root }
    pure (.ok (r.stdout ++ r.stderr))
  catch e => pure (.error s!"{e}")
  IO.FS.writeFile path original
  if (← IO.FS.readFile path) != original then
    return .error s!"{target} was not restored; fix the source before trusting anything else"
  return res

def printAll (ls : Array String) : IO Unit := do
  let out ← IO.getStdout
  for l in ls do out.putStrLn l

def runPrice (root : System.FilePath) (original : String) (lines : Array String) (reason : String) : IO UInt32 := do
  match applyDelete lines reason with
  | .error e => die e
  | .ok (patched, lo, hi) =>
    match ← leanOn root original patched with
    | .error e => die e
    | .ok out => printAll (priceReport reason (priceCensus lines (lo, hi) out)); pure 0

def runPhantom (root : System.FilePath) (original : String) (lines : Array String) (which : String) : IO UInt32 := do
  match applyNarrow lines which with
  | .error e => die e
  | .ok (patched, decl, hit) =>
    match ← leanOn root original patched with
    | .error e => die e
    | .ok out => printAll (phantomReport lines which decl hit out); pure 0

def runReaches (root : System.FilePath) (original : String) (lines : Array String) : IO UInt32 := do
  let apps := callSites lines reachDecl
  IO.println (s!"{reachDecl}: {apps.length} applications " ++ ", ".intercalate (apps.map fun a => s!"L{a}"))
  let mut declines : List (Nat × List String) := []
  let mut relays : List Nat := []
  for binder in contexts do
    match narrowBinder lines reachDecl binder with
    | .error e => return ← die e
    | .ok (patched, _) =>
      match ← leanOn root original patched with
      | .error e => return ← die e
      | .ok out =>
        let (rows, dec, rel) := reachRows lines apps binder out
        for site in dec do
          declines := match declines.find? (·.1 == site) with
            | some _ => declines.map fun (s, bs) => if s == site then (s, bs ++ [binder]) else (s, bs)
            | none => declines ++ [(site, [binder])]
        relays := relays ++ rel
        printAll (binderLines binder rows)
  printAll (reachSummary lines apps declines relays)
  return 0

def run (args : List String) : IO UInt32 := do
  if args.contains "-h" || args.contains "--help" then IO.println usage; return 0
  if args.contains "-V" || args.contains "--version" then IO.println version; return 0
  let args := if args.headD "" == "--" then args.drop 1 else args
  let rec opts : List String → System.FilePath → List String → Except String (System.FilePath × List String)
    | [], r, pos => .ok (r, pos.reverse)
    | "-C" :: v :: t, _, pos | "--root" :: v :: t, _, pos => opts t v pos
    | a :: t, r, pos => if a.startsWith "-" && a.length > 1 then .error s!"unknown option '{a}'" else opts t r (a :: pos)
  let (root, pos) ← match opts args "." [] with
    | .ok x => pure x
    | .error e => return ← die s!"{e}\n{usage}" 2
  let which := pos.headD "all"
  if pos.length > 1 then return ← die s!"one mode at a time\n{usage}" 2
  let root ← IO.FS.realPath root
  let path := root / target
  if !(← path.pathExists) then return ← die s!"{path} not found (pass -C ROOT)" 2
  let original ← IO.FS.readFile path
  let lines := readLines original
  if which == "reaches" then return ← runReaches root original lines
  if which == "split" then printAll (splitReport lines); return 0
  if phantomNames.contains which then return ← runPhantom root original lines which
  if which == "phantom" then
    for k in phantomNames do
      let rc ← runPhantom root original lines k
      if rc != 0 then return rc
    return 0
  if !(reasons.contains which || which == "all") then
    return ← die s!"usage: lake run punt-price -- [{usageModes}]" 1
  for reason in (if which == "all" then reasons else [which]) do
    let rc ← runPrice root original lines reason
    if rc != 0 then return rc
  return 0

end Scripts.PuntPrice

public def main (args : List String) : IO UInt32 := Scripts.PuntPrice.run args
