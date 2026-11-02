module

public import Scripts.Pack.Census
public import Scripts.Pack.Residue
public import Scripts.Flip.Patch
public import Scripts.Pins

@[expose] public section Blanket

/-!
# scripts-pack-census — the PACK flip census and the residue's classes

```
lake run pack-census -- [-C ROOT] <cmd> [options]
  flip     [-t|--tsv PATH] [-m|--max-rounds N] [-d|--dump-dir DIR]   PACK-FLIP    (pack_flip_census.py --alt false)
  residue  [-t|--tsv PATH] [-m|--max-rounds N] [-d|--dump-dir DIR]   PACK-RESIDUE (pack_flip_census.py --alt refused)
  classes  [-t|--tsv PATH]                                           RESIDUE-CLASSES (residue_classes.py)
```

The port of `scripts/pack_flip_census.py` and `scripts/residue_classes.py` (Rule 9 phase 2).
`flip` and `residue` EDIT `L4YAML/Proofs/Production/StreamAccum.lean` in place and run
`lake env lean -DmaxErrors=5000` on it to a fixpoint (`Scripts.Pack.Census`); the file is
restored byte-identical whatever happens (a `.pack-flip.bak` beside it meanwhile), and the
hashes are printed on stderr.  Never run them beside another `lake build`.  `classes` runs
nothing (`Scripts.Pack.Residue`).  stdout is the Python's, line for line, except the pin
line: the pin `def expected… : String :=` in `Tests/Guards/Proofs/BlockDeferralClasses.lean`
is read through the dated `--` notes between the head and the literal (`Scripts.Pins.defSpan`),
so a moved pin is reported MOVED where the Python (literal on the next line only) said `absent`.

exit status: 0 complete (pin absent or agreeing); 1 pin MOVED, file not restored, or a
census error (unbalanced group, a missing anchor); 2 usage; 3 `lake env lean` failed without
a StreamAccum diagnostic (its output kept beside the TSV, else under `.lake/`); 4 incomplete
census (`did not converge` or `stopping on an unhandled site`) — the partial summary is
still printed and the TSV written, then the status says it is not a reading.
-/

open Scripts.Pack
open Scripts.Pack.Census (Mode Prepared State Err rel)

namespace Scripts.PackCensus

def usage : String := "usage: lake run pack-census -- [-C ROOT] <cmd> [options]

  flip     [-t|--tsv PATH] [-m|--max-rounds N] [-d|--dump-dir DIR]   PACK-FLIP: both PackAlt bodies False (the declines)
  residue  [-t|--tsv PATH] [-m|--max-rounds N] [-d|--dump-dir DIR]   PACK-RESIDUE: PackAlt = ExplicitValueRefused (the residue)
  classes  [-t|--tsv PATH]                                           RESIDUE-CLASSES: the declines by existential index

options
  -C, --root ROOT       repository root (default: the current directory)
  -t, --tsv PATH        flip/residue: write the per-site rows (round, line, column, kind, declaration, message
                        head, source line) and each round's raw output beside it (<stem>-roundN.out);
                        classes: read such a residue TSV for the sites= / orSites= / bareParamSites= counts
  -m, --max-rounds N    flip/residue: rounds before `did not converge` (default 40)
  -d, --dump-dir DIR    flip/residue: write the patched StreamAccum of every round (round-N.lean)
  -h, --help            this text
  -V, --version         version

flip and residue edit L4YAML/Proofs/Production/StreamAccum.lean in place and restore it byte-identical;
never run them beside another lake build."

structure Opts where
  root : System.FilePath := "."
  tsv : Option System.FilePath := none
  maxRounds : Nat := 40
  dumpDir : Option System.FilePath := none
  positional : Array String := #[]
  deriving Inhabited

def die (msg : String) (code : UInt32 := 1) : IO UInt32 := do
  IO.eprintln msg
  return code

partial def parseOpts (args : List String) (o : Opts) : Except String Opts :=
  match args with
  | [] => pure o
  | "-C" :: v :: t | "--root" :: v :: t => parseOpts t { o with root := v }
  | "-t" :: v :: t | "--tsv" :: v :: t => parseOpts t { o with tsv := some v }
  | "-d" :: v :: t | "--dump-dir" :: v :: t => parseOpts t { o with dumpDir := some v }
  | "-m" :: v :: t | "--max-rounds" :: v :: t =>
    match v.toNat? with
    | some n => parseOpts t { o with maxRounds := n }
    | none => throw s!"--max-rounds expects a number, got '{v}'"
  | "--" :: t => pure { o with positional := o.positional ++ t.toArray }
  | a :: t =>
    if a.startsWith "-" && a.length > 1 then throw s!"unknown option '{a}'"
    else parseOpts t { o with positional := o.positional.push a }

def pinFile := "Tests/Guards/Proofs/BlockDeferralClasses.lean"
def auditFile := "Tests/Guards/Proofs/OrTrueAudit.lean"

/-- The pinned literal of `def NAME : String :=`, read through the dated `--` notes between the head
and the literal (`Scripts.Pins.defSpan`, as `repin` reads it).  The Python matched only a literal on
the very next line, so a commented pin read `absent`; this port reads it. -/
def pinValue? (pinText name : String) : Option String := do
  let lines := (pinText.splitOn "\n").toArray
  let span ← Scripts.Pins.defSpan lines name
  let body := (lines.extract (span.start + 1 + span.comments.size) span.stop).toList
  let lit ← body.findSome? fun l =>
    let t := Scripts.Pins.pyStrip l
    if t.startsWith "\"" then some t else none
  let inner := Census.sub lit 1
  return Census.sub inner 0 (Census.findFrom inner "\"")

def stemOut (tsv : System.FilePath) (rnd : Nat) : System.FilePath :=
  tsv.withFileName s!"{tsv.fileStem.getD "census"}-round{rnd}.out"

/-- The rounds, on the patched tree: `(state, rounds, broke)`; throws on an unbalanced group. -/
inductive Outcome where
  | converged | unhandled | exhausted
  deriving BEq, Repr

def runRounds (o : Opts) (m : Mode) (p : Prepared) (orig tbl : Array String) (t : System.FilePath) :
    IO (State × Nat × Outcome) := do
  let t0 ← IO.monoMsNow
  let mut st : State := { lines := p.lines }
  let mut rounds := 0
  let mut outcome := Outcome.exhausted
  for rnd in [1:o.maxRounds + 1] do
    rounds := rnd
    let text := "\n".intercalate st.lines.toList
    IO.FS.writeFile t text
    if let some d := o.dumpDir then
      IO.FS.createDirAll d
      IO.FS.writeFile (d / s!"round-{rnd}.lean") text
    let r ← IO.Process.output { cmd := "lake", args := #["env", "lean", "-DmaxErrors=5000", rel], cwd := some o.root }
    let log := r.stdout ++ r.stderr
    let kept ← match o.tsv with
      | some tsv => pure (stemOut tsv rnd)
      | none =>
        IO.FS.createDirAll (o.root / ".lake")
        pure (o.root / ".lake" / s!"pack-census-{m.name}-round{rnd}.out")
    IO.FS.writeFile kept log
    let errs := Census.parseErrors log
    if errs.isEmpty && r.exitCode != 0 then
      throw (IO.userError s!"lake env lean exited {r.exitCode} with no {rel} diagnostic (round {rnd}; output in {kept})")
    let secs := ((← IO.monoMsNow) - t0 + 500) / 1000
    IO.println s!"round {rnd}: {errs.size} errors ({secs}s)"
    let settled := Census.settledProbes st.lines errs
    let errs := if settled.isEmpty then errs else errs.filter fun e => !settled.any (fun s => s.line == e.line && s.col == e.col)
    if !settled.isEmpty then
      IO.println s!"  {settled.size} pattern(s) of an already-probed `.imp … (fun h => alt_probe h)` relay, settled"
    if errs.isEmpty then
      outcome := .converged
      break
    let some st' := Census.step m p orig tbl rnd st errs
      | throw (IO.userError "unbalanced group")
    st := st'
    for l in st.out do IO.println l
    st := { st with out := #[] }
    if st.stop then
      IO.println "stopping on an unhandled site"
      outcome := .unhandled
      break
  if outcome == .exhausted then IO.println "did not converge"
  return (st, rounds, outcome)

def runFlip (o : Opts) (m : Mode) : IO UInt32 := do
  let t := o.root / rel
  let origBytes ← IO.FS.readBinFile t
  let orig := (String.fromUTF8! origBytes).splitOn "\n" |>.toArray
  let p ← match Census.prepare m orig with
    | .error e => return ← die e 1
    | .ok p => pure p
  IO.println s!"--alt {m.name}: flipped {p.flipped} bodies, sorried {p.stubs} stubs, substituted {p.promised} promised bodies"
  let tbl := Census.declTable orig
  let bak := o.root / (rel ++ ".pack-flip.bak")
  IO.FS.writeBinFile bak origBytes
  let res ← try (Except.ok <$> runRounds o m p orig tbl t) catch e =>
    pure (Except.error (toString e))
  IO.FS.writeBinFile t origBytes
  try IO.FS.removeFile bak catch _ => pure ()
  let now ← IO.FS.readBinFile t
  let same := now == origBytes
  IO.eprintln s!"restored {rel} hash {Scripts.Flip.Patch.digest now} (orig {Scripts.Flip.Patch.digest origBytes}) identical={same}"
  if !same then return ← die "StreamAccum NOT restored" 1
  let (st, rounds, outcome) ← match res with
    | .error e => return ← die e (if e.startsWith "lake env lean exited" then 3 else 1)
    | .ok r => pure r
  if let some tsv := o.tsv then
    IO.FS.writeFile tsv ("\n".intercalate (st.census.map (·.tsv)).toList ++ "\n")
  let s := Census.summary m orig st.census rounds p.stubs p.promised
  for l in s.out do IO.println l
  IO.println s!"{s.label} {s.line}"
  if outcome != .converged then
    return ← die s!"incomplete census ({if outcome == .unhandled then "stopped on an unhandled site" else "did not converge"} after {rounds} round(s)): the {s.label} line above is partial, not a reading" 4
  let pinText ← IO.FS.readFile (o.root / pinFile)
  match pinValue? pinText s.pin with
  | none => IO.println s!"{s.label}-PIN absent"; return 0
  | some v =>
    if v == s.line then IO.println s!"{s.label}-PIN agrees"; return 0
    else
      IO.println s!"{s.label}-PIN MOVED\n  got      {s.line}\n  expected {v}"
      return 1

def runClasses (o : Opts) : IO UInt32 := do
  let audit ← IO.FS.readFile (o.root / auditFile)
  let src := (← IO.FS.readFile (o.root / rel)).splitOn "\n" |>.toArray
  let some positions := Residue.leanList audit "expectedPositions"
    | die s!"no `def expectedPositions : List String :=` in {auditFile}" 1
  let some supply := Residue.leanList audit "expectedSupply"
    | die s!"no `def expectedSupply : List String :=` in {auditFile}" 1
  let tsv ← match o.tsv with
    | none => pure none
    | some f =>
      let rows := ((← IO.FS.readFile f).splitOn "\n").filter (· ≠ "") |>.map fun l => (l.splitOn "\t").toArray
      pure (some rows.toArray)
  for l in Residue.report positions supply src tsv do IO.println l
  return 0

def run (args : List String) : IO UInt32 := do
  let args := if args.headD "" == "--" then args.drop 1 else args
  if args.isEmpty then
    IO.println usage
    return 2
  let opts := args.takeWhile (· != "--")
  if opts.contains "-h" || opts.contains "--help" then
    IO.println usage
    return 0
  if opts.contains "-V" || opts.contains "--version" then
    IO.println "scripts-pack-census 1.0 (Rule 9 phase 2)"
    return 0
  match parseOpts args {} with
  | .error e => die s!"{e}\n{usage}" 2
  | .ok o =>
    match o.positional.toList with
    | ["flip"] => runFlip o Census.modeFalse
    | ["residue"] => runFlip o Census.modeRefused
    | ["classes"] => runClasses o
    | [] => die usage 2
    | c :: _ => die s!"unknown command '{c}'\n{usage}" 2

end Scripts.PackCensus

public def main (args : List String) : IO UInt32 := Scripts.PackCensus.run args
