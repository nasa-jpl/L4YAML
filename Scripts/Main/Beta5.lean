module

public import Scripts.Flip.Beta5
public import Scripts.Flip.Patch

/-!
# `lake run flip-beta5` / `lake run beta5-arms` / `lake run beta5-map` — β.5 for real

The port of `scripts/flip_beta5.py` (DOCS item 263), `scripts/beta5_arms.py`
(item 264) and the `--map` mapper of `scripts/flip_210.py` (item 230), Rule 9
phase 3.2b.  The readings are `Scripts.Flip.Beta5`; this is the IO:

* `fixpoint [--max-rounds N] [--log-dir DIR] [--probe LEAN]` — apply β.5's
  edit, `lake build`, sorry every broken proof (statement byte-identical),
  neutralize every moved census, rebuild, until clean, stuck or `N` rounds;
  then the summary, the optional axiom probe, `FIXLINE …` and `FIX-PIN`
  against `Tests/Guards/Proofs/ParkBill.lean`'s `expectedFixpoint`.
* `arms [--end control|arms]… [--log-dir DIR]` — β.5's edit alone, then with
  the eight dead blocks deleted; `lake build L4YAML` each; `BROKEN …` per end,
  `ARMLINE …` and `ARM-PIN` against `expectedArms`.
* `map LOG` — the definitions enclosing a build log's error locations.

Destructive while it runs: every file it writes is first copied to
`<file>.beta5-backup` (a run refuses to start while one exists), restored
from memory when the run ends however it ends, and both digests are printed.
Never run it beside a `lake build`.

exit status: 0 the reading printed (the pins' verdicts are in the text, as the
Python's were); 1 an anchor moved, a span could not be neutralized, or a file
was not restored; 2 usage.
-/

namespace Scripts.Beta5Main

public section

open Scripts.Flip Scripts.Flip.Beta5

def version : String := "scripts-beta5 1.0 (Rule 9 phase 3.2b)"

def usage : String := "usage: lake run flip-beta5 -- [--max-rounds N] [--log-dir DIR] [--probe LEAN] [-C ROOT]
       lake run beta5-arms -- [--end control|arms]... [--log-dir DIR] [-C ROOT]
       lake run beta5-map  -- LOG [-C ROOT]

  flip-beta5       β.5's edit (retire pendingFlow, delete scannerDrop, delete dropClose) driven to a
                   sorry-fixpoint over `lake build`; FIXLINE and FIX-PIN (ParkBill.lean)
    --max-rounds N stop after N rounds (default 25), still restoring
    --log-dir DIR  keep every round's build log (flip.beta5.roundN.log, flip.beta5.axioms.log)
    --probe LEAN   a Lean file to elaborate at the fixpoint (the axiom census), via L4YAML/Scratch
    -d, --dry      compute the edit (both commands), print the edited texts' digests, write and build
                   nothing; with --log-dir DIR the edited texts go to DIR/dry.<end>.<file>
  beta5-arms       the same edit alone (control) and with the eight dead blocks deleted (arms),
                   `lake build L4YAML` each; ARMLINE and ARM-PIN
    --end E        one end only (repeatable; default both)
  beta5-map LOG    the declarations enclosing LOG's error locations (BROKEN / UNMAPPED / COUNT)
  -C, --root ROOT  repository root (default: the current directory)
  -h, --help / -V, --version"

def die (msg : String) (code : UInt32 := 1) : IO UInt32 := do
  IO.eprintln msg; pure code

def noCensus : String := "gone=? carried=? free=?"

structure Opts where
  root : System.FilePath := "."
  maxRounds : Nat := 25
  logDir : Option String := none
  probe : Option String := none
  ends : List String := []
  dry : Bool := false
  pos : List String := []

def parseOpts : List String → Opts → Except String Opts
  | [], o => .ok { o with pos := o.pos.reverse }
  | "-C" :: v :: t, o | "--root" :: v :: t, o => parseOpts t { o with root := v }
  | "--max-rounds" :: v :: t, o =>
    match v.toNat? with
    | some n => parseOpts t { o with maxRounds := n }
    | none => .error s!"--max-rounds wants a number, not '{v}'"
  | "--log-dir" :: v :: t, o => parseOpts t { o with logDir := some v }
  | "--probe" :: v :: t, o => parseOpts t { o with probe := some v }
  | "--dry" :: t, o | "-d" :: t, o => parseOpts t { o with dry := true }
  | "--end" :: v :: t, o =>
    if v == "control" || v == "arms" then parseOpts t { o with ends := o.ends ++ [v] }
    else .error s!"--end wants control or arms, not '{v}'"
  | a :: t, o =>
    if a.startsWith "-" && a.length > 1 then .error s!"unknown option '{a}'"
    else parseOpts t { o with pos := a :: o.pos }

/-! ## Backups and restores -/

structure Touched where
  rel : String
  path : System.FilePath
  backup : System.FilePath
  before : String
  original : ByteArray

def backupOf (p : System.FilePath) : System.FilePath := ⟨p.toString ++ ".beta5-backup"⟩

/-- Back `rel` up the first time it is touched; print its digest. -/
def touch (root : System.FilePath) (ref : IO.Ref (Array Touched)) (rel : String) : IO Unit := do
  if (← ref.get).any (·.rel == rel) then return
  let path := root / rel
  let backup := backupOf path
  if ← backup.pathExists then
    throw <| IO.userError s!"{backup} exists: an earlier run was interrupted, so {rel} may be a patched copy; inspect it, restore from the backup, delete the backup, then rerun"
  let bytes ← IO.FS.readBinFile path
  let d := Patch.digest bytes
  IO.FS.writeBinFile backup bytes
  IO.println s!"digest before  {rel}  {d}"
  ref.modify (·.push ⟨rel, path, backup, d, bytes⟩)

/-- Restore every touched file from memory, drop its backup, print and check its digest. -/
def restoreAll (ref : IO.Ref (Array Touched)) (flagged : Bool := false) : IO Bool := do
  let mut ok := true
  for t in ← ref.get do
    IO.FS.writeBinFile t.path t.original
    if ← t.backup.pathExists then IO.FS.removeFile t.backup
    let after := Patch.digest (← IO.FS.readBinFile t.path)
    let same := after == t.before
    let flag := if !flagged then "" else if same then "  ==" else "  !! DIFFERS"
    IO.println s!"digest after   {t.rel}  {after}{flag}"
    ok := ok && same
  return ok

def readText (p : System.FilePath) : IO String := IO.FS.readFile p

def lakeBuild (root : System.FilePath) (target : Array String) : IO (UInt32 × String) := do
  let r ← IO.Process.output { cmd := "lake", args := #["build"] ++ target, cwd := some root }
  return (r.exitCode, r.stdout ++ r.stderr)

def keepLog (logDir : Option String) (name log : String) : IO Unit := do
  if let some d := logDir then
    IO.FS.createDirAll d
    IO.FS.writeFile (System.FilePath.mk d / name) log

def ofExcept {α : Type} : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError e)

/-! ## The fixpoint -/

def runFixpoint (o : Opts) : IO UInt32 := do
  let root := o.root
  let touched ← IO.mkRef (#[] : Array Touched)
  let res ← try
    touch root touched acc
    touch root touched doc
    let (a, d) ← ofExcept (beta5Edits (← readText (root / acc)) (← readText (root / doc)))
    let mut state : Array (String × String) := #[(acc, a), (doc, d)]
    IO.println "EDIT retire pendingFlow + delete scannerDrop + delete dropClose"
    let mut t : Tally := {}
    let mut rc : UInt32 := 1
    for rnd in [1:o.maxRounds + 1] do
      for (rel, text) in state do IO.FS.writeFile (root / rel) text
      let (rc', log) ← lakeBuild root #[]
      rc := rc'
      keepLog o.logDir s!"flip.beta5.round{rnd}.log" log
      t := { t with rounds := rnd }
      if rc == 0 then
        IO.println s!"ROUND {rnd} CLEAN — the fixpoint is reached"
        t := { t with clean := true }
        break
      let locs := errorLocs log
      let mut byfile : Array (String × List Nat) := #[]
      for (rel, line) in locs do
        if !(← (root / rel).pathExists) then
          t := { t with unmapped := t.unmapped.push s!"no such file: {rel}" }
          continue
        if !state.any (·.1 == rel) then
          touch root touched rel
          state := state.push (rel, ← readText (root / rel))
        match byfile.findIdx? (·.1 == rel) with
        | some i => byfile := byfile.modify i fun (r, ls) => (r, ls ++ [line])
        | none => byfile := byfile.push (rel, [line])
      let mut progress := 0
      for (rel, errLines) in byfile do
        let some i := state.findIdx? (·.1 == rel) | continue
        let lines := ((state[i]!).2.splitOn "\n").toArray
        let fr ← ofExcept (roundFile rel lines errLines)
        for e in fr.events do
          IO.println (eventLine rnd rel e)
          if e.progress then progress := progress + 1
          match e.kind with
          | .sorried => t := { t with sorried := t.sorried.push (rnd, e.kw, s!"{rel}:{e.name}") }
          | .pin => t := { t with pinned := t.pinned.push (rnd, rel, e.start + 1) }
          | .restatement => t := { t with restated := t.restated.push (rnd, e.kw, s!"{rel}:{e.name}") }
          | .deleted => t := { t with deleted := t.deleted.push (rnd, e.kw, s!"{rel}:{e.name}") }
          | .refused => t := { t with refused := t.refused.push (rnd, e.kw, s!"{rel}:{e.name}") }
        t := { t with unmapped := t.unmapped ++ fr.unmapped }
        state := state.set! i (rel, "\n".intercalate fr.lines.toList)
      IO.println s!"ROUND {rnd} patched {progress} declaration(s); {locs.length} error location(s)"
      if progress == 0 then
        IO.println s!"ROUND {rnd} STUCK — every remaining error is a RESTATEMENT, a refusal or unmappable; the fixpoint cannot advance and the rest of the tree stays unread"
        break
    IO.println ""
    for l in summaryLines t rc do IO.println l
    let mut census := noCensus
    if let some probe := o.probe then
      IO.println ""
      IO.println s!"=== AXIOM CENSUS ({if rc == 0 then "at the FIXPOINT" else "at a STUCK point: only what built is readable"}) ==="
      let scratch := root / "L4YAML" / "Scratch"
      let hadScratch ← scratch.pathExists
      IO.FS.createDirAll scratch
      let name := (System.FilePath.mk probe).fileName.getD "probe.lean"
      let dest := scratch / name
      if ← dest.pathExists then
        throw <| IO.userError s!"{dest} exists; the probe is copied there and removed after, so move that file first"
      IO.FS.writeBinFile dest (← IO.FS.readBinFile probe)
      let r ← IO.Process.output { cmd := "lake", args := #["env", "lean", s!"L4YAML/Scratch/{name}"], cwd := some root }
      let axlog := r.stdout ++ r.stderr
      keepLog o.logDir "flip.beta5.axioms.log" axlog
      IO.println s!"PROBE exit={r.exitCode}"
      IO.println axlog
      IO.FS.removeFile dest
      if !hadScratch && (← scratch.readDir).isEmpty then IO.FS.removeDir scratch
      if r.exitCode != 0 then
        IO.println "THE PROBE DID NOT ELABORATE — a module it imports did not build, so no profile was read.  A missing reading is not a clean one."
      census := (census? axlog).getD noCensus
    let line := fixline t census
    IO.println ""
    IO.println s!"FIXLINE {line}"
    let pinPath := root / pinFile
    let pinSrc ← if ← pinPath.pathExists then some <$> readText pinPath else pure none
    for l in pinVerdict "FIX-PIN" "expectedFixpoint" line pinSrc do IO.println l
    pure (Except.ok ())
  catch e => pure (.error s!"{e}")
  let ok ← restoreAll touched
  if !ok then
    return ← die "the restore did not restore; fix the sources before trusting anything else in this run"
  IO.println "rebuilding so no later probe reads the flipped oleans..."
  let _ ← lakeBuild root #[]
  match res with
  | .ok () => return 0
  | .error e => return ← die e

/-! ## The arms -/

def blurb : String → String
  | "control" => "β.5's three deletions alone — item 263's seven, re-derived"
  | _ => "…and the dead branches deleted — what is left is the REPAIR"

def runEnd (o : Opts) (name : String) : IO (Except String (List (String × String × Nat))) := do
  let root := o.root
  IO.println s!"=== END {name}: {blurb name} ==="
  let touched ← IO.mkRef (#[] : Array Touched)
  let res ← try
    touch root touched acc
    touch root touched doc
    let (a, d) ← ofExcept (beta5Edits (← readText (root / acc)) (← readText (root / doc)))
    let a ← if name == "arms" then do
        let (a', notes) ← ofExcept (deleteDead a)
        for n in notes do IO.println s!"  DELETED  {n}"
        pure a'
      else pure a
    IO.FS.writeFile (root / acc) a
    IO.FS.writeFile (root / doc) d
    let (_, log) ← lakeBuild root #["L4YAML"]
    keepLog o.logDir s!"arms.{name}.log" log
    pure (Except.ok (brokenRows log [(acc, (a.splitOn "\n").toArray), (doc, (d.splitOn "\n").toArray)]))
  catch e => pure (.error s!"{e}")
  let ok ← restoreAll touched (flagged := true)
  if !ok then return .error s!"{root / acc} or {root / doc} was not restored"
  match res with
  | .error e => return .error e
  | .ok rows =>
    IO.println s!"BROKEN {rows.length}"
    for (rel, decl, line) in rows do IO.println s!"  {rel}:{line}  {decl}"
    return .ok rows

def runArms (o : Opts) : IO UInt32 := do
  let ends := if o.ends.isEmpty then ["control", "arms"] else o.ends
  let mut counts : List (String × List (String × String × Nat)) := []
  for name in ends do
    match ← runEnd o name with
    | .error e => return ← die e
    | .ok rows => counts := counts ++ [(name, rows)]
    IO.println ""
  if ends.contains "control" && ends.contains "arms" then
    let names (n : String) : List String :=
      ((counts.filter (·.1 == n)).map (·.2)).flatten.map (·.2.1)
    let (line, extra) := armLines (names "control") (names "arms")
    IO.println s!"ARMLINE {line}"
    for l in extra do IO.println l
    let pinPath := o.root / pinFile
    let pinSrc ← if ← pinPath.pathExists then some <$> readText pinPath else pure none
    for l in pinVerdict "ARM-PIN" "expectedArms" line pinSrc do IO.println l
  return 0

/-! ## The mapper -/

def runMap (o : Opts) (logPath : String) : IO UInt32 := do
  let log ← readText logPath
  let locs := errorLocs log
  let mut files : List (String × Option (Array String)) := []
  for (p, _) in locs do
    if files.any (·.1 == p) then continue
    let path := o.root / p
    let content ← if ← path.pathExists then some <$> (fun s => (s.splitOn "\n").toArray) <$> readText path else pure none
    files := files ++ [(p, content)]
  let (defs, n, complaints) := brokenDefinitions locs fun p => (files.lookup p).getD none
  for l in mapperReport defs n complaints do IO.println l
  return if complaints.isEmpty then 0 else 1

/-- `--dry`: the edits computed and digested, nothing written to the tree. -/
def runDry (o : Opts) : IO UInt32 := do
  let root := o.root
  let accT ← readText (root / acc)
  let docT ← readText (root / doc)
  let (a, d) ← match beta5Edits accT docT with
    | .ok x => pure x
    | .error e => return ← die e
  let dump (end_ rel text : String) : IO Unit := do
    IO.println s!"--dry {end_}  {rel}  {Patch.digest text.toUTF8}"
    if let some dir := o.logDir then
      IO.FS.createDirAll dir
      IO.FS.writeFile (System.FilePath.mk dir / s!"dry.{end_}.{(System.FilePath.mk rel).fileName.getD rel}") text
  dump "control" acc a
  dump "control" doc d
  if o.pos == ["arms"] then
    let (a', notes) ← match deleteDead a with
      | .ok x => pure x
      | .error e => return ← die e
    for n in notes do IO.println s!"  DELETED  {n}"
    dump "arms" acc a'
  return 0

def run (args : List String) : IO UInt32 := do
  if args.contains "-h" || args.contains "--help" then IO.println usage; return 0
  if args.contains "-V" || args.contains "--version" then IO.println version; return 0
  let args := if args.headD "" == "--" then args.drop 1 else args
  let o ← match parseOpts args {} with
    | .ok o => pure o
    | .error e => return ← die s!"{e}\n{usage}" 2
  let root ← try IO.FS.realPath o.root catch e => return ← die s!"invalid root: {e}" 2
  let o := { o with root }
  if o.dry && (o.pos == ["fixpoint"] || o.pos == ["arms"]) then return ← runDry o
  match o.pos with
  | ["fixpoint"] =>
    if !(← (root / acc).pathExists) then return ← die s!"{root / acc} not found (pass -C ROOT)" 2
    runFixpoint o
  | ["arms"] =>
    if !(← (root / acc).pathExists) then return ← die s!"{root / acc} not found (pass -C ROOT)" 2
    runArms o
  | ["map", logPath] => runMap o logPath
  | _ => die s!"one of: fixpoint | arms | map LOG\n{usage}" 2

end

end Scripts.Beta5Main

@[expose] public def main (args : List String) : IO UInt32 :=
  Scripts.Beta5Main.run args
