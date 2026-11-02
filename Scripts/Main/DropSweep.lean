module

public import Scripts.Drop.Sweep
public import Scripts.Pins

/-!
# `lake run drop-sweep` — the WIDE reading of `scannerDrop`'s dependents

The port of `scripts/drop_sweep.py` (DOCS item 238; Rule 9 phase 2).  The walk itself
(`Tests.Guards.DropDependents.census`) is Lean already and pinned by that file against
its own import closure; this instrument is the WIDE reading — every `L4YAML.*` and
`Tests.*` module with an olean imported into one environment, plus the executable entry
points (a root `main` each; two in one environment is an import error, not a
measurement) probed one at a time against their own closures — and `DropDependents.lean`
pins that reading as `expectedWide` / `expectedWideCensus`.

The generated Lean lives in `L4YAML/Scratch/` and is removed on the way out; nothing in
the tree is edited.  Never run it beside a `lake build` (it runs `lake env lean`, and
`lake build MOD` on an entry point whose olean is unreadable).  stdout is the Python's,
line for line; the two pins are read through the dated notes (`Scripts.Pins.defSpan`)
and through a string gap (`\` + newline), on the definition line or below it.

exit status: 0 complete (quick) or complete with both pins agreeing; 1 a pin missing or
disagreeing, the walk not running clean or never composing, the walk's own module not
imported; 2 usage.
-/

open Scripts.Drop.Sweep

namespace Scripts.DropSweep

def version : String := "scripts-drop-sweep 1.0 (Rule 9 phase 2)"

def usage : String := "usage: lake run drop-sweep -- [-C ROOT] [-q]

  the wide walk over every built L4YAML.*/Tests.* module, then each entry point probed
  against its own closure, compared with the pins in Tests/Guards/Proofs/DropDependents.lean

options
  -C, --root ROOT   repository root, relative or absolute (default: the current directory)
  -q, --quick       the wide walk only (no per-entry-point probes, no pin comparison)
  -h, --help        this text
  -V, --version     version"

structure Opts where
  root : System.FilePath := "."
  quick : Bool := false
  deriving Inhabited

def die (msg : String) (code : UInt32 := 1) : IO UInt32 := do
  IO.eprintln msg
  return code

partial def parseOpts (args : List String) (o : Opts) : Except String Opts :=
  match args with
  | [] => pure o
  | "-C" :: v :: t | "--root" :: v :: t => parseOpts t { o with root := v }
  | "-q" :: t | "--quick" :: t => parseOpts t { o with quick := true }
  | a :: _ => throw s!"unexpected argument '{a}'"

def instrument : System.FilePath := "Tests" / "Guards" / "Proofs" / "DropDependents.lean"

/-- Every `.lean` under `dir` (relative paths), `Scratch/` excluded. -/
partial def leanFiles (root dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for e in (← (root / dir).readDir) do
    let rel := dir / e.fileName
    if (← e.path.isDir) then
      if e.fileName != "Scratch" then out := out ++ (← leanFiles root rel)
    else if e.fileName.endsWith ".lean" then out := out.push rel
  return out

/-- Python sorts `Path`s by their components, so a directory's files precede `Dir.lean`. -/
def pathLt (a b : System.FilePath) : Bool :=
  let rec go : List String → List String → Bool
    | [], [] => false
    | [], _ => true
    | _, [] => false
    | x :: xs, y :: ys => if x == y then go xs ys else decide (x < y)
  go a.components b.components

def run_ (root : System.FilePath) (args : Array String) : IO (UInt32 × String) := do
  let r ← IO.Process.output { cmd := "lake", args, cwd := some root }
  return (r.exitCode, r.stdout ++ r.stderr)

def pin? (text name : String) : Option String := do
  let lines := (text.splitOn "\n").toArray
  let span ← Scripts.Pins.defSpan lines name
  let body := "\n".intercalate (lines.extract (span.start + 1 + span.comments.size) span.stop).toList
  pinOfSpan? span.head.same body

def sweep (o : Opts) : IO UInt32 := do
  let scratch := o.root / "L4YAML" / "Scratch"
  let lib := o.root / ".lake" / "build" / "lib" / "lean"
  IO.FS.createDirAll scratch
  let files := ((← leanFiles o.root "L4YAML") ++ (← leanFiles o.root "Tests")).qsort pathLt
  let mut mods : Array String := #[]
  let mut excluded : Array String := #[]
  let mut unbuilt : Array String := #[]
  for f in files do
    let m := moduleOf f.toString
    if !(← (lib / (f.withExtension "olean")).pathExists) then unbuilt := unbuilt.push m
    else if hasMain (← IO.FS.readFile (o.root / f)) then excluded := excluded.push m
    else mods := mods.push m
  for m in unbuilt do
    IO.println s!"NO-OLEAN {m} (no Lake target; UNMEASURED by this sweep)"
  let walk := scratch / "DropSweep.lean"
  let mut code : UInt32 := 0
  let mut out := ""
  let mut composed := false
  for _ in [0:64] do
    IO.FS.writeFile walk ("\n".intercalate (mods.map (s!"import {·}")).toList ++ "\n\n" ++ walkBody)
    (code, out) ← run_ o.root #["env", "lean", walk.toString]
    match refused? out with
    | none => composed := true; break
    | some bad =>
      excluded := excluded.push bad
      mods := mods.filter (· != bad)
  if !composed then
    return ← die "the walk never composed; 64 modules refused and that is not an import conflict but a broken build"
  if code != 0 then
    IO.println out
    return ← die "the walk did not run clean"
  let mut closure := 0
  let mut census := ""
  for line in out.splitOn "\n" do
    if line.startsWith "WIDE" then
      IO.println line
      if let some c := closure? line then closure := c
      if let some c := census? line then census := c
  IO.println s!"WIDE imported={mods.size} excluded={excluded.size}"
  if !mods.contains "Tests.Guards.Proofs.DropDependents" then
    return ← die "the walk's own module is not in the import list; `lake build` it first or this sweep measures nothing"
  if o.quick then return 0
  let probe := scratch / "DropOne.lean"
  let mut decls := 0
  let mut hits := 0
  let mut reported := 0
  let mut unreadable : Array String := #[]
  for mod in excluded do
    IO.FS.writeFile probe s!"import {mod}\nimport Lean.Elab.Command\n{probeBody mod}"
    let mut (_, o1) ← run_ o.root #["env", "lean", probe.toString]
    if (o1.splitOn "MOD ").length < 2 then
      let _ ← run_ o.root #["build", mod]
      (_, o1) ← run_ o.root #["env", "lean", probe.toString]
    let mut saw := false
    for line in o1.splitOn "\n" do
      if line.startsWith "HIT " then
        IO.println line
        hits := hits + 1
      else if line.startsWith "MOD " then
        saw := true
        reported := reported + 1
        decls := decls + declsOf line
    if !saw then
      unreadable := unreadable.push mod
      IO.println s!"UNREADABLE {mod} :: {((o1.splitOn "\n").head?).getD ""}"
  let wide := wideLine closure mods.size excluded.size reported unreadable.size decls hits
  IO.println s!"EXCLUDED modules={excluded.size} readable={reported} unreadable={unreadable.size} decls={decls} dropRefs={hits}"
  IO.println s!"WIDE-LINE {wide}"
  let text ← IO.FS.readFile (o.root / instrument)
  let some pin := pin? text "expectedWide"
    | return ← die "no `expectedWide` pin in the instrument to compare against; this sweep would report a number nothing holds"
  if pin != wide then
    return ← die s!"the sweep and the instrument disagree:\n  swept  {wide}\n  pinned {pin}"
  let some pinC := pin? text "expectedWideCensus"
    | return ← die "no `expectedWideCensus` pin in the instrument; the four counts the whole tree reads would go unchecked"
  if pinC != census then
    return ← die s!"the sweep and the instrument disagree on the counts:\n  swept  {census}\n  pinned {pinC}"
  IO.println "WIDE-PIN agrees with Tests/Guards/Proofs/DropDependents.lean"
  for mod in excluded do IO.println s!"EXCLUDED-MOD {mod}"
  return 0

def cleanup (root : System.FilePath) : IO Unit := do
  let scratch := root / "L4YAML" / "Scratch"
  for f in [scratch / "DropSweep.lean", scratch / "DropOne.lean"] do
    if (← f.pathExists) then IO.FS.removeFile f
  if (← scratch.isDir) && (← scratch.readDir).isEmpty then IO.FS.removeDir scratch

def run (args : List String) : IO UInt32 := do
  if args.any (fun a => a == "-h" || a == "--help") then IO.println usage; return 0
  if args.any (fun a => a == "-V" || a == "--version") then IO.println version; return 0
  let o ← match parseOpts args {} with
    | .ok o => pure o
    | .error e => return ← die s!"{e}\n{usage}" 2
  let o := { o with root := ← IO.FS.realPath o.root }
  let res ← (sweep o).toBaseIO
  cleanup o.root
  match res with
  | .ok c => return c
  | .error e => die (toString e)

end Scripts.DropSweep

public def main (args : List String) : IO UInt32 := Scripts.DropSweep.run args
