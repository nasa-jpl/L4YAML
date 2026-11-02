module

public import Scripts.Lean.AxiomLog

@[expose] public section Blanket

/-!
# scripts-check-serialization-proofs — kernel axiom profiles of the serialization proofs

```
lake run check-serialization-proofs           -- or: lake exe scripts-check-serialization-proofs [-C ROOT] [-k DIR]
lake exe scripts-check-serialization-proofs --validate BUILD+AXIOMS.log SORRY.log SITES.txt
```

Formerly `scripts/check-serialization-proofs.sh` + `check-serialization-axioms.py`.
Builds `L4YAML.Proofs.Serialization`, runs a deliberate-`sorry` probe through
`lake env lean` (the negative control must show both placeholder signals),
collects every `#print axioms` site of `L4YAML/Proofs/Serialization.lean` and
`L4YAML/Proofs/Serialization/**` (at least 45, or the sweep is broken), runs
them all in one `lake env lean` probe over `import L4YAML.Proofs.Serialization`,
and validates the observations (`Scripts.Lean.AxiomLog.validate`): no
placeholder, only the standard three axioms, one profile per name, every site
observed, the two headline sets exact.  `--validate` runs that last step alone
on saved logs (the shape the Python took), so the two readings can be diffed.
-/

open Scripts.Lean.AxiomLog

namespace Scripts.CheckSerializationProofs

def version : String := "scripts-check-serialization-proofs 0.1.0 (L4YAML serialization hygiene gate)"

def usage : String :=
"usage: lake exe scripts-check-serialization-proofs [options]
       lake exe scripts-check-serialization-proofs --validate LOG SORRY SITES

Serialization proof hygiene: build L4YAML.Proofs.Serialization, run the sorry
negative control, observe every `#print axioms` site under
L4YAML/Proofs/Serialization{.lean,/}, and validate: no placeholder, only
propext / Classical.choice / Quot.sound, every site observed, exact headline
profiles.

options:
  -C, --root DIR      repository root (default: .)
  -k, --keep DIR      write build.log, sorry.log, sites.txt, axioms.log,
                      qualification.log to DIR (default: a temporary directory)
  -m, --min-sites N   minimum number of `#print axioms` sites (default: 45)
      --validate LOG SORRY SITES
                      validate saved logs only (LOG = build + axioms output)
  -V, --version       print the version and exit
  -h, --help          print this help and exit

exit status: 0 green, 1 a check failed, 2 usage, build or probe failure."

structure Options where
  root : String := "."
  keep : Option String := none
  minSites : Nat := 45
  validate : Option (String × String × String) := none

inductive Parsed where
  | run (o : Options)
  | help
  | version
  | bad (msg : String)

def parseArgs : List String → Options → Parsed
  | [], o => .run o
  | ("-h" :: _), _ | ("--help" :: _), _ => .help
  | ("-V" :: _), _ | ("--version" :: _), _ => .version
  | ("-C" :: d :: rest), o | ("--root" :: d :: rest), o => parseArgs rest { o with root := d }
  | ("-k" :: d :: rest), o | ("--keep" :: d :: rest), o => parseArgs rest { o with keep := some d }
  | ("-m" :: n :: rest), o | ("--min-sites" :: n :: rest), o =>
    match n.toNat? with
    | some k => parseArgs rest { o with minSites := k }
    | none => .bad s!"--min-sites wants a number, got `{n}`"
  | ("--validate" :: l :: s :: t :: rest), o => parseArgs rest { o with validate := some (l, s, t) }
  | (a :: _), _ => .bad s!"unknown argument `{a}`"

def sorryProbe : String :=
  "theorem serializationSorryProbe : True := by\n  sorry\n#print axioms serializationSorryProbe\n"

/-- Run `cmd args` in `root`, returning the exit code and stdout++stderr, and
echo the output (the `.sh` `tee`d every step). -/
def runLogged (root : String) (cmd : String) (args : Array String) : IO (UInt32 × String) := do
  let r ← IO.Process.output { cmd, args, cwd := some root }
  let text := r.stdout ++ r.stderr
  IO.print text
  return (r.exitCode, text)

/-- `#print axioms NAME` lines of a file, in order. -/
def axiomSites (text : String) : List String :=
  (text.splitOn "\n").filterMap fun l =>
    if l.startsWith "#print axioms " then some ((l.drop "#print axioms ".length).toString) else none

def leanFilesUnder (dir : System.FilePath) : IO (Array System.FilePath) := do
  if !(← dir.isDir) then return #[]
  let ps ← dir.walkDir
  return (ps.filter (·.extension == some "lean")).qsort (fun a b => a.toString < b.toString)

def report (sites : Nat) : String :=
  s!"Serialization proof hygiene: {sites} observed profiles; exact headline sets; no placeholders or reduction axioms"

def validateFiles (log sorryLog sites : System.FilePath) : IO UInt32 := do
  let siteList := ((← IO.FS.readFile sites).splitOn "\n").filter (· != "")
  match validate (← IO.FS.readFile log) (← IO.FS.readFile sorryLog) siteList with
  | .error e => IO.eprintln e; return 1
  | .ok _ => IO.println (report siteList.length); return 0

def run (o : Options) : IO UInt32 := do
  if let some (l, s, t) := o.validate then
    return ← validateFiles l s t
  -- absolute paths throughout: the probes are written here and read by a
  -- child whose cwd is `root`, so a relative `-C` or `-k` must not be resolved twice
  let root : System.FilePath ← IO.FS.realPath o.root
  let rootS := root.toString
  let work : System.FilePath ← match o.keep with
    | some d => do
      let d : System.FilePath := d
      let cwd ← IO.currentDir
      pure (if d.isAbsolute then d else cwd / d)
    | none => pure (root / ".lake" / "scratch" / "serialization-proofs")
  IO.FS.createDirAll work
  let (bc, buildLog) ← runLogged rootS "lake" #["build", "L4YAML.Proofs.Serialization"]
  IO.FS.writeFile (work / "build.log") buildLog
  if bc != 0 then
    IO.eprintln "scripts-check-serialization-proofs: lake build L4YAML.Proofs.Serialization failed"
    return 2
  IO.FS.writeFile (work / "SerializationSorryProbe.lean") sorryProbe
  let (_, sorryLog) ← runLogged rootS "lake" #["env", "lean", (work / "SerializationSorryProbe.lean").toString]
  IO.FS.writeFile (work / "sorry.log") sorryLog
  let mut sites : List String := []
  for f in #[root / "L4YAML" / "Proofs" / "Serialization.lean"] ++ (← leanFilesUnder (root / "L4YAML" / "Proofs" / "Serialization")) do
    sites := sites ++ axiomSites (← IO.FS.readFile f)
  IO.FS.writeFile (work / "sites.txt") ("\n".intercalate sites ++ (if sites.isEmpty then "" else "\n"))
  if sites.length < o.minSites then
    IO.println s!"axiom-site sweep found {sites.length} sites, expected >= {o.minSites}"
    return 1
  let probe := "import L4YAML.Proofs.Serialization\n" ++ "\n".intercalate (sites.map (s!"#print axioms {·}")) ++ "\n"
  IO.FS.writeFile (work / "SerializationAxiomProbe.lean") probe
  let (_, axLog) ← runLogged rootS "lake" #["env", "lean", (work / "SerializationAxiomProbe.lean").toString]
  IO.FS.writeFile (work / "axioms.log") axLog
  IO.FS.writeFile (work / "qualification.log") (buildLog ++ axLog)
  let code ← validateFiles (work / "qualification.log") (work / "sorry.log") (work / "sites.txt")
  if o.keep.isNone then
    for f in ["build.log", "sorry.log", "sites.txt", "axioms.log", "qualification.log",
              "SerializationSorryProbe.lean", "SerializationAxiomProbe.lean"] do
      IO.FS.removeFile (work / f)
    try IO.FS.removeDir work catch _ => pure ()
  return code

end Scripts.CheckSerializationProofs

open Scripts.CheckSerializationProofs in
public def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .help => IO.println usage; return 0
  | .version => IO.println version; return 0
  | .bad m => IO.eprintln s!"scripts-check-serialization-proofs: {m}\n{usage}"; return 2
  | .run o => run o
