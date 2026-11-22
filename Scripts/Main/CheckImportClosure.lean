module

public import Scripts.Lean.ImportClosure

@[expose] public section Blanket

/-!
# scripts-check-import-closure — the no-orphan-modules gate

```
lake run check-import-closure         -- builds L4YAML + the emitter exes first, then:
lake exe scripts-check-import-closure [-C ROOT] [-v]
```

Formerly `scripts/check_import_closure.py`; see `Scripts.Lean.ImportClosure`.
-/

open Scripts.Lean.ImportClosure

namespace Scripts.CheckImportClosure

def version : String := "scripts-check-import-closure 0.1.0 (L4YAML import-closure gate)"

def usage : String :=
"usage: lake exe scripts-check-import-closure [options]

Import-closure gate, off the .olean headers of a default-target build:
every L4YAML/**/*.lean is reachable from the default targets (L4YAML and
the four emitter exes), every reached module has a .olean to read, and every
Tests/Reflections/*.lean is imported by Tests/Reflections.lean.  Run after
`lake build L4YAML l4yaml-event l4yaml-json l4yaml-event-ix l4yaml-json-ix`
(`lake run check-import-closure` does that first).

options:
  -C, --root DIR      repository root (default: .)
  -v, --verbose       list every module reached, with its import count
  -V, --version       print the version and exit
  -h, --help          print this help and exit

exit status: 0 green, 1 violations, 2 usage or I/O error."

structure Options where
  root : String := "."
  verbose : Bool := false

inductive Parsed where
  | run (o : Options)
  | help
  | version
  | bad (msg : String)

def parseArgs : List String → Options → Parsed
  | [], o => .run o
  | ("-h" :: _), _ | ("--help" :: _), _ => .help
  | ("-V" :: _), _ | ("--version" :: _), _ => .version
  | ("-v" :: rest), o | ("--verbose" :: rest), o => parseArgs rest { o with verbose := true }
  | ("-C" :: d :: rest), o | ("--root" :: d :: rest), o => parseArgs rest { o with root := d }
  | (a :: _), _ => .bad s!"unknown argument `{a}`"

/-- Relative `.lean` paths under `dir` (recursive), `/`-separated, sorted. -/
def leanFiles (root dir : String) (recursive : Bool) : IO (Array String) := do
  let base : System.FilePath := root
  let d := base / dir
  if !(← d.isDir) then return #[]
  let paths ← if recursive then d.walkDir else pure ((← d.readDir).map (·.path))
  let prefix_ := (base / "").toString
  let out := paths.filterMap fun p =>
    if p.extension == some "lean" then
      let s := p.toString
      some (if s.startsWith prefix_ then String.ofList (s.toList.drop prefix_.length) else s)
    else none
  return out.qsort (· < ·)

/-- The header imports of module `m`, or `none` when its `.olean` is absent. -/
def headerImports (root m : String) : IO (Option (Array String)) := do
  let olean : System.FilePath := (root : System.FilePath) / oleanDir / (pathOf m ++ ".olean")
  if !(← olean.pathExists) then return none
  let (data, _) ← Lean.readModuleData olean
  return some (data.imports.map (·.module.toString))

def run (o : Options) : IO UInt32 := do
  let libFiles ← leanFiles o.root "L4YAML" true
  let onDisk := libFiles.map moduleOf
  let (seen, missingMods) ← closure (headerImports o.root) roots
  if o.verbose then
    for m in seen do
      let n := (← headerImports o.root m).map (·.size)
      IO.println s!"  {m}: {match n with | some k => s!"{k} imports" | none => "no header"}"
  let orphans := (onDisk.zip libFiles).filterMap fun (m, p) => if seen.contains m then none else some p
  let missing := missingMods.map fun m => pathOf m ++ ".lean"
  let indexText ← IO.FS.readFile ((o.root : System.FilePath) / "Tests" / "Reflections.lean")
  let indexed := importsOfText indexText
  let reflFiles ← leanFiles o.root "Tests/Reflections" false
  let unindexed := reflFiles.filter fun p => !indexed.contains (moduleOf p)
  let f : Findings := { onDisk := onDisk.size, orphans, missing, unindexed, indexed := indexed.size }
  if f.count == 0 then
    IO.println f.okLine
    return 0
  for l in f.lines do IO.println l
  IO.eprintln s!"error: {f.count} import-closure violations"
  return 1

end Scripts.CheckImportClosure

open Scripts.CheckImportClosure in
public def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .help => IO.println usage; return 0
  | .version => IO.println version; return 0
  | .bad m => IO.eprintln s!"scripts-check-import-closure: {m}\n{usage}"; return 2
  | .run o => run o
