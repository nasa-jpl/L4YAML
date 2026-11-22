module

public import Scripts.Lean.GateVocab

@[expose] public section Blanket

/-!
# scripts-gate-vocab — gate names in prose resolve (DOCS items 265, 266)

```
lake run check-gate-vocab [-- --list]   -- or, under `lake env`: lake exe scripts-gate-vocab [-C ROOT] [-l] [-w]
```

Formerly `python3 scripts/gate_vocab.py [--list]`; see `Scripts.Lean.GateVocab`.
The environment is read off `.olean` headers found through `LEAN_PATH`
(`lake env`, or the `lake run` wrapper, sets it); the modules read are every
built `L4YAML/**` and `Tests/**` module (not under `Scratch/`) and their
transitive imports.  `-w` (`--wide-only`) excludes the exe root modules (those
defining `main`), which is the set the Python's single-environment dump could
read; the default reads them too.
-/

open Scripts.Lean.GateVocab

namespace Scripts.GateVocab

def version : String := "scripts-gate-vocab 0.1.0 (L4YAML gate-vocabulary census)"

def usage : String :=
"usage: lake exe scripts-gate-vocab [options]

Every backticked gate name (`scanNextToken_…`, `scanLoop_…`, `scanLoopIx_…`,
short `check<Upper><Upper>…`) and refutation name (`…_refuted`) in L4YAML/**
and Tests/** prose resolves to a constant of the built environment; the
reading is compared with `expectedGateVocab` in
Tests/Guards/Proofs/GateVocabulary.lean.  Needs LEAN_PATH (run under
`lake env` or as `lake run check-gate-vocab`).

options:
  -C, --root DIR      repository root (default: .)
  -l, --list          print every mention of every gate name (OK / MISS)
  -w, --wide-only     exclude exe root modules (files defining `main`)
  -V, --version       print the version and exit
  -h, --help          print this help and exit

exit status: 0 green, 1 unresolved names, no pin, pin disagrees or nothing
scanned; 2 usage or I/O error."

structure Options where
  root : String := "."
  list : Bool := false
  wideOnly : Bool := false

inductive Parsed where
  | run (o : Options)
  | help
  | version
  | bad (msg : String)

def parseArgs : List String → Options → Parsed
  | [], o => .run o
  | ("-h" :: _), _ | ("--help" :: _), _ => .help
  | ("-V" :: _), _ | ("--version" :: _), _ => .version
  | ("-l" :: rest), o | ("--list" :: rest), o => parseArgs rest { o with list := true }
  | ("-w" :: rest), o | ("--wide-only" :: rest), o => parseArgs rest { o with wideOnly := true }
  | ("-C" :: d :: rest), o | ("--root" :: d :: rest), o => parseArgs rest { o with root := d }
  | (a :: _), _ => .bad s!"unknown argument `{a}`"

/-- `L4YAML/**/*.lean` and `Tests/**/*.lean`, not under `Scratch/`, relative,
in Python's `sorted(Path)` order. -/
def sources (root : String) : IO (Array String) := do
  let base : System.FilePath := root
  let prefix_ := (base / "").toString
  let mut out : Array String := #[]
  for dir in ["L4YAML", "Tests"] do
    for p in (← (base / dir).walkDir) do
      if p.extension == some "lean" then
        let s := p.toString
        let rel := if s.startsWith prefix_ then String.ofList (s.toList.drop prefix_.length) else s
        if !(rel.splitOn "/Scratch/").length > 1 then out := out.push rel
  return out.qsort pathLt

def moduleOf (rel : String) : String := ".".intercalate (((rel.dropEnd 5).toString).splitOn "/")

/-- Final string components of every non-internal constant of `mods` and their
transitive imports, off the `.olean` headers. -/
def constantNames (mods : Array String) : IO (Std.HashSet String × Nat) := do
  let mut seen : Std.HashSet Lean.Name := {}
  let mut names : Std.HashSet String := {}
  let mut frontier : List Lean.Name := mods.toList.map String.toName
  let mut count := 0
  while !frontier.isEmpty do
    let m := frontier.head!
    frontier := frontier.tail
    if seen.contains m then continue
    seen := seen.insert m
    let path ← Lean.findOLean m
    let (data, _) ← Lean.readModuleData path
    count := count + 1
    for n in data.constNames do
      if n.isInternal then continue
      if let .str _ s := n then names := names.insert s
    for i in data.imports do frontier := i.module :: frontier
  return (names, count)

def run (o : Options) : IO UInt32 := do
  let files ← sources o.root
  let mut scan : Scan := {}
  let mut mods : Array String := #[]
  let root : System.FilePath := o.root
  for rel in files do
    let text ← IO.FS.readFile (root / rel)
    scan := scanFile scan rel text (rel == pinFile)
    let m := moduleOf rel
    let olean := root / ".lake" / "build" / "lib" / "lean" / (("/".intercalate (m.splitOn ".")) ++ ".olean")
    if (← olean.pathExists) && !(o.wideOnly && definesMain text) then mods := mods.push m
  if scan.hits.isEmpty then
    IO.println "gate_vocab: no gate or refutation name found in any comment — the scan is reading nothing, which is not the same as a clean tree"
    return 1
  Lean.initSearchPath (← Lean.findSysroot)
  let (names, count) ← try constantNames mods
    catch e => do
      IO.eprintln s!"scripts-gate-vocab: the environment could not be read ({e}); run under `lake env` or as `lake run check-gate-vocab`"
      return 2
  IO.println s!"environment: {names.size} distinct final name components ({count} modules read)"
  let r := reading scan names
  IO.println s!"GATEVOCAB {r.got}"
  if o.list then
    for n in r.sortedNames do
      let k := ((scan.hits.find? (·.1 == n)).map (·.2.size)).getD 0
      IO.println s!"  {if resolves names n then "OK " else "MISS"} {n}  ({k})"
  for n in r.unresolved do
    IO.println s!"  UNRESOLVED {n}"
    if let some (_, ms) := scan.hits.find? (·.1 == n) then
      for (f, i) in ms do IO.println s!"      {f}:{i}"
  let mut rc : UInt32 := 0
  let pinPath := root / pinFile
  let want ← if (← pinPath.pathExists) then pure (expectedPin (← IO.FS.readFile pinPath)) else pure none
  match want with
  | none => IO.println s!"no pin in {pinFile}"; rc := 1
  | some w =>
    if w != r.got then
      IO.println s!"GATE-PIN DISAGREES\n  Lean:   {w}\n  script: {r.got}"; rc := 1
    else IO.println s!"GATE-PIN agrees with {pinFile}"
  if !r.unresolved.isEmpty then rc := 1
  return rc

end Scripts.GateVocab

open Scripts.GateVocab in
public def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .help => IO.println usage; return 0
  | .version => IO.println version; return 0
  | .bad m => IO.eprintln s!"scripts-gate-vocab: {m}\n{usage}"; return 2
  | .run o => run o
