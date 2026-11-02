module

public import Scripts.Flip.Patch
public import Scripts.Flip.Round
public import Scripts.Flip.Report
public import Scripts.Git
public import Lean.Data.Json

@[expose] public section Blanket

/-!
# scripts-flip — price a flip spec at a revision

```
lake exe scripts-flip SPEC.json [-C ROOT] [--rev REV] [--keep] [--dry] [-h] [-V]
```

The one driver behind every `scripts/flip_*.py`: a spec names a library
file, the revision whose text its anchors were written against, the
anchored replacements, the build target and the report's tag.  The run

1. refuses when any other `L4YAML/**` file differs between REV and the
   working tree (uncommitted edits count) — the build would read a mixed tree;
   run it in a `git worktree` of REV instead;
2. takes the file from `git show REV:path`, applies the patches (each anchor
   exactly `count` times or the run stops before touching the tree);
3. writes the patched copy over the working-tree file, prints the content
   hash both sides, builds the target, saves the log, and bills every error
   site in the file to its enclosing declaration;
4. restores the working tree's own bytes, checks they are identical, and
   rebuilds the target so no later probe reads a flipped `.olean` (`--keep`
   leaves the patched tree in place, the pay's starting point).

Never run it beside another `lake build`.  Spec format (JSON, read by
`Lean.Json` — core, no new dependency; a spec is data, not code, and an
array of lines keeps the Lean text literal):

```json
{ "item": 416, "tag": "KSLOTE-FLIP", "rev": "55d03804",
  "file": "L4YAML/Proofs/Production/StreamAccum.lean", "target": "L4YAML",
  "log": "scratch/kslote_flip.log", "msgWidth": 100, "rounds": 1,
  "report": "owners" | "bodies", "filter": "Type mismatch" (bodies: list only the sites whose head starts with it, case-insensitive),
  "patches": [ { "name": "FIELD", "old": ["line", "line"], "new": ["line"], "count": 1 } ] }
```
-/

open Lean Scripts.Flip Scripts.Flip.Round Scripts.Flip.Report Scripts.Lean.BuildLog

namespace Scripts.FlipMain

def version : String := "scripts-flip 0.1.0 (L4YAML Rule 9 flip library)"

def usage : String :=
"usage: lake exe scripts-flip SPEC.json [-C ROOT] [--rev REV] [--keep] [--dry]

Price the flip SPEC.json describes: patch the spec's file as it reads at
REV (default: the spec's rev) into the working tree, build the target,
report every error site with its enclosing declaration, restore the file
byte-identically.  Refuses when another L4YAML/** file differs between
REV and the working tree.  Never run beside another lake build.

  -C, --root ROOT   repository root (default: .)
  -r, --rev REV     revision holding the un-paid text (default: spec.rev)
  -k, --keep        leave the patched tree in place
  -d, --dry         check that every anchor matches; write and build nothing
  -V, --version     print the version and exit
  -h, --help        print this help and exit

exit status: 0 run complete, files restored and rebuilt; 1 a file not
restored identically; 2 usage, spec, git or anchor error; 3 incomplete probe
(the build failed with no attributable site, or only dependent modules
fail); 4 the rebuild of the restored tree failed."

structure PatchJ where
  name : String
  old : Array String
  new : Array String
  count : Nat := 1
  line : Option Nat := none

structure FileJ where
  file : String
  patches : Array PatchJ
  deriving Inhabited

structure Spec where
  item : Nat
  tag : String
  rev : String
  files : Array FileJ
  target : String := "L4YAML"
  log : String
  msgWidth : Nat := 100
  rounds : Nat := 1
  lib : String := "L4YAML"
  report : String := "owners"
  filter : Option String := none

/-- A field with a default when the key is absent (derived `FromJson` would
require every key). -/
def getOr {α : Type} [FromJson α] (j : Json) (k : String) (d : α) : Except String α :=
  match j.getObjVal? k with
  | .ok v => fromJson? v
  | .error _ => .ok d

instance : FromJson PatchJ where
  fromJson? j := do
    let name ← j.getObjValAs? String "name"
    let old ← j.getObjValAs? (Array String) "old"
    let new ← j.getObjValAs? (Array String) "new"
    let count ← getOr j "count" 1
    let line ← getOr j "line" (none : Option Nat)
    return { name, old, new, count, line }

instance : FromJson FileJ where
  fromJson? j := do
    return { file := ← j.getObjValAs? String "file", patches := ← j.getObjValAs? (Array PatchJ) "patches" }

/-- A spec names either one `file` with its `patches` or a `files` array. -/
instance : FromJson Spec where
  fromJson? j := do
    let item ← j.getObjValAs? Nat "item"
    let tag ← j.getObjValAs? String "tag"
    let rev ← j.getObjValAs? String "rev"
    let files ← match j.getObjVal? "files" with
      | .ok v => fromJson? v
      | .error _ => do
        let file ← j.getObjValAs? String "file"
        let patches ← j.getObjValAs? (Array PatchJ) "patches"
        pure #[{ file, patches : FileJ }]
    if files.isEmpty then throw "spec names no file"
    let target ← getOr j "target" "L4YAML"
    let log ← j.getObjValAs? String "log"
    let msgWidth ← getOr j "msgWidth" 100
    let rounds ← getOr j "rounds" 1
    let lib ← getOr j "lib" "L4YAML"
    let report ← getOr j "report" "owners"
    if report != "owners" && report != "bodies" then throw s!"report must be `owners` or `bodies`, not `{report}`"
    let filter ← getOr j "filter" (none : Option String)
    return { item, tag, rev, files, target, log, msgWidth, rounds, lib, report, filter }

def PatchJ.toPatch (p : PatchJ) : Patch.Patch :=
  ⟨p.name, "\n".intercalate p.old.toList, "\n".intercalate p.new.toList, p.count⟩

/-- Apply a file's patches in order: anchored (`count` occurrences in the
file) or line-keyed (`line` given: once within that line). -/
def applyFile (t : String) : List PatchJ → Except String String
  | [] => .ok t
  | p :: ps => do
    let t' ← match p.line with
      | some ln => Patch.applyAt t ln p.toPatch
      | none => Patch.apply1 t p.toPatch
    applyFile t' ps

structure Opts where
  spec : String := ""
  root : String := "."
  rev : Option String := none
  keep : Bool := false
  dry : Bool := false

inductive Parsed | help | version | bad (msg : String) | run (o : Opts)

def parseArgs (args : List String) : Parsed :=
  if args.isEmpty || args.contains "-h" || args.contains "--help" then .help
  else if args.contains "-V" || args.contains "--version" then .version
  else go args {} false
where
  go : List String → Opts → Bool → Parsed
    | [], o, seen => if seen then .run o else .bad "SPEC.json is required"
    | a :: rest, o, seen =>
      if a == "-C" || a == "--root" then
        match rest with
        | v :: rest' => go rest' { o with root := v } seen
        | [] => .bad s!"`{a}` needs a value"
      else if a == "-r" || a == "--rev" then
        match rest with
        | v :: rest' => go rest' { o with rev := some v } seen
        | [] => .bad s!"`{a}` needs a value"
      else if a == "-k" || a == "--keep" then go rest { o with keep := true } seen
      else if a == "-d" || a == "--dry" then go rest { o with dry := true } seen
      else if a.startsWith "-" then .bad s!"unknown option `{a}`"
      else if seen then .bad s!"too many arguments at `{a}`"
      else go rest { o with spec := a } true

/-- Python `str.splitlines()`-shaped line table (see `scripts-flip-census`). -/
def splitLines (s : String) : Array String :=
  let arr := (s.splitOn "\n").toArray
  if arr.size > 0 && arr.back! == "" then arr.pop else arr

def readSpec (path : String) : IO (Except String Spec) := do
  let txt ← try IO.FS.readFile path catch e => return .error s!"cannot read {path}: {e}"
  return Json.parse txt >>= fromJson?

/-- Sites of a dependent file, resolved against its own source under `root`
(owner prefixed by the file); `file ?` when the file cannot be read. -/
def otherSites (root : System.FilePath) (errs : Array (ErrLine × String)) (f : String) : IO (Array Site) := do
  try
    let txt ← IO.FS.readFile (root / f)
    return resolveSites errs f (splitLines txt) (fun n => s!"{f} {n}")
  catch _ =>
    return errs.filterMap fun (e, body) => if e.file == f then some ⟨f, e.line, e.msg, s!"{f} ?", body⟩ else none

/-- One build round: build (`target` empty = the whole `lake build`), save the
log, return (exit, sites in the flipped files resolved against `texts`, sites
in every other file). -/
def round (root : System.FilePath) (spec : Spec) (texts : Array (String × Array String)) : IO (UInt32 × Array Site × Array Site) := do
  let args := if spec.target.isEmpty then #["build"] else #["build", spec.target]
  let o ← IO.Process.output { cmd := "lake", args, cwd := some root }
  let out := o.stdout ++ o.stderr
  let logPath := root / spec.log
  if let some d := logPath.parent then IO.FS.createDirAll d
  IO.FS.writeFile logPath out
  let errs := errsOf out
  let mut main := #[]
  for (f, ls) in texts do
    main := main ++ resolveSites errs f ls (fun n => if texts.size == 1 then n else s!"{f} {n}")
  let mut others := #[]
  for f in filesOf errs do
    if !(texts.any fun (g, _) => namesFile f g) then others := others ++ (← otherSites root errs f)
  return (o.exitCode, main, others)

def runSpec (o : Opts) : IO UInt32 := do
  let root : System.FilePath := o.root
  let spec ← match ← readSpec o.spec with
    | .ok s => pure s
    | .error e => IO.eprintln s!"scripts-flip: {e}"; return 2
  let rev := o.rev.getD spec.rev
  let names := spec.files.map (·.file)
  if ← Scripts.Git.othersDiffer root rev spec.lib names.toList then
    IO.eprintln s!"library files other than {", ".intercalate names.toList} differ between {rev} and the working tree; run the probe in a `git worktree` of {rev} instead"
    return 2
  -- patched text per file, before anything is written
  let mut patched : Array (String × String) := #[]
  for fj in spec.files do
    let shown ← match ← Scripts.Git.showAt root rev fj.file with
      | .ok t => pure t
      | .error e => IO.eprintln s!"cannot read {fj.file} at {rev}: {e}"; return 2
    match applyFile shown fj.patches.toList with
    | .ok t => patched := patched.push (fj.file, t)
    | .error e => IO.eprintln s!"scripts-flip: {fj.file}: {e}"; return 2
  let mut origs : Array (String × ByteArray) := #[]
  for (f, _) in patched do
    origs := origs.push (f, ← IO.FS.readBinFile (root / f))
  let hashes := origs.map fun (f, b) => s!"{f} {Patch.digest b}"
  IO.println s!"pricing {", ".intercalate names.toList} at {rev} (working tree hash {" ".intercalate hashes.toList})"
  (← IO.getStdout).flush
  let nPatches := spec.files.foldl (· + ·.patches.size) 0
  if o.dry then
    IO.println s!"--dry: {nPatches} anchor(s) found exactly as the spec says; nothing written"
    return 0
  let mut texts : Array (String × Array String) := patched.map fun (f, t) => (f, splitLines t)
  let mut restoredOk := true
  let mut cleanupOk := true
  let mut incomplete : Option String := none
  let primary := spec.files[0]!.file
  try
    for (f, t) in patched do IO.FS.writeFile (root / f) t
    IO.println s!"flip tree hash {" ".intercalate (patched.map fun (f, t) => s!"{f} {Patch.digest t.toUTF8}").toList}; building {if spec.target.isEmpty then "everything" else spec.target} …"
    (← IO.getStdout).flush
    let mut r := 1
    let mut seen : Array Site := #[]
    repeat
      let (code, main, others) ← round root spec texts
      let fresh := (main ++ others).filter fun s => !(seen.any (·.owner == s.owner))
      if r == 1 then
        IO.println (headline spec.tag code (main ++ others))
        if spec.report == "bodies" then
          let listed := match spec.filter with
            | some f => main.filter fun s => s.msg.toLower.startsWith f.toLower   -- the Python's `[Tt]ype mismatch` head
            | none => main
          if let some f := spec.filter then
            IO.println s!"  {listed.size} site(s) match `{f}`; {main.size - listed.size} other diagnostic(s) in the flipped file(s)"
          for l in bodyLines listed do IO.println l
          let rest := main.filter fun s => !(listed.any (· == s))
          if !rest.isEmpty then
            IO.println "  other diagnostics (not matching the filter):"
            for l in ownerLines rest spec.msgWidth do IO.println l
        else
          for l in ownerLines main spec.msgWidth do IO.println l
        if !others.isEmpty then
          IO.println s!"  other files: {others.size} site(s) in {(byOwner others).size} declaration(s)"
          for l in ownerLines others spec.msgWidth do IO.println l
      else
        IO.println s!"round {r}: exit={code} errors={main.size + others.size} new decls={(byOwner fresh).size}"
        for l in ownerLines fresh spec.msgWidth do IO.println l
      seen := seen ++ fresh
      if code == 0 then
        if r > 1 then IO.println s!"round {r}: build green — fixpoint"
        break
      if main.isEmpty && others.isEmpty then
        incomplete := some "the build failed with no diagnostic attributable to a source line (wrong target? Lake error?) — see the log"
        break
      if r ≥ spec.rounds then break
      let freshMain := fresh.filter fun s => texts.any (·.1 == s.file)
      if freshMain.isEmpty then
        incomplete := some s!"no new site in the flipped file(s) but the build still fails ({others.size} site(s) in dependent modules, outside the flip's scope)"
        break
      texts := texts.map fun (f, ls) => (f, sorryBodies ls (main.filter (·.file == f)))
      for (f, ls) in texts do IO.FS.writeFile (root / f) ("\n".intercalate ls.toList ++ "\n")
      r := r + 1
    if spec.rounds > 1 then
      IO.println s!"after {r} round(s): errors={seen.size} decls={(byOwner seen).size}"
    if let some why := incomplete then IO.println s!"INCOMPLETE: {why}"
    IO.println s!"FLOOR: one build of `{if spec.target.isEmpty then "everything" else spec.target}` per round; guard modules behind it unmeasured."
  finally
    if o.keep then
      for (f, t) in patched do IO.FS.writeFile (root / f) t
      IO.println s!"--keep: patched copy of {rev}:{primary}{if patched.size > 1 then " (+" ++ toString (patched.size - 1) ++ " file(s))" else ""} left in place (the spec's text, no round's sorry)"
    else
      for (f, b) in origs do
        IO.FS.writeBinFile (root / f) b
        let now ← IO.FS.readBinFile (root / f)
        let same := now == b
        IO.println s!"restored {f} hash {Patch.digest now} (orig {Patch.digest b}) identical={same}"
        if !same then restoredOk := false
      -- as flip_210.py did: rebuild so no later probe reads a flipped .olean
      let args := if spec.target.isEmpty then #["build"] else #["build", spec.target]
      let o ← IO.Process.output { cmd := "lake", args, cwd := some root }
      IO.println s!"rebuilt {if spec.target.isEmpty then "everything" else spec.target} on the restored tree: exit={o.exitCode}"
      if o.exitCode != 0 then cleanupOk := false
  return if !restoredOk then 1 else if !cleanupOk then 4 else if incomplete.isSome then 3 else 0

end Scripts.FlipMain

open Scripts.FlipMain in
def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .help => IO.println usage; return (if args.isEmpty then 2 else 0)
  | .version => IO.println version; return 0
  | .bad m => IO.eprintln s!"scripts-flip: {m}\n{usage}"; return 2
  | .run o => runSpec o
