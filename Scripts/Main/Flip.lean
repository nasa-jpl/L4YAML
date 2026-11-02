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
4. restores the working tree's own bytes and checks they are identical
   (`--keep` leaves the patched tree in place, the pay's starting point).

Never run it beside another `lake build`.  Spec format (JSON, read by
`Lean.Json` — core, no new dependency; a spec is data, not code, and an
array of lines keeps the Lean text literal):

```json
{ "item": 416, "tag": "KSLOTE-FLIP", "rev": "55d03804",
  "file": "L4YAML/Proofs/Production/StreamAccum.lean", "target": "L4YAML",
  "log": "scratch/kslote_flip.log", "msgWidth": 100, "rounds": 1,
  "patches": [ { "name": "FIELD", "old": ["line", "line"], "new": ["line"], "count": 1 } ] }
```
-/

open Lean Scripts.Flip Scripts.Flip.Round Scripts.Flip.Report

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
  -d, --dry         check the anchors and print the sites; do not build
  -V, --version     print the version and exit
  -h, --help        print this help and exit

exit status: 0 run complete and file restored, 1 file not restored
identically, 2 usage, spec, git or anchor error."

structure PatchJ where
  name : String
  old : Array String
  new : Array String
  count : Nat := 1

structure Spec where
  item : Nat
  tag : String
  rev : String
  file : String
  target : String := "L4YAML"
  log : String
  msgWidth : Nat := 100
  rounds : Nat := 1
  lib : String := "L4YAML"
  patches : Array PatchJ

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
    return { name, old, new, count }

instance : FromJson Spec where
  fromJson? j := do
    let item ← j.getObjValAs? Nat "item"
    let tag ← j.getObjValAs? String "tag"
    let rev ← j.getObjValAs? String "rev"
    let file ← j.getObjValAs? String "file"
    let target ← getOr j "target" "L4YAML"
    let log ← j.getObjValAs? String "log"
    let msgWidth ← getOr j "msgWidth" 100
    let rounds ← getOr j "rounds" 1
    let lib ← getOr j "lib" "L4YAML"
    let patches ← j.getObjValAs? (Array PatchJ) "patches"
    return { item, tag, rev, file, target, log, msgWidth, rounds, lib, patches }

def PatchJ.toPatch (p : PatchJ) : Patch.Patch :=
  ⟨p.name, "\n".intercalate p.old.toList, "\n".intercalate p.new.toList, p.count⟩

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

/-- One build round: build, save the log, return (exit, sites). -/
def round (root : System.FilePath) (spec : Spec) (lines : Array String) : IO (UInt32 × Array Site) := do
  let o ← IO.Process.output { cmd := "lake", args := #["build", spec.target], cwd := some root }
  let out := o.stdout ++ o.stderr
  let logPath := root / spec.log
  if let some d := logPath.parent then IO.FS.createDirAll d
  IO.FS.writeFile logPath out
  return (o.exitCode, sitesOf out spec.file lines)

def runSpec (o : Opts) : IO UInt32 := do
  let root : System.FilePath := o.root
  let spec ← match ← readSpec o.spec with
    | .ok s => pure s
    | .error e => IO.eprintln s!"scripts-flip: {e}"; return 2
  let rev := o.rev.getD spec.rev
  if ← Scripts.Git.othersDiffer root rev spec.lib spec.file then
    IO.eprintln s!"library files other than {spec.file} differ between {rev} and the working tree; run the probe in a `git worktree` of {rev} instead"
    return 2
  let shown ← match ← Scripts.Git.showAt root rev spec.file with
    | .ok t => pure t
    | .error e => IO.eprintln s!"cannot read {spec.file} at {rev}: {e}"; return 2
  let patches := spec.patches.toList.map PatchJ.toPatch
  let patched ← match Patch.applyAll shown patches with
    | .ok t => pure t
    | .error e => IO.eprintln s!"scripts-flip: {e}"; return 2
  let src := root / spec.file
  let orig ← IO.FS.readBinFile src
  let h0 := Patch.digest orig
  IO.println s!"pricing {spec.file} at {rev} (working tree hash {h0})"
  (← IO.getStdout).flush
  if o.dry then
    IO.println s!"--dry: {patches.length} anchor(s) found exactly as the spec says; nothing written"
    return 0
  let mut lines := splitLines patched
  let mut restoredOk := true
  try
    IO.FS.writeFile src patched
    IO.println s!"flip tree hash {Patch.digest patched.toUTF8}; building {spec.target} …"
    (← IO.getStdout).flush
    let mut r := 1
    let mut allSites : Array Site := #[]
    repeat
      let (code, sites) ← round root spec lines
      if r == 1 then
        IO.println (headline spec.tag code sites)
        for l in ownerLines sites spec.msgWidth do IO.println l
        allSites := sites
      else
        let fresh := sites.filter fun s => !(allSites.any (·.owner == s.owner))
        IO.println s!"round {r}: exit={code} errors={sites.size} new decls={(byOwner fresh).size}"
        for l in ownerLines fresh spec.msgWidth do IO.println l
        allSites := allSites ++ fresh
        if fresh.isEmpty then break
      if r ≥ spec.rounds then break
      lines := sorryBodies lines sites
      IO.FS.writeFile src ("\n".intercalate lines.toList ++ "\n")
      r := r + 1
    if spec.rounds > 1 then
      IO.println s!"fixpoint after {r} round(s): errors={allSites.size} decls={(byOwner allSites).size}"
    IO.println s!"FLOOR: one build of `{spec.target}` per round; guard modules behind it unmeasured."
  finally
    if o.keep then
      let now ← IO.FS.readBinFile src
      IO.println s!"--keep: patched copy of {rev}:{spec.file} left in place (hash {Patch.digest now}; working tree was {h0})"
    else
      IO.FS.writeBinFile src orig
      let now ← IO.FS.readBinFile src
      let same := now == orig
      IO.println s!"restored hash {Patch.digest now} (orig {h0}) identical={same}"
      restoredOk := same
  return if restoredOk then 0 else 1

end Scripts.FlipMain

open Scripts.FlipMain in
def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .help => IO.println usage; return (if args.isEmpty then 2 else 0)
  | .version => IO.println version; return 0
  | .bad m => IO.eprintln s!"scripts-flip: {m}\n{usage}"; return 2
  | .run o => runSpec o
