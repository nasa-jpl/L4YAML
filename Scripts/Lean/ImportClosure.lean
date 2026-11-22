module

public import Lean.Environment

@[expose] public section Blanket

/-!
# Scripts.Lean.ImportClosure — no orphan modules, off the `.olean` headers

Formerly `scripts/check_import_closure.py`, which parsed `import` lines with a
regex.  Here the import *graph* is read without elaborating anything: each
built module's `.olean` header (`Lean.readModuleData` → `imports`) lists its
imports exactly as the module system resolved them — `public import`, `meta
import`, `import all` and the legacy bare form alike, and never a fenced
docstring example.  No environment is merged: the two obstacles the plan
records (the duplicate equation-lemma error over the Proofs closure, and the
emitter exes each defining a root `main` — `import Tests.EmitJson failed,
environment already contains 'main' from Tests.EmitEvents`, reproduced on this
toolchain) do not arise for header reads.

1. **Library reachability.**  Every `L4YAML/**/*.lean` on disk must be in the
   closure of the `@[default_target]` roots (`roots`: the library plus the
   four emitter exes) over header imports.  The candidate set is the on-disk
   inventory — an orphan has no `.olean` after a default-target build, so a
   header-only inventory could never see it.  Two classes, each a failure:
   *orphan* (not in the closure) and *missing header* (reached, but its
   `.olean` is absent — unbuilt, so unverifiable).  Freshness of the headers
   is Lake's call, not this gate's: `lake run check-import-closure` runs
   `lake build L4YAML l4yaml-event l4yaml-json l4yaml-event-ix l4yaml-json-ix`
   first (a no-op when the traces match), so the headers read are the ones
   the sources produce.  An mtime comparison is *not* that criterion — Lake's
   outputs are content-addressed, so a byte-identical restore (a flip's) leaves
   the source newer than an `.olean` Lake rightly did not rewrite; the first
   draft of this gate flagged `StreamAccum.lean` that way.
2. **Reflections index completeness.**  Every `Tests/Reflections/*.lean` is
   imported by `Tests/Reflections.lean`, read off the index's own text (it is
   not part of the default-target build, so it has no header to read at gate
   time).
-/

namespace Scripts.Lean.ImportClosure

/-- Closure roots: every `@[default_target]` whose root is a module — the
library and the four emitter exes (`lakefile.lean`). -/
def roots : List String :=
  ["L4YAML", "Tests.EmitEvents", "Tests.EmitJson", "Tests.EmitEventsIx", "Tests.EmitJsonIx"]

def oleanDir : String := ".lake/build/lib/lean"

/-- `L4YAML/A/B.lean` → `L4YAML.A.B`. -/
def moduleOf (rel : String) : String :=
  let rel := if rel.endsWith ".lean" then (rel.dropEnd 5).toString else rel
  ".".intercalate (rel.splitOn "/")

/-- `L4YAML.A.B` → `L4YAML/A/B` (append `.lean` or `.olean`). -/
def pathOf (m : String) : String := "/".intercalate (m.splitOn ".")

def isLib (m : String) : Bool := m == "L4YAML" || m.startsWith "L4YAML."

/-- Depth-first closure over `imports`, following only library modules, as
the Python did; `imports m = none` means the header could not be read (the
module is still *seen*, and recorded under `missing`). -/
partial def closure {M : Type → Type} [Monad M] (imports : String → M (Option (Array String)))
    (frontier : List String) (seen missing : Array String := #[])
    : M (Array String × Array String) := do
  match frontier with
  | [] => pure (seen, missing)
  | mod :: rest =>
    if seen.contains mod then closure imports rest seen missing
    else
      let seen := seen.push mod
      match ← imports mod with
      | none => closure imports rest seen (missing.push mod)
      | some imps =>
        let next := imps.toList.filter isLib
        closure imports (next ++ rest) seen missing

/-- `(public )?(meta )?import (all )?NAME` at the start of a line → `NAME`;
fenced code blocks (```` ``` ````) are skipped. -/
def importsOfText (text : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut fenced := false
  for line in text.splitOn "\n" do
    if line.startsWith "```" then fenced := !fenced; continue
    if fenced then continue
    let ws := (line.splitOn " ").filter (· != "")
    let ws := match ws with | "public" :: t => t | t => t
    let ws := match ws with | "meta" :: t => t | t => t
    match ws with
    | "import" :: t =>
      let t := match t with | "all" :: u => u | u => u
      if let some m := t.head? then
        if line.startsWith "public" || line.startsWith "meta" || line.startsWith "import" then
          out := out.push m
    | _ => pure ()
  return out

structure Findings where
  onDisk : Nat
  orphans : Array String        -- source paths
  missing : Array String        -- source or root paths whose header is absent
  unindexed : Array String      -- Tests/Reflections/X.lean paths
  indexed : Nat

def Findings.lines (f : Findings) : Array String := Id.run do
  let mut out : Array String := #[]
  let rootList := ", ".intercalate roots
  for p in f.orphans do
    out := out.push s!"orphan library module (unreachable from any default target — {rootList}): {p}"
  for p in f.missing do
    out := out.push s!"missing header (no .olean — unbuilt, so unverifiable; run `lake build`): {p}"
  for p in f.unindexed do
    out := out.push s!"unindexed reflection (add `import {moduleOf p}` to Tests/Reflections.lean): {p}"
  return out

def Findings.count (f : Findings) : Nat :=
  f.orphans.size + f.missing.size + f.unindexed.size

def Findings.okLine (f : Findings) : String :=
  s!"OK: {f.onDisk} library modules reachable from {roots.length} default targets; Tests/Reflections index complete ({f.indexed} imports)"

#guard moduleOf "L4YAML/Proofs/Production/StreamAccum.lean" == "L4YAML.Proofs.Production.StreamAccum"
#guard moduleOf "L4YAML.lean" == "L4YAML"
#guard pathOf "Tests.EmitEvents" == "Tests/EmitEvents"
#guard isLib "L4YAML" && isLib "L4YAML.Document" && !isLib "L4YAMLX" && !isLib "Tests.EmitEvents"
#guard importsOfText "module\n\npublic import L4YAML.A\nmeta import L4YAML.B\nimport all L4YAML.C\nimport Init\n  import Indented\n```\nimport Fenced\n```\n"
  == #["L4YAML.A", "L4YAML.B", "L4YAML.C", "Init"]

private def graph : List (String × Array String) :=
  [("L4YAML", #["L4YAML.A", "Init"]), ("L4YAML.A", #["L4YAML.B", "Std"]), ("L4YAML.B", #[]),
   ("Tests.EmitEvents", #["L4YAML", "L4YAML.E"]), ("L4YAML.E", #["L4YAML.Missing"]),
   ("L4YAML.Orphan", #["L4YAML"])]
private def imp (m : String) : Id (Option (Array String)) := pure (graph.lookup m)
#guard (closure imp ["L4YAML", "Tests.EmitEvents"] |>.run)
  == (#["L4YAML", "L4YAML.A", "L4YAML.B", "Tests.EmitEvents", "L4YAML.E", "L4YAML.Missing"], #["L4YAML.Missing"])
#guard ((closure imp ["L4YAML"] |>.run).1.contains "L4YAML.Orphan") == false

end Scripts.Lean.ImportClosure
