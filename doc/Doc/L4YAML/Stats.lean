/-
  L4YAML Documentation — Build-time statistics

  Scans `L4YAML/Proofs/` at elaboration time and exposes the resulting
  theorem count and proof-module count as Verso roles, so the front-page
  paragraph always reports the numbers that the source tree actually
  contains.

  Note: Lake does not see the proof sources as dependencies of this
  module, so changes under `L4YAML/Proofs/` do not invalidate the cached
  counts.  Run `lake clean` in `doc/` after proof edits to force a
  refresh.
-/
import Lean
import VersoManual

open Lean Elab
open Verso.Doc.Elab
open Verso.Genre Manual

namespace Doc.L4YAML.Stats

/-- `(theorem-or-lemma count, `.lean` file count)` under `dir`. -/
def scanProofs (dir : System.FilePath) : IO (Nat × Nat) := do
  let files ← System.FilePath.walkDir dir
  let leanFiles := files.filter fun p => p.extension == some "lean"
  let mut thms := 0
  for p in leanFiles do
    let content ← IO.FS.readFile p
    for line in content.splitOn "\n" do
      let t := line.trimAsciiStart
      if t.startsWith "theorem " || t.startsWith "lemma " then
        thms := thms + 1
  return (thms, leanFiles.size)

/-- Locate `L4YAML/Proofs/` relative to whatever working directory
    `lake build` is invoked from. -/
def resolveProofsDir : IO System.FilePath := do
  let cwd ← IO.currentDir
  let candidates := #[
    cwd / ".." / "L4YAML" / "Proofs",
    cwd / "L4YAML" / "Proofs"
  ]
  for c in candidates do
    if ← c.pathExists then return c
  throw (IO.userError s!"scanProofs: cannot find L4YAML/Proofs from {cwd}")

elab "l4yaml_theorem_count" : term => do
  let dir ← resolveProofsDir
  let (thms, _) ← scanProofs dir
  return mkNatLit thms

elab "l4yaml_proof_module_count" : term => do
  let dir ← resolveProofsDir
  let (_, mods) ← scanProofs dir
  return mkNatLit mods

def theoremCount : Nat := l4yaml_theorem_count
def proofModuleCount : Nat := l4yaml_proof_module_count

private def addCommas : List Char → List Char
  | [] => []
  | c :: rest =>
    let tail := addCommas rest
    if rest.length > 0 && rest.length % 3 == 0 then c :: ',' :: tail
    else c :: tail

/-- Format `n` with US-style comma thousands separators (e.g. `2309 ↦ "2,309"`). -/
def formatWithCommas (n : Nat) : String :=
  String.ofList (addCommas (toString n).toList)

def theoremCountStr : String := formatWithCommas theoremCount
def proofModuleCountStr : String := toString proofModuleCount

/-- Inline role: `{numTheorems}[]` expands to the comma-formatted theorem count. -/
@[role]
def numTheorems : RoleExpanderOf Unit
  | (), _ => ``(Verso.Doc.Inline.text Doc.L4YAML.Stats.theoremCountStr)

/-- Inline role: `{numProofModules}[]` expands to the proof-module count. -/
@[role]
def numProofModules : RoleExpanderOf Unit
  | (), _ => ``(Verso.Doc.Inline.text Doc.L4YAML.Stats.proofModuleCountStr)

end Doc.L4YAML.Stats
