module

public import L4YAML.Output.Align

@[expose] public section Blanket

/-!
# AlignTest — golden tests for `l4yaml-fmt`

Every `Tests/align/NAME.in.yaml` is formatted with the options in
`NAME.opts` (if present, in `l4yaml-fmt` syntax) and must

* equal `NAME.out.yaml` byte for byte,
* be a fixed point (formatting the output changes nothing), and
* have the same token values and comments as the input (`scanShape`).

```
lake build aligntest && lake exe aligntest [fixture-dir]
```
-/

open L4YAML.Align

namespace AlignTest

def defaultDir : System.FilePath := "Tests" / "align"

def firstDiffLine (a b : String) : Nat := Id.run do
  let la := a.splitOn "\n"
  let lb := b.splitOn "\n"
  let mut i := 0
  for x in la, y in lb do
    if x != y then return i + 1
    i := i + 1
  return i + 1

def readOpts (p : System.FilePath) : IO (List String) := do
  if ← p.pathExists then
    let s ← IO.FS.readFile p
    pure ((s.replace "\n" " ").splitOn " " |>.filter (· ≠ ""))
  else pure []

def runOne (dir : System.FilePath) (name : String) : IO Bool := do
  let inText ← IO.FS.readFile (dir / (name ++ ".in.yaml"))
  let expected ← IO.FS.readFile (dir / (name ++ ".out.yaml"))
  let opts ← readOpts (dir / (name ++ ".opts"))
  match parseArgs opts {} with
  | .error msg =>
    IO.println s!"FAIL {name}: bad .opts: {msg}"; pure false
  | .ok o =>
    match format o.cfg inText with
    | .error err =>
      IO.println s!"FAIL {name}: {err}"; pure false
    | .ok got =>
      let mut ok := true
      if got != expected then
        IO.println s!"FAIL {name}: output differs from {name}.out.yaml (first difference at line {firstDiffLine got expected})"
        ok := false
      match format o.cfg got with
      | .ok again =>
        if again != got then
          IO.println s!"FAIL {name}: not idempotent (first difference at line {firstDiffLine again got})"
          ok := false
      | .error err =>
        IO.println s!"FAIL {name}: second pass refused: {err}"; ok := false
      if scanShape got != scanShape inText then
        IO.println s!"FAIL {name}: token stream or comments changed"; ok := false
      if ok then IO.println s!"PASS {name}"
      pure ok

def main (args : List String) : IO UInt32 := do
  let dir := match args with
    | d :: _ => System.FilePath.mk d
    | [] => defaultDir
  let entries ← dir.readDir
  let names := (entries.filterMap fun e =>
      if e.fileName.endsWith ".in.yaml" then some (String.ofList (e.fileName.toList.take (e.fileName.length - ".in.yaml".length))) else none)
    |>.qsort (· < ·)
  let mut failed := 0
  for n in names do
    unless ← runOne dir n do failed := failed + 1
  IO.println s!"aligntest: {names.size - failed} passed, {failed} failed"
  return if failed == 0 then 0 else 1

end AlignTest

def main (args : List String) : IO UInt32 := AlignTest.main args

end Blanket
