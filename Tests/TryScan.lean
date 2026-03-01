import Lean4Yaml.Scanner

/-!
# TryScan — scanner token-stream diagnostic

Reads YAML from a file or inline string and prints the token stream
produced by `Lean4Yaml.Scanner.scan`.  Useful for diagnosing scanner
behaviour on individual inputs without running the full test suite.

## Usage

```
lake build tryscan

# From a file:
./.lake/build/bin/tryscan examples/5/example-5.1.yaml

# From an inline string (--str flag):
./.lake/build/bin/tryscan --str 'key: |
  content
'
```

Exits 0 on successful scan, 1 on scan error.
-/

open Lean4Yaml
open Lean4Yaml.Scanner

/-- Scan `input` and print every token (one per line). -/
def showTokens (label : String) (input : String) : IO UInt32 := do
  IO.println s!"--- {label} ---"
  IO.println s!"Input: {repr input}"
  match scan input with
  | .ok tokens =>
    for t in tokens do
      IO.println s!"  {repr t.val}"
    IO.println ""
    return 0
  | .error e =>
    IO.println s!"  ERROR: {e}"
    IO.println ""
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--str", s] =>
    showTokens "(inline)" s
  | ["--str"] =>
    IO.eprintln "tryscan: --str requires a string argument"
    return 2
  | [path] =>
    let content ← IO.FS.readFile path
    showTokens path content
  | paths@(_ :: _ :: _) =>
    -- Multiple file paths: scan each, exit 1 if any fail
    let mut exitCode : UInt32 := 0
    for p in paths do
      if p == "--str" then
        IO.eprintln "tryscan: --str must be the only flag, followed by a single string"
        return 2
      let content ← IO.FS.readFile p
      let rc ← showTokens p content
      if rc != 0 then exitCode := rc
    return exitCode
  | _ =>
    IO.eprintln "Usage: tryscan <file.yaml> [file2.yaml ...]"
    IO.eprintln "       tryscan --str '<yaml string>'"
    return 2
