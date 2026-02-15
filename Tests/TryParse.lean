import Lean4Yaml

/-!
# TryParse — single-file YAML parse attempt

Reads a YAML file from the path given as the first argument.
Exits 0 on successful parse, 1 on parse error.
Used by the suite runner with `timeout` for OS-level isolation.
-/

open Lean4Yaml

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let content ← IO.FS.readFile path
    match Parse.parseYaml content with
    | .ok _ => return 0
    | .error e =>
      IO.eprintln e
      return 1
  | _ =>
    IO.eprintln "Usage: tryparse <file.yaml>"
    return 2
