import L4YAML

/-!
# TryParse — single-file YAML parse attempt

Reads a YAML file from the path given as the first argument.
Exits 0 on successful parse, 1 on parse error.
Used by the suite runner with `timeout` for OS-level isolation.

An optional second argument selects a limits preset:
  `unlimited` (default) | `default` | `strict` | `permissive` | `safe_tags`
-/

open L4YAML

/-- Map a CLI preset name to `ParserLimits`. -/
def parsePreset (s : String) : Option ParserLimits :=
  match s with
  | "unlimited"  => some ParserLimits.unlimited
  | "default"    => some {}
  | "strict"     => some ParserLimits.strict
  | "permissive" => some ParserLimits.permissive
  | "safe_tags"  => some ParserLimits.safeTagsOnly
  | _ => none

def main (args : List String) : IO UInt32 := do
  let (path, limits) ← match args with
    | [p] => pure (p, none)
    | [p, presetName] =>
      match parsePreset presetName with
      | some lim => pure (p, some lim)
      | none =>
        IO.eprintln s!"Unknown preset '{presetName}'; choose from: unlimited, default, strict, permissive, safe_tags"
        return 2
    | _ =>
      IO.eprintln "Usage: tryparse <file.yaml> [preset]"
      return 2
  let content ← IO.FS.readFile path
  match limits with
  | none =>
    match TokenParser.parseYaml content with
    | .ok _ => return 0
    | .error e => IO.eprintln (toString e); return 1
  | some lim =>
    match parseYamlSafe content lim with
    | .ok _ => return 0
    | .error e => IO.eprintln (toString e); return 1
