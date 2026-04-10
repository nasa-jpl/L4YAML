import L4YAML

/-!
# TryDump — parse YAML then dump with configurable style

Reads a YAML file and a JSON configuration file for `DumpConfig`,
parses the YAML, then dumps it using the specified configuration.
Output goes to stdout.

## Usage

```bash
.lake/build/bin/trydump input.yaml config.json
```

## JSON config format

All fields are optional (defaults match `DumpConfig {}`):

```json
{
  "indent": 2,
  "defaultStyle": "block",
  "scalarStyle": "auto",
  "lineWidth": 80,
  "sortKeys": false
}
```

`defaultStyle`: `"block"` | `"flow"` | `"auto"`
`scalarStyle`: `"plain"` | `"doubleQuoted"` | `"singleQuoted"` | `"auto"`

## Exit codes

| Code | Meaning                          |
|------|----------------------------------|
| 0    | Success — dumped YAML to stdout  |
| 1    | YAML parse error                 |
| 2    | JSON config parse/decode error   |
| 3    | Usage error                      |
-/

open L4YAML
open L4YAML.Dump

def main (args : List String) : IO UInt32 := do
  match args with
  | [yamlPath, configPath] =>
    -- Read the JSON config
    let configStr ← IO.FS.readFile configPath
    let cfg ← match Lean.Json.parse configStr with
      | .ok json =>
        match (Lean.FromJson.fromJson? json : Except String DumpConfig) with
        | .ok cfg => pure cfg
        | .error e =>
          IO.eprintln s!"Config decode error: {e}"
          return 2
      | .error e =>
        IO.eprintln s!"JSON parse error: {e}"
        return 2
    -- Parse the YAML
    let yamlStr ← IO.FS.readFile yamlPath
    match TokenParser.parseYaml yamlStr with
    | .ok docs =>
      let output := dumpDocuments docs cfg
      IO.print output
      return 0
    | .error e =>
      IO.eprintln s!"YAML parse error: {e}"
      return 1
  | _ =>
    IO.eprintln "Usage: trydump <input.yaml> <config.json>"
    return 3
