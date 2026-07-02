import L4YAML.Output.Json

/-!
# l4yaml-json — Core-Schema JSON emitter

Reads a YAML stream from stdin and writes JSON (one document per line) to stdout,
matching the yaml-test-suite `in.json` oracle.  On a scan/parse error it writes
the error to stderr and exits `1`.
-/

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match L4YAML.Json.streamToJson input with
  | .ok js =>
    IO.println js
    return 0
  | .error e =>
    IO.eprintln (toString e)
    return 1
