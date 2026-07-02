import L4YAML.Output.Events

/-!
# l4yaml-event — test-suite event stream emitter

Reads a YAML stream from stdin and writes the
[yaml-test-suite](https://github.com/yaml/yaml-test-suite) event notation to
stdout.  On a scan/parse error it writes the error to stderr and exits `1`,
matching the convention used by the other processors in
[yaml-runtimes](https://github.com/yaml/yaml-runtimes).
-/

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match L4YAML.Events.streamToEvents input with
  | .ok events =>
    IO.print events
    return 0
  | .error e =>
    IO.eprintln (toString e)
    return 1
