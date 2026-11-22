module

public import L4YAML.Output.JsonIx

@[expose] public section Blanket

/-!
# l4yaml-json-ix — Core-Schema JSON emitter, indexed pipeline

Same contract as `l4yaml-json` (stdin → JSON on stdout, exit `1` with the
error on stderr for a scan/parse failure), but parsing through the indexed
pipeline.  Used to score the indexed pipeline on the yaml-test-suite matrix.
-/

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match L4YAML.Json.streamToJsonIx input with
  | .ok js =>
    IO.println js
    return 0
  | .error e =>
    IO.eprintln (toString e)
    return 1

end Blanket
