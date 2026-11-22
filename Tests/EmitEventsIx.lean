module

public import L4YAML.Output.EventsIx

@[expose] public section Blanket

/-!
# l4yaml-event-ix — test-suite event stream emitter, indexed pipeline

Same contract as `l4yaml-event` (stdin → event notation on stdout, exit `1`
with the error on stderr for a scan/parse failure), but scanning and parsing
through the indexed pipeline.  Used to score the indexed pipeline on the
yaml-test-suite matrix.
-/

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match L4YAML.Events.streamToEventsIx input with
  | .ok events =>
    IO.print events
    return 0
  | .error e =>
    IO.eprintln (toString e)
    return 1

end Blanket
