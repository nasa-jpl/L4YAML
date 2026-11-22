/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Output.Json
public import L4YAML.Parser.IndexedComposition

@[expose] public section Blanket

/-!
# Core-Schema JSON Emitter — indexed-pipeline twin

`streamToJsonIx` is `streamToJson` with the parse swapped from legacy
`TokenParser.parseYaml` to the indexed `TokenParser.Indexed.parseYamlIx`.
It exists so the yaml-test-suite matrix can score the indexed pipeline
against the same `in.json` oracles the legacy pipeline scores 100% on
(DOCS.md § Indexed-pipeline parity gap, plan item 5).  All JSON
serialization (`docsToJson`, schema resolution, escaping) is shared, so
any score difference is attributable to scan/parse alone.
-/

namespace L4YAML.Json

/-- Indexed twin of `streamToJson`: parse `input` through the indexed
    pipeline and produce its Core-Schema JSON, or a scan/parse error. -/
def streamToJsonIx (input : String) : Except ScanError String :=
  match L4YAML.TokenParser.Indexed.parseYamlIx input with
  | .ok docs => .ok (docsToJson docs)
  | .error e => .error e

end L4YAML.Json

end Blanket
