module

public import L4YAML.Parser.Composition
public meta import L4YAML.Parser.Composition

/-! # Rule-2 exhibit: `:` glued to a flow value after a non-JSON key

Spec `[147] c-ns-flow-map-separate-value ::= ":" (s-separate(n,c) ns-flow-node(n,c) | e-node)`
requires `s-separate` between the `:` and a present value; the separator-free form is
`[149] c-ns-flow-map-adjacent-value`, reachable only through
`[148] c-ns-flow-map-json-key-entry` (a JSON-like key).  With `[66] s-separate-in-line`
narrowed to col 0 the Surface derivation of `{a:[1]}` has no arm: `a` is a yaml key, so
`[147]` is the only entry, and nothing non-empty separates `:` from `[`.

`parseYaml` accepts the three inputs below anyway — a scanner/grammar disagreement
(recorded, not proved around).  The JSON-key inputs are spec-valid via `[148]`/`[149]`,
which `L4YAML/Surface/Node.lean` does not define; they are listed as the companion gap. -/

namespace L4YAML.Tests.Guards.FlowGluedColonExhibit

open L4YAML

def accepts (s : String) : Bool := (TokenParser.parseYaml s).isOk

-- Spec-invalid under [147] (yaml key, no s-separate after `:`), accepted by the parser.
#guard accepts "{a:[1]}" = true
#guard accepts "[a:[1]]" = true
#guard accepts "{a:{b: c}}" = true

-- Spec-valid via [148]/[149]; no Surface arm (companion grammar-completeness gap).
#guard accepts "{\"a\":b}" = true
#guard accepts "{\"a\":[1]}" = true

-- Controls: separated value, and a plain scalar `a:b` (`:` followed by ns-plain-safe).
#guard accepts "{a: [1]}" = true
#guard accepts "{a:b}" = true

end L4YAML.Tests.Guards.FlowGluedColonExhibit
