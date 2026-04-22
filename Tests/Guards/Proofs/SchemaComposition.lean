import L4YAML.Proofs.Schema.SchemaComposition

namespace L4YAML.Proofs.SchemaComposition

open L4YAML
open L4YAML.Schema

-- resolve ∘ toYaml primitive checks
#guard resolvesTo true (.bool true)
#guard resolvesTo false (.bool false)
#guard resolvesTo () .null
#guard resolvesTo (0 : Nat) (.int 0)
#guard resolvesTo (1 : Nat) (.int 1)
#guard resolvesTo (42 : Nat) (.int 42)
#guard resolvesTo (100 : Nat) (.int 100)
#guard resolvesTo (0 : Int) (.int 0)
#guard resolvesTo (100 : Int) (.int 100)
#guard resolvesTo (-7 : Int) (.int (-7))
#guard resolvesTo (-17 : Int) (.int (-17))
#guard resolvesTo "hello" (.str "hello")
#guard resolvesTo "world" (.str "world")
#guard resolvesTo "foo bar" (.str "foo bar")
#guard resolvesTo "" .null  -- empty string is null per §10.3.2

-- resolve ∘ toYaml option composition
#guard resolvesTo (some true : Option Bool) (.bool true)
#guard resolvesTo (some false : Option Bool) (.bool false)
#guard resolvesTo (some "hello" : Option String) (.str "hello")
#guard resolvesTo (none : Option String) .null
#guard resolvesTo (none : Option Bool) .null

-- fromYaml? ∘ toYaml round-trip checks
#guard schemaRoundTrips true
#guard schemaRoundTrips false
#guard schemaRoundTrips ()
#guard schemaRoundTrips (0 : Nat)
#guard schemaRoundTrips (1 : Nat)
#guard schemaRoundTrips (42 : Nat)
#guard schemaRoundTrips (100 : Nat)
#guard schemaRoundTrips (0 : Int)
#guard schemaRoundTrips (100 : Int)
#guard schemaRoundTrips (-7 : Int)
#guard schemaRoundTrips (-17 : Int)
#guard schemaRoundTrips "hello"
#guard schemaRoundTrips "world"
#guard schemaRoundTrips "foo bar"
#guard schemaRoundTrips (some true : Option Bool)

end L4YAML.Proofs.SchemaComposition
