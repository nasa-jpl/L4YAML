module

public import L4YAML.Scanner.Scanner
public import L4YAML.Parser.Composition
public meta import L4YAML.Scanner.Scanner
public meta import L4YAML.Parser.Composition

/-! # Rule-2 exhibit: `:` glued to a flow collection value after a non-JSON key

Spec `[147] c-ns-flow-map-separate-value ::= ":" (s-separate(n,c) ns-flow-node(n,c) | e-node)`
requires `s-separate` between the `:` and a present value; the separator-free form is
`[149] c-ns-flow-map-adjacent-value`, reachable only through
`[148] c-ns-flow-map-json-key-entry` (a JSON-like key).  With `[66] s-separate-in-line`
narrowed to col 0 the Surface derivation of `{a:[1]}` has no arm: `a` is a yaml key, so
`[147]` is the only entry, and nothing non-empty separates `:` from `[`.

The scanner used to accept these (`isValueCandidate`'s `[147]` branch takes a flow
indicator after `:` as the value indicator and then scans the collection with no
separator).  `scanValueValidate` / `scanValueValidateIx` now refuse them
(`flowGluedCollectionValue`, error `unseparatedValue`); the JSON-key shapes stay accepted.
`[148]`/`[149]` themselves are not yet in `L4YAML/Surface/Node.lean` — companion gap. -/

namespace L4YAML.Tests.Guards.FlowGluedColonExhibit

open L4YAML

def accepts (s : String) : Bool := (TokenParser.parseYaml s).isOk

-- Refused: yaml key (plain, empty, or explicit), `:` glued to `[`/`{` — [147] needs s-separate.
#guard accepts "{a:[1]}" = false
#guard accepts "[a:[1]]" = false
#guard accepts "{a:{b: c}}" = false
#guard accepts "[a:{b: c}]" = false
#guard accepts "{a:[]}" = false
#guard accepts "{a:{}}" = false
#guard accepts "{a :[1]}" = false
#guard accepts "{:[1]}" = false
#guard accepts "[:[1]]" = false
#guard accepts "{? a :[1]}" = false
#guard accepts "[? a :[1]]" = false

-- Accepted: JSON-like key, adjacent value ([148]/[149]) — spec-valid, no Surface arm yet.
#guard accepts "{\"a\":b}" = true
#guard accepts "{\"a\":[1]}" = true
#guard accepts "{'a':{b: c}}" = true
#guard accepts "{[a]:[1]}" = true

-- Controls: separated value; `a:b` is one plain scalar (`:` followed by ns-plain-safe).
#guard accepts "{a: [1]}" = true
#guard accepts "{a:b}" = true
#guard accepts "{a:\"x\"}" = true
#guard accepts "a: [1]" = true

/-- The scalar tokens of `scan`, in order. -/
def scalars (s : String) : List (String × ScalarStyle) :=
  match L4YAML.Scanner.scan s with
  | .ok toks => toks.toList.filterMap fun t => match t.val with
      | .scalar c st => some (c, st)
      | _ => none
  | .error _ => []

-- The other glued indicators `" ' & ! *` never reach the value validator: in flow context
-- `:` followed by them continues the plain scalar (`ns-plain-safe(c)` excludes only `[ ] { } ,`),
-- so there is nothing to refuse — the key absorbs them.  `[`/`{` are the only glued shapes.
#guard scalars "{a:\"x\"}" = [("a:\"x\"", .plain)]
#guard scalars "{a:'x'}" = [("a:'x'", .plain)]
#guard scalars "{a:&x b}" = [("a:&x b", .plain)]
#guard scalars "{a:!t b}" = [("a:!t b", .plain)]
#guard scalars "{a:*x}" = [("a:*x", .plain)]
#guard scalars "[a:*x]" = [("a:*x", .plain)]
#guard scalars "a:[1]" = [("a:[1]", .plain)]
-- In block context the same glued `:` after a JSON key is already refused (§8.2.2).
#guard accepts "\"a\":[1]" = false


/-! ## B3 ε-arm probes (2026-10-24): what parks glued to a flow `:` or `?`

`SSeparateLines_at_interior`'s ε arm (`sp_prep = sp_scan`, col > 0) is routed per frame
tail.  Before refuting the `.colon false` / `.question` arms we probed what the scanner
does when the character after `:`/`?` is content and the key was NOT JSON-like: either
the `:` is swallowed into the plain scalar (`ns-plain-safe(flow)` admits `" ' & ! *`),
or the input is refused (`[`/`{` by `[147]`, `?` glued by `isKeyCandidate`).  No new
scanner/grammar disagreement; the arms are scanner-unreachable. -/

-- A space BEFORE the `:` does not change the reading: still one plain scalar.
#guard scalars "{a :\"x\"}" = [("a :\"x\"", .plain)]
#guard scalars "{a :'x'}" = [("a :'x'", .plain)]
#guard scalars "{a :&x b}" = [("a :&x b", .plain)]
#guard scalars "{a :*x}" = [("a :*x", .plain)]
#guard scalars "{a :!t b}" = [("a :!t b", .plain)]
#guard scalars "{a :b}" = [("a :b", .plain)]
#guard scalars "[a :\"x\"]" = [("a :\"x\"", .plain)]
#guard scalars "[:a]" = [(":a", .plain)]
-- `?` glued to content is a plain scalar (`?&x a`, `?"a"`), or refused before `[`.
#guard scalars "{?&x a: b}" = [("?&x a", .plain), ("b", .plain)]
#guard scalars "{?\"a\": b}" = [("?\"a\"", .plain), ("b", .plain)]
#guard accepts "[?[a]]" = false
-- JSON key, white before the `:` (`[155] s-separate-in-line?`): adjacent value, accepted.
#guard accepts "{\"a\" :\"x\"}" = true
#guard scalars "{\"a\" :\"x\"}" = [("a", .doubleQuoted), ("x", .doubleQuoted)]

/-! ### Recorded looseness (not fixed here): a BREAK between a JSON key and its `:`

Spec `[148]`/`[155]` allow only `s-separate-in-line?` between `c-flow-json-node(0,flow-key)`
and the `:`, so `{"a"⏎ :b}` is spec-invalid.  The scanner accepts it, and the Surface
grammar derives it because `SFlowMapEntry.jsonKeyAdjacentValue` (#90) takes
`GOpt (SSeparate n c)` there — scanner and grammar agree with each other and are both
looser than `[155]`.  The sequence twin is refused ("invalid implicit key"). -/
#guard accepts "{\"a\"\n :b}" = true
#guard scalars "{\"a\"\n :b}" = [("a", .doubleQuoted), ("b", .plain)]
#guard accepts "[\"a\"\n :b]" = false

/-! ### B3 probe 2 — explicit (`?`) entries with a JSON key: the scanner refuses a glued
    `:` value there (stricter than [149], conservative), accepts the separated form.  The
    `.colon true` ε arm after `?`-key is therefore scanner-unreachable in both collections.
    Sequence pairs with a JSON key accept the glued value ([153]/[155] via `[149]`). -/
#guard accepts "{? \"a\":b}" = false
#guard accepts "[? \"a\":b]" = false
#guard accepts "{? \"a\" :b}" = false
#guard accepts "[? \"a\" :b]" = false
#guard accepts "[? [a]:b]" = false
#guard accepts "[? \"a\"\n :b]" = false
#guard scalars "{? \"a\" : b}" = [("a", .doubleQuoted), ("b", .plain)]
#guard scalars "[? \"a\" : b]" = [("a", .doubleQuoted), ("b", .plain)]
#guard scalars "{? a :b}" = [("a :b", .plain)]
#guard scalars "[\"a\":b]" = [("a", .doubleQuoted), ("b", .plain)]
#guard scalars "[\"a\" :b]" = [("a", .doubleQuoted), ("b", .plain)]

/-! ### B3 probe 3 — multi-line quoted implicit keys in a flow SEQUENCE: the scanner accepts
them, the grammar has no derivation: `[153]→[155] c-s-implicit-json-key(flow-key)` reads the
key as `c-flow-json-node(0,flow-key)`, one line.  The map side (`[148]`, same restriction) is
read by `SFlowMapEntry.jsonKeyAdjacentValue` at `SCFlowJsonNode n c` — a pre-existing leniency
shared with `pairValue`.  Scanner ← gap, recorded here, not fixed in B3. -/
#guard accepts "[\"a\nb\":c]" = true
#guard accepts "['a\nb':c]" = true
#guard accepts "[\"a\nb\": c]" = true
#guard accepts "{\"a\nb\":c}" = true
-- The other multi-line seq-key shapes ARE refused ("invalid implicit key").
#guard accepts "[\"a\"\n:b]" = false
#guard accepts "[[a\n]:b]" = false
#guard accepts "[a\nb: c]" = false

end L4YAML.Tests.Guards.FlowGluedColonExhibit
