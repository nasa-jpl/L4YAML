module

public import L4YAML.Parser.Composition
public meta import L4YAML.Parser.Composition
public import L4YAML.Proofs.Parser.TokenGrammar
public meta import L4YAML.Proofs.Parser.TokenGrammar

/-! # Rule-2 probes for `TokenGrammar` / `TokenStateOk` against `parseStream`

Each probe records the triple `(parseStream ok, checkTokenGrammar, checkFrom {} (tokenEvents ts))`.
The lemma under test is `parseStream_accepts`: `TokenGrammar ts → TokenStateOk ts →
parseStream ts = .ok _`, so the forbidden outcome is `(false, true, true)` — none
occurs.  Scanner-produced streams agree exactly; the hand-written arrays record the
parser's token-level over-acceptances (`(true, false, _)`), which bound the unproved
soundness direction `parseStream ts = .ok docs → TokenGrammar ts`. -/

namespace L4YAML.Tests.Guards.TokenGrammarProbes

open L4YAML
open L4YAML.Proofs.TokenGrammar

def verdict (ts : Toks) : Bool × Bool × Bool :=
  ((TokenParser.parseStream ts).toOption.isSome, checkTokenGrammar ts,
    L4YAML.Proofs.Serialization.SerializationWellFormed.checkFrom {}
      (L4YAML.Proofs.Serialization.TokenEvents.tokenEvents ts))

/-- Scanner-produced probe; `none` when the scanner itself rejects the text. -/
def scanned (y : String) : Option (Bool × Bool × Bool) :=
  match Scanner.scanFiltered y with
  | .ok ts => some (verdict ts)
  | .error _ => none

/-- Hand-written array; token `k` sits on line `k` so block-collection line checks pass. -/
def mk (l : List YamlToken) : Toks :=
  l.toArray.mapIdx fun i t =>
    { pos := { offset := i, line := i, col := 0 }, val := t,
      endPos := { offset := i, line := i, col := 1 } }

-- Scanner-produced: parser verdict = grammar ∧ state on every probe.
#guard scanned "a: 1" = some (true, true, true)
#guard scanned "- a" = some (true, true, true)
#guard scanned "[a, b]" = some (true, true, true)
#guard scanned "{a: b}" = some (true, true, true)
#guard scanned "&x a" = some (true, true, true)
#guard scanned "&x [*x]" = some (true, true, true)
#guard scanned "--- a" = some (true, true, true)
#guard scanned "%YAML 1.2\n---" = some (true, true, true)
#guard scanned "!!str a" = some (true, true, true)
#guard scanned "? a\n: b" = some (true, true, true)
#guard scanned "a\n--- b\n...\n" = some (true, true, true)
#guard scanned "" = some (true, true, true)
#guard scanned "- a\n- - b\n" = some (true, true, true)
#guard scanned "a:\n  - b\n" = some (true, true, true)
#guard scanned "{\"foo\"\n: bar}" = some (true, true, true)
#guard scanned "[a: b, {c: d}, ]" = some (true, true, true)
#guard scanned "%TAG !e! foo\n--- !e!x" = some (true, true, true)
#guard scanned "a: &x b\nc: *x" = some (true, true, true)
#guard scanned "- &x a\n- *x" = some (true, true, true)
#guard scanned "[&x a, *x]" = some (true, true, true)
#guard scanned "{a: &x b, c: *x}" = some (true, true, true)
#guard scanned "---\n---\n" = some (true, true, true)
#guard scanned "a\n...\n---\nb" = some (true, true, true)
#guard scanned "? a" = some (true, true, true)
#guard scanned "- " = some (true, true, true)
#guard scanned "a: !!int 1" = some (true, true, true)
#guard scanned "&x\n- a" = some (true, true, true)
#guard scanned "&x [a]\n" = some (true, true, true)
#guard scanned "!!map {a: b}" = some (true, true, true)
#guard scanned "{a, b: c, d}" = some (true, true, true)
#guard scanned "[ ]" = some (true, true, true)
#guard scanned "{ }" = some (true, true, true)
#guard scanned "- - - a" = some (true, true, true)
#guard scanned "x: [a, {b: c}]" = some (true, true, true)
-- Undeclared handle: shape fine, state rejects — exactly `undeclaredTagHandle`.
#guard scanned "!e!x" = some (false, true, false)
-- The scanner rejects these before the parser sees them.
#guard scanned "*x" = none
#guard scanned "&a a\n--- *a" = none
#guard scanned "&x a\n---\n&y b\n...\n*y" = none
#guard scanned "[a, , b]" = none
#guard scanned "a: b: c" = none

-- Hand-written arrays.
#guard verdict (mk [.streamStart, .streamEnd]) = (true, true, true)
#guard verdict (mk [.streamStart, .scalar "a" .plain, .streamEnd]) = (true, true, true)
#guard verdict (mk [.streamStart, .tagDirective "!e!" "p", .documentStart, .tag "!e!" "x",
  .streamEnd]) = (true, true, true)
-- State rejections (alias before/outside its anchor's document, undeclared handle).
#guard verdict (mk [.streamStart, .flowSequenceStart, .alias "x", .flowEntry, .anchor "x",
  .scalar "a" .plain, .flowSequenceEnd, .streamEnd]) = (false, true, false)
#guard verdict (mk [.streamStart, .anchor "x", .scalar "a" .plain, .documentStart, .alias "x",
  .streamEnd]) = (false, true, false)
#guard verdict (mk [.streamStart, .tag "!e!" "x", .streamEnd]) = (false, true, false)
#guard verdict (mk [.streamStart, .tagDirective "!e!" "p", .documentStart, .scalar "a" .plain,
  .documentEnd, .tag "!e!" "x", .streamEnd]) = (false, true, false)
-- Shape rejections shared by parser and grammar.
#guard verdict (mk [.streamStart, .scalar "a" .plain, .scalar "b" .plain, .streamEnd])
  = (false, false, true)
#guard verdict (mk [.streamStart, .flowSequenceStart, .scalar "a" .plain, .streamEnd])
  = (false, false, true)
#guard verdict (mk [.scalar "a" .plain, .streamEnd]) = (false, false, true)
#guard verdict (mk [.streamStart, .anchor "a", .anchor "b", .scalar "x" .plain, .streamEnd])
  = (false, false, true)
#guard verdict (mk [.streamStart, .anchor "a", .tag "!" "t", .anchor "b", .scalar "x" .plain,
  .streamEnd]) = (false, false, true)
-- Token-level checks the parser does not make (the scanner does): a duplicate `%YAML` is
-- accepted by both; a `---`-less directive run is accepted by the parser only — `TG.DocStart`
-- is narrowed to spec [209] (S5 slice 2), the scanner refuses it (`directiveWithoutDocument`).
#guard verdict (mk [.streamStart, .versionDirective 1 2, .versionDirective 1 2, .documentStart,
  .streamEnd]) = (true, true, true)
#guard verdict (mk [.streamStart, .versionDirective 1 2, .scalar "a" .plain, .streamEnd])
  = (true, false, true)
-- Verbatim tags (empty handle) and `%TAG` on a builtin handle denote no event.
#guard scanned "!<tag:x> a" = some (true, true, true)
#guard verdict (mk [.streamStart, .tag "" "tag:x", .scalar "a" .plain, .streamEnd])
  = (true, true, true)
#guard verdict (mk [.streamStart, .tagDirective "!" "!x", .documentStart, .tag "!" "a",
  .scalar "v" .plain, .streamEnd]) = (true, true, true)
#guard verdict (mk [.streamStart, .tagDirective "!!" "tag:y,2002:", .documentStart,
  .tag "!!" "str", .scalar "v" .plain, .streamEnd]) = (true, true, true)
-- Parser over-acceptances (outside the grammar, accepted by `parseStream`).
#guard verdict (mk [.streamStart, .scalar "a" .plain]) = (true, false, true)
#guard verdict (mk [.streamStart, .blockEnd]) = (true, false, true)
#guard verdict (mk [.streamStart, .streamEnd, .scalar "a" .plain]) = (true, false, true)
#guard verdict (mk [.streamStart, .blockSequenceStart, .blockEntry, .scalar "a" .plain,
  .streamEnd]) = (true, false, true)
#guard verdict (mk [.streamStart, .anchor "a", .anchor "b", .flowSequenceStart,
  .flowSequenceEnd, .streamEnd]) = (true, false, true)
#guard verdict (mk [.streamStart, .tag "!" "a", .tag "!" "b", .scalar "x" .plain, .streamEnd])
  = (true, false, true)

end L4YAML.Tests.Guards.TokenGrammarProbes
