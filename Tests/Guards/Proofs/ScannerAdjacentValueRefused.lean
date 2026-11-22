module

public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx
public meta import L4YAML.Output.EventsIx
public import L4YAML.Scanner.Scanner

public meta import L4YAML.Scanner.Scanner
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The adjacent-value refusal (DOCS item 47)

`scanNextToken_checkAdjacentValue` refuses a `:` that fell through
`isValueCandidate` while the line still belongs to a completed node: the last
real token completes a value and no structural break has re-armed
`simpleKeyAllowed`.  Read as a `[126]` plain head, that `:` would start a
SECOND node in a slot `[194]` gives exactly one — `"a" :b` has no derivation.

The condition's two conjuncts are exactly what the parked accumulation
invariant carries (`StaleNodeTail`), which is what lets the content parks'
`:`-residue arms refute the check's success instead of deferring.  The
simple-key state is deliberately NOT consulted: `:foo: v` at a line start is
a legal `:`-headed plain KEY after a completed entry (yaml-test-suite 2EBW),
and the break that re-arms `simpleKeyAllowed` is what separates it from the
glued families below.

§1 pins the refused family (was scanner-accepted parser-refused — row 19's
over-acceptance, closed by item 47).  §2 pins the preserved neighbours on
every side of the condition's three conjuncts. -/

namespace L4YAML.Tests.Guards.ScannerAdjacentValueRefused

open L4YAML L4YAML.Scanner

private def scanAccepts (input : String) : Bool :=
  match Scanner.scan input with | .ok _ => true | .error _ => false

/-- Both pipelines reject with the SAME error. -/
private def rejectsAlike (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error e₁, .error e₂ => toString (repr e₁) == toString (repr e₂)
  | _, _ => false

/-- Both pipelines accept. -/
private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok _, .ok _ => true
  | _, _ => false

/-! ## §1  The refused family: a glued `:` after a completed node -/

#guard !scanAccepts "\"a\" :b\n" && rejectsAlike "\"a\" :b\n"
#guard !scanAccepts "'a' :b\n" && rejectsAlike "'a' :b\n"
#guard !scanAccepts "\"a\":b\n" && rejectsAlike "\"a\":b\n"
#guard !scanAccepts "'a':b\n" && rejectsAlike "'a':b\n"
#guard !scanAccepts "[1] :b\n" && rejectsAlike "[1] :b\n"
#guard !scanAccepts "[1]:b\n" && rejectsAlike "[1]:b\n"
#guard !scanAccepts "{a: 1} :b\n" && rejectsAlike "{a: 1} :b\n"
#guard !scanAccepts "- [1] :b\n" && rejectsAlike "- [1] :b\n"
#guard !scanAccepts "k:\n  \"a\" :b\n" && rejectsAlike "k:\n  \"a\" :b\n"
#guard !scanAccepts "x: &x a\ny: *x :b\n"
-- …and the multi-line tokens: their interior breaks are the TOKEN's own, so
-- the line after the closing quote/bracket still belongs to the node.
#guard !scanAccepts "\"a\n b\" :c\n" && rejectsAlike "\"a\n b\" :c\n"
#guard !scanAccepts "'a\n b' :c\n"
#guard !scanAccepts "[x,\n y] :c\n" && rejectsAlike "[x,\n y] :c\n"
#guard !scanAccepts "k:\n  [x,\n   y] :c\n"

/-! ## §2  The preserved neighbours, one per conjunct

The `:` that IS the value indicator (blank-followed → `isValueCandidate`,
never reaches the check); the `:`-headed plain at a node-head position (the
last real token does not complete a value); and the line-start `:`-key (a
break re-armed `simpleKeyAllowed`). -/

#guard accepts "\"a\" : b\n"
#guard accepts "\"a\": b\n"
#guard accepts "[1]: b\n"
#guard accepts "\"a\" :\n"
#guard accepts "k: :b\n"
#guard accepts "- :b\n"
#guard accepts ":b\n"
#guard accepts "? :b\n"
#guard accepts "&x :b\n"
#guard accepts "--- :b\n"
#guard accepts "a :b\n"          -- one plain scalar "a :b" — never parks
-- 2EBW's shape: the `:`-headed plain KEY at a line start, after a completed
-- entry — the break re-armed the flag, so the check stays out of the way.
#guard accepts "?foo: safe question mark\n:foo: safe colon\n-foo: safe dash\n"
-- Cross-line glued `:` after a completed node is not THIS check's: the flag
-- is re-armed, so item 47's `!simpleKeyAllowed` is false.  It is §9.2's — a
-- completed ROOT node and content on a later line — and the scanner refuses
-- it there (item 132), at the same position the parser used to.
#guard !scanAccepts "\"a\"\n:b\n" && rejectsAlike "\"a\"\n:b\n"

end L4YAML.Tests.Guards.ScannerAdjacentValueRefused

end Blanket
