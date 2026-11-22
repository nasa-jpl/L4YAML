module

public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
public meta import L4YAML.Scanner.Scanner
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The explicit entry's compact slots compose (DOCS item 51)

`[187] c-l-block-map-explicit-key` and `[197] l-block-map-explicit-value`
both take `[185] s-l+block-indented`, compact alternatives included — so
`? - a` (the KEY slot) and `? a⏎: - w` (the VALUE slot) are grammatical
where the implicit `:`'s `s-l+block-node` slot is not (`k: - a`, refused by
item 48).  Item 51 gives the accumulation the ONE `[188]` entry these inputs
are: the `?` producer's route rides the pending (`h_expl`), the key park
derives its value pack from it (`h_vpack`), the landed `:` at the key's own
column parks the value slot (`h_vslot`), and the same-line `-`/`?`/`:`
fills the compact alternatives.

The runtime's share is the `[197]` COLUMN discrimination: the `:` is the
pending `?`'s value line only AT `explicitKeyCol` — s-indent(n) is exact.
A keyless `:` at any other live column is an ordinary implicit `:` (it
stamps, so a same-line collection there is refused), and a DEEPER entry —
keyed or empty-key — keeps the `?` alive (spec 8.19).

§1 pins the compact fills (all ACCEPT).  §2 pins the column discrimination:
two former over-acceptances refused, one former over-refusal accepted, and
the preserved boundaries on both sides. -/

namespace L4YAML.Tests.Guards.ScannerExplicitValueCompose

open L4YAML L4YAML.Scanner

private def scanAccepts (input : String) : Bool :=
  match Scanner.scan input with | .ok _ => true | .error _ => false

/-- Both pipelines reject with the SAME error. -/
private def rejectsAlike (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error e₁, .error e₂ => toString (repr e₁) == toString (repr e₂)
  | _, _ => false

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

/-! ## §1  The compact fills of the two explicit slots -/

-- The KEY slot: `'?' s-l+block-indented(n,block-out)`.
#guard emits "? - a\n"
  ["+STR", "+DOC", "+MAP", "+SEQ", "=VAL :a", "-SEQ", "=VAL :", "-MAP",
   "-DOC", "-STR"]
#guard emits "? - a\n  - b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "=VAL :",
   "-MAP", "-DOC", "-STR"]
#guard emits "? ? b\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :b", "=VAL :", "-MAP", "=VAL :",
   "-MAP", "-DOC", "-STR"]
#guard emits "? : v\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :", "=VAL :v", "-MAP", "=VAL :",
   "-MAP", "-DOC", "-STR"]

-- The VALUE slot: `s-indent(n) ':' s-l+block-indented(n,block-out)`, with
-- an `e-node` key (`?⏎: - w`), a scalar key, and each compact alternative.
#guard emits "?\n: - w\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "+SEQ", "=VAL :w", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard emits "? a\n: - w\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "=VAL :w", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard emits "? a\n: - - w\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "+SEQ", "=VAL :w", "-SEQ",
   "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "? a\n: ? b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "=VAL :", "-MAP",
   "-MAP", "-DOC", "-STR"]
#guard emits "? a\n: : v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :", "=VAL :v", "-MAP",
   "-MAP", "-DOC", "-STR"]
#guard emits "? a\n: b: c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "=VAL :c", "-MAP",
   "-MAP", "-DOC", "-STR"]

-- Nested: the `?` at the entry's index pays the same fields.
#guard emits "k:\n  ? a\n  : - w\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+SEQ", "=VAL :w",
   "-SEQ", "-MAP", "-MAP", "-DOC", "-STR"]

-- The mapping continues past the entry: two explicit siblings.
#guard emits "? a\n: - w\n? b\n: - x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "=VAL :w", "-SEQ", "=VAL :b",
   "+SEQ", "=VAL :x", "-SEQ", "-MAP", "-DOC", "-STR"]

/-! ## §2  The `[197]` column discrimination -/

-- A dedented `:` is NOT the `?`'s value line — it is an implicit `:` at the
-- outer level, it stamps, and its same-line collection is refused (was
-- ACCEPTED end-to-end before item 51).
#guard !scanAccepts "k:\n  ? a\n: - w\n" && rejectsAlike "k:\n  ? a\n: - w\n"
-- …while its scalar sibling stays: `: v` at the root is `[189]`'s
-- empty-key entry, and the `? a` closed as a key-only entry.
#guard emits "k:\n  ? a\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :", "-MAP",
   "=VAL :", "=VAL :v", "-MAP", "-DOC", "-STR"]

-- A DEEPER empty-key `:` is inside the key's content, not the value line:
-- it stamps (same-line collection refused — was ACCEPTED before item 51)…
#guard !scanAccepts "? earth: blue\n  : - w\n" && rejectsAlike "? earth: blue\n  : - w\n"
-- …and the pending `?` SURVIVES it, so the col-0 value line still lands —
-- with its compact value (was REFUSED before item 51).
#guard emits "? earth: blue\n  : x\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :earth", "=VAL :blue", "=VAL :",
   "=VAL :x", "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]

-- Spec 8.19's own example, unchanged on both sides of the edit.
#guard emits "? earth: blue\n: moon: white\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :earth", "=VAL :blue", "-MAP",
   "+MAP", "=VAL :moon", "=VAL :white", "-MAP", "-MAP", "-DOC", "-STR"]

-- The misindented value lines stay refused ([197] is exact)…
#guard !scanAccepts "? a\n : v\n" && rejectsAlike "? a\n : v\n"
#guard !scanAccepts "? a\n  : v\n" && rejectsAlike "? a\n  : v\n"
#guard !scanAccepts "k:\n  ? a\n   : v\n" && rejectsAlike "k:\n  ? a\n   : v\n"
-- …the implicit stamps stay (item 48's families)…
#guard !scanAccepts ": - a\n" && rejectsAlike ": - a\n"
#guard !scanAccepts "k: - a\n" && rejectsAlike "k: - a\n"
-- …and a property run before the compact still refuses (`[200]` puts
-- `s-l-comments` between properties and a collection).
#guard !scanAccepts "? a\n: &x - w\n" && rejectsAlike "? a\n: &x - w\n"
-- The props-headed VALUE itself is fine — only the collection is not.
#guard emits "? a\n: &x w\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL &x :w", "-MAP", "-DOC", "-STR"]

end L4YAML.Tests.Guards.ScannerExplicitValueCompose

end Blanket
