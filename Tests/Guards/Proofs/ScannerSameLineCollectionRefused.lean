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

/-! # The same-line collection refusal (DOCS item 48)

`scanBlockEntry`/`scanKey` refuse a block-context `-`/`?`, and
`scanValueValidate` a `:`, whose line still carries one of three facts the
scanner now records: an IMPLICIT `:` (`implicitValueLine`, stamped by
`scanValue` for `[194]`'s value slot, which is `s-l+block-node` and has no
same-line alternative), a parked `[96] c-ns-properties` run (`[200]` puts
`s-l-comments` between a node's properties and its collection), or a `---`
(`[203]`'s line admits one same-line NODE and nothing else).

The EXPLICIT `:`/`?`/`-` predecessors set none of the three: `[185]`, `[192]`
and `[193]` route through `s-l+block-indented`, whose compact alternatives are
exactly the same-line collections the implicit slot lacks — so `? - a`,
`? a⏎: - w` and `- - : a` stay green while `k: - a` dies.  The pending
`?` survives an implicit `:` RESOLVED DEEPER than the mapping's own column
(spec 8.19's `? earth: blue⏎: moon: white`), which is what keeps the explicit
classification honest across compact keys.

§1 pins the three refused families (all were scanner-accepted and
parser-refused — row 19's over-acceptance, closed by item 48; three were
wrongly ACCEPTED end-to-end: `- : - a`, `: : v`, `: &p a: 1`).  §2 pins the
preserved neighbours at every boundary of the three conditions. -/

namespace L4YAML.Tests.Guards.ScannerSameLineCollectionRefused

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

/-! ## §1a  Behind an implicit `:` — the `implicitValueLine` stamp -/

#guard !scanAccepts "k: - a\n" && rejectsAlike "k: - a\n"
#guard !scanAccepts "k: ? a\n" && rejectsAlike "k: ? a\n"
#guard !scanAccepts "k: b: c\n" && rejectsAlike "k: b: c\n"
#guard !scanAccepts "a: b: c\n" && rejectsAlike "a: b: c\n"
#guard !scanAccepts "k: v : w\n" && rejectsAlike "k: v : w\n"
#guard !scanAccepts "k: &a : b\n" && rejectsAlike "k: &a : b\n"
-- The empty-key implicit `:` stamps too — three of these were wrongly
-- ACCEPTED end-to-end before item 48.
#guard !scanAccepts ": - a\n" && rejectsAlike ": - a\n"
#guard !scanAccepts ": ? a\n" && rejectsAlike ": ? a\n"
#guard !scanAccepts ": : v\n" && rejectsAlike ": : v\n"
#guard !scanAccepts "- : - a\n" && rejectsAlike "- : - a\n"
-- …and the stamp travels to an indented line's own implicit `:`.
#guard !scanAccepts "k:\n  a: b: c\n" && rejectsAlike "k:\n  a: b: c\n"

/-! ## §1b  Behind a parked property run — the trailing-token read -/

#guard !scanAccepts "&a - b\n" && rejectsAlike "&a - b\n"
#guard !scanAccepts "!t - b\n" && rejectsAlike "!t - b\n"
#guard !scanAccepts "&a ? b\n" && rejectsAlike "&a ? b\n"
#guard !scanAccepts "&a !t - b\n" && rejectsAlike "&a !t - b\n"
#guard !scanAccepts "k:\n  &p - a\n" && rejectsAlike "k:\n  &p - a\n"

/-! ## §1c  Behind a `---` — the line walk -/

#guard !scanAccepts "--- - a\n" && rejectsAlike "--- - a\n"
#guard !scanAccepts "--- ? a\n" && rejectsAlike "--- ? a\n"
#guard !scanAccepts "--- : a\n" && rejectsAlike "--- : a\n"
#guard !scanAccepts "--- a: b\n" && rejectsAlike "--- a: b\n"
#guard !scanAccepts "--- \"a\" : b\n" && rejectsAlike "--- \"a\" : b\n"
-- The walk crosses the intervening tokens of a same-line node…
#guard !scanAccepts "--- \"a\": b\n" && rejectsAlike "--- \"a\": b\n"
-- …and a property run behind the marker is refused by EITHER read.
#guard !scanAccepts "--- &x - a\n" && rejectsAlike "--- &x - a\n"

/-! ## §2  The preserved neighbours

The EXPLICIT routes (`[185]`/`[192]`/`[193]`) have compact alternatives, so
none of them stamps; a break resets all three reads; and `&a : b` is
`[154]`'s anchored empty key — the `:` never asks the props question
(item 49's legal inhabitant). -/

#guard accepts "? - a\n"
#guard accepts "? a\n: - w\n"
#guard accepts "- - : a\n"
#guard accepts "- ? - a\n"
-- Spec 8.19: the pending `?` survives an implicit `:` inside its own
-- compact key, so the NEXT `:` still classifies explicit.
#guard accepts "? earth: blue\n: moon: white\n"
#guard accepts "? a: 1\n  b: 2\n: - w\n"
-- A break resets all three reads.
#guard accepts "k:\n  - a\n"
#guard accepts "---\n- a\n"
#guard accepts ": a\n: b\n"
-- The `[194]` value slot DOES admit a same-line flow node and plain scalar.
#guard accepts "k: [a, b]\n"
#guard accepts "--- [1]\n"
#guard accepts "--- a\n"
-- The anchored empty key, and the glued `:`-heads (plain content, not a
-- value indicator — item 47's boundary is untouched).
#guard accepts "&a : b\n"
#guard accepts "&x :b\n"
#guard accepts "--- :b\n"
#guard accepts "? :b\n"

end L4YAML.Tests.Guards.ScannerSameLineCollectionRefused

end Blanket
