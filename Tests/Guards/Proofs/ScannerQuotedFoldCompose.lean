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

/-! # The multi-line quoted value reads at the entry's index (DOCS item 53)

Since item 45 a multi-line quoted token was a `*Crossed` witness — the
reading renounced at any nonzero index — and the indented arms deferred it.
Item 53 pays the reading: the scanner's own fold guards (the §6.1 tab gate,
the §9.1.2 marker check, the §8.1 under-indent check) refuse every landing
`s-flow-line-prefix(n)` cannot read, so the same loop inductions that build
the 0-readings build the reading at any `n ≤ currentIndent + 1`
(`collectDoubleQuotedLoop_prod_at` / `collectSingleQuotedLoop_prod_at`),
and both indented content arms consume it through the analysis lemma's new
fold disjunct.

The runtime's share: the ESCAPED-break landing (`"x\⏎y"`) had no checks at
all — `[112] s-double-escaped(n)` ends in the same `s-flow-line-prefix(n)`,
so item 53 gives the escaped landing the fold's three checks (on a CONTENT
landing; a blank landing is `l-empty` and is checked by the fold next
iteration).  §1 pins the compositions; §2 the escaped-landing flips and the
preserved boundaries. -/

namespace L4YAML.Tests.Guards.ScannerQuotedFoldCompose

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

/-! ## §1  Multi-line quoted values at indented entries -/

#guard emits "k:\n  - \"x\n    y\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL \"x y", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  - 'a\n   b'\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL 'a b", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  : \"x\n    y\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL \"x y", "-MAP",
   "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  ? \"x\n    y\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL \"x y", "=VAL :", "-MAP",
   "-MAP", "-DOC", "-STR"]
-- The escaped break and the interior empty line fold inside the same token.
#guard emits "k:\n  - \"x\\\n    y\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL \"xy", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  - \"x\n\n    y\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL \"x\\ny", "-SEQ", "-MAP",
   "-DOC", "-STR"]

/-! ## §2  The escaped-break landing clears the fold's floor (runtime flips) -/

-- Under-indented CONTENT landings after `\⏎` are refused (were accepted).
#guard !scanAccepts "k:\n  a: \"x\\\ny\"\n" && rejectsAlike "k:\n  a: \"x\\\ny\"\n"
#guard !scanAccepts "k:\n  a: \"x\\\n y\"\n" && rejectsAlike "k:\n  a: \"x\\\n y\"\n"
#guard !scanAccepts "a: \"x\\\ny\"\n" && rejectsAlike "a: \"x\\\ny\"\n"
-- The tab-in-zone and marker landings refuse like the fold's.
#guard !scanAccepts "k:\n  a: \"x\\\n\t y\"\n" && rejectsAlike "k:\n  a: \"x\\\n\t y\"\n"
#guard !scanAccepts "\"x\\\n--- \"\n" && rejectsAlike "\"x\\\n--- \"\n"
-- Cleared landings stay accepted…
#guard scanAccepts "k:\n  a: \"x\\\n   y\"\n"
#guard scanAccepts "a: \"x\\\n y\"\n"
#guard scanAccepts "\"x\\\ny\"\n"
-- …and BLANK landings are `l-empty`, checked by the fold next iteration.
#guard scanAccepts "k:\n  a: \"x\\\n\n   y\"\n"
#guard scanAccepts "k:\n  a: \"x\\\n \n   y\"\n"
-- The fold's own refusals are unmoved.
#guard !scanAccepts "k:\n  a: \"x\ny\"\n" && rejectsAlike "k:\n  a: \"x\ny\"\n"
#guard !scanAccepts "k:\n  a: \"x\n  y\"\n" && rejectsAlike "k:\n  a: \"x\n  y\"\n"

end L4YAML.Tests.Guards.ScannerQuotedFoldCompose

end Blanket
