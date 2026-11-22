module

public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The multi-line PLAIN value reads at the entry's index (DOCS item 54)

The plain twin of item 53: `collectPlainScalar_handleBlockLineBreak`'s own
under-indent guard (`col < contentIndent → terminate`) is the reading's
justification at any `n ≤ contentIndent` — `handleBlockLineBreak_prod_at` /
`collectPlainScalarLoop_prod_at` / `scanPlainScalar_to_flowNode_at` re-run
the 0-inductions, and the analysis lemma's fold disjunct (now carrying the
plain walk's trailing whites) serves both indented arms.  ZERO runtime
edits: every pin is an ACCEPT pin with the folded event shape. -/

namespace L4YAML.Tests.Guards.ScannerPlainFoldCompose

open L4YAML

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

#guard emits "k:\n  - a\n     b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :a b", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  : a\n     b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :a b", "-MAP",
   "-MAP", "-DOC", "-STR"]
-- The entry-level snoc survives the fold.
#guard emits "k:\n  - a\n     b\n  - c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :a b", "=VAL :c", "-SEQ",
   "-MAP", "-DOC", "-STR"]
-- The folded KEY under an explicit `?`, closed by its value line.
#guard emits "k:\n  ? a\n     b\n  : v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a b", "=VAL :v", "-MAP",
   "-MAP", "-DOC", "-STR"]

end L4YAML.Tests.Guards.ScannerPlainFoldCompose

end Blanket
