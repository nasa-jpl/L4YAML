/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Elab.Declaration
import L4YAML.CapstoneAttr

/-!
# L4YAML.Init — project prelude

Imported (directly or transitively) by every library module. Provides:

- the `lemma` command, a synonym for `theorem` (same macro-expansion
  approach as `Mathlib/Tactic/Lemma.lean`, core-only). Project policy
  (`Blueprint/06-discipline.md`): the `theorem` keyword is reserved for
  the `@[capstone]`-tagged blueprint capstones; **every other proof is
  a `lemma`**. Enforced by `scripts/check-theorem-keyword.sh`.
- the `@[capstone]` attribute machinery, via `L4YAML.CapstoneAttr`.

The `lemma` expander is a *macro* (not a `command_elab`) so that it
also works inside `mutual` blocks: core's `elabMutual` macro-expands
non-`declaration` elements (`expandMutualElement`). The parser priority
sits above the identically-shaped (error-by-default) `lemmaCmd` that
batteries registers, so interactive sessions with `L4YAML_LEANCOPILOT=on`
parse unambiguously.
-/

namespace L4YAML
open Lean

/-- `lemma` means the same as `theorem`. The `theorem` keyword itself is
    reserved for `@[capstone]` declarations (see module docstring). -/
syntax (name := lemmaCmd) (priority := default + 1) declModifiers
  group("lemma " declId ppIndent(declSig) declVal) : command

/-- Expand `lemma` to `theorem` by re-kinding the syntax node — resilient
    against changes to `theorem`'s internal structure. -/
@[macro lemmaCmd] def expandLemma : Macro := fun stx =>
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration

end L4YAML
