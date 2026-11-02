/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Lean
public meta import Lean

-- This module's `elab` bodies are `meta` definitions, while the helpers they
-- call are ordinary code that the library also uses at runtime.  A declaration
-- carries one phase and the `meta` modifier cannot be dropped retroactively,
-- so mixed references inside this module need to be permitted explicitly.
set_option compiler.relaxedMetaCheck true

@[expose] public section Blanket

/-!
# Capstone registry: `@[capstone]`, `#capstones`, `#assert_capstone_axioms`

In-repo, declaration-site registry of the blueprint capstones
(`Blueprint/04-capstones.md`). The `theorem` keyword is reserved for
`@[capstone]`-tagged declarations; every other proof uses `lemma`
(see `L4YAML/Init.lean`; enforced by `lake run check-theorem-keyword`).

- `#capstones` prints the tagged set, one fully-qualified name per line
  (pinned by `#guard_msgs` in `L4YAML/Capstones.lean`, so silently
  gaining or losing a capstone fails the build).
- `#assert_capstone_axioms` recomputes every tagged declaration's axiom
  profile via `Lean.collectAxioms` and **fails the build** on any
  `sorryAx`, any project-declared axiom, or any axiom outside the
  allowed kernel set. It prints one `name: pure|native` line per
  capstone (`native` = the proof carries `native_decide` reflected-decide
  leaves), which `L4YAML/Capstones.lean` also pins — so a capstone
  silently acquiring a `native_decide` dependency fails the build too.

The same catalogue is mirrored in prose by `Blueprint/04-capstones.md`
(the primary, per `Blueprint/06-discipline.md` Rule 4) and consumed by
the sibling `L4YAML.FGM` repo's `@[key_theorem]` catalogue.
-/

namespace L4YAML
open Lean

initialize capstoneAttr : TagAttribute ←
  registerTagAttribute `capstone
    "capstone theorem (Blueprint/04-capstones.md): kept under the `theorem` keyword; all other proofs use `lemma`"

/-- All `@[capstone]`-tagged declarations visible in `env` (imported
    modules + current module), sorted for deterministic output.
    `TagAttribute`'s `addImportedFn` is a no-op, so imported entries
    must be read per-module via `getModuleEntries` (as
    `TagAttribute.hasTag` does). -/
def capstoneDecls (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for i in [0:env.header.moduleData.size] do
    out := out ++ capstoneAttr.ext.getModuleEntries env i
  for n in (capstoneAttr.ext.getState env).toList do
    out := out.push n
  return out.qsort Name.quickLt

/-- Kernel axioms a capstone proof may depend on.  `native_decide` adds no
    named axiom: it emits one per-call-site `…_native.native_decide.ax_*`
    leaf, which is `Name.isInternalDetail` and so is filtered out before
    this check — `#assert_capstone_axioms` reads that leaf, not a name
    here, to classify a capstone `native`. -/
def allowedCapstoneAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

open Elab Command in
/-- `#capstones` — list all `@[capstone]`-tagged declarations. -/
elab "#capstones" : command => do
  let names := capstoneDecls (← getEnv)
  if names.isEmpty then
    logInfo "No @[capstone] declarations."
  else
    logInfo <| String.intercalate "\n" (names.toList.map toString)

open Elab Command in
/-- `#assert_capstone_axioms` — recompute every capstone's axiom profile.
    Hard-fails on `sorryAx` or any axiom outside `allowedCapstoneAxioms`;
    otherwise prints one `name: pure|native` line per capstone. -/
elab "#assert_capstone_axioms" : command => do
  let env ← getEnv
  let mut lines : Array String := #[]
  for n in capstoneDecls env do
    let axs ← collectAxioms n
    if axs.contains ``sorryAx then
      throwError "capstone {n} depends on sorryAx"
    let visible := axs.filter (fun a => !a.isInternalDetail)
    let bad := visible.filter (fun a => !allowedCapstoneAxioms.contains a)
    unless bad.isEmpty do
      throwError "capstone {n} depends on non-allowed axioms: {bad}"
    let native := axs.any (·.isInternalDetail)
    lines := lines.push s!"{n}: {if native then "native" else "pure"}"
  if lines.isEmpty then
    logInfo "No @[capstone] declarations."
  else
    logInfo <| String.intercalate "\n" lines.toList

end L4YAML

end Blanket
