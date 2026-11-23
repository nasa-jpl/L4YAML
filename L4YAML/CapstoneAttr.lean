/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Lean
public import Lean.Meta.Native
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
  profile via `Lean.collectAxioms`. It rejects `sorryAx` and every
  nonstandard axiom whose closed Boolean claim cannot be replayed. It
  prints `name: pure|native`; `native` means replay-validated Boolean
  axioms, not authenticated historical origin in `native_decide`.
  `L4YAML/Capstones.lean` pins this profile as well as the tagged set.

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

/-- Axioms admitted without replay. All other dependencies, including private
    and generated-looking names, must pass `replayBooleanAxiom`. -/
def allowedCapstoneAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

initialize registerTraceClass `L4YAML.axiomReplay

/-- Validate the proposition of a nonstandard Boolean axiom independently of
    its name. Lean 4.36's `nativeEqTrue` records an ordinary `Eq Bool e true`
    axiom and an optional source range; neither authenticates tactic origin.

    The claim must be closed and its transitive axiom dependencies must be
    only itself and the standard foundations. In particular a computation
    carrying an arbitrary proof assumption is rejected before evaluation.
    First try a fresh kernel-checked reflexivity proof (with kernel checking
    forced on and a small finite budget). If opacity or cost prevents that,
    replay the closed Boolean
    with Lean's native evaluator, the same additional trust as native_decide.
    The temporary declaration/environment is discarded. Unreadable claims,
    exceptions, non-Boolean axioms and a false computation fail closed.

    A fabricated but independently true Boolean assertion can pass replay;
    this is claim validation, not a declaration-origin certificate. Callers
    must retain raw axiom counts rather than claim that no axiom was declared. -/
def replayBooleanAxiom (name : Name) : CoreM Bool := withCurrHeartbeats do
  try
    let env := (← getEnv).setExporting false
    -- Read the checked kernel environment, as `collectAxioms` does. During
    -- asynchronous/module elaboration, the public elaborator view can omit
    -- generated axioms even though the checked proof already depends on them.
    let some (.axiomInfo info) := env.toKernelEnv.find? name | do
      trace[L4YAML.axiomReplay] "unreadable: {name}"
      return false
    if info.isUnsafe then return false
    let .app (.app (.app (.const ``Eq _) (.const ``Bool _)) lhs)
        (.const ``Bool.true _) := info.type | do
      trace[L4YAML.axiomReplay] "not Boolean: {name}: {info.type}"
      return false
    if lhs.hasFVar || lhs.hasMVar || lhs.hasLooseBVars then return false
    let deps ← collectAxioms name
    unless deps.all (fun a => a == name || allowedCapstoneAxioms.contains a) do
      trace[L4YAML.axiomReplay] "dependencies: {name}: {deps}"
      return false
    let proofName ← mkFreshUserName `_l4yamlAxiomReplay
    let decl := Declaration.thmDecl {
      name := proofName
      levelParams := info.levelParams
      type := info.type
      value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) lhs
    }
    let opts := debug.skipKernelTC.set (← getOptions) false
    -- Do not spend the full elaboration budget reducing a large finite test
    -- in the kernel before replaying it with the evaluator that produced it.
    let budget := maxHeartbeats.get opts
    let opts := maxHeartbeats.set opts (if budget == 0 then 2000 else min budget 2000)
    match env.toKernelEnv.addDecl opts decl with
    | .ok _ =>
      trace[L4YAML.axiomReplay] "kernel validated: {name}"
      return true
    | .error _ =>
      trace[L4YAML.axiomReplay] "native fallback: {name}"
      let result ← ((do
        withoutModifyingEnv do
          setEnv env
          withOptions (debug.skipKernelTC.set · false) do
            Meta.nativeEqTrue `l4yaml_axiom_replay lhs : MetaM Meta.NativeEqTrueResult).run' {} {})
      match result with
      | .success _ =>
        trace[L4YAML.axiomReplay] "native validated: {name}"
        return true
      | .notTrue => return false
  catch ex =>
    trace[L4YAML.axiomReplay] "replay exception: {name}: {ex.toMessageData}"
    return false

/-- Per-invocation cache: a shared dependency is replayed once per gate/census.
    It is never reused after an environment or source change. -/
abbrev AxiomReplayM := StateT (NameMap Bool) CoreM

/-- Common admission rule used by the capstone and compiled-environment gates.
    Namespace, private visibility and generated-looking names grant no exemption. -/
def axiomAdmitted (name : Name) : AxiomReplayM Bool := do
  if allowedCapstoneAxioms.contains name then return true
  if let some accepted := (← get).find? name then return accepted
  let accepted ← replayBooleanAxiom name
  modify fun cache => cache.insert name accepted
  return accepted

/-- Unsupported transitive dependencies of a declaration, including assumptions
    outside the declaration's namespace. -/
def unvalidatedAxioms (name : Name) : AxiomReplayM (Array Name) := do
  let axs ← collectAxioms name
  axs.filterM fun a => return !(← axiomAdmitted a)

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
    Hard-fails on `sorryAx` or an unvalidated nonstandard axiom. `native`
    records replay-validated Boolean axioms, not trusted name provenance. -/
elab "#assert_capstone_axioms" : command => do
  let lines ← liftCoreM <| (do
    let env ← getEnv
    let mut lines : Array String := #[]
    for n in capstoneDecls env do
      let axs ← collectAxioms n
      if axs.contains ``sorryAx then
        throwError "capstone {n} depends on sorryAx"
      let bad ← unvalidatedAxioms n
      unless bad.isEmpty do
        throwError "capstone {n} depends on non-allowed axioms: {bad}"
      let native := axs.any (fun a => !allowedCapstoneAxioms.contains a)
      lines := lines.push s!"{n}: {if native then "native" else "pure"}"
    return lines : AxiomReplayM (Array String)).run' {}
  if lines.isEmpty then
    logInfo "No @[capstone] declarations."
  else
    logInfo <| String.intercalate "\n" lines.toList

end L4YAML

end Blanket
