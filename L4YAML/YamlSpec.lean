/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# YAML 1.2.2 Spec Attribute

Custom attribute `@[yaml_spec]` for linking Lean definitions to the
YAML 1.2.2 specification sections and production rules.

## Usage

```lean
-- Link to a spec section only
@[yaml_spec "5.1"]
def isPrintable ...

-- Link to a spec section and production rule
@[yaml_spec "5.1" 1 "c-printable"]
def isPrintable ...

-- Multiple spec references on the same definition
@[yaml_spec "5.4" 24 "b-line-feed"]
@[yaml_spec "5.4" 26 "b-char"]
def isLineBreak ...
```

## Commands

- `#yaml_spec_coverage` — Lists all `@[yaml_spec]`-tagged definitions.
-/

namespace L4YAML

open Lean

/-- A reference to a YAML 1.2.2 specification element. -/
structure YamlSpecRef where
  /-- Spec section number, e.g., `"5.1"` for §5.1 Character Set. -/
  specSection : String
  /-- Production rule number from the YAML 1.2.2 grammar, e.g., `1` for [1] c-printable. -/
  rule : Option Nat := none
  /-- Production rule name, e.g., `"c-printable"`. -/
  name : Option String := none
  deriving Inhabited, BEq, Hashable

namespace YamlSpecRef

/-- Generate a URL to the production rule in the YAML 1.2.2 spec.
    Strips parameters from the name for the URL anchor, e.g.,
    `s-indent(n)` → `https://yaml.org/spec/1.2.2/#rule-s-indent`. -/
def ruleUrl (ref : YamlSpecRef) : Option String :=
  ref.name.map fun n =>
    let base := n.takeWhile (· ≠ '(')
    s!"https://yaml.org/spec/1.2.2/#rule-{base}"

/-- Pretty-print the reference, e.g., `[1] c-printable (§5.1)`. -/
protected def toString (ref : YamlSpecRef) : String :=
  let prod := match ref.rule, ref.name with
    | some r, some n => s!"[{r}] {n} "
    | some r, none   => s!"[{r}] "
    | none,  some n  => s!"{n} "
    | none,  none    => ""
  s!"{prod}(§{ref.specSection})"

instance : ToString YamlSpecRef := ⟨YamlSpecRef.toString⟩

end YamlSpecRef

/-- Add an entry to the yaml spec map, accumulating refs for the same declaration. -/
def addSpecEntry
    (map : NameMap (Array YamlSpecRef))
    (entry : Name × YamlSpecRef) : NameMap (Array YamlSpecRef) :=
  let (name, ref) := entry
  map.insert name (((map.find? name).getD #[]).push ref)

/-- Environment extension mapping declaration names to their YAML spec references.
    Supports multiple `@[yaml_spec]` annotations on the same declaration. -/
initialize yamlSpecExt :
    SimplePersistentEnvExtension (Name × YamlSpecRef) (NameMap (Array YamlSpecRef)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addSpecEntry
    addImportedFn := fun arrays =>
      arrays.foldl (init := Std.TreeMap.empty) fun map arr =>
        arr.foldl (init := map) addSpecEntry
  }

/-- Look up the YAML spec references for a declaration. -/
def getYamlSpecRefs (env : Environment) (declName : Name) : Array YamlSpecRef :=
  ((yamlSpecExt.getState env).find? declName).getD #[]

/-- Get all declarations tagged with `@[yaml_spec]`. -/
def getAllYamlSpecDecls (env : Environment) : Array (Name × Array YamlSpecRef) :=
  (yamlSpecExt.getState env).toList.toArray

/-- Attribute syntax: `@[yaml_spec "§"]` or `@[yaml_spec "§" N "prod-name"]`. -/
syntax (name := yaml_spec) "yaml_spec" str (num str)? : attr

/-- Register the `@[yaml_spec]` attribute handler. -/
initialize registerBuiltinAttribute {
  name := `yaml_spec
  descr := "Link a definition to a YAML 1.2.2 spec section and/or production rule.\n\
            Usage: @[yaml_spec \"section\"] or @[yaml_spec \"section\" rule \"name\"]"
  applicationTime := .afterTypeChecking
  add := fun declName stx _kind => do
    let sect ← match stx[1].isStrLit? with
      | some s => pure s
      | none => throwError
          "@[yaml_spec] expects a string literal for the section, \
           e.g., @[yaml_spec \"5.1\"]"
    let opt := stx[2]
    let ref : YamlSpecRef :=
      if opt.isNone then
        { specSection := sect }
      else
        { specSection := sect, rule := opt[0].isNatLit?, name := opt[1].isStrLit? }
    modifyEnv fun env => yamlSpecExt.addEntry env (declName, ref)
}

open Lean.Elab.Command in
/-- `#yaml_spec_coverage` prints all `@[yaml_spec]`-tagged definitions
    and their spec references, sorted by declaration name. -/
elab "#yaml_spec_coverage" : command => do
  let env ← getEnv
  let entries := getAllYamlSpecDecls env
  if entries.isEmpty then
    logInfo "No @[yaml_spec] declarations found."
    return
  let sorted := entries.qsort fun (a, _) (b, _) => a.toString < b.toString
  let lines := sorted.map fun (name, refs) =>
    let refStrs := refs.map YamlSpecRef.toString
    s!"{name}: {String.intercalate ", " refStrs.toList}"
  logInfo (String.intercalate "\n" lines.toList)

end L4YAML
