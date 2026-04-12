/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Key Theorem & Key Function Attributes

Custom attributes for marking architecturally significant definitions
and capstone theorems in L4YAML. These form the two sides of a
bipartite dependency graph:

- **`@[key_function]`** — marks a function/definition as architecturally
  significant (e.g., `scanNextToken`, `parseNode`, `advance`).
- **`@[key_theorem]`** — marks a theorem as a capstone result worth
  documenting (e.g., `advance_offset_lt`, `parseYaml_pipeline`).

Together they support:
1. **Guided bipartite search**: find all key theorems about key functions
2. **Coverage analysis**: identify key functions lacking key theorem coverage
3. **Functorial chain discovery**: find parallel function→function and
   theorem→theorem dependency chains

## Usage

```lean
-- Functions
@[key_function "scanner" "Top-level scanner entry point"]
def scan ...

@[key_function "Fundamental single-character advance"]
def ScannerState.advance ...

-- Theorems
@[key_theorem "progress" "Scanner advance strictly increases offset"]
theorem advance_offset_lt ...

@[key_theorem "End-to-end scanner-parser pipeline composition"]
theorem parseYaml_pipeline ...
```

## Commands

- `#key_theorems`  — Lists all `@[key_theorem]`-tagged declarations.
- `#key_functions` — Lists all `@[key_function]`-tagged declarations.
- `#key_coverage`  — Cross-reference: which key functions have/lack key theorem coverage.
-/

namespace L4YAML

open Lean

/-! ## Shared metadata structure -/

/-- Metadata for a key annotation (`@[key_theorem]` or `@[key_function]`). -/
structure KeyAnnotation where
  /-- Optional category for grouping (e.g., "pipeline", "progress", "scanner"). -/
  category : Option String := none
  /-- One-line description of the declaration's significance. -/
  description : Option String := none
  deriving Inhabited, BEq, Hashable

namespace KeyAnnotation

protected def toString (ref : KeyAnnotation) : String :=
  match ref.category, ref.description with
  | some cat, some desc => s!"[{cat}] {desc}"
  | none,    some desc => desc
  | some cat, none     => s!"[{cat}]"
  | none,    none      => "(no description)"

instance : ToString KeyAnnotation := ⟨KeyAnnotation.toString⟩

end KeyAnnotation

/-- Parse the common syntax `(str)? (str)?` into a `KeyAnnotation`. -/
def parseKeyAnnotation (stx : Syntax) (argIdx1 argIdx2 : Nat) : KeyAnnotation :=
  let arg1 := stx[argIdx1]
  let arg2 := stx[argIdx2]
  if arg1.isNone then
    {}
  else if arg2.isNone then
    { description := arg1[0].isStrLit? }
  else
    { category := arg1[0].isStrLit?, description := arg2[0].isStrLit? }

-- Keep backward compat type alias
abbrev KeyTheoremRef := KeyAnnotation

/-! ## @[key_theorem] -/

initialize keyTheoremExt :
    SimplePersistentEnvExtension (Name × KeyAnnotation) (NameMap KeyAnnotation) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun map (name, ref) => map.insert name ref
    addImportedFn := fun arrays =>
      arrays.foldl (init := Std.TreeMap.empty) fun map arr =>
        arr.foldl (init := map) fun m (name, ref) => m.insert name ref
  }

def getKeyTheoremRef (env : Environment) (declName : Name) : Option KeyAnnotation :=
  (keyTheoremExt.getState env).find? declName

def isKeyTheorem (env : Environment) (declName : Name) : Bool :=
  (keyTheoremExt.getState env).contains declName

def getAllKeyTheorems (env : Environment) : Array (Name × KeyAnnotation) :=
  (keyTheoremExt.getState env).toList.toArray

syntax (name := key_theorem) "key_theorem" (str)? (str)? : attr

initialize registerBuiltinAttribute {
  name := `key_theorem
  descr := "Mark a theorem as a key/capstone theorem for documentation and visualization.\n\
            Usage: @[key_theorem], @[key_theorem \"desc\"], or @[key_theorem \"category\" \"desc\"]"
  applicationTime := .afterTypeChecking
  add := fun declName stx _kind => do
    let ref := parseKeyAnnotation stx 1 2
    modifyEnv fun env => keyTheoremExt.addEntry env (declName, ref)
}

/-! ## @[key_function] -/

initialize keyFunctionExt :
    SimplePersistentEnvExtension (Name × KeyAnnotation) (NameMap KeyAnnotation) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun map (name, ref) => map.insert name ref
    addImportedFn := fun arrays =>
      arrays.foldl (init := Std.TreeMap.empty) fun map arr =>
        arr.foldl (init := map) fun m (name, ref) => m.insert name ref
  }

def getKeyFunctionRef (env : Environment) (declName : Name) : Option KeyAnnotation :=
  (keyFunctionExt.getState env).find? declName

def isKeyFunction (env : Environment) (declName : Name) : Bool :=
  (keyFunctionExt.getState env).contains declName

def getAllKeyFunctions (env : Environment) : Array (Name × KeyAnnotation) :=
  (keyFunctionExt.getState env).toList.toArray

syntax (name := key_function) "key_function" (str)? (str)? : attr

initialize registerBuiltinAttribute {
  name := `key_function
  descr := "Mark a function/definition as architecturally significant.\n\
            Usage: @[key_function], @[key_function \"desc\"], or @[key_function \"category\" \"desc\"]"
  applicationTime := .afterTypeChecking
  add := fun declName stx _kind => do
    let ref := parseKeyAnnotation stx 1 2
    modifyEnv fun env => keyFunctionExt.addEntry env (declName, ref)
}

/-! ## Commands -/

open Lean.Elab.Command in
elab "#key_theorems" : command => do
  let env ← getEnv
  let entries := getAllKeyTheorems env
  if entries.isEmpty then
    logInfo "No @[key_theorem] declarations found."
    return
  let mut msgs : Array MessageData := #[]
  let sorted := entries.qsort fun (a, _) (b, _) => a.toString < b.toString
  for (name, ref) in sorted do
    msgs := msgs.push m!"  {name} — {ref.toString}"
  logInfo (MessageData.joinSep msgs.toList "\n")

open Lean.Elab.Command in
elab "#key_functions" : command => do
  let env ← getEnv
  let entries := getAllKeyFunctions env
  if entries.isEmpty then
    logInfo "No @[key_function] declarations found."
    return
  let mut msgs : Array MessageData := #[]
  let sorted := entries.qsort fun (a, _) (b, _) => a.toString < b.toString
  for (name, ref) in sorted do
    msgs := msgs.push m!"  {name} — {ref.toString}"
  logInfo (MessageData.joinSep msgs.toList "\n")

open Lean.Elab.Command in
/-- `#key_coverage` cross-references key functions and key theorems,
    reporting which key functions have theorem coverage and which don't. -/
elab "#key_coverage" : command => do
  let env ← getEnv
  let keyFns := getAllKeyFunctions env
  let keyThms := getAllKeyTheorems env
  if keyFns.isEmpty then
    logInfo "No @[key_function] declarations found. Tag functions with @[key_function]."
    return
  let mut covered : Array MessageData := #[]
  let mut uncovered : Array MessageData := #[]
  for (fn, fnRef) in keyFns do
    -- Find key theorems whose type mentions this function
    let mut thmNames : Array Name := #[]
    for (thm, _) in keyThms do
      match env.find? thm with
      | some (.thmInfo v) =>
        let typeConsts := v.type.getUsedConstantsAsSet
        if typeConsts.contains fn then
          thmNames := thmNames.push thm
      | _ => pure ()
    if thmNames.isEmpty then
      uncovered := uncovered.push m!"  ✗ {fn} — {fnRef.toString}"
    else
      let thmList := ", ".intercalate (thmNames.toList.map Name.toString)
      covered := covered.push m!"  ✓ {fn} — {thmList}"
  logInfo m!"Key Function Coverage ({covered.size}/{keyFns.size} covered)\n\
             \nCovered:\n{MessageData.joinSep covered.toList "\n"}\
             \n\nUncovered:\n{MessageData.joinSep uncovered.toList "\n"}"

end L4YAML
