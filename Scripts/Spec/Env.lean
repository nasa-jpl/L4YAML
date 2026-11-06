module

public import Lean.Environment
public import Lean.DeclarationRange
public import Lean.PrivateName
public import L4YAML.Spec.YamlSpec
public import Scripts.Lean.DeclRanges

/-!
# `Scripts.Spec.Env` — the `@[yaml_spec]` references a module registered, off its `.olean`

Rule 9 §2: a question about declarations is answered from the environment, not from the
text.  The `yaml_spec` attribute records every reference it is given in `L4YAML.yamlSpecExt`
(`L4YAML/Spec/YamlSpec.lean`), exported to the module's `.olean`; this module reads those
entries back — the declaration each one is attached to and its `YamlSpecRef` — and places
the declaration in its source file through `Lean.declRangeExt` (`Scripts.Lean.DeclRanges`),
so a diagnostic can name `file:line decl`.  Prose, strings, comments and inactive code hold
no entry and are not read.
-/

open Lean

namespace Scripts.Spec.Env

public section

unsafe def readSpecRefsImpl (olean : System.FilePath) : IO (Array (Name × L4YAML.YamlSpecRef)) := do
  let parts ← readModuleDataParts #[olean]
  let some (data, _) := parts[0]? | throw (IO.userError s!"{olean}: no module data")
  match data.entries.find? (·.1 == ``L4YAML.yamlSpecExt) with
  | some (_, es) => return unsafeCast es
  | none => return #[]

/-- The `(declaration, reference)` entries the module `olean` registered with `@[yaml_spec]`,
    in the order the attribute was applied. -/
@[implemented_by readSpecRefsImpl]
opaque readSpecRefs (olean : System.FilePath) : IO (Array (Name × L4YAML.YamlSpecRef))

/-- The declaration the user wrote, not an auxiliary one the elaborator derived from it and
    re-applied the attribute to (`foo._unary` of a well-founded recursion, `foo._unsafe_rec` of a
    `partial def`): a reference is counted once, on the declaration carrying it. -/
def isUserDecl (n : Name) : Bool := !((privateToUserName? n).getD n).isInternal

#guard isUserDecl `A.foo && !isUserDecl `A.foo._unary && !isUserDecl `A.foo._unsafe_rec

/-- The declaration's name as the source spells it (`private` undone). -/
def userName (n : Name) : String := ((privateToUserName? n).getD n).toString (escape := false)

/-- The line the declaration's name is on (`selectionRange`), when the module declares it. -/
def declLine? (rs : Array (Name × DeclarationRanges)) (n : Name) : Option Nat :=
  (rs.find? (·.1 == n)).map (·.2.selectionRange.pos.line)

/-- The module's references in source order: by the owning declaration's line, then by the
    order of application (a declaration's attribute list is read left to right); a reference
    to a declaration of another module (`attribute [yaml_spec …] X` on an imported `X`) sorts
    first, with no line. -/
def ordered (refs : Array (Name × L4YAML.YamlSpecRef)) (rs : Array (Name × DeclarationRanges)) :
    Array (Option Nat × Name × L4YAML.YamlSpecRef) :=
  let withIdx : Array (Option Nat × Nat × Name × L4YAML.YamlSpecRef) :=
    refs.zipIdx.map fun p => (declLine? rs p.1.1, p.2, p.1.1, p.1.2)
  let before (x y : Option Nat × Nat × Name × L4YAML.YamlSpecRef) : Bool :=
    match x.1, y.1 with
    | none, none => x.2.1 < y.2.1
    | none, some _ => true
    | some _, none => false
    | some a, some b => a < b || (a == b && x.2.1 < y.2.1)
  (withIdx.qsort before).map fun x => (x.1, x.2.2.1, x.2.2.2)

end

end Scripts.Spec.Env
