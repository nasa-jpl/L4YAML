module

public import Lean.Environment
public import Lean.DeclarationRange
public import Lean.PrivateName

/-!
# Scripts.Lean.DeclRanges — which declaration owns a source line, off the environment

Rule 9 §2: a question about declarations is answered from the environment, not from the
text.  The price instruments group a probe's error lines by the declaration they fall in;
this module reads the module's declaration ranges (`Lean.declRangeExt`, exported to the
`.olean.server` part) and answers "which declaration owns line *n*" from them.  A probe
may have inserted lines, so `lineMap` carries a patched line back to the pristine one the
ranges describe.
-/

open Lean

namespace Scripts.Lean.DeclRanges

public section

/-- One declaration of the module: the name as the source spells it, first and last line (1-based). -/
structure Decl where
  name : String
  start : Nat
  stop : Nat
  deriving Repr, BEq, Inhabited

unsafe def readRangesImpl (olean : System.FilePath) : IO (Array (Name × DeclarationRanges)) := do
  let server := System.FilePath.mk (olean.toString ++ ".server")
  if !(← server.pathExists) then throw (IO.userError s!"{server} is missing")
  let parts ← readModuleDataParts #[olean, server]
  let some (data, _) := parts[parts.size - 1]? | throw (IO.userError s!"{server}: no module data")
  let some (_, es) := data.entries.find? (·.1 == ``Lean.declRangeExt)
    | throw (IO.userError s!"{server}: no declaration ranges")
  return unsafeCast es

/-- `(name, ranges)` of every declaration the module `olean` elaborated. -/
@[implemented_by readRangesImpl]
opaque readRanges (olean : System.FilePath) : IO (Array (Name × DeclarationRanges))

/-- The namespace the module's declarations live in: the longest prefix shared by more than half of them. -/
def moduleNamespace (names : Array Name) : Name := Id.run do
  let some first := names[0]? | return .anonymous
  let first := (privateToUserName? first).getD first
  let mut p := first.getPrefix
  while p != .anonymous do
    let n := (names.filter fun x => p.isPrefixOf ((privateToUserName? x).getD x)).size
    if 2 * n > names.size then return p
    p := p.getPrefix
  return .anonymous

/-- The declaration's name as the source spells it: `private` undone, the module namespace dropped. -/
def displayName (ns n : Name) : String :=
  let n := (privateToUserName? n).getD n
  let n := if ns != .anonymous && ns.isPrefixOf n && n != ns then n.replacePrefix ns .anonymous else n
  n.toString (escape := false)

#guard displayName `A.B `A.B.foo.bar' == "foo.bar'"
#guard displayName `A.B `A.C.foo == "A.C.foo"
#guard displayName .anonymous `A.foo == "A.foo"
#guard moduleNamespace #[`A.B.x, `A.B.y, `A.B.C.z, `Q.w] == `A.B
#guard moduleNamespace #[`A.x, `B.y] == .anonymous

def decls (rs : Array (Name × DeclarationRanges)) : Array Decl :=
  let ns := moduleNamespace (rs.map (·.1))
  rs.map fun (n, r) => { name := displayName ns n, start := r.range.pos.line, stop := r.range.endPos.line }

/-- The declaration owning 1-based `line`: the outermost one containing it (a structure, not
    its constructor); `<file scope>` when none does. -/
def ownerOf (ds : Array Decl) (line : Nat) : String :=
  let owners := ds.filter fun d => d.start ≤ line && line ≤ d.stop
  let best := owners.foldl (init := (none : Option Decl)) fun acc d =>
    match acc with
    | none => some d
    | some b =>
      if d.start < b.start || (d.start == b.start && d.stop > b.stop)
         || (d.start == b.start && d.stop == b.stop && d.name.length < b.name.length) then some d else some b
  (best.map (·.name)).getD "<file scope>"

#guard ownerOf #[⟨"T", 10, 20⟩, ⟨"T.mk", 12, 13⟩, ⟨"u", 30, 31⟩] 12 == "T"
#guard ownerOf #[⟨"T", 10, 20⟩, ⟨"u", 30, 31⟩] 31 == "u"
#guard ownerOf #[⟨"T", 10, 20⟩, ⟨"u", 30, 31⟩] 25 == "<file scope>"

/-- `lineMap original patched`: for each line of `patched` (0-based index), the 1-based line of
    `original` it stands for — itself when the patch replaced lines in place, the next pristine
    line when the patch inserted it. -/
def lineMap (original patched : Array String) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty patched.size
  let mut i := 0
  let mut extra := patched.size - original.size
  for j in [0:patched.size] do
    if i < original.size && patched[j]! == original[i]! then
      out := out.push (i + 1); i := i + 1
    else if extra > 0 && (i ≥ original.size || (j + 1 < patched.size && patched[j + 1]! == original[i]!)) then
      out := out.push (min (i + 1) original.size); extra := extra - 1
    else
      out := out.push (min (i + 1) original.size); i := i + 1
  return out

#guard lineMap #["a", "b", "c"] #["a", "X", "c"] == #[1, 2, 3]
#guard lineMap #["a", "b", "c"] #["a", "x", "b", "c"] == #[1, 2, 2, 3]
#guard lineMap #["a", "b", "c"] #["a", "x", "b", "y", "c"] == #[1, 2, 2, 3, 3]
#guard lineMap #["a", "b", "c"] #["a", "X", "y", "c"] == #[1, 2, 3, 3]
#guard lineMap #["a", "b"] #["a", "b", "z"] == #[1, 2, 2]

end

end Scripts.Lean.DeclRanges
