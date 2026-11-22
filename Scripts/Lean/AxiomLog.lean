module

@[expose] public section Blanket

/-!
# Scripts.Lean.AxiomLog — `#print axioms` observations and the placeholder signals

The pure half of `scripts-check-serialization-proofs` (formerly
`scripts/check-serialization-axioms.py`): read every
`'<name>' depends on axioms: [a, b]` / `'<name>' does not depend on any axioms`
line of a `lake env lean` log, refuse any axiom outside the standard three,
refuse a name observed with two different profiles, require an observation
for every `#print axioms` site, and require the two headline declarations'
exact profiles.  The negative control — a deliberate `sorry` probe — must show
BOTH of Lean's placeholder signals (`sorryAx` in the axiom list and the
``declaration uses `sorry` `` warning), so that a Lean whose wording changed
would fail the control rather than let a real placeholder through.
-/

namespace Scripts.Lean.AxiomLog

def allowed : List String := ["propext", "Classical.choice", "Quot.sound"]

/-- Python's `repr` of a sorted list of strings: `['a', 'b']`. -/
def pyList (xs : List String) : String :=
  "[" ++ ", ".intercalate (xs.map fun x => s!"'{x}'") ++ "]"

/-- Headline declarations whose profile must be exactly this. -/
def exact : List (String × List String) :=
  [("L4YAML.Proofs.Serialization.SerializationWellFormed.checkFrom_correct", ["propext"]),
   ("L4YAML.Proofs.Serialization.parse_iff_executable_language", allowed)]

/-- Python: `declaration uses [`']sorry[`']`. -/
def hasPlaceholder (s : String) : Bool :=
  (s.splitOn "declaration uses `sorry`").length > 1 || (s.splitOn "declaration uses 'sorry'").length > 1

def hasSorryAx (s : String) : Bool := (s.splitOn "sorryAx").length > 1

/-- The set-like profile: trimmed, de-duplicated, sorted. -/
def profileOf (axioms : String) : List String :=
  ((axioms.splitOn ",").map (·.trimAscii.toString) |>.filter (· != "")).eraseDups.mergeSort (· ≤ ·)

/-- Every `'name' depends on axioms: [..]` / `'name' does not depend on any axioms`
observation in the log, in order.  Python: `'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))`
with DOTALL (the bracket list may wrap lines). -/
partial def observations (log : String) : List (String × List String) :=
  go log.toList []
where
  go (cs : List Char) (acc : List (String × List String)) : List (String × List String) :=
    match cs with
    | [] => acc.reverse
    | '\'' :: t =>
      let name := t.takeWhile (· != '\'')
      let after := t.drop name.length
      match after with
      | '\'' :: ' ' :: rest =>
        let restS := String.ofList rest
        if restS.startsWith "depends on axioms:" then
          let r := (rest.drop "depends on axioms:".length).dropWhile Char.isWhitespace
          match r with
          | '[' :: body =>
            let inner := body.takeWhile (· != ']')
            if inner.length == body.length then go rest acc   -- no closing bracket: not a match
            else go (body.drop (inner.length + 1)) ((String.ofList name, profileOf (String.ofList inner)) :: acc)
          | _ => go rest acc
        else if restS.startsWith "does not depend on any axioms" then
          go (rest.drop "does not depend on any axioms".length) ((String.ofList name, []) :: acc)
        else go after acc
      | _ => go after acc
    | _ :: t => go t acc

/-- The Python's `validate`: `.error msg` on the first violation, else the
profiles observed. -/
def validate (log probe : String) (sites : List String) : Except String (List (String × List String)) := do
  if !hasSorryAx probe || !hasPlaceholder probe then
    throw "Negative control must expose both Lean placeholder signals"
  if hasSorryAx log || hasPlaceholder log then
    throw "Proof placeholder in serialization build or axiom output"
  let mut profiles : List (String × List String) := []
  for (name, profile) in observations log do
    let bad := profile.filter (!allowed.contains ·)
    if !bad.isEmpty then
      throw s!"Unapproved axioms for {name}: {pyList bad}"
    match profiles.lookup name with
    | some p => if p != profile then throw s!"Conflicting profiles for {name}"
    | none => profiles := profiles ++ [(name, profile)]
  let missing := (sites.filter fun s => (profiles.lookup s).isNone).mergeSort (· ≤ ·)
  if !missing.isEmpty then
    throw s!"Missing axiom observations: {pyList missing}"
  for (name, want) in exact do
    let got := profiles.lookup name
    if got != some (want.mergeSort (· ≤ ·)) then
      throw s!"Exact axiom profile mismatch for {name}: {match got with | some p => s!"{p}" | none => "None"}"
  return profiles

#guard observations "'A.b' depends on axioms: [propext, Classical.choice]\n'A.c' does not depend on any axioms\n"
  == [("A.b", ["Classical.choice", "propext"]), ("A.c", [])]
#guard observations "'A.b' depends on axioms: [propext,\n  Quot.sound]" == [("A.b", ["Quot.sound", "propext"])]
#guard observations "'x' depends on axioms: [a" == []
#guard observations "note 'A.b' is fine\n'A.b' depends on axioms: []" == [("A.b", [])]
#guard hasPlaceholder "warning: declaration uses `sorry`" && hasPlaceholder "declaration uses 'sorry'" && !hasPlaceholder "sorry"
#guard (validate "'L4YAML.Proofs.Serialization.SerializationWellFormed.checkFrom_correct' depends on axioms: [propext]\n'L4YAML.Proofs.Serialization.parse_iff_executable_language' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
  "'p' depends on axioms: [sorryAx]\nwarning: declaration uses `sorry`" ["L4YAML.Proofs.Serialization.parse_iff_executable_language"]).isOk
/-- The error of a failed validation, for the guards. -/
def errOf (r : Except String (List (String × List String))) : Option String :=
  match r with | .error e => some e | .ok _ => none

#guard errOf (validate "" "no signals" []) == some "Negative control must expose both Lean placeholder signals"
#guard errOf (validate "'q' depends on axioms: [sorryAx]" "'p' depends on axioms: [sorryAx]\ndeclaration uses `sorry`" [])
  == some "Proof placeholder in serialization build or axiom output"
#guard errOf (validate "'q' depends on axioms: [propext, Lean.ofReduceBool]" "'p' depends on axioms: [sorryAx]\ndeclaration uses `sorry`" [])
  == some "Unapproved axioms for q: ['Lean.ofReduceBool']"
#guard errOf (validate "'q' depends on axioms: [propext]\n'q' does not depend on any axioms" "'p' depends on axioms: [sorryAx]\ndeclaration uses `sorry`" [])
  == some "Conflicting profiles for q"
#guard errOf (validate "'q' depends on axioms: [propext]" "'p' depends on axioms: [sorryAx]\ndeclaration uses `sorry`" ["r", "q"])
  == some "Missing axiom observations: ['r']"
#guard errOf (validate "'q' depends on axioms: [propext]" "'p' depends on axioms: [sorryAx]\ndeclaration uses `sorry`" [])
  == some "Exact axiom profile mismatch for L4YAML.Proofs.Serialization.SerializationWellFormed.checkFrom_correct: None"

end Scripts.Lean.AxiomLog
