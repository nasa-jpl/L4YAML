module

public import Lean.Data.Json
public meta import Lean.Data.Json

/-!
# Scripts.Stats.Hygiene — the kernel-accurate proof-hygiene gate's reading

The pure half of `lake run check-hygiene` (Rule 9 phase 4 row 3): the `env`
section of `collect-stats`'s `stats.json` — counted over the compiled
environment by `Lean.collectAxioms`, not by grepping sources — must show zero
theorems with a (direct or transitive) `sorry`, zero theorems resting on a custom
axiom and zero custom axioms.  This was the `python3 - <<'EOF'` heredoc in
`test-coverage.yml` and `generate-all.sh`; the verdict lines are the heredoc's.
-/

@[expose] public section

namespace Scripts.Stats.Hygiene

open Lean (Json)

instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e, .error f => e == f
    | _, _ => false

/-- The four counters that must be zero, in the heredoc's order (its `bad` dict prints
    in this order). -/
def mustBeZero : List String :=
  ["theorems_with_transitive_sorry", "theorems_with_direct_sorry",
   "theorems_with_custom_axiom", "axioms"]

/-- Python's `repr` of the `bad` dict: `{'axioms': 1, …}`. -/
def pyDict (kvs : List (String × Int)) : String :=
  "{" ++ ", ".intercalate (kvs.map fun (k, v) => s!"'{k}': {v}") ++ "}"

#guard pyDict [("axioms", 1)] == "{'axioms': 1}"
#guard pyDict [] == "{}"

/-- The verdict off the parsed `stats.json`: `.ok line` for a clean environment,
    `.error line` for the gate failing or the file not having the shape. -/
def verdict (stats : Json) : Except String String := do
  let env ← match stats.getObjVal? "env" with
    | .ok e => pure e
    | .error _ => throw "stats.json has no `env` section"
  let get (k : String) : Except String Int :=
    match env.getObjVal? k with
    | .ok v => match v.getInt? with
      | .ok n => pure n
      | .error _ => throw s!"env.{k} is not an integer"
    | .error _ => throw s!"env has no `{k}`"
  let mut bad : List (String × Int) := []
  for k in mustBeZero do
    let n ← get k
    if n != 0 then bad := bad ++ [(k, n)]
  if !bad.isEmpty then throw s!"proof-hygiene gate failed: {pyDict bad}"
  let theorems ← get "theorems"
  return s!"env clean: {theorems} theorems, 0 sorries, 0 custom axioms"

def verdictOf (text : String) : Except String String := Json.parse text >>= verdict

#guard verdictOf "{\"env\": {\"theorems\": 1778, \"axioms\": 0, \"theorems_with_direct_sorry\": 0, \"theorems_with_transitive_sorry\": 0, \"theorems_with_custom_axiom\": 0}}"
  == .ok "env clean: 1778 theorems, 0 sorries, 0 custom axioms"
#guard verdictOf "{\"env\": {\"theorems\": 5, \"axioms\": 1, \"theorems_with_direct_sorry\": 0, \"theorems_with_transitive_sorry\": 2, \"theorems_with_custom_axiom\": 0}}"
  == .error "proof-hygiene gate failed: {'theorems_with_transitive_sorry': 2, 'axioms': 1}"
#guard verdictOf "{\"env\": {\"theorems\": 5}}" == .error "env has no `theorems_with_transitive_sorry`"
#guard verdictOf "{\"files\": []}" == .error "stats.json has no `env` section"
#guard (verdictOf "{").toOption == none

end Scripts.Stats.Hygiene

end
