module

/-!
# `Scripts.Restate.Probes` — the roster probes of items 226 and 227, verbatim

Both instruments read their roster off the ENVIRONMENT, not the text: a throwaway
file under `L4YAML/Scratch/` imports the premise-necessity census and prints one
`ROSTER lemma|binder|index|kind` line per optional (`_ ∨ True`) binder of
`StreamAccum`'s declarations — item 227's probe adds a fifth field, `chain` when the
elaborator accepts `⟨[], by simp⟩` for the LEFT disjunct (its premise is vacuous on
its own).  `lake env lean` elaborates the probe against the `.olean`s in `.lake/build`,
which is why the instruments build before writing it and again after restoring.
-/

namespace Scripts.Restate.Probes

@[expose] public section

/-- `L4YAML/Scratch/OptionalRoster.lean` (`decline_all_optional.PROBE_SRC`). -/
def optionalRoster : String := r#"import Tests.Guards.Proofs.PremiseNecessityCensus

open Lean Elab Command in
open L4YAML.Proofs.StreamAccum in
open L4YAML.Tests.Guards.RelaySupplyCensus in
open Tests.Guards.HypothesisReaderCensus in
run_cmd do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? ``colon_fires_implicit_key
  let mut rows : Array String := #[]
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    if isMechanism env nm then continue
    for (i, bn) in (optBinders ci.type).1 do
      let kind := if (match env.find? nm with
        | some (.ctorInfo _) => true | _ => false) then "ctor" else "lemma"
      rows := rows.push s!"ROSTER {nm.getString!}|{bn}|{i}|{kind}"
  logInfo (String.intercalate "\n" (rows.qsort (· < ·)).toList)
"#

/-- `L4YAML/Scratch/ChainRoster.lean` (`pay_chain_optional.PROBE_SRC`). -/
def chainRoster : String := r#"import Tests.Guards.Proofs.PremiseNecessityCensus

open Lean Elab Command Meta Term in
open L4YAML.Proofs.StreamAccum in
open L4YAML.Tests.Guards.RelaySupplyCensus in
open Tests.Guards.HypothesisReaderCensus in
run_cmd do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? ``colon_fires_implicit_key
  let stx ← `(term| by exact ⟨[], by simp⟩)
  let mut rows : Array String := #[]
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    if isMechanism env nm then continue
    for (i, bn) in (optBinders ci.type).1 do
      let kind := if (match env.find? nm with
        | some (.ctorInfo _) => true | _ => false) then "ctor" else "lemma"
      let chain ← liftTermElabM do
        forallBoundedTelescope ci.type (some i) fun _ body => do
          match body with
          | .forallE _ a _ _ =>
              withoutModifyingState do
                try
                  let e ← withoutErrToSorry do elabTerm stx (some (a.getArg! 0))
                  synthesizeSyntheticMVarsNoPostponing
                  let e ← instantiateMVars e
                  if e.hasExprMVar || e.hasSorry then pure false
                  else do check e; pure true
                catch _ => pure false
          | _ => pure false
      rows := rows.push
        s!"ROSTER {nm.getString!}|{bn}|{i}|{kind}|{if chain then "chain" else "-"}"
  logInfo (String.intercalate "\n" (rows.qsort (· < ·)).toList)
"#

#guard (optionalRoster.splitOn "\n").length == 20
#guard optionalRoster.endsWith "toList)\n"
#guard chainRoster.startsWith "import Tests.Guards.Proofs.PremiseNecessityCensus\n\nopen Lean Elab Command Meta Term in"

end

end Scripts.Restate.Probes
