/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML
import Tests.Guards.Proofs.SuffixGapAudit

/-!
# What the verified surface says for free (DOCS item 237)

Item 236 derived `InYamlLanguage s` for every string `s` from
`SLYamlStream.scannerDrop`, and left the number nothing held: **how much of the
verified surface is currently true for free?**  A theorem is free here when its
conclusion is provable WITHOUT its hypotheses — every premise it names is dead
weight while the broken arm stands.

Over the library's 103 theorems that mention the top-level surface, **17 are
free, and 15 of those stop being free when β.5 retires the arm.**  That is what
β.5 BUYS.  Every measurement in row 12 before this one priced what it COSTS.

The other 86 are already worth their statement.  Two of the 17 are free by a
route that does not touch the broken arm (`SLYamlStream.single` relates a
position to itself), so β.5 buys nothing at those two and they are not debt.

## The three ways a statement hides from a grep

`InYamlLanguage` is named in five library theorems, and a grep finds all five.
It is ASSERTED in six, because `scan_content_gives_stream_v2` spells the
definition out — `∃ sp_final, SLYamlStream ⟨input.toList, 0⟩ sp_final ∧
sp_final.chars = []` is `InYamlLanguage input`, `rfl`, and §2 checks that.  It
is the lemma the whole `DocumentProduction` chain rests on, and no search for
the name reaches it.

Eleven more are free at `SLYamlStream` itself, where the name `InYamlLanguage`
does not occur at all.  Nine of those are provable by one application of
`scannerDrop` over `stream_refl`, from a single `SSLComments _ target`
hypothesis with every other hypothesis — including their own `SLYamlStream`
premise — discarded.

Provable that way is not proved that way: `ssl_comments_extend_stream` ships a
proof through `implicitContinue`, and this file claims only what it checks,
which is what the STATEMENTS carry.

## What the census reads

The environment, not the source, and its own import closure rather than the
library — the closure is pinned below, and the four library modules outside it
are the serializers, which hold no theorems.  §1 checks that too, because a
coverage census that reads half a library and reports a whole one is how item
236 published `missing=23` for a supply that was already in the build.

## The direction that turned out to be empty

Item 236 recorded a failure mode to watch: `InYamlLanguage` in a HYPOTHESIS
restricts rather than trivializes, and β.5 would weaken such a theorem instead
of strengthening it.  **No library theorem takes `InYamlLanguage` as a
hypothesis** — §1 pins the count at zero, so the direction has no instance
here and β.5 spends nothing in it.
-/

set_option autoImplicit false

namespace Tests.Guards.FreeSurfaceCensus

open Lean Lean.Meta Lean.Elab
open L4YAML.Surface
open Tests.Guards.SuffixGapAudit

/-! ## §1 The census

Each library theorem is telescoped, its conclusion reduced at `reducible`
transparency, and sorted into one slot by WHERE the top-level surface appears:
at the conclusion's head as `InYamlLanguage`, at its head as `SLYamlStream`,
nested inside the conclusion, or in a hypothesis alone.

Then four candidate proofs are built for it and typechecked against its own
conclusion.  Three come from item 236 — `inYamlLanguage_everything`,
`stream_anything`, `stream_refl` — and the fourth applies `scannerDrop` over
`stream_refl` to one `SSLComments` hypothesis.  A theorem is free when any of
them typechecks, and it survives β.5 when `stream_refl` alone does it. -/

/-- The four modules the census does not read.  They are reported rather than
    assumed: a census names what it could not see. -/
def expectedUnread : List Name :=
  [`L4YAML.Output.Events, `L4YAML.Output.EventsIx,
   `L4YAML.Output.Json, `L4YAML.Output.JsonIx]

def expectedClosure : String := "modulesSeen=268"
-- 265 → 266 on 2026-10-28: `Proofs.Serialization.ParseCheckFrom` (S5 slice 1, `parse_ok_checkFrom`)
-- 252 → 253 on 2026-10-23: `Proofs.Production.Acceptance.Quoted`, the one-line
-- quoted-scalar scanner converses.  -- 253 → 255 on 2026-10-23: `Proofs.Parser.TokenGrammar`, `StreamCompleteness` (Stream D)
-- 255 → 256 on 2026-10-23: `Proofs.Production.Acceptance.Plain`, the one-line plain-scalar
-- scanner converse (Stream E).
-- 228 → 239 on 2026-10-05: the eleven modules of `L4YAML.Proofs.Serialization`
-- (PR #1), which `L4YAML.lean` imports so the kernel-accurate hygiene gate can
-- see them.  Only the closure moved: `expectedCensus` and `expectedFree` are
-- unchanged, so none of the eleven states a goal this census reads.
-- 227 → 228 on 2026-10-02: `L4YAML/Proofs/Parser/ParserScannableBase.lean`,
-- the `Scannable`-valued compose chain, is a new module in this closure.  It
-- is a separate module and not a section of `ParserGrammableBase` because the
-- two `maxHeartbeats 4000000` inductions over `YamlValue` do not elaborate
-- together.

-- 2026-10-27 (item 371): headStream 37 → 35, nestedConcl 55 → 57 — `explFrameValueLine` and
-- `accum_flow_open_depth0`'s value-line conclusions now head `ResumeFrames`, not `SLYamlStream`.
def expectedCensus : String :=
  "theorems=108 headYaml=5 headStream=35 nestedConcl=60 hypOnly=8 free=17 \
survivesBeta5=2 yamlInHypothesis=0"

/-- Every free theorem, with the route that closes it.  A count alone would not
    notice one leaving as another arrives. -/
def expectedFree : List String :=
  ["L4YAML.Proofs.DocumentProduction.empty_InYamlLanguage=everything",
   "L4YAML.Proofs.DocumentProduction.empty_to_stream=refl",
   "L4YAML.Proofs.DocumentProduction.empty_yaml_stream=anything refl",
   "L4YAML.Proofs.DocumentProduction.parse_strict_proof=everything",
   "L4YAML.Proofs.DocumentProduction.scan_strict_proof=everything",
   "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.value=drop",
   "L4YAML.Proofs.StreamAccum.PendingNode.close_with_ssl=drop",
   "L4YAML.Proofs.StreamAccum.PendingNode.propsClose=drop",
   "L4YAML.Proofs.StreamAccum.dropClose=drop",
   "L4YAML.Proofs.StreamAccum.nodocFlowResumeSep=drop",
   "L4YAML.Proofs.StreamAccum.scan_content_gives_stream_v2=unfolded",
   "L4YAML.Proofs.StreamAccum.ssl_comments_extend_stream=drop",
   "L4YAML.Proofs.StreamAccum.suffixFlowResumeSep=drop",
   "L4YAML.Proofs.StreamAccum.topLevelFlowResumeSep=drop",
   "L4YAML.Proofs.StreamAccum.topLevelFlowResumeSep_or_refused=drop",
   "L4YAML.Surface.parse_strict=everything",
   "L4YAML.Surface.scan_strict=everything"]

/-- The two capstones whose statements are currently vacuous. -/
def expectedFreeCapstones : List Name :=
  [`L4YAML.Proofs.DocumentProduction.parse_strict_proof,
   `L4YAML.Proofs.DocumentProduction.scan_strict_proof]

private def mentions (e : Expr) : Bool :=
  (e.find? fun x => x.isConstOf ``InYamlLanguage || x.isConstOf ``SLYamlStream).isSome

private inductive Slot where
  | headYaml | headStream | nestedConcl | hypOnly | out
deriving DecidableEq, Inhabited

/-- A declaration a human wrote, as opposed to one the `inductive` or equation
    compiler generated beside it. -/
private def isAuthored (env : Environment) (n : Name) : Bool := Id.run do
  if n.isInternal || n.hasMacroScopes then return false
  if env.isConstructor n then return false
  for c in n.components.map toString do
    if c.startsWith "match_" || c.startsWith "proof_" || c.startsWith "eq_"
       || c == "below" || c == "brecOn" || c == "binductionOn" || c == "casesOn"
       || c == "rec" || c == "recOn" || c == "noConfusion" || c == "noConfusionType"
       || c == "ibelow" || c == "ndrec" || c == "ndrecOn" || c == "induct"
       || c == "inj" || c == "injEq" || c == "sizeOf_spec" then
      return false
  return true

private def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => Name.anonymous

private def slotOf (t : Expr) : MetaM Slot :=
  forallTelescopeReducing t fun xs body => do
    let b ← whnfR body
    if b.isAppOfArity ``InYamlLanguage 1 then return .headYaml
    if b.isAppOfArity ``SLYamlStream 2 then return .headStream
    if mentions b then return .nestedConcl
    for x in xs do
      if mentions (← whnfR (← inferType x)) then return .hypOnly
    return .out

/-- Does the candidate prove exactly this declaration's conclusion?  `addDecl`
    is not usable for the question: it reports kernel failures through the
    message log rather than by throwing, so a `catch` around it reads every
    candidate as accepted. -/
private def accepts (ci : ConstantInfo)
    (mk : Array Expr → Expr → MetaM (Option Expr)) : MetaM Bool :=
  forallTelescope ci.type fun xs body => do
    let b ← whnfR body
    let some pf ← (try mk xs b catch _ => pure none) | return false
    if pf.hasSorry || pf.hasExprMVar then return false
    try
      let ty ← inferType pf
      unless ← withNewMCtxDepth (isDefEq ty b) do return false
      check pf
      return true
    catch _ => return false

/-- `inYamlLanguage_everything`, against a conclusion that names the predicate. -/
private def viaEverything (_xs : Array Expr) (b : Expr) : MetaM (Option Expr) := do
  unless b.isAppOfArity ``InYamlLanguage 1 do return none
  return some (mkApp (mkConst ``inYamlLanguage_everything) b.appArg!)

/-- `inYamlLanguage_everything`, against a conclusion that SPELLS THE
    DEFINITION OUT instead of naming it. -/
private def viaUnfolded (_xs : Array Expr) (b : Expr) : MetaM (Option Expr) := do
  if b.isAppOfArity ``InYamlLanguage 1 then return none
  unless b.isAppOf ``Exists do return none
  let sMv ← mkFreshExprMVar (mkConst ``String)
  unless ← isDefEq b (mkApp (mkConst ``InYamlLanguage) sMv) do return none
  let s ← instantiateMVars sMv
  if s.hasExprMVar then return none
  return some (mkApp (mkConst ``inYamlLanguage_everything) s)

/-- `stream_anything` — the target is reached because it opens a line. -/
private def viaAnything (_xs : Array Expr) (b : Expr) : MetaM (Option Expr) := do
  unless b.isAppOfArity ``SLYamlStream 2 do return none
  return some (mkApp2 (mkConst ``stream_anything) b.appFn!.appArg!
                (mkApp (mkConst ``SurfPos.chars) b.appArg!))

/-- `stream_refl` — the stream does not move.  The ONE route here that does not
    pass through `scannerDrop`, so the theorems it closes survive β.5. -/
private def viaRefl (_xs : Array Expr) (b : Expr) : MetaM (Option Expr) := do
  unless b.isAppOfArity ``SLYamlStream 2 do return none
  return some (mkApp (mkConst ``stream_refl) b.appFn!.appArg!)

/-- `scannerDrop` over `stream_refl` — the conclusion follows from ONE
    `SSLComments _ target` hypothesis, discarding every other. -/
private def viaDrop (xs : Array Expr) (b : Expr) : MetaM (Option Expr) := do
  unless b.isAppOfArity ``SLYamlStream 2 do return none
  let src := b.appFn!.appArg!
  for x in xs do
    let tx ← whnfR (← inferType x)
    if tx.isAppOfArity ``SSLComments 2 then
      if ← isDefEq tx.appArg! b.appArg! then
        return some (mkApp6 (mkConst ``SLYamlStream.scannerDrop) src src
          tx.appFn!.appArg! b.appArg! (mkApp (mkConst ``stream_refl) src) x)
  return none

run_cmd Command.liftTermElabM do
  let env ← getEnv
  let caps := L4YAML.capstoneDecls env
  let seen := env.header.moduleNames.filter (fun m => (`L4YAML).isPrefixOf m)
  let gotClosure := s!"modulesSeen={seen.size}"
  if gotClosure != expectedClosure then
    throwError "the census's own import closure moved.\nexpected: {expectedClosure}\n\
      got:      {gotClosure}\n\
      A coverage census reports the closure it was given, not the library."
  for m in expectedUnread do
    if seen.contains m then
      throwError "{m} is now inside the closure; the unread list is stale."
  let mut rows : Array (Name × Slot × String) := #[]
  let mut yamlHyp : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal || n.hasMacroScopes then continue
    unless (`L4YAML).isPrefixOf (modOf env n) do continue
    unless isAuthored env n && Lean.wasOriginallyTheorem env n do continue
    let s ← slotOf ci.type
    if s == .out then continue
    let hypYaml ← forallTelescopeReducing ci.type fun xs _ => do
      for x in xs do
        if ((← whnfR (← inferType x)).find? (·.isConstOf ``InYamlLanguage)).isSome then
          return true
      return false
    if hypYaml then yamlHyp := yamlHyp.push n
    let mut how := ""
    if ← accepts ci viaEverything then how := how ++ "everything "
    if ← accepts ci viaUnfolded then how := how ++ "unfolded "
    if ← accepts ci viaAnything then how := how ++ "anything "
    if ← accepts ci viaRefl then how := how ++ "refl "
    if ← accepts ci viaDrop then how := how ++ "drop "
    rows := rows.push (n, s, how.trimAscii.toString)
  let count (s : Slot) := (rows.filter (fun r => r.2.1 == s)).size
  let free := rows.filter (fun r => r.2.2 != "")
  let survives := free.filter (fun r => (r.2.2.splitOn "refl").length > 1)
  let got := s!"theorems={rows.size} headYaml={count .headYaml} \
headStream={count .headStream} nestedConcl={count .nestedConcl} \
hypOnly={count .hypOnly} free={free.size} survivesBeta5={survives.size} \
yamlInHypothesis={yamlHyp.size}"
  if got != expectedCensus then
    throwError "the free surface moved.\nexpected: {expectedCensus}\ngot:      {got}\n\
      free: {(free.map (fun r => s!"{r.1}={r.2.2}")).qsort (· < ·) |>.toList}"
  let gotFree := (free.map (fun r => s!"{r.1}={r.2.2}")).qsort (· < ·) |>.toList
  if gotFree != expectedFree then
    throwError "the free set changed membership without changing size.\n\
      expected: {expectedFree}\ngot:      {gotFree}"
  let gotCaps := ((free.filterMap (fun r => if caps.contains r.1 then some r.1 else none)).qsort
    (fun a b => a.toString < b.toString)).toList
  if gotCaps != expectedFreeCapstones then
    throwError "the vacuous capstones moved.\nexpected: {expectedFreeCapstones}\n\
      got:      {gotCaps}"

/-! ## §2 The three classes, compiled

Each class is exhibited once.  `parse_strict` and `scan_strict` are NOT
restated here — `SuffixGapAudit.lean` §5 already discharges their statements —
and neither is `empty_InYamlLanguage`, whose standing as the exception that is
not one was recorded at item 236. -/

/-- **A statement can be `InYamlLanguage` without naming it.**  This is
    `scan_content_gives_stream_v2`'s conclusion, and the equation is `rfl`. -/
example (input : String) :
    (∃ sp_final : SurfPos, SLYamlStream ⟨input.toList, 0⟩ sp_final ∧
      sp_final.chars = []) = InYamlLanguage input := rfl

/-- `scan_content_gives_stream_v2`'s statement, discharged without its
    hypothesis.  It is what the whole `DocumentProduction` chain rests on. -/
example (input : String) (tokens : Array (L4YAML.Positioned L4YAML.YamlToken))
    (_h : L4YAML.Scanner.scan input = .ok tokens) :
    ∃ sp_final : SurfPos, SLYamlStream ⟨input.toList, 0⟩ sp_final ∧
      sp_final.chars = [] :=
  inYamlLanguage_everything input

/-- `ssl_comments_extend_stream`'s statement, discharged without its stream
    hypothesis — the nine-theorem `drop` class.  The shipped proof goes through
    `implicitContinue` and uses both; what is free is the STATEMENT. -/
example (sp_start sp sp_final : SurfPos)
    (_h_stream : SLYamlStream sp_start sp) (h_ssl : SSLComments sp sp_final) :
    SLYamlStream sp_start sp_final :=
  SLYamlStream.scannerDrop sp_start sp_start sp sp_final (stream_refl sp_start) h_ssl

/-! ## §3 What β.5 buys

Fifteen of the seventeen are free only through `scannerDrop`.  When β.5 lands,
§1 throws, and the count it reports is the content those fifteen statements
gained — including both acceptance capstones, which say nothing today.

Two do not move.  `empty_to_stream` and `empty_yaml_stream` close by
`SLYamlStream.single`, which relates a position to itself and is untouched by
β.5; they were never debt.

What this file does NOT establish is that the fifteen become unprovable.  It
found one route to each and that route runs through the broken arm; whether
another exists is settled by β.5 landing, not by this census.  An inconclusive
direction is recorded as inconclusive. -/

end Tests.Guards.FreeSurfaceCensus
