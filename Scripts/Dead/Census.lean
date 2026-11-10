module

public import Lean.Environment
public import Lean.PrivateName
public import Lean.Util.FoldConsts
public import Lean.Meta.Match.MatcherInfo
public import Lean.Compiler.ExportAttr
public import Std.Data.HashSet
public import Std.Data.HashMap
public meta import Std.Data.HashSet.Basic
public import Scripts.Path.CapstonePath
public import L4YAML.CapstoneAttr

@[expose] public section Blanket

/-!
# Scripts.Dead.Census — the dead-declaration census (DOCS items 476 / 477)

Every user-named library declaration (`L4YAML.*` modules) that no root reaches, where a root
is a `@[capstone]`-tagged declaration (`L4YAML.capstoneDecls`, the set `L4YAML/Capstones.lean`
pins), an `@[export]` FFI entry, or a declaration of the Rule 2 / instrument modules
(`Tests.Guards`, `Tests.AdversarialInstantiation`, `Tests.Reflections`), and reach is the
transitive closure through types and values (`Scripts.Path.CapstonePath.reach`).

The unreached declarations split into four classes — the roster is class (B) alone:

| class | rule | reported as |
|---|---|---|
| (A) campaign in progress | module under `campaignNamespaces` — a Blueprint capstone row with no declaration yet (7.7's S3 / S5 chain) | count + modules |
| (C) API by convention | module not under `L4YAML.Proofs` — the user-facing library no capstone states anything about; not decidable mechanically, so bucketed, never called dead | count + modules |
| (D) Rule 2 / instrument-only | reached from the test modules but from no capstone or export | count |
| (B) scaffolding behind no capstone | the rest — the roster, pinned as a SET of fully-qualified names (`Tests/Guards/Proofs/DeadDeclarationRoster.lean`), shrink-only | names |

"Unreached" is not "unreferenced": a dead lemma applied only by other dead lemmas is in the
roster.  The `referrers` column counts, per (B) declaration, the dead declarations that mention
it; a (B) declaration with none is a cluster root — deleting it frees what it alone held.
-/

open Lean

namespace Scripts.Dead.Census

/-- Class (A): capstone 7.7 (`parse_iff_grammar` converse) has no declaration yet; its S3 / S5
    chain lives here (`scanFiltered_parseStream_ok_checkFrom_full`, `TraceOf/*`, the Scanner
    shape modules of items 446–452).  Alive by Rule 1's chain to a NAMED future capstone. -/
def campaignNamespaces : List Name :=
  [`L4YAML.Proofs.Serialization,
   `L4YAML.Proofs.Scanner.DocStartLiveInv,
   `L4YAML.Proofs.Scanner.StructDepth,
   `L4YAML.Proofs.Scanner.TagShape]

/-- The Rule 2 / instrument module roots (class (D)). -/
def testRootPrefixes : List Name := [`Tests.Guards, `Tests.AdversarialInstantiation, `Tests.Reflections]

inductive Kind where
  | thm | defn | ind | ctor | opaque | other
  deriving DecidableEq, Repr

def Kind.show : Kind → String
  | .thm => "thm" | .defn => "def" | .ind => "ind" | .ctor => "ctor" | .opaque => "opaque" | .other => "other"

def kindOf : ConstantInfo → Kind
  | .thmInfo _ => .thm | .defnInfo _ => .defn | .inductInfo _ => .ind
  | .ctorInfo _ => .ctor | .opaqueInfo _ => .opaque | _ => .other

/-- Compiler- and elaborator-generated constants are not declarations a person wrote.  Private
    declarations ARE (`_private.<module>.0.<name>` is read through `privateToUserName`), and so
    are authored names that merely start with `_` (`_inline_scalar_preserves_prefix`): only the
    generated `_`-prefixes are filtered, by name. -/
def generatedUnderscore : List String :=
  ["_proof", "_eq", "_sunfold", "_unsafe", "_cstage", "_closed", "_lam", "_elam", "_rarg", "_boxed",
   "_redArg", "_spec", "_sizeOf", "_override", "_impl", "_regBuiltin", "_hyg", "_uniq", "_aux", "_private",
   "_root_", "_example", "_simp", "_mutual", "_nested", "_ind", "_at", "_fun", "_match", "_bind", "_let",
   "_sparseCasesOn", "_flat", "_f", "_unary", "_auto"]

def generatedComponent : List String :=
  ["sizeOf_spec", "injEq", "inj", "below", "ibelow", "brecOn", "binductionOn", "casesOn", "recOn",
   "noConfusionType", "noConfusion", "toCtorIdx", "ofNat", "ctorIdx", "ctorElim", "congr_simp"]

def isAux (env : Environment) (n : Name) : Bool :=
  isAuxRecursor env n || isNoConfusion env n || isRecCore env n
  || (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome
  || (privateToUserName n).components.any fun c => match c with
      | .str _ s => s.startsWith "proof_" || s.startsWith "match_" || s.startsWith "eq_"
        || generatedComponent.contains s || generatedUnderscore.any (fun g => s.startsWith g)
      | .num _ _ => true
      | _ => false

def modOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

structure Decl where
  name : Name
  module : Name
  kind : Kind

inductive Class where
  | campaign | api | testOnly | roster
  deriving DecidableEq, Repr

def Class.show : Class → String
  | .campaign => "A-campaign" | .api => "C-api" | .testOnly => "D-test-only" | .roster => "B-roster"

structure Report where
  population : Nat
  thms : Nat
  defs : Nat
  capstoneRoots : Nat
  exportRoots : Nat
  testRoots : Nat
  unreached : Nat
  unreachedThms : Nat
  campaign : Nat
  api : Nat
  testOnly : Nat
  roster : Array Decl
  rosterThms : Nat
  rosterClusterRoots : Nat
  perModule : Array (Name × Nat)          -- (B) per module, descending
  campaignModules : Array (Name × Nat)
  apiModules : Array (Name × Nat)

/-- The whole census off a loaded environment. -/
def classify (env : Environment) : Report := Id.run do
  let mut lib : Array Decl := #[]
  let mut exps : List Name := []
  let mut tests : List Name := []
  for (n, ci) in env.constants.toList do
    match modOf env n with
    | some m =>
      if (`L4YAML).isPrefixOf m then
        if (getExportNameFor? env n).isSome then exps := n :: exps
        if !isAux env n then lib := lib.push ⟨n, m, kindOf ci⟩
      else if testRootPrefixes.any (·.isPrefixOf m) then tests := n :: tests
    | none => pure ()
  let caps := (L4YAML.capstoneDecls env).toList
  let reached := Scripts.Path.CapstonePath.reach env (caps ++ exps)
  let testReached := Scripts.Path.CapstonePath.reach env tests
  let dead := lib.filter fun d => !reached.contains d.name
  let deadSet : Std.HashSet Name := dead.foldl (fun s d => s.insert d.name) {}
  let classOf (d : Decl) : Class :=
    if campaignNamespaces.any (·.isPrefixOf d.module) then .campaign
    else if !(`L4YAML.Proofs).isPrefixOf d.module then .api
    else if testReached.contains d.name then .testOnly
    else .roster
  let roster := (dead.filter fun d => classOf d == .roster).qsort fun a b => Name.quickLt a.name b.name
  let rosterSet : Std.HashSet Name := roster.foldl (fun s d => s.insert d.name) {}
  -- referrers among the dead: a (B) name mentioned by no dead declaration is a cluster root
  let mut referred : Std.HashSet Name := {}
  for d in dead do
    for m in Scripts.Path.CapstonePath.rawRefs env d.name do
      if m != d.name && rosterSet.contains m then referred := referred.insert m
  let count (xs : Array Decl) (k : Kind) := (xs.filter fun d => d.kind == k).size
  let byModule (xs : Array Decl) : Array (Name × Nat) :=
    let m : Std.HashMap Name Nat := xs.foldl (fun h d => h.insert d.module (h.getD d.module 0 + 1)) {}
    m.toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && Name.quickLt a.1 b.1)
  let _ := deadSet
  return {
    population := lib.size, thms := count lib .thm, defs := count lib .defn
    capstoneRoots := caps.length, exportRoots := exps.length, testRoots := tests.length
    unreached := dead.size, unreachedThms := count dead .thm
    campaign := (dead.filter fun d => classOf d == .campaign).size
    api := (dead.filter fun d => classOf d == .api).size
    testOnly := (dead.filter fun d => classOf d == .testOnly).size
    roster := roster, rosterThms := count roster .thm
    rosterClusterRoots := (roster.filter fun d => !referred.contains d.name).size
    perModule := byModule roster
    campaignModules := byModule (dead.filter fun d => classOf d == .campaign)
    apiModules := byModule (dead.filter fun d => classOf d == .api) }

/-- The one-line pin (`expectedDeadCensus` in `Tests/Guards/Proofs/DeadDeclarationCensus.lean`). -/
def Report.summary (r : Report) : String :=
  s!"population={r.population} thm={r.thms} def={r.defs} roots=capstone:{r.capstoneRoots}+export:{r.exportRoots} unreached={r.unreached} thm={r.unreachedThms} A-campaign={r.campaign} C-api={r.api} D-test-only={r.testOnly} B-roster={r.roster.size} thm={r.rosterThms} cluster-roots={r.rosterClusterRoots}"

/-- The roster as the SET pin: fully-qualified names, sorted, one per line. -/
def Report.rosterText (r : Report) : String :=
  "\n".intercalate (r.roster.toList.map fun d => s!"{d.name} {d.kind.show}")

def Report.render (r : Report) (modules : Nat := 25) : String := Id.run do
  let mut out := r.summary ++ "\n"
  let section_ (title : String) (xs : Array (Name × Nat)) : String :=
    s!"{title} ({xs.size} modules):\n" ++ "".intercalate ((xs.toList.take modules).map fun (m, c) => s!"  {m}: {c}\n")
  out := out ++ section_ "(B) roster by module" r.perModule
  out := out ++ section_ "(A) campaign in progress by module" r.campaignModules
  out := out ++ section_ "(C) API by convention by module" r.apiModules
  return out

/-- What a pinned roster and the fresh one disagree on, by NAME (the kind column is informational:
    a `lemma` restated as a `def` is the same declaration): `(entered, left, kindChanged)`. -/
def rosterDiff (pinned fresh : String) : List String × List String × List String :=
  let nameOf (l : String) : String := ((l.splitOn " ").head?).getD l
  let rows (t : String) : List String := (t.splitOn "\n").filter (· ≠ "")
  let p := rows pinned
  let f := rows fresh
  let pm : Std.HashMap String String := p.foldl (fun h l => h.insert (nameOf l) l) {}
  let fm : Std.HashMap String String := f.foldl (fun h l => h.insert (nameOf l) l) {}
  (f.filter (fun l => !pm.contains (nameOf l)) |>.map nameOf,
   p.filter (fun l => !fm.contains (nameOf l)) |>.map nameOf,
   f.filter (fun l => match pm.get? (nameOf l) with | some o => o != l | none => false) |>.map nameOf)

end Scripts.Dead.Census
