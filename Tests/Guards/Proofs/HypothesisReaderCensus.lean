import Tests.Guards.Proofs.ArmSpendCensus

/-!
# The reader census: which premises are READ, and which are carried (item 225)

Item 224 built the SPEND CENSUS and closed with the question it was built to
ask, now askable of any premise: **which of β.5's remaining hypotheses have
readers, and which are carried?**  Its instrument could not be the one that
answers it.  The weakening probe loosens one binder, rebuilds, and reads the
errors — one build per binder.  That is why it was run on eight binders and not
on a library, and a question about "β.5's remaining hypotheses" is a question
about thousands.

This file moves the probe into the ENVIRONMENT.  For every binder of every
declaration it classifies the occurrences of that binder in the ELABORATED
proof term:

| verdict | what the term does with the binder |
|---|---|
| `READ` | eliminates it HERE — scrutinee of a recursor, `casesOn` or matcher, argument of a projection, a `.proj`, or applied to arguments |
| `RELAY` | hands it to another constant, and nothing else |
| `FIELD` | stores it in a constructor |
| `RETURN` | hands it back bare |
| `UNUSED` | does not mention it at all |
| `ETA` | the proof term does not BIND it — see §1 |

One walk of the module, ten seconds, every binder.

## §2's calibration is the reason to believe any of it

Item 224's eight rebuild verdicts are ground truth for eight of these binders,
and the census reproduces all eight — one `READ` (`colon_fires_implicit_key`),
seven not, and `block_dispatch_deferred` named `FIELD`, which is the mechanism
item 224 had to read off the error text by hand ("CONDUIT → `PendingNode.
pendingFlow`'s field").  Eight agreements at one build instead of eight.

## What it says about the three premises the mandate named

* **`content_dispatch_routed`'s optional contexts are all read.**  Five of the
  six — `h_keyctx`, `h_suffixctx`, `h_nodocctx`, `h_markerctx`, `h_propsctx` —
  are eliminated in the lemma's own term.  The sixth, `h_ref` (item 144's fifth
  arm), is a RELAY, and §5 chases it: it is eliminated one hop on, inside
  `rootMapRoute_or_refused` and `rootMapRouteF_or_refused`, where the left
  disjunct refutes the `h_op = false` branch outright.  **Not carried.**
* **R3's seven productions cannot be priced by readership, and §6 proves why.**
  `KeyPackPunt.noKeyContext` is NULLARY (`.dedent` was too, until item 297
  deleted it), so `KeyPackPunt sc` is
  inhabited at every state — `punt_is_unconditional` — and therefore any
  consumer that takes `A ∨ KeyPackPunt sc` as a premise proves its conclusion
  without it (`punt_premise_buys_nothing`).  There is nothing to read, not
  because the census cannot see it but because the type carries none.  The
  price of a punt is the CASE SPLIT it forces, which is what
  `scripts/punt_reason_price.py` already measures; the two instruments are
  asking the only question available.
* **Item 183's flip order** is where `h_ref`'s readers live:
  `rootMapRoute_or_refused` and `rootMapRouteF_or_refused` are two of the flip's
  five definitions, so the premise the flip's REFUTABLE halves carry is read at
  every one of its four call sites.

**The rule this item adds: a premise has no reader for two different reasons,
and only one of them is about proofs.**  It can be threaded and never
eliminated — which the census measures — or its TYPE can be unconditionally
inhabited, which no census of terms can see and which one `example` settles.
R3's seven productions are the second kind.

## The debt this instrument carries, exhibited in §7

A relay's chase terminates inside the callee, and there the census cannot tell
a READ from a RE-STATEMENT: `Or.elim h f g` hands the decision to the caller's
own alternatives and `Or.imp_left f h` decides nothing, and BOTH are a relay at
the call site terminating in `Or.casesOn` one hop on.  §7 pins the two with the
same verdict, so the limit is machine-exhibited rather than asserted.
-/

namespace Tests.Guards.HypothesisReaderCensus

set_option autoImplicit false

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs

open Lean Elab Command
open L4YAML.Tests.Guards.RelaySupplyCensus

/-! ## §1  The instrument

The one delicate point is the telescope.  A lemma's TYPE keeps producing
`forall` binders past the end of its premise list whenever its conclusion is
itself a function — `rootMapRoute_or_refused` has thirteen leading foralls and
eleven lambdas, and the last two are `∀ sp_v, SBlockMapEntry k sp_key sp_v →`,
part of what it CONCLUDES.  So the telescope to peel is the shorter of the two,
and a binder the value never binds gets no verdict at all rather than a guessed
one: that is the `ETA` lane, and it is exactly the conclusion's own binders. -/

/-- What one occurrence of a binder does where it stands. -/
inductive Use where
  | elim (g : Name) (idx : Nat)
  | applied
  | projd
  | relay (g : Name) (idx : Nat)
  | field (g : Name) (idx : Nat)
  | bare
  | inTy
deriving Inhabited, BEq

/-- The struct-argument index of a projection function, read off the
    environment rather than off a list of projection names. -/
def projIdx (env : Environment) (g : Name) : Option Nat :=
  (env.getProjectionFnInfo? g).map (fun i => i.numParams)

def isCtor (env : Environment) (g : Name) : Bool :=
  match env.find? g with | some (.ctorInfo _) => true | _ => false

/-- What a term IS, for the purposes of the walk: the sub-term that carries it,
    plus whatever the peel discarded, which is still walked so that no
    occurrence can vanish.

    **Item 226 added this seam and it is not decoration.**  This item's walk
    peels NOTHING (`noPeel`), and that is why §5 below reports nine premises it
    cannot land in the library: `Or.imp` and an over-applied `Eq.ndrec` are
    PIPES — item 213 named them and item 215's `peelPipe` taught the SUPPLY
    census to see through them — and a walk that stops at a pipe reports the
    pipe.  `Tests.Guards.PremiseNecessityCensus` supplies the pipe peel and
    lands all nine. -/
abbrev Peel := Expr → Expr × Array Expr

/-- Item 225's peel: a term is itself. -/
def noPeel : Peel := fun e => (e, #[])

/-- Every occurrence of the binder whose de Bruijn index is `tgt` at depth 0.
    `d` is the extra binder depth, so the variable is `tgt + d`; `hasLooseBVar`
    prunes every subterm that cannot contain it. -/
partial def usesWith (peel : Peel) (env : Environment) (tgt : Nat) :
    Nat → Expr → Array Use → Array Use
  | d, e, acc =>
    if !e.hasLooseBVar (tgt + d) then acc else
    match e with
    | .bvar _ => acc.push .bare
    | .mdata _ b => usesWith peel env tgt d b acc
    | .proj _ _ s => if s == .bvar (tgt + d) then acc.push .projd
                     else usesWith peel env tgt d s acc
    | .lam _ t b _ =>
        let acc := if t.hasLooseBVar (tgt + d) then acc.push .inTy else acc
        usesWith peel env tgt (d + 1) b acc
    | .forallE _ t b _ =>
        let acc := if t.hasLooseBVar (tgt + d) then acc.push .inTy else acc
        usesWith peel env tgt (d + 1) b acc
    | .letE _ t v b _ =>
        let acc := if t.hasLooseBVar (tgt + d) then acc.push .inTy else acc
        let acc := usesWith peel env tgt d v acc
        usesWith peel env tgt (d + 1) b acc
    | .app .. =>
        let (hd, hside) := peel e
        if hd != e then
          let acc := hside.foldl (fun a x => usesWith peel env tgt d x a) acc
          usesWith peel env tgt d hd acc
        else Id.run do
          let f := e.getAppFn
          let args := e.getAppArgs
          let mut acc := acc
          if f == .bvar (tgt + d) then acc := acc.push .applied
          else acc := usesWith peel env tgt d f acc
          for k in [0:args.size] do
            let (a, side) := peel args[k]!
            for x in side do acc := usesWith peel env tgt d x acc
            if a == .bvar (tgt + d) then
              match f with
              | .const g _ =>
                  if majorOf env g == some k then acc := acc.push (.elim g k)
                  else if projIdx env g == some k then acc := acc.push (.elim g k)
                  else if isCtor env g then acc := acc.push (.field g k)
                  else acc := acc.push (.relay g k)
              | _ => acc := acc.push .bare
            else acc := usesWith peel env tgt d a acc
          return acc
    | _ => acc

/-- Item 225's walk: `usesWith` with nothing peeled. -/
def uses (env : Environment) (tgt : Nat) :
    Nat → Expr → Array Use → Array Use := usesWith noPeel env tgt

/-- The uses of binder `i` of `c`, or `none` when the proof term does not bind
    it (the `ETA` lane). -/
def binderUsesWith (peel : Peel) (env : Environment) (c : Name) (i : Nat) :
    Option (Array Use) := do
  let ci ← env.find? c
  let v ← ci.value? (allowOpaque := true)
  let (_, n) := optBinders ci.type
  guard (i < n)
  let m := min n (lamDepth v)
  guard (i < m)
  let mut body := v
  for _ in [0:m] do
    body := match body with | .lam _ _ b _ => b | x => x
  return usesWith peel env (m - 1 - i) 0 body #[]

def binderUses (env : Environment) (c : Name) (i : Nat) : Option (Array Use) :=
  binderUsesWith noPeel env c i

/-- The verdict: what the binder does inside THIS declaration's own term. -/
def direct (us : Array Use) : String :=
  if us.isEmpty then "UNUSED"
  else if us.any (fun u => match u with
        | .elim .. => true | .applied => true | .projd => true | _ => false)
    then "READ"
  else if us.any (fun u => match u with | .relay .. => true | _ => false)
    then "RELAY"
  else if us.any (fun u => match u with | .field .. => true | _ => false)
    then "FIELD"
  else if us.any (fun u => match u with | .bare => true | _ => false)
    then "RETURN"
  else "TYPE"

def verdictWith (peel : Peel) (env : Environment) (c : Name) (i : Nat) : String :=
  match binderUsesWith peel env c i with | none => "ETA" | some us => direct us

def verdict (env : Environment) (c : Name) (i : Nat) : String :=
  verdictWith noPeel env c i

/-- A hygienic binder name is not a name; print one underscore for all of them
    so a pin does not move when the elaborator renumbers (item 221's lesson). -/
def shownName (n : Name) : String :=
  let s := n.toString
  if (s.splitOn "_@").length > 1 || (s.splitOn "._hyg").length > 1 then "_" else s

/-- Chase a RELAY chain to the sites it terminates at.  The terminal is printed
    verbatim — `KIND@const#idx` — and NOT collapsed into a verdict, because §7
    shows the collapse is not available. -/
partial def chaseWith (peel : Peel) (env : Environment) (fuel : Nat)
    (seen : Std.HashSet String) (c : Name) (i : Nat) : Std.HashSet String :=
  -- Print the USER name: a private-mangled `_private.<module>.0.<name>` makes
  -- `isLibTerminal` read a library terminal as a core one, which moved 13 binders
  -- into the CORE-TERMINAL shortlist.  The `seen` set stays keyed on the RAW name,
  -- because two modules' private declarations can share one user name.
  let kraw := s!"{c}#{i}"
  let k := s!"{Lean.privateToUserName c}#{i}"
  if fuel == 0 then (({} : Std.HashSet String).insert "FUEL")
  else if seen.contains kraw then {}
  else
    let seen := seen.insert kraw
    match binderUsesWith peel env c i with
    | none =>
        if isCtor env c then (({} : Std.HashSet String).insert s!"FIELD@{k}")
        else if isMechanism env c then (({} : Std.HashSet String).insert s!"SPLIT@{k}")
        else (({} : Std.HashSet String).insert s!"ETA@{k}")
    | some us =>
        if us.isEmpty then (({} : Std.HashSet String).insert s!"UNUSED@{k}")
        else Id.run do
          let mut out : Std.HashSet String := {}
          for u in us do
            match u with
            | .elim g j => out := out.insert s!"ELIM@{Lean.privateToUserName c}#{i}>{Lean.privateToUserName g}#{j}"
            | .applied => out := out.insert s!"APPLIED@{k}"
            | .projd => out := out.insert s!"PROJ@{k}"
            | .field g j => out := out.insert s!"FIELD@{Lean.privateToUserName g}#{j}"
            | .bare => out := out.insert s!"RETURN@{k}"
            | .inTy => out := out.insert s!"TYPE@{k}"
            | .relay g j =>
                for t in chaseWith peel env (fuel - 1) seen g j do out := out.insert t
          return out

def chase (env : Environment) (fuel : Nat) (seen : Std.HashSet String)
    (c : Name) (i : Nat) : Std.HashSet String :=
  chaseWith noPeel env fuel seen c i

/-- A terminal inside our own library, as opposed to one inside core. -/
def isLibTerminal (t : String) : Bool :=
  ((t.splitOn "@").getD 1 "").startsWith "L4YAML"

/-- The `Prop` binders of `c`, by index and name. -/
def propBinders (c : Name) : CommandElabM (Array (Nat × Name)) :=
  liftTermElabM do
    let env ← getEnv
    let some ci := env.find? c | return #[]
    Meta.forallTelescope ci.type fun xs _ => do
      let mut out := #[]
      for k in [0:xs.size] do
        let x := xs[k]!
        if ← Meta.isProp (← Meta.inferType x) then
          out := out.push (k, (← x.fvarId!.getDecl).userName)
      return out

/-! ## §2  The calibration

Item 224 measured these sixteen by hand, eight of them by rebuild.  Those eight
are the ground truth: its table reads one READ and seven not, and it had to name
`block_dispatch_deferred`'s mechanism from the error text.  The census
reproduces the split and names the mechanism itself.

The eight LOOSE rows beneath are the other half of item 224's finding and the
census sees it too: four of them DO eliminate their arm — they read the FLAG,
which is the loose arm's whole left disjunct — while the conjunct's one reader
is `colon_fires_implicit_key` alone.  Disjoint readers, from the term. -/

-- 2026-10-21 (item 311): `flowKeyRoute_of_open`'s `h_park` is binder #15 and `flowKeyRoute_of_root`'s #10 — both lemmas
-- take the flow frame's gate `{g : Option ScannerState}` before it (their conclusions carry the frame's named alternative
-- `PackAltG g`); the rows are re-indexed, the verdicts stand (the index is fixed in the table below, the name is printed from it).
-- 2026-10-24 (B3 [66] col-0 threading): `preprocess_flow_thread#9 (h_park)` READ → RELAY: the
-- park is now handed on to the `sp_gram`-stated step frames instead of being destructured here.
def expectedCalibration : List String :=
  [ "FIELD block_dispatch_deferred#5 (h_arm)",
    "RELAY block_dispatch_deferred_stamp_offcol#8 (h_arm)",
    "RELAY block_dispatch_deferred_stamp_nopack#7 (h_arm)",
    "RELAY block_dispatch_deferred_inline#7 (h_arm)",
    "RELAY accum_block_on_closeThenBlock#17 (h_park)",
    "READ colon_fires_implicit_key#11 (h_arm)",
    "RELAY accum_block_on_pendingContent#23 (h_park)",
    "RELAY accum_block_on_pendingBlockContent#25 (h_park)",
    "RELAY accum_block_on_noPending#13 (h_arm)",
    "RELAY accum_content_on_noPending#14 (h_park)",
    "READ flowKeyRoute_of_open#15 (h_park)",
    "RELAY flowKeyRoute_of_root#10 (h_park)",
    "RELAY keyctx_of_preprocess#11 (h_park)",
    "READ landing_or_park_save#6 (h_park)",
    "READ landing_or_park_ska#6 (h_park)",
    "RELAY preprocess_flow_thread#9 (h_park)" ]

run_cmd do
  let env ← getEnv
  let rows : List (Name × Nat × Name) :=
    [ (``block_dispatch_deferred, 5, `h_arm),
      (``block_dispatch_deferred_stamp_offcol, 8, `h_arm),
      (``block_dispatch_deferred_stamp_nopack, 7, `h_arm),
      (``block_dispatch_deferred_inline, 7, `h_arm),
      (``accum_block_on_closeThenBlock, 17, `h_park),
      (``colon_fires_implicit_key, 11, `h_arm),
      (``accum_block_on_pendingContent, 23, `h_park),
      (``accum_block_on_pendingBlockContent, 25, `h_park),
      (``accum_block_on_noPending, 13, `h_arm),
      (``accum_content_on_noPending, 14, `h_park),
      (``flowKeyRoute_of_open, 15, `h_park),
      (``flowKeyRoute_of_root, 10, `h_park),
      (``keyctx_of_preprocess, 11, `h_park),
      (``landing_or_park_save, 6, `h_park),
      (``landing_or_park_ska, 6, `h_park),
      (``preprocess_flow_thread, 9, `h_park) ]
  let got := rows.map (fun (c, i, bn) =>
    s!"{verdict env c i} {c.getString!}#{i} ({bn})")
  if got != expectedCalibration then
    throwError "the CALIBRATION moved.\nexpected:\n{
      String.intercalate "\n" expectedCalibration}\ngot:\n{
      String.intercalate "\n" got}"

/-! ## §3  The module census

`StreamAccum`'s own `Prop` binders, by verdict.  `RELAY` is the majority lane
by a factor of two over `READ`, which is the shape a threaded invariant has and
the reason a spend census could not be a signature census.

`UNUSED` is the lane a reader expects to be full and it is nearly empty — and
the reason is worth recording, because it is not a fact about this library.
Lean's own `unusedVariables` linter already gates it, and seven of the nine
rows are spelled with a leading underscore precisely to silence it.  **The
cheap end of "carried" is already enforced by the toolchain; the expensive end
— threaded and never eliminated — is not, and that is the lane this census
adds.**   `constants` counts the module's non-internal constants, generated ones
    included; it read 1124 on Lean v4.33.0 and 1123 on v4.34.0, which no longer
    generates the derived enum's `FrameTail.toCtorIdx` (see
    `RelaySupplyCensus.expectedTally`). -/

/-- Item 256 moves this line by one binder and two matchers: `h_mono` at
    `accum_block_on_noPending` is a `RELAY` (handed to
    `IndentStackCover.covered_nil_of_ntop`), and the content sibling's `match`
    on `h_closeF_old` with the pattern lambda inside it are two new `match_*`
    constants of the module, whose discriminant and alternative binders are
    all Props and all `READ` (three and two): `constants` 1123 → 1125,
    `decls` 945 → 947, `READ` 1016 → 1021, `RELAY` 1997 → 1998.  Item 257
    moves one binder from `FIELD` to `RELAY`: `h_mono` at
    `accum_block_on_closeThenBlock`, whose one use was inside an `Or.inl ⟨h_mono,
    h_base, …⟩` at the landed arm's floor face, is handed by the compact fill's
    literal to `IndentStackCover.covered_nil_of_top_le`, and a relay outranks a
    field in `direct`; no matcher, so no new constant.  Item 259 moves three:
    `compact_open_map`'s two new binders `h_mono` and `h_top` are each handed
    to `covered_nil_of_top_le` (`RELAY` +2), and its `h_top_in`, whose one use
    was inside the slot's `Or.inl ⟨h_top_in, …⟩`, is now also consumed by the
    `omega` that pins the top (`FIELD` → `RELAY`): `FIELD` 153 → 152, `RELAY`
    1999 → 2002.  The prediction counted the two binders and not the third.

    Item 267 moves the line by thirty-four constants and nothing else.  The
    module's park anchor is split — `ParkCore` carries the four transport
    readings, `ParkAnchor` extends it with the `[96]` property alone, and
    `ParkSlot` extends it with the carrier — so four inherited projections are
    replaced by one parent projection, nineteen constants arrive with the core
    and sixteen with the carrier, and two more are the carrier's source
    (`preprocess_pops_of_below` and `preprocess_landing_on_stack`):
    `constants` 1125 → 1159, of which thirty-two hold a `Prop` binder
    (`decls` 947 → 979).  Every moved lane is the new declarations' own
    (`READ` 1021 → 1047, `RELAY` 2002 → 2084, `eta` 364 → 369); `FIELD`,
    `RETURN` and `UNUSED` do not move, and the `UNUSED` roster below is
    unchanged, which is what says no existing binder changed lane.

    Item 269 restates that source at the landing's own resting floor, as a
    chain of four declarations where item 267's form is two: `constants` 1159
    → 1161 and `decls` 979 → 981 are the two arrivals, both holding a `Prop`
    binder.  The walk is this module's alone — it is taken over the module
    `colon_fires_implicit_key` belongs to — so the one retirement the item
    makes, `unwindIndents_pops` in `Proofs.Scanner.PreprocessIndentStable`, is
    outside it and moves nothing here.  `READ` 1047 → 1048 and `RELAY` 2084 →
    2086 are the same thirteen binders, named: item 267's two declarations
    carry ten `Prop` binders and every one relays; the four carry thirteen —
    one at `landing_on_stack_of_floor_eq`, four at `preprocess_floor_eq`, four
    at each of the two it feeds.  Exactly one is a `READ`,
    `preprocess_floor_eq`'s `h_floor`, because item 147's disjunct is the only
    premise of the chain that is taken apart rather than handed on.  The
    verdicts are read over both forms in one environment by this module's own
    classifier, not compared across two builds
    (`scratchpad/l4yaml-beta5-item269/verdict.out`).

    Item 271 adds `underRunEnd_col_le_currentIndent` and item 272
    `underRunEnd_landing_on_stack`, one declaration each: `constants` 1161 →
    1163, `decls` 981 → 983.  The first holds six `Prop` binders, two of them
    `READ` — `h_floor` and `hcorr`, each projected (`.2`, `.col_eq`) — and four
    `RELAY`.  The second holds nine and every one relays, because the
    declaration IS the composition: three go to
    `preprocess_landing_on_stack` and six to the first.  So `READ` 1048 → 1050
    and `RELAY` 2086 → 2099, with no other lane moving and the `UNUSED` roster
    unchanged (`scratchpad/l4yaml-beta5-item272/verdict.out`).

    Lean v4.35.0 moves ten verdicts and no constant: `eta` 369 → 374, `READ`
    1050 → 1055, `RELAY` 2120 → 2110, with `constants`, `decls`, `FIELD`,
    `RETURN` and the `UNUSED` roster all unchanged.  `verdictWith` reports
    `ETA` when a value's `lamDepth` is under its type's binder count, so the
    five that entered that lane are declarations v4.35.0 elaborates
    eta-shorter, and the five that left `RELAY` for `READ` now appear applied.
    Every NAMED pin held — the fifteen ground-truth rows below, `expectedUnused`
    and `CloseStackCover`'s rosters — so no verdict this census ARGUES moved,
    only its lane totals.  The ten are not named here: naming them needs a
    v4.34.0 olean baseline to diff against and none was kept.  The roster this
    build does emit is
    `scratchpad/l4yaml-435-migration/verdict-roster-435.out`, so the next move
    is diffable. -/
-- 2026-10-17: `constants` 1165 → 1271, `decls` 985 → 1002, `RELAY` 2110 → 2139
-- when the library took `module` headers.  Every other lane held exactly --
-- `eta=374 FIELD=152 READ=1055 RETURN=49 UNUSED=9` -- and the roster says what
-- moved rather than only that something did: diffing
-- `scratchpad/l4yaml-modules/verdict-roster-modules.out` (3778 rows) against the
-- pre-migration `scratchpad/l4yaml-435-migration/verdict-roster-435.out` (3749)
-- gives ZERO rows lost and 29 gained, and all 29 are matcher EQUATION lemmas
-- (`<decl>.match_N.eq_M`, anonymous binders) that `@[expose]` now forces into the
-- environment.  The +106 constants are their declarations plus the ones carrying
-- no Prop binder.  So the denominator grew; no verdict moved.
-- 2026-10-18 (item 281): `constants` 1284 -> 1286 and `RELAY` 2171 -> 2173 when
-- `YamlToken.offersNodeSlot` took its sixth arm, and the roster NAMES both --
-- `scratchpad/l4yaml-r3-carrier/verdict-roster-281.out` (3818 rows) against
-- `scratchpad/l4yaml-modules/verdict-roster-modules.out` (3778).  A match with a
-- catch-all generates one equation per arm plus the catch-all's, so a sixth arm
-- adds `offersNodeSlot.eq_6` and `offersNodeSlot.match_1.eq_6` as ARM equations
-- and renumbers the two catch-alls to `eq_7`; the catch-all carries one
-- excluded-pattern hypothesis per arm, so each gains a `RELAY` binder (5 -> 6)
-- while the two new arm equations carry none.  +2 constants, +2 RELAY, and every
-- other lane and the `UNUSED` roster held exactly.  The equations are named
-- `L4YAML.YamlToken.*` and counted HERE because they are generated on demand,
-- when this module's own `simp` first unfolds the predicate -- which is why an
-- edit to `Token.lean` moves a census scoped to `StreamAccum`.
-- 2026-10-18 (item 284): `constants` 1286 -> 1343, `decls` 1010 -> 1062, and
-- every lane but `UNUSED` moves, with ZERO rows lost.  The roster NAMES it --
-- `scratchpad/l4yaml-row12-steps/verdict-roster-284.out` (3952 rows) against
-- item 281's (3818), compared per declaration with matcher numbering and the
-- private prefix normalized.  The 49 new declarations (the slot face, its gate
-- and their transports) and their auxiliaries bring 124 rows: RELAY 90, READ
-- 28, RETURN 3, FIELD 3.  Existing declarations gain exactly ten: four ETA,
-- the four new park FIELDS (`pendingProps.h_slot` and the three
-- `h_offer`s -- a constructor has no body to read them in), and six RELAY,
-- the gate parameter `h_src` on the six lemmas that hand it on
-- (`content_dispatch_routed`, `content_dispatch_after_close`,
-- `accum_content_on_noPending`, the two `accum_content_on_*_indented`, and
-- `indentedValue_reads_at_any_indent`).  `UNUSED` holds at 9: no hypothesis
-- this item added goes unread.
-- 2026-10-18 (item 285): `constants` 1343 -> 1344, `decls` 1062 -> 1063, `READ`
-- 1086 -> 1088: ONE new constant, the matcher `slot_ride`'s `match h_optok`
-- generates inside `accum_flow_open_depth0`, whose two binders are both read.
-- Roster `scratchpad/l4yaml-row12-steps/verdict-roster-285.out` (3954 rows)
-- against item 284's: those two rows gained, none lost.
-- 2026-10-19 (item 287): `constants` 1344 -> 1356, `decls` 1063 -> 1074, `READ`
-- 1088 -> 1112, `RELAY` 2269 -> 2276, `RETURN` 51 -> 48.  Roster
-- `scratchpad/l4yaml-row12-steps/232-roster-287.out` (3982 rows) against item
-- 285's: 37 rows gained, 9 lost, and every row named.  The line-stop lemmas
-- and `sslComments_refutes_inline_residue`, with their matchers, bring 11
-- declarations (12 constants with `CommentStop`) and 33 rows.  The wrapper
-- reads its premises off the dispatch, so `h_arm`, `h_nodir` and `h_nic0` go
-- and `h_preprocess`, `h_dispatch` come (RELAY either way).  The four
-- `h_stream_fallback`s retire (2 READ, 1 RELAY, 1 RETURN).  And the two
-- `h_punt`s are builders now, so their verdict moves RETURN -> READ -- the
-- only verdict of a surviving binder that moved.
-- 2026-10-19 (item 289): `eta` 380 -> 382, `READ` 1112 -> 1113.  Roster
-- `scratchpad/l4yaml-row12-steps/311-roster-289.out` (3985 rows) against item
-- 287's (item 288 moved no lane): three rows gained, none lost.
-- `KeyPackPunt.tab`'s two new fields, `h_poss` and `h_kline`, are ETA (a
-- constructor has no body to read them in), and `keyPackPunt_transport`'s new
-- premise `h_poss` is READ, in its `tab` case.
-- 2026-10-19 (item 293): `constants` 1356 -> 1364, `decls` 1074 -> 1082, `eta`
-- +5, `FIELD` +1, `READ` +6, `RELAY` +30.  Roster
-- `scratchpad/l4yaml-row12-steps/365-roster-293.out` (4027 rows) against item
-- 289's: 42 rows gained, none lost.  The eight new lemmas are the eight
-- constants and 28 of the rows; the four new park fields (`pendingContent` and
-- `pendingBlockContent`'s `h_live`, `pendingFlow.h_live0`,
-- `pendingProps.h_poss`) are four ETA; and ten are new parameters on existing
-- declarations — `colon_fires_implicit_key.h_live` and `KmSound.push.h_poss_new`
-- READ, `block_dispatch_deferred.h_live0` FIELD (it fills the park's), and the
-- relays (`h_live` at the two block consumers, `h_possD` at the two routed
-- lemmas, `h_live0` at the two stamp wrappers, `km_push_at_open.h_poss_new`).
-- The two narrowed binders change type and keep their verdicts.
-- 2026-10-19 (item 296): `READ` +2, `RELAY` -2 — `entryKeyPack_of_dispatch#9`
-- and `entryPropsKeyPack_of_dispatch#9` (`h_node`), which item 293's roster
-- reads RELAY, are applied at the dedent branch's frameless exit: the awaited
-- entry's empty close (`SBlockNode.emptyNode`).
-- 2026-10-20 (item 297): `constants` 1364 → 1363, `eta` 387 → 386, `RELAY`
-- 2304 → 2302 — `KeyPackPunt.dedent` is deleted, and the roster
-- (`scratchpad/l4yaml-row12-steps/501-roster-297.out` against
-- `365-roster-293.out`: 4027 → 4024 rows) loses exactly its three eliminator
-- rows, `KeyPackPunt.rec#3 (dedent)` ETA, `KeyPackPunt.casesOn#4 (dedent)` and
-- `KeyPackPunt.recOn#4 (dedent)` RELAY; the later minor premises renumber and
-- keep their verdicts.  No other row moves: the deleted alternatives bound
-- nothing, and the `w ∉ ks` exits apply binders the frameless exit already
-- reads (item 296's two `h_node` rows read READ, as pinned).
-- 2026-10-20 (item 299): `constants` 1363 → 1364, `eta` 386 → 387, `RELAY`
-- 2302 → 2301.  The roster (`scratchpad/l4yaml-row12-steps/525-roster-299.out`
-- against `501-roster-297.out`, 4024 rows both) loses the three deleted token
-- walk lemmas' six RELAY binders (`docStartOnLineLoop_hit#3/#4`,
-- `docStartOnLineLoop_skip_ph#3`, `docStartOnLine_of_lastReal#3/#4/#5`) and
-- gains six: `PendingNode.pendingDocStart#11 (h_docline)` ETA, and five RELAY
-- — `dispatch_refutes_sameLine#8 (h_dsl_eq)`, `ad_docStartLine#4/#5`,
-- `dispatchContent_docStartLine#3`, `preprocess_preserves_docStartLine#3`.
-- `dispatch_refutes_sameLine`'s later binders renumber and keep their
-- verdicts; no other row moves.
-- 2026-10-20 (item 300): `constants` 1364 → 1366 (`KeyPackPunt.markerLine`,
-- `flowOpen_marker`), `decls` +2, `eta` 387 → 390, `READ` 1121 → 1125, `RELAY`
-- 2301 → 2314.  The roster (`scratchpad/l4yaml-row12-steps/556-roster-300.out`
-- against `525-roster-299.out`, 4024 → 4044 rows) gains exactly twenty: ETA
-- `KeyPackPunt.markerLine#1 (h_doc)`, `#2 (h_kline)` and `KeyPackPunt.rec#4
-- (markerLine)`; READ `KeyPackPunt.casesOn#5 (markerLine)`,
-- `content_dispatch_routed#26 (h_markerline)`, `KmSound.push#17 (h_marker_new)`
-- and `flowOpen_marker#4 (h_doc)`; RELAY `KeyPackPunt.recOn#5 (markerLine)`,
-- `flowOpen_marker#5 (h_pre)` and `#6 (h_dsl')`, `km_push_at_open#20 (h_dsl')`
-- and `#21 (h_marker_new)`, and the field-equality premises `h_dsl`/`h_dsl'`/
-- `h_dsl_open` of `KmSound.transport`, `colon_transport`, `push`, `pop`,
-- `close_km_pop`, `close_col_of_base`, `keyPackPunt_transport` and
-- `accum_flow_open_depth0`.  Later binders renumber and keep their verdicts;
-- no other row moves.
-- 2026-10-20 (item 303): `constants` 1366 → 1386, `decls` 1084 → 1103, `eta`
-- 390 → 414, `READ` 1125 → 1138, `RELAY` 2314 → 2330 — `KeyFrames`, item 302's
-- value-line resume stack over mixed levels (the inductive with its three
-- constructors and recursors, `KeyFrames.close`, `KeyFrames.ofResumeFrames`,
-- `KeyFrames.resumeAt`), which nothing in the library reads yet.  The roster
-- (`scratchpad/l4yaml-row12-steps/601-roster-303.out` against
-- `556-roster-300.out`, 4044 → 4097 rows) gains exactly the 53 rows of those
-- declarations and nothing else: ETA 24 — `KeyFrames.bottom#1`, `mapLevel#4/#5`,
-- `seqLevel#4/#5`, `rec#4–#7`, and the structural-recursion auxiliaries
-- `below#1`, `below.bottom#1`, `below.mapLevel#…` ×4, `below.seqLevel#…` ×4,
-- `below.rec#…` ×5; READ 13 — `casesOn` ×3, `below.casesOn` ×3, `brecOn#…`,
-- and the `match_1` auxiliaries of `close` ×2, `ofResumeFrames` ×2,
-- `resumeAt` ×2; RELAY 16 — `recOn` ×4, `casesOn#…`, `below.casesOn` ×2,
-- `brecOn#…`, `close#…`, `ofResumeFrames#…`, `resumeAt` ×2 and the three
-- `match_1` auxiliaries ×1/×1/×2.  No existing row moves or renumbers.
-- 2026-10-20 (item 304): `constants` 1386 → 1388, `decls` 1103 → 1105 (the
-- route helpers' `KeyFrames` twins `resumeFrameRouteK`, `resumeMapRouteK`),
-- `FIELD` 158 → 163, `READ` 1138 → 1144, `eta`/`RELAY` unchanged — the
-- value-line stacks are `KeyFrames` (item 302's stack).  The roster
-- (`scratchpad/l4yaml-row12-steps/611-roster-304.out` against
-- `601-roster-303.out`, 4097 → 4108 rows) gains exactly eleven rows and loses
-- none: FIELD `resumeFrameRouteK#5 (h_ind)`, `#8 (_)`, `resumeMapRouteK#5
-- (h_ind)`, `#8 (_)`, `#10 (_)` — the twins' indent premise and conclusion
-- binders; READ `resumeFrameRouteK#6 (h_frames)`, `resumeMapRouteK#6
-- (h_frames)`, and the `h_2` binder of the four `match_1` auxiliaries
-- (`entryKeyPack_of_dispatch.match_1_14/_18`, `entryPropsKeyPack_of_dispatch
-- .match_1_12/_16`) that split `KeyFrames.resumeAt`'s sum at the two key-pack
-- lemmas' value-line resumes.  No existing row moves or renumbers.
-- 2026-10-20 (item 307): `constants` 1388 → 1392, `decls` 1105 → 1109, `READ` 1144 → 1154 — `closeThenBlock`'s three new
-- haves (`h_resSeqV`, `h_resKslot`, `h_slotV'`) and their match auxiliaries; the γ roots read `h_closeFV_old`/`h_mapFV108`.
-- 2026-10-20 (item 307, second chain): `constants` 1392 → 1393, `decls` 1109 → 1110, `READ` 1154 → 1160, `RELAY` 2330 → 2329 — the three relays are `match`es
-- (one more auxiliary, one more read each; the `.imp` relay gone).
-- 2026-10-20 (item 309): `constants` 1393 → 1398, `decls` 1110 → 1114, `READ` 1160 → 1161, `RELAY` 2329 → 2337 — `ExplicitValueRefused`, the three sentinel
-- lemmas and the refutation; the generic helpers relay their alternative.
-- 2026-10-21 (item 311): `constants` 1398 → 1403, `decls` 1114 → 1117, `UNUSED` 9 → 12 — the named alternative's two
-- abbrevs and three stubs (`PackAlt.ofRefused`, `PackAltG.ofPark`, `PackAlt.ofGateClose`), each stub's `_h` unused by
-- construction until its lane proves it.
-- 2026-10-21 (item 313): `constants` 1403 → 1405, `decls` 1117 → 1119, `READ` +1, `RELAY` +2, `UNUSED` 12 → 15 —
-- `ExplicitValueRefused.step_content` (reads its predicate, relays the two step facts) and `PackAlt.step_content`, whose
-- three binders are unused until the promise after `-- refused:` is its body.
-- 2026-10-21 (item 314): `constants` 1405 → 1407, `decls` 1119 → 1121, `READ` +1, `RELAY` +1, `UNUSED` 15 → 17 — the
-- dispatch-only transport and its promised wrapper (two unused binders until the promise is its body).
-- 2026-10-21 (item 315): `RELAY` 2340 → 2341 — `entryPropsKeyPack_of_dispatch`'s `h_dispatch`, relayed to the step lemma.
-- 2026-10-21 (item 318): `constants` 1407 → 1408, `decls` 1121 → 1122, `READ` 1163 → 1161, `RELAY` 2341 → 2343,
-- `UNUSED` 17 → 24 — the block lane's two transports and their two wrappers (+4) less item 309's three indent lemmas (−3);
-- `not_of_classA` lost its indent premise and the two content transports hand `h` on whole (one register equation each)
-- where they destructured it; the seven `_`-binders of `PackAlt.step_blockEntry` and `PackAlt.step_value` are the new UNUSED.
-- 2026-10-21 (item 320): `constants` 1408 → 1409, `decls` 1122 → 1123, `eta` 414 → 416, `READ` 1161 → 1166 — the marker
-- constructors' new field `h_noek` (read at the eight `PackAlt.ofRefused` payments and the two probes), the two split
-- arms' `h_alt`, and the `h_seqFramesV` relay's wrapper; RELAY, RETURN and UNUSED stand.
-- 2026-10-21 (item 322): `READ` 1166 → 1168 — the two colon openers' new step premise `h_alt_step` is applied inside each
-- (a READ); the callers' `PackAlt.step_value …` arguments are terms, not hypotheses, so RELAY stands.
-- 2026-10-21 (item 324): `constants`/`decls` +2, `RELAY` 2343 → 2345, `UNUSED` 24 → 26 — `ExplicitValueRefused.step_preprocess`
-- relays its two hypotheses into the preprocess register lemma; its wrapper `PackAlt.step_preprocess` holds the same two unused
-- (`trivial` while `PackAlt` is `True`, the promise after `-- refused:`), like the family's four other wrappers.
-- 2026-10-23 (item 344): constants/decls +1 (the `match` on `h_closeFV_old` behind the relayed `h_valFV`), READ 1162 → 1165
-- (the relays read `h_closeFV_old`, `h_sep_p`, `h_run`).
-- 2026-10-23 (item 345): constants/decls +1, READ +3 — the `h_kslotUp` singleton relays' tactic block compiles to one
-- auxiliary declaration and reads three more hypotheses.
-- 2026-10-23 (item 349): constants 1420 → 1424, decls 1130 → 1132, READ 1168 → 1169, RELAY 2372 → 2383 —
-- the two dispatch bridges and `h_sound`/`h_dead` relayed through the seven content-step lemmas.
-- 2026-10-24 (B3 [66] col-0 threading): +160 decls (JSON-key carry, reservation transport, gate
-- lemmas); UNUSED 26 → 27 (`gate_of_peek#3`, `park_gate_of_peek#2`; `question_open_map`'s `_h_noflow_disp` is now spent), see `expectedUnused`.
-- 2026-10-26 (item 367, `[82]`): `SSLComments_prepend_comment`, `directiveTail_prepend_SSLComments`, `scannedDirective_toSL` join StreamAccum: decls 1317 → 1320, READ +3, RELAY +6, FIELD +1.
-- 2026-10-26 (item 369): READ 1313 → 1314 — `accum_block_on_pendingBlock` reads `h_closeF_old` (the `-` park's frames)
-- at the `:`/`?` landing for `indicator_open_map`'s `h_res_land`.
-- 2026-10-26 (item 370): constants 1681 → 1682, decls 1320 → 1321 (the sibling `-` arm's `match h_closeF_old` auxiliary),
-- READ 1314 → 1317 — `h_closeF_old`, `h_node_old` and the cover read once more at the re-park.
def expectedModuleTally : String :=
  -- 2026-10-26 (item 365): RELAY 2830 → 2836 — `h_sound` ×3, `h_fl0` ×2 and `h_alt` ×1 passed whole from
  -- `accum_step_content`/`accum_content_pending`/the `_indented` pair to the content lane's payers.
  -- 2026-10-24 (item 350): constants 1424 → 1430, decls 1132 → 1137, READ 1169 → 1171,
  -- RELAY 2383 → 2388 — `NotQuestionPark`, `notQuestion_push_top`, `scanValue_notQuestion`,
  -- `dispatchBlock_colon_notQuestion` and `explFrameValueLine`'s split alternative.
  -- 2026-10-26 (item 366): RELAY 2836 → 2838 — `h_sound` passed whole into the two new `Sound sc` binders.
  -- 2026-10-27 (item 371): constants/decls +1, READ +1 — `ResumeFrames.one` (its `h_tail` is read once).
  "constants=1701 decls=1338 eta=442 FIELD=168 READ=1357 RELAY=2862 RETURN=54 \
UNUSED=27"
-- 2026-10-25 (#112 review): the `FlowStackK` `MarkedColsIn` carrier reverted (Rule 8: a projection of the closed state is decided at the close by `Classical.em`); the two transport helpers and `h_pk'` go (constants 1683 → 1681, decls 1322 → 1320, READ 1325 → 1323, RELAY 2838 → 2830); `Mono sc` stays on `accum_step_flow`.
-- 2026-10-25 (item 363): the flow OPEN lane read off the block state (`h_refused`, one `Classical.em`; five `match` blocks deleted): the five deleted `match` auxiliaries: constants 1681 → 1676, decls 1320 → 1315, READ 1323 → 1306.

-- 2026-10-21 (item 311): `flowKeyPack_of_close`'s unused `_` is binder #11 (`{g}` precedes it); the three conversion stubs
-- (`PackAlt.ofRefused`, `PackAltG.ofPark`, `PackAlt.ofGateClose`) leave their `_h` unused until their lanes prove them.
-- 2026-10-21 (item 318): seven rows added — `PackAlt.step_blockEntry`'s `_h_preprocess`/`_h_dispatch`/`_h` (#3–#5: three
-- implicit states precede them, where `step_content` also has `{c}`) and `PackAlt.step_value`'s four (#3–#6, `_h_noflow` among
-- them); regenerated from the census's own `got` rows.
-- 2026-10-21 (item 324): two rows added — `PackAlt.step_preprocess`'s `_h_preprocess`/`_h` (#3–#4: two implicit states and
-- `{c}` precede them), unused while its promise is not yet its body, like the family's other wrappers; rows from the guard's `got`.
def expectedUnused : List String :=
  -- Item 287: the wrapper reads its premises off the dispatch, so `_h_res` is
  -- its thirteenth binder.
  [ "block_dispatch_deferred_inline#12 (_h_res)",
    "block_dispatch_deferred_stamp_nopack#10 (_h_src)",
    "block_dispatch_deferred_stamp_nopack#11 (_h_indent)",
    "block_dispatch_deferred_stamp_nopack#12 (_h_park)",
    "block_dispatch_deferred_stamp_offcol#11 (_h_src)",
    "block_dispatch_deferred_stamp_offcol#12 (_h_indent)",
    "block_dispatch_deferred_stamp_offcol#13 (_h_ne)",
    "flowKeyPack_of_close#11 (_)",
    "gate_of_peek#3 (_)",
    "ofGateClose#2 (_h)",
    "ofPark#2 (_h)",
    "ofRefused#1 (_h)",
    "park_gate_of_peek#2 (_)",
    "step_blockEntry#3 (_h_preprocess)",
    "step_blockEntry#4 (_h_dispatch)",
    "step_blockEntry#5 (_h)",
    "step_content#4 (_h_preprocess)",
    "step_content#5 (_h_dispatch)",
    "step_content#6 (_h)",
    "step_dispatch#3 (_h_dispatch)",
    "step_dispatch#4 (_h)",
    "step_preprocess#3 (_h_preprocess)",
    "step_preprocess#4 (_h)",
    "step_value#3 (_h_preprocess)",
    "step_value#4 (_h_dispatch)",
    "step_value#5 (_h_noflow)",
    "step_value#6 (_h)" ]

run_cmd do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? ``colon_fires_implicit_key
  let mut names : Array Name := #[]
  for (nm, _) in env.constants.toList do
    -- Filter on the USER name, not the raw one.  Since the library took `module`
    -- headers its generated auxiliaries are private, so their real names read
    -- `_private.<module>.0.<name>`; such a name starts with `_`, so `isInternal`
    -- is true for it and the L4YAML prefix test fails.  Filtering the raw name
    -- therefore DISCARDS them -- `constants` read 959 instead of 1165 -- while the
    -- declarations are still in the environment.
    --
    -- `authoredPrivate` is the other half: the module system privatises GENERATED
    -- auxiliaries, and recovering those is the point, but a declaration the author
    -- wrote `private` was mangled before the migration too and this census never
    -- counted it.  Recovering that one as well would widen what the instrument
    -- reports about the library's surface, so it stays excluded.
    let un := Lean.privateToUserName nm
    if un.isInternal then continue
    if Lean.isPrivateName nm && !un.isInternalDetail then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    names := names.push nm
  let mut tally : Std.HashMap String Nat := {}
  let mut unused : Array String := #[]
  let mut eta := 0
  let mut decls := 0
  for c in names do
    let pbs ← propBinders c
    if pbs.isEmpty then continue
    decls := decls + 1
    for (i, bn) in pbs do
      match binderUses env c i with
      | none => eta := eta + 1
      | some us =>
          let d := direct us
          tally := tally.insert d ((tally.getD d 0) + 1)
          if d == "UNUSED" then
            unused := unused.push s!"{c.getString!}#{i} ({shownName bn})"
  let body := String.intercalate " " ((tally.toList.mergeSort
    (fun a b => a.1 < b.1)).map (fun (k, v) => s!"{k}={v}"))
  let got := s!"constants={names.size} decls={decls} eta={eta} {body}"
  if got != expectedModuleTally then
    throwError "the MODULE CENSUS moved.\nexpected: {expectedModuleTally}\ngot:      {got}"
  let gotU := (unused.qsort (· < ·)).toList
  if gotU != expectedUnused then
    throwError "the UNUSED lane moved.\nexpected ({expectedUnused.length}):\n{
      String.intercalate "\n" expectedUnused}\ngot ({gotU.length}):\n{
      String.intercalate "\n" gotU}"

/-! ## §4  The optional contexts, read rather than supplied

Items 212–218 censused the `_ ∨ True` premises by SUPPLY — who pays, who
declines, what relays.  Nothing there asked who READS one when it is paid, and
this is that census over the same population, with the matcher auxiliaries that
inherit their parents' binders filtered out so the denominator is declarations. -/

-- Item 287: `accum_block_on_closeThenBlock`'s `h_vslot` is no longer a
-- `_ ∨ True` (a READ one), so it leaves the population.  Item 288: nor is
-- `PendingNode.pendingMapValue.h_vslot` (a constructor field, read ETA).
-- Item 300: two more optional contexts, both READ — `content_dispatch_routed`'s
-- `h_markerline` (cased in both cascades) and `km_push_at_open`'s
-- `h_marker_new` (applied to the base-open premise).
-- 2026-10-20 (item 307): `READ` 86 → 87, `RELAY` 44 → 43 — `accum_block_on_pendingContent`'s `h_mapFV108` is READ
-- (a `match`) where it was RELAYed.
-- 2026-10-24 (item 350): total 163 → 159, ETA 33 → 31, READ 87 → 85 — the `h_expl`/`h_explUp`
-- `inr` arms no longer read their alternative (they pay an empty chain instead).
-- 2026-10-26 (item 369): total=165 → total=166, READ=88 → READ=89 — `accum_block_on_pendingBlock.h_closeF_old`
-- (the `-` park's frames, read by the `:`/`?` landing for `h_res_land`).
def expectedOptTally : String := "total=166 ETA=31 READ=91 RELAY=44"

/-- The six item 212 enumerated, by verdict — seven since item 300.  Six are
    read in `content_dispatch_routed`'s own term (`h_markerline`, the marker
    reason's payload, cased in both cascades); `h_ref` alone relays, and §5
    says where it lands. -/
def expectedContentDispatch : List String :=
  [ "READ content_dispatch_routed#18 (h_keyctx)",
    "READ content_dispatch_routed#20 (h_suffixctx)",
    "READ content_dispatch_routed#21 (h_nodocctx)",
    "READ content_dispatch_routed#22 (h_markerctx)",
    "RELAY content_dispatch_routed#24 (h_ref)",
    "READ content_dispatch_routed#25 (h_propsctx)",
    "READ content_dispatch_routed#26 (h_markerline)" ]

run_cmd do
  let env ← getEnv
  let mut tally : Std.HashMap String Nat := {}
  let mut total := 0
  for (nm, ci) in env.constants.toList do
    let un := Lean.privateToUserName nm
    if un.isInternal then continue
    if Lean.isPrivateName nm && !un.isInternalDetail then continue
    if !(`L4YAML).isPrefixOf un then continue
    if (`L4YAML.Tests).isPrefixOf un then continue
    if isMechanism env nm then continue
    for (i, _) in (optBinders ci.type).1 do
      total := total + 1
      let v := verdict env nm i
      tally := tally.insert v ((tally.getD v 0) + 1)
  let body := String.intercalate " " ((tally.toList.mergeSort
    (fun a b => a.1 < b.1)).map (fun (k, v) => s!"{k}={v}"))
  let got := s!"total={total} {body}"
  if got != expectedOptTally then
    throwError "the OPTIONAL-CONTEXT census moved.\nexpected: {expectedOptTally}\ngot:      {got}"
  let rows := (optBinders (env.find? ``content_dispatch_routed).get!.type).1
  let gotC := rows.toList.map (fun (i, bn) =>
    s!"{verdict env ``content_dispatch_routed i} content_dispatch_routed#{i} ({bn})")
  if gotC != expectedContentDispatch then
    throwError "content_dispatch_routed's contexts moved.\nexpected:\n{
      String.intercalate "\n" expectedContentDispatch}\ngot:\n{
      String.intercalate "\n" gotC}"

/-! ## §5  The chase, and the nine premises ~~it cannot land in the library~~
    **a PIPE-BLIND chase cannot land**

~~Of the forty-four relayed optional premises, nine reach no elimination inside
`L4YAML` at all: every terminal of their chase is a core combinator.  That is
NOT a verdict of "carried" — §7 is why — but it is the shortlist, and it is
where a reader looking for a carried premise should look first.~~

**Item 226: the shortlist is a measurement of THIS walk's blind spot, not of
the library.**  `chase` here runs at `noPeel`, and five of the nine terminate
at `Or.imp#6` or at an over-applied `Eq.ndrec` — both PIPES, both named by item
213 and both seen through by the supply census since item 215.  With the same
`pipeArg` list peeled, ALL NINE land, and two of them land on a LIBRARY
elimination, which is exactly what the struck sentence denied.  The nine rows
below are kept and still pinned, because a blind spot that is pinned at a
number is one a later walk can be held against; `Tests.Guards.PremiseNecessityCensus`
pins where each of them actually goes.

`h_ref` is deliberately not on it.  Its chase lands twice in the library, at
`rootMapRoute_or_refused` and `rootMapRouteF_or_refused` — two of item 183's
five flip definitions — where the left disjunct is spent to refute the
`h_op = false` branch outright.  A premise read only in refutation is exactly
the shape item 224 found at the arm's one reader, one workstream over.  (Its
third terminal, `SPLIT@Eq.ndrec#9`, is the pipe: item 226 peels it and two
remain.) -/

-- 2026-10-24 (B3 [66] col-0 threading): binder indices shift with the new park fields.
-- 2026-10-28 (item 380, PR #146 review): 11 → 9 — `colon_open_map_explicit#21` and `compact_open_map#29` (both
-- `h_outer`) leave the shortlist: their chase ended at a `Classical.em … |>.elim` terminal, which is a two-arm
-- split now (`RelaySupplyCensus.isTwoArm`), i.e. a READ at the site and no terminal at all.
def expectedCoreTerminal : List String :=
  -- Item 287: the three `accum_block_on_*` rows read two binders earlier, past
  -- the retired `sp_block_ctx` and `h_stream_fallback`.
  [ "accum_block_on_pendingBlock#29 (h_seqF_old)",
    "accum_block_on_pendingBlockContent#34 (h_seqF_old)",
    "accum_block_on_pendingContent#33 (h_seqF168)",
    "accum_content_on_pendingMapValue_indented#14 (h_ncol_old)",
    "colon_open_map#24 (h_cov_in)",
      "flowKeyRoute_of_root#24 (h_tail143)",  -- item 311: `{g}` precedes it
    "indicator_open_map#26 (h_ref_land)",
    "question_open_map#23 (h_cov_in)",
    "question_open_map#24 (h_cov_nil)" ]

/-- Where `h_ref` is eliminated, named. -/
def expectedRefTerminals : List String :=
  [ "ELIM@L4YAML.Proofs.StreamAccum.rootMapRouteF_or_refused#7>L4YAML.Proofs.StreamAccum.rootMapRouteF_or_refused.match_1_1#4",
    "ELIM@L4YAML.Proofs.StreamAccum.rootMapRoute_or_refused#7>L4YAML.Proofs.StreamAccum.rootMapRoute_or_refused.match_1_1#4",
    "SPLIT@Eq.ndrec#9" ]

run_cmd do
  let env ← getEnv
  let mut core : Array String := #[]
  for (nm, ci) in env.constants.toList do
    let un := Lean.privateToUserName nm
    if un.isInternal then continue
    if Lean.isPrivateName nm && !un.isInternalDetail then continue
    if !(`L4YAML).isPrefixOf un then continue
    if (`L4YAML.Tests).isPrefixOf un then continue
    if isMechanism env nm then continue
    for (i, bn) in (optBinders ci.type).1 do
      if verdict env nm i != "RELAY" then continue
      let ts := chase env 30 {} nm i
      if ts.toList.all (fun t => !isLibTerminal t) then
        core := core.push s!"{nm.getString!}#{i} ({shownName bn})"
  let got := (core.qsort (· < ·)).toList
  if got != expectedCoreTerminal then
    throwError "the CORE-TERMINAL shortlist moved.\nexpected ({expectedCoreTerminal.length}):\n{
      String.intercalate "\n" expectedCoreTerminal}\ngot ({got.length}):\n{
      String.intercalate "\n" got}"
  let refT := (chase env 30 {} ``content_dispatch_routed 24).toList.mergeSort
    (fun a b => a < b)
  if refT != expectedRefTerminals then
    throwError "h_ref's terminals moved.\nexpected:\n{
      String.intercalate "\n" expectedRefTerminals}\ngot:\n{
      String.intercalate "\n" refT}"

/-! ## §6  The premise no census of terms can price

R3's remaining debt is seven PRODUCTIONS of two `KeyPackPunt` reasons, and the
reader census does not apply to them — not because the instrument is short, but
because the reasons carry nothing.  `dedent` and `noKeyContext` are nullary, so
the type is inhabited at every state, so a premise of that shape constrains
nothing and a consumer that takes one proves its conclusion without it.  (Item
297 deletes `dedent`; `noKeyContext` keeps the type inhabited, and the point
stands.)

**A premise has no reader for two different reasons, and only one of them is
about proofs.** -/

/-- The two unpayable reasons are argument-free; the two payable ones are not. -/
def expectedPuntFields : String :=
  -- Item 289: `tab` carries the saved key's possibility and line beside the
  -- scan's reading and the park's flags.  Item 297: `dedent` is deleted.
  -- Item 300: `markerLine` carries the field read and the key's line.
  "tab=4 implicitValue=3 markerLine=2 noKeyContext=0"

run_cmd do
  let env ← getEnv
  let got := String.intercalate " " ([``KeyPackPunt.tab,
      ``KeyPackPunt.implicitValue, ``KeyPackPunt.markerLine, ``KeyPackPunt.noKeyContext].map (fun c =>
    match env.find? c with
    | some (.ctorInfo cv) => s!"{c.getString!}={cv.numFields}"
    | _ => s!"{c.getString!}=?"))
  if got != expectedPuntFields then
    throwError "KeyPackPunt's field counts moved.\nexpected: {
      expectedPuntFields}\ngot:      {got}"

/-- **`KeyPackPunt sc` is inhabited at every state.**  This is the whole of R3's
    seven productions as a proposition: while ~~`dedent`~~ `noKeyContext` stands
    (`dedent` went at item 297), producing one is free. -/
lemma punt_is_unconditional (sc : ScannerState) : KeyPackPunt sc := .noKeyContext

/-- …so a consumer that takes a punt as a premise proves its goal without it. -/
lemma punt_premise_buys_nothing {sc : ScannerState} {P : Prop}
    (k : KeyPackPunt sc → P) : P := k (punt_is_unconditional sc)

/-- …and the same for the disjunction the productions actually hand over, which
    is the shape item 223's §3 exhibited at one call site and this states for
    every consumer there will ever be. -/
lemma punt_disjunct_buys_nothing {sc : ScannerState} {A P : Prop}
    (k : A ∨ KeyPackPunt sc → P) : P := k (Or.inr (punt_is_unconditional sc))

/-! ## §7  What ~~the census~~ **a pipe-blind census** cannot decide, exhibited

A `RELAY` chase terminates inside the callee.  Two relays with the same
terminal can be opposite things: `Or.elim` hands the decision back to the
caller's own alternatives, so the caller READS; `Or.imp_left` rebuilds a weaker
disjunction and decides nothing.  Both are an argument to a constant at the
call site, and both are eliminated by `Or.casesOn` one hop on.

The pin below states that the census gives them the same verdict.  That is the
limit, machine-exhibited: a terminal-based reading of the chase would call the
re-statement a read, which is why §5 publishes terminals and stops.

~~…which is why the `RELAY` lane's rows are a shortlist and not a verdict.~~
**Item 226 decided it, and the answer was already in the repo.**  `Or.imp_left`
is a PIPE; peel it and `restates_by_imp` reads `RETURN` — the premise IS the
conclusion, weakened — while `reads_by_elim` still reads `RELAY` into a
constant that eliminates.  The two exhibits below are kept and still pinned at
the SAME verdict, because that pin is what says this walk is the blind one;
`PremiseNecessityCensus` pins them apart.

**Item 380 (PR #146 review) told them apart here too.**  `Or.elim` is a two-arm
SPLIT for the supply walker now (`RelaySupplyCensus.isTwoArm`: the site decides,
on the disjunction's two arms), so `reads_by_elim` READS its premise — the
`Or.elim` is the site's own `casesOn` — while `restates_by_imp` still RELAYS it
into the pipe.  The pin keeps both verdicts, now different: the blind spot this
section exhibited is closed on the `elim` side and open on the `imp` side. -/

lemma reads_by_elim {a b c : Prop} (h : a ∨ b) (f : a → c) (g : b → c) : c :=
  h.elim f g

lemma restates_by_imp {a b c : Prop} (h : a ∨ b) (f : a → c) : c ∨ b :=
  h.imp_left f

-- 2026-10-28 (item 380, PR #146 review): `reads_by_elim#3` RELAY → READ — `Or.elim` is a two-arm split.
def expectedIndistinguishable : String :=
  "reads_by_elim#3=READ restates_by_imp#3=RELAY"

run_cmd do
  let env ← getEnv
  let got := s!"reads_by_elim#3={verdict env ``reads_by_elim 3} restates_by_imp#3={
    verdict env ``restates_by_imp 3}"
  if got != expectedIndistinguishable then
    throwError "§7's two relays moved (item 380 reads the `elim` side, the `imp` side stays blind).\nexpected: {
      expectedIndistinguishable}\ngot:      {got}"

end Tests.Guards.HypothesisReaderCensus
