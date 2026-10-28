import Tests.Guards.Proofs.HypothesisReaderCensus

/-!
# The necessity census: a premise that is READ is not thereby NEEDED (item 226)

Item 225 closed with the lane it found and did not spend: **`RELAY` is 1997
binders in `StreamAccum` alone and nothing gates it**, and §5's nine-row
core-terminal shortlist was named "the first place one would look for a premise
that could simply be dropped".  This item went there.  Nothing in that lane is
droppable, the shortlist was an artifact of the walk that made it, and the
premises that ARE free are free for a reason no census of terms can see — the
same reason item 225 proved for `KeyPackPunt` and never applied to the
population it had just measured.

## Three instruments, in the order they were needed

**1.  The walk was pipe-blind.**  Item 213 named `Or.imp` and `Eq.ndrec` PIPES
— they carry a decision and make none — and item 215's `peelPipe` taught the
SUPPLY census to see through them.  The reader census never got that list, so
`uses` stopped at `Or.imp#6` and at an over-applied `Eq.ndrec` and reported the
pipe.  §1 peels them with the SAME `pipeArg`, and nothing is discarded: a
pipe's other arguments go on a side list and are walked, so no occurrence can
vanish into the peel.

Peeled, item 225's pins move and its two disputed sections resolve:

| | item 225 | here |
|---|---|---|
| module tally | `FIELD=154 READ=1016 RELAY=1997 RETURN=48` | `FIELD=172 READ=1052 RELAY=1864 RETURN=127` |
| optional tally | `total=163 ETA=34 READ=85 RELAY=44` | `ETA=34 FIELD=4 READ=85 RELAY=38 RETURN=2` |
| §5's shortlist | 9 rows | **0** — all nine land, two on a LIBRARY elimination |
| `h_ref`'s terminals | 3 | **2** — the third was the pipe |
| §7's two exhibits | `RELAY` / `RELAY` | `RELAY` / **`RETURN`** |

The calibration against item 224's eight REBUILDS is **unchanged**, and so is
`content_dispatch_routed`'s six and the nine-row `UNUSED` lane — so the peel
moves what a pipe was hiding and nothing else.

**2.  The dead-parameter fixpoint** (§5): the least fixpoint of ALIVE over the
relay graph.  A binder is ALIVE if it is eliminated, applied, projected, stored
in a constructor, returned, or named in a later binder's TYPE — that last one
is a check a census does not need and a DROP does — and a relay is ALIVE iff
its target is.  DEAD is therefore a sound under-approximation.  Over every
`Prop` binder of `StreamAccum` and every `_ ∨ True` binder in `L4YAML`, 4266
nodes: **ten are dead and every one of them is `UNUSED`.  The `RELAY` lane has
none.**

**3.  The substitution probe** (`scripts/decline_all_optional.py`): replace a
binder's uses with the canonical inhabitant of its type and rebuild.  For
`A ∨ True` that inhabitant is `Or.inr trivial`, so the probe is available for
the whole optional population — and **all 119 of `StreamAccum`'s optional
premises that live in a tactic proof can be declined AT ONCE, in one build,
with zero errors**, after which Lean's own `unusedVariables` linter names 95 of
them.  The probe's whole content is that it converts the ungated `RELAY` lane
into the gated `UNUSED` one and lets the toolchain answer.

## The rule this item adds

**A premise that is READ is not thereby NEEDED.**  `READ` measures what a proof
DOES with a binder; necessity is a question about the lemma's STATEMENT, and
for `A ∨ True` the statement answers it alone: the type is unconditionally
inhabited, so `opt_premise_buys_nothing` discharges it in one line and all 163
optional contexts — **85 of them `READ`** — buy nothing today.  Item 225 proved
exactly this for `KeyPackPunt` and stopped there.  (**165**, corrected at item
227: two more hide behind `ResumeKeyCtx`, and the lemma covers those too — see
`Tests.Guards.NarrowingWorthCensus` §6.)

## And the ten dead ones are not droppable either

Read in source they are three kinds, and none is a premise carried by accident:

* **class markers, 7.**  `block_dispatch_deferred_stamp_offcol`,
  `…_stamp_nopack` and `…_inline` have ONE call in the body —
  `block_dispatch_deferred …` — and the premise the body does not read is the
  only thing that says which dispatch class the site is in.  Item 187's own
  comment records `_h_park` as placed LAST "so the existing applications'
  positional arguments still bind".  Dropping them would not simplify the
  library; it would delete the taxonomy and merge three lemmas back into one.
* **family uniformity, 2.**  `h_noflow_disp` is a premise of six sibling
  openers and five of them use it; `scanTagDirective_corr`'s `_hcorr` is the
  `*_corr` family's shared leading triple.
* **the conclusion's own binder, 1.**  `flowKeyPack_of_close`'s `intro _` takes
  `sc.simpleKey.possible = true` out of the CONCLUSION, whose shape is fixed by
  the obligation the lemma discharges.

**An underscore silences the linter; it does not justify the premise.**  Seven
of these nine carry one, and the justification is in none of them — it is in
the body's shape, in a sibling's signature, and in the conclusion.

## Nothing is spent, and that is the answer

The 163 optional contexts are the NARROWING SURFACE: items 212–218 built a
supply census precisely to price replacing `∨ True` with the bare premise, and
item 218 recorded that "a `PAY` is an answer about the PROOF, and it does not
promise the site survives a narrowing."  Dropping a vacuous premise today
deletes the slot the narrowing lands in.  The mandate asked which premise could
simply be dropped; the measured answer is that the lane it pointed at has none
and the lane that does is one the plan is holding open on purpose.
-/

namespace Tests.Guards.PremiseNecessityCensus

set_option autoImplicit false

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs

open Lean Elab Command
open L4YAML.Tests.Guards.RelaySupplyCensus
open Tests.Guards.HypothesisReaderCensus

/-! ## §1  The pipe peel

`pipeArg` is item 214's list and `arityOf` item 215's; neither is re-typed
here.  Two rules, and both keep everything:

* a SATURATED pipe IS its carrier, and the pipe's other arguments go on the
  side list;
* an OVER-APPLIED pipe transports a FUNCTION, so `P … m … x₁ … xₙ` becomes
  `m x₁ … xₙ` (head-beta'd) with the pipe's own arguments on the side list.

The side list is what makes the peel safe: a binder occurring inside the `f` of
`Or.imp f g h` is still walked, so the peel can move a verdict and cannot
invent an `UNUSED`. -/

/-- Peel saturated pipes; `side` collects what the peel stepped over. -/
partial def peelSat (env : Environment) (e : Expr) (side : Array Expr) :
    Expr × Array Expr :=
  match e with
  | .mdata _ b => peelSat env b side
  | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      match f with
      | .const g _ =>
          match pipeArg g with
          | some i =>
              if i < args.size && args.size == arityOf env g then
                let side := (List.range args.size).foldl
                  (fun (acc : Array Expr) k => if k == i then acc else acc.push args[k]!) side
                peelSat env args[i]! side
              else (e, side)
          | none => (e, side)
      | _ => (e, side)
  | _ => (e, side)

/-- An over-applied pipe transports a function: rewrite to what it transports
    applied to the trailing arguments. -/
def peelOver (env : Environment) (e : Expr) : Option (Expr × Array Expr) :=
  let f := e.getAppFn
  let args := e.getAppArgs
  match f with
  | .const g _ =>
      match pipeArg g with
      | some i =>
          let ar := arityOf env g
          if i < args.size && ar < args.size then
            let side := (List.range ar).foldl
              (fun (acc : Array Expr) k => if k == i then acc else acc.push args[k]!) #[]
            some ((mkAppN args[i]! (args.extract ar args.size)).headBeta, side)
          else none
      | none => none
  | _ => none

/-- Item 226's peel, for `usesWith`. -/
def pipePeel (env : Environment) : Peel := fun e =>
  match peelOver env e with
  | some (e', side) => (e', side)
  | none => peelSat env e #[]

def verdictP (env : Environment) (c : Name) (i : Nat) : String :=
  verdictWith (pipePeel env) env c i

def binderUsesP (env : Environment) (c : Name) (i : Nat) : Option (Array Use) :=
  binderUsesWith (pipePeel env) env c i

def chaseP (env : Environment) (fuel : Nat) (c : Name) (i : Nat) : Std.HashSet String :=
  chaseWith (pipePeel env) env fuel {} c i

/-! ## §2  The calibration, and what the peel does NOT move

Item 224's eight rebuild verdicts are still the ground truth, and the peeled
walk reproduces item 225's sixteen rows exactly.  A peel that moved the
calibration would be a peel that changed the answer, not the instrument. -/

run_cmd do
  let env ← getEnv
  let got := expectedCalibration.length
  let rows : List (Name × Nat) :=
    [ (``block_dispatch_deferred, 5), (``block_dispatch_deferred_stamp_offcol, 8),
      (``block_dispatch_deferred_stamp_nopack, 7), (``block_dispatch_deferred_inline, 7),
      (``accum_block_on_closeThenBlock, 17), (``colon_fires_implicit_key, 11),
      (``accum_block_on_pendingContent, 23), (``accum_block_on_pendingBlockContent, 25),
      (``accum_block_on_noPending, 13), (``accum_content_on_noPending, 14),
      (``flowKeyRoute_of_open, 15), (``flowKeyRoute_of_root, 10),
      (``keyctx_of_preprocess, 11), (``landing_or_park_save, 6),
      (``landing_or_park_ska, 6), (``preprocess_flow_thread, 9) ]
  if rows.length != got then
    throwError "the calibration's row count moved: {rows.length} vs {got}"
  let peeled := rows.map (fun (c, i) => verdictP env c i)
  let blind := expectedCalibration.map (fun r => (r.splitOn " ").head!)
  if peeled != blind then
    throwError "the PEEL moved item 224's calibration.\nblind:  {
      String.intercalate " " blind}\npeeled: {String.intercalate " " peeled}"

/-! ## §3  The tallies the peel does move

`constants` is the module's non-internal constant count, generated ones
included: 1124 on Lean v4.33.0, 1123 on v4.34.0, which no longer generates the
derived enum's `FrameTail.toCtorIdx` (see `RelaySupplyCensus.expectedTally`).
Item 257 moves one binder from `FIELD` to `RELAY` under the peel as in the
reader census: `h_mono` at `accum_block_on_closeThenBlock`, handed by the
compact fill's literal to `IndentStackCover.covered_nil_of_top_le`.  Item 259
moves three, as in the reader census: `compact_open_map`'s two new binders
relayed to the same lemma, and its `h_top_in` from `FIELD` to `RELAY` (the
`omega` pinning the slot's top now consumes it): `FIELD` 171 → 170, `RELAY`
1866 → 1869.  Item 267 splits the park anchor into a transport core and two
payloads and adds the carrier's source, which is thirty-four new constants and
thirty-two new binder holders; the peel scores their binders `FIELD` 170 → 171,
`READ` 1057 → 1083, `RELAY` 1869 → 1949 and `RETURN` 127 → 128.  The `UNUSED`
roster is unchanged, which is what says the lanes moved by the new
declarations' own binders and not by a rescoring of an existing one.

    Item 269 restates that source as four declarations where item 267's form is
    two, which is two more constants and two more holders, and the peel scores
    their thirteen `Prop` binders exactly as the reader census does — `READ`
    1083 → 1084 and `RELAY` 1949 → 1951, the one `READ` being
    `preprocess_floor_eq`'s `h_floor`.  That the two classifiers agree on the
    same thirteen is the reading: the peel and the reader differ on what a
    binder is used FOR, and here there is nothing for them to differ about.

    Item 271 adds the under-run's column reading and item 272 the composition
    that spends it, one constant and one holder each: `constants` 1161 → 1163,
    `decls` 981 → 983.  The peel scores their fifteen `Prop` binders the way
    the reader does — `READ` 1084 → 1086, `RELAY` 1951 → 1964 — and the two
    `READ`s are both item 271's, `h_floor` and `hcorr`, each projected.  Item
    272's nine all relay, which is what a composition is.

    Lean v4.35.0 moves the same ten verdicts the reader census records, scored
    through this peel: `eta` 369 → 374, `READ` 1088 → 1093, `RELAY` 1983 →
    1973.  `constants`, `decls`, `FIELD`, `RETURN` and the `UNUSED` roster hold,
    and so does every named roster below — the lane totals moved, no conclusion
    did. -/

-- 2026-10-17: `constants` 1165 → 1271, `decls` 985 → 1002, `RELAY` 1973 → 2002
-- when the library took `module` headers; `eta`, `FIELD`, `READ`, `RETURN` and
-- `UNUSED` all held exactly.  The deltas are the SAME +106/+17/+29 that
-- `HypothesisReaderCensus` reads under a different peel, which is the evidence
-- that one set of declarations moved rather than two censuses drifting apart --
-- and the roster names them: `scratchpad/l4yaml-modules/verdict-roster-modules.out`
-- against `scratchpad/l4yaml-435-migration/verdict-roster-435.out` is zero rows
-- lost and 29 gained, every one a matcher equation lemma `<decl>.match_N.eq_M`
-- that `@[expose]` now forces into the environment.  See [[HypothesisReaderCensus]]
-- and TODO/l4yaml-module-system.md.
-- 2026-10-18 (item 281): `constants` 1284 -> 1286 and `RELAY` 2034 -> 2036 when
-- `YamlToken.offersNodeSlot` took its sixth arm.  The SAME +2/+2 this census's
-- sibling reads under a different peel, which is again the evidence that one set
-- of declarations moved rather than two censuses drifting apart -- and the two are
-- the match's renumbered catch-all equations, named in [[HypothesisReaderCensus]]
-- from `scratchpad/l4yaml-r3-carrier/verdict-roster-281.out`.
-- 2026-10-18 (item 284): `constants` 1286 -> 1343 and every lane but `UNUSED`,
-- the SAME constants/decls/eta/UNUSED move [[HypothesisReaderCensus]] reads.  It
-- is the same rows under this census's peel: excluding item 284's 49 new
-- declarations and the ten rows it adds to existing ones (the four new park
-- fields and the six `h_src` gate parameters), BOTH censuses read their
-- item-281 pins exactly, all eight numbers each
-- (`scratchpad/l4yaml-row12-steps/84-peeled-check.log`).
-- 2026-10-18 (item 285): +1 constant, +1 decl, +2 `READ` — the SAME move its
-- sibling reads: the one matcher `slot_ride`'s `match h_optok` generates, both of
-- whose binders are read under either peel.
-- 2026-10-19 (item 287): the SAME +12 constants, +11 decls and +24 `READ` its
-- sibling reads, from the same rows.  The two censuses differ on five of them:
-- the matcher binders `hb`, `hc`, `h₁`, `hcol` and `hws` in the new line-stop
-- lemmas read RELAY there and RETURN under this peel, every other row reading
-- the same under both (`scratchpad/l4yaml-row12-steps/239-rosterP-287.out`
-- against `232-roster-287.out`).  So the sibling's `RELAY` +7 / `RETURN` -3
-- reads +2 / +2 here -- counting the nine rows that left at their unpeeled
-- verdicts, since item 285 kept no peeled roster to read them from.
-- 2026-10-19 (item 289): the SAME `eta` +2 and `READ` +1 its sibling reads, from
-- the same three rows under this peel: `KeyPackPunt.tab`'s `h_poss` and
-- `h_kline` (ETA) and `keyPackPunt_transport`'s `h_poss` (READ)
-- (`scratchpad/l4yaml-row12-steps/319-rosterP-289.out` against
-- `239-rosterP-287.out`: three rows gained, none lost).
-- 2026-10-19 (item 293): the SAME 42 rows its sibling gains, eight constants
-- with them (`scratchpad/l4yaml-row12-steps/368-rosterP-293.out` against
-- `319-rosterP-289.out`: 42 gained, none lost).  Two read differently under
-- this peel — `live_of_dispatch.h_poss` and
-- `preprocess_saved_key_possible_post.h_noflow` are RETURN here and RELAY
-- there, each spent by its proof's final `exact` — so the sibling's `RELAY`
-- +30 reads +28 here, with `RETURN` +2.
-- 2026-10-19 (item 296): the same two rows its sibling moves, `h_node` at both
-- entry pack producers (#9), RELAY under this peel too (`368-rosterP-293.out`)
-- and READ now that the frameless dedent exit applies it.
-- 2026-10-20 (item 297): `constants` 1364 → 1363, `eta` 387 → 386, `RELAY`
-- 2153 → 2151 — `KeyPackPunt.dedent` is deleted, and its three eliminator rows
-- with it (`KeyPackPunt.rec#3 (dedent)` ETA, `KeyPackPunt.casesOn#4 (dedent)`
-- and `KeyPackPunt.recOn#4 (dedent)` RELAY), as at its sibling.  No verdict
-- moves under this peel either.
-- 2026-10-20 (item 299): `constants` 1363 → 1364, `eta` 386 → 387, `READ`
-- 1160 → 1159 — the same rows its sibling's roster names (`525-roster-299.out`:
-- the three deleted token walk lemmas' six binders go, `pendingDocStart#11
-- (h_docline)` ETA and five binders of the `docStartLine` transport arrive),
-- read under this peel: `docStartOnLine_of_lastReal#3 (h)` was READ here
-- (RELAY at the sibling), the other five walk binders RELAY, and the five
-- arriving transport binders RELAY — so one READ fewer and RELAY unmoved
-- (`526-rosterP-299.out` against `368-rosterP-293.out`, which also shows
-- items 296 and 297's rows and nothing else).
-- 2026-10-20 (item 300): `constants` 1364 → 1366, `decls` +2, `eta` 387 → 390,
-- `READ` 1159 → 1163, `RELAY` 2151 → 2164 — the sibling's twenty new rows
-- with the same verdicts under this peel (`557-rosterP-300.out` against
-- `526-rosterP-299.out`, 4024 → 4044 rows; no other row moves).
-- 2026-10-20 (item 303): `constants` 1366 → 1386, `decls` 1084 → 1103, `eta`
-- 390 → 414, `READ` 1163 → 1176, `RELAY` 2164 → 2180 — `KeyFrames` (item 302's
-- value-line resume stack: the inductive, its constructors and recursors,
-- `close`, `ofResumeFrames`, `resumeAt`), read by nothing in the library yet.
-- The peeled roster (`scratchpad/l4yaml-row12-steps/602-rosterP-303.out`
-- against `557-rosterP-300.out`, 4044 → 4097 rows) gains exactly the 53 rows
-- the plain roster gains (`HypothesisReaderCensus`'s note), with the SAME
-- verdicts — ETA 24, READ 13, RELAY 16 — because none of the new declarations
-- has an `h_*` binder for the peeled reading to treat differently; no existing
-- row moves.
-- 2026-10-20 (item 304): `constants` 1386 → 1388, `decls` 1103 → 1105
-- (`resumeFrameRouteK`, `resumeMapRouteK`), `FIELD` 180 → 185, `READ` 1176 →
-- 1182, the rest unchanged — the same binders the plain roster names
-- (`HypothesisReaderCensus`'s note), read peeled — the same eleven rows with the
-- same verdicts (`602-rosterP-303.out` → `612-rosterP-304.out`, 4097 → 4108).
-- 2026-10-20 (item 307): `constants` 1388 → 1393, `decls` 1105 → 1110, `READ` 1182 → 1198, `RELAY` 2180 → 2179 — as `HypothesisReaderCensus`:
-- `closeThenBlock`'s three new haves and their match auxiliaries, and the γ roots' reads.
-- 2026-10-20 (item 309): by `HypothesisReaderCensus`'s deltas (the five new declarations).
-- 2026-10-21 (item 311): `constants` 1398 → 1403, `decls` 1114 → 1117, `UNUSED` 9 → 12 — the named alternative's two abbrevs
-- and three stubs, whose `_h` is unused until its lane proves it (HypothesisReaderCensus's tally moves the same way).
-- 2026-10-21 (item 313): `constants` 1403 → 1405, `decls` 1117 → 1119, `READ` +1, `RELAY` +2, `UNUSED` 12 → 15 — the
-- content-step lemma and its promised wrapper (HypothesisReaderCensus's tally moves the same way).
-- 2026-10-21 (item 314): `constants` 1405 → 1407, `decls` 1119 → 1121, `READ` +1, `RELAY` +1, `UNUSED` 15 → 17 — the
-- dispatch-only transport and its promised wrapper (HypothesisReaderCensus's tally moves the same way).
-- 2026-10-21 (item 315): `RELAY` 2190 → 2191 — `entryPropsKeyPack_of_dispatch`'s `h_dispatch` (as in the unpeeled tally).
-- 2026-10-21 (item 318): `constants` 1407 → 1408, `decls` 1121 → 1122, `READ` 1201 → 1199, `RELAY` 2191 → 2192,
-- `RETURN` 138 → 139, `UNUSED` 17 → 24 — the block lane's two transports and two wrappers (+4) less item 309's three
-- indent lemmas (−3); `not_of_classA` reads one premise fewer, the two content transports return their one equation,
-- and the two wrappers' seven `_`-binders are the new UNUSED.
-- 2026-10-21 (item 320): `constants` 1408 → 1409, `decls` 1122 → 1123, `eta` 414 → 416, `READ` 1199 → 1204 — the marker
-- constructors' new field `h_noek` (read at the eight `PackAlt.ofRefused` payments and the two probes), the two split arms'
-- `h_alt`, and the `h_seqFramesV` relay's wrapper; RELAY, RETURN and UNUSED stand.
-- 2026-10-21 (item 322): `READ` 1204 → 1206 — the two colon openers' new step premise `h_alt_step` is applied inside each
-- (a READ); RELAY, RETURN and UNUSED stand.
-- 2026-10-21 (item 324): `constants`/`decls` +2, `RELAY` 2192 → 2194, `UNUSED` 24 → 26 — `ExplicitValueRefused.step_preprocess`
-- relays its two hypotheses and its wrapper `PackAlt.step_preprocess` holds the same two unused; as `HypothesisReaderCensus`.
-- (The item 320 and 322 notes above are corrected: their scripts garbled the field names.)
-- 2026-10-23 (item 344): constants/decls +1, READ 1200 → 1203 — the relayed `h_valFV`'s `match` and the relays' reads.
-- 2026-10-23 (item 345): constants 1419 → 1420, decls 1129 → 1130, READ 1203 → 1206 — the `h_kslotUp` singleton relays' tactic block: one auxiliary declaration, three more reads (same as HypothesisReaderCensus).
-- 2026-10-24 (B3 [66] col-0 threading): +160 decls (JSON-key carry, reservation transport, gate lemmas).
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-354 base (constants 1650 → 1660, decls 1290 → 1297).
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-355 base.
-- 2026-10-25 (#99 review): PEELED constants 1667 → 1662, decls 1304 → 1301, FIELD 191 → 190, READ 1333 → 1331 — the dead `FlowLead` (+ its two lemmas) deleted; `leadFree`/`closeFree` are `Bool`.
-- 2026-10-26 (item 367, `[82]`): the three `s-l-comments` composition lemmas join StreamAccum: decls 1317 → 1320, FIELD +2, READ +4, RELAY +4.
-- 2026-10-26 (item 369): READ=1375 → READ=1376 — `accum_block_on_pendingBlock.h_closeF_old` (the `-` park's frames, read at the `:`/`?` landing for `h_res_land`).
-- Item 374: `h_base` on `resumectx_of_landing` and the resume context's face disjunct — constants/decls +2, READ +6, RELAY +1.
def expectedModuleTallyP : String :=
  -- 2026-10-24 (item 350): constants 1424 → 1430, decls 1132 → 1137, READ 1207 → 1209, RELAY 2233 → 2237,
  -- RETURN 139 → 140 — `NotQuestionPark` and its three lemmas; `explFrameValueLine`'s split alternative.
-- 2026-10-25 (#112 review): the `FlowStackK` `MarkedColsIn` carrier reverted (Rule 8: a projection of the closed state is decided at the close by `Classical.em`); as HypothesisReaderCensus (constants 1683 → 1681, decls 1322 → 1320, READ 1386 → 1384, RELAY 2641 → 2633).
-- 2026-10-25 (item 363): the flow OPEN lane read off the block state (`h_refused`, one `Classical.em`; five `match` blocks deleted): as HypothesisReaderCensus (constants 1681 → 1676, decls 1320 → 1315; READ from the build).
-- 2026-10-25 (item 363): the flow OPEN lane read off the block state (`h_refused`, one `Classical.em`; five `match` blocks deleted): READ=1384 → 1367
  -- 2026-10-26 (item 365): RELAY 2633 → 2639 — the same six premises `HypothesisReaderCensus` counts
  -- (`h_sound` ×3, `h_fl0` ×2, `h_alt` ×1) passed whole along the content lane.
  -- 2026-10-26 (item 366): RELAY 2639 → 2641 — the same two `h_sound` relays (pre-pinned with `HypothesisReaderCensus`).
  -- 2026-10-26 (item 370): constants/decls +1 (the sibling `-` arm's `match h_closeF_old` auxiliary), READ 1376 → 1379.
-- Item 371: constants/decls +1, READ +1 — `ResumeFrames.one` (the restated value-line pack's one-level bottom).
-- Item 372 (2026-10-27): `SeqTopKey`, `SeqTopKey.of_eq`, `seqTopKey_refuted_at_colon` and the exit (a) face (+5 constants, +4 decls).
  -- 2026-10-28 (item 380, PR #146 review): READ 1408 → 1421, RELAY 2673 → 2660 — `Or.elim` is a two-arm split
  -- (`RelaySupplyCensus.isTwoArm`): the thirteen premises handed to a `Classical.em … |>.elim` are read at the site.
  "constants=1701 decls=1338 eta=442 FIELD=192 READ=1421 RELAY=2660 RETURN=168 UNUSED=27"

-- Item 287: `accum_block_on_closeThenBlock`'s `h_vslot`, a READ one, left the
-- `_ ∨ True` population — its sibling's move, under this peel.  Item 288: and
-- `PendingNode.pendingMapValue.h_vslot`, a constructor field read ETA.
-- Item 300: the two new optional contexts (`h_markerline`, `h_marker_new`)
-- read READ under this peel too.
-- 2026-10-20 (item 307): `READ` 86 → 87, `RELAY` 38 → 37 — `accum_block_on_pendingContent`'s `h_mapFV108` is READ
-- (a `match`) where it was RELAYed; as `HypothesisReaderCensus.expectedOptTally`.
-- 2026-10-26 (item 369): total=165 → total=166, READ=88 → READ=89 — `accum_block_on_pendingBlock.h_closeF_old` (the `-` park's frames, read at the `:`/`?` landing for `h_res_land`).
def expectedOptTallyP : String :=
  -- 2026-10-24 (item 350): total 163 → 159, ETA 33 → 31, READ 87 → 85 — the `h_expl`/`h_explUp` `inr`
  -- arms pay an empty chain and no longer read their alternative.
  -- 2026-10-28 (item 380, PR #146 review): READ 89 → 91, RELAY 40 → 38 — the two optional contexts eliminated by `Or.elim`.
  "total=166 ETA=31 FIELD=4 READ=91 RELAY=38 RETURN=2"

run_cmd do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? ``colon_fires_implicit_key
  let mut names : Array Name := #[]
  for (nm, _) in env.constants.toList do
    -- Filter the USER name: the library's generated auxiliaries are private under
    -- the module system, so their real names read `_private.<module>.0.<name>`,
    -- which `isInternal` and the prefix test both reject.  Authored privates stay
    -- excluded -- they were mangled before the migration too.
    let nmU := Lean.privateToUserName nm
    if nmU.isInternal then continue
    if Lean.isPrivateName nm && !nmU.isInternalDetail then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    names := names.push nm
  let mut tally : Std.HashMap String Nat := {}
  let mut eta := 0
  let mut decls := 0
  let mut unused : Array String := #[]
  for c in names do
    let pbs ← propBinders c
    if pbs.isEmpty then continue
    decls := decls + 1
    for (i, bn) in pbs do
      match binderUsesP env c i with
      | none => eta := eta + 1
      | some us =>
          let d := direct us
          tally := tally.insert d ((tally.getD d 0) + 1)
          if d == "UNUSED" then
            unused := unused.push s!"{c.getString!}#{i} ({shownName bn})"
  let body := String.intercalate " " ((tally.toList.mergeSort
    (fun a b => a.1 < b.1)).map (fun (k, v) => s!"{k}={v}"))
  let got := s!"constants={names.size} decls={decls} eta={eta} {body}"
  if got != expectedModuleTallyP then
    throwError "the PEELED module census moved.\nexpected: {
      expectedModuleTallyP}\ngot:      {got}"
  -- the `UNUSED` lane is the one thing the peel must NOT move: it is what the
  -- toolchain already gates, and item 225 pinned it at these nine rows.
  if (unused.qsort (· < ·)).toList != expectedUnused then
    throwError "the peel moved the UNUSED lane.\nexpected:\n{
      String.intercalate "\n" expectedUnused}\ngot:\n{
      String.intercalate "\n" (unused.qsort (· < ·)).toList}"

run_cmd do
  let env ← getEnv
  let mut tally : Std.HashMap String Nat := {}
  let mut total := 0
  for (nm, ci) in env.constants.toList do
    -- Filter the USER name: the library's generated auxiliaries are private under
    -- the module system, so their real names read `_private.<module>.0.<name>`,
    -- which `isInternal` and the prefix test both reject.  Authored privates stay
    -- excluded -- they were mangled before the migration too.
    let nmU := Lean.privateToUserName nm
    if nmU.isInternal then continue
    if Lean.isPrivateName nm && !nmU.isInternalDetail then continue
    if !(`L4YAML).isPrefixOf nmU then continue
    if (`L4YAML.Tests).isPrefixOf nmU then continue
    if isMechanism env nm then continue
    for (i, _) in (optBinders ci.type).1 do
      total := total + 1
      let v := verdictP env nm i
      tally := tally.insert v ((tally.getD v 0) + 1)
  let body := String.intercalate " " ((tally.toList.mergeSort
    (fun a b => a.1 < b.1)).map (fun (k, v) => s!"{k}={v}"))
  let got := s!"total={total} {body}"
  if got != expectedOptTallyP then
    throwError "the PEELED optional-context census moved.\nexpected: {
      expectedOptTallyP}\ngot:      {got}"
  -- and `content_dispatch_routed`'s six are where item 225 left them
  let rows := (optBinders (env.find? ``content_dispatch_routed).get!.type).1
  let gotC := rows.toList.map (fun (i, bn) =>
    s!"{verdictP env ``content_dispatch_routed i} content_dispatch_routed#{i} ({bn})")
  if gotC != expectedContentDispatch then
    throwError "the peel moved content_dispatch_routed's contexts.\nexpected:\n{
      String.intercalate "\n" expectedContentDispatch}\ngot:\n{
      String.intercalate "\n" gotC}"

/-! ## §4  Item 225's §5, landed

Every one of the nine reaches a mechanism.  Two of them reach a LIBRARY
elimination — `accum_block_on_closeThenBlock`'s `Or.casesOn` — which is exactly
what "no terminal inside `L4YAML`" denied, and `indicator_open_map`'s lands at
`rootMapRoute_or_refused`, the same refutation site item 225 found for
`content_dispatch_routed`'s `h_ref`.

The count is asserted beside the rows, because an empty shortlist that is not
also counted passes vacuously. -/

-- Item 287: the three `accum_block_on_*` rows, and the `closeThenBlock` binder
-- two of them land at, read two binders earlier — `sp_block_ctx` and
-- `h_stream_fallback` retired from all four.
-- 2026-10-24 (B3): binder indices shift with the new park fields (pendingBlock 27→28, pendingBlockContent 32→33,
-- pendingContent 30→33, flowKeyRoute_of_root 21→24); the readers are unchanged.
-- 2026-10-28 (item 380, PR #146 review): back to nine — `colon_open_map_explicit#21` / `compact_open_map#29`
-- (`h_outer`, item 360's two rows) are READ now: their `Classical.em … |>.elim` is a two-arm split
-- (`RelaySupplyCensus.isTwoArm`), the site's own decision, not a relay into a library elimination.
def expectedNineResolved : List String :=
  [ "accum_block_on_pendingBlock#29 (h_seqF_old) => ELIM@L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock#28>Or.casesOn#3",
    "accum_block_on_pendingBlockContent#34 (h_seqF_old) => ELIM@L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock#28>Or.casesOn#3",
    "accum_block_on_pendingContent#33 (h_seqF168) => RETURN@L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent#33",
    "accum_content_on_pendingMapValue_indented#14 (h_ncol_old) => FIELD@L4YAML.Proofs.StreamAccum.PendingNode.pendingProps#19",
    "colon_open_map#24 (h_cov_in) => FIELD@And.intro#2",
    "flowKeyRoute_of_root#24 (h_tail143) => RETURN@L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root#24",  -- item 311: `{g}` precedes it
    "indicator_open_map#26 (h_ref_land) => ELIM@L4YAML.Proofs.StreamAccum.rootMapRouteF_or_refused#7>L4YAML.Proofs.StreamAccum.rootMapRouteF_or_refused.match_1_1#4, ELIM@L4YAML.Proofs.StreamAccum.rootMapRoute_or_refused#7>L4YAML.Proofs.StreamAccum.rootMapRoute_or_refused.match_1_1#4",
    "question_open_map#23 (h_cov_in) => FIELD@And.intro#2",
    "question_open_map#24 (h_cov_nil) => FIELD@And.intro#2" ]

/-- `h_ref`'s terminals, with the pipe peeled: the `SPLIT@Eq.ndrec#9` row item
    225 published was the over-applied transport, not a site. -/
def expectedRefTerminalsP : List String :=
  [ "ELIM@L4YAML.Proofs.StreamAccum.rootMapRouteF_or_refused#7>L4YAML.Proofs.StreamAccum.rootMapRouteF_or_refused.match_1_1#4",
    "ELIM@L4YAML.Proofs.StreamAccum.rootMapRoute_or_refused#7>L4YAML.Proofs.StreamAccum.rootMapRoute_or_refused.match_1_1#4" ]

run_cmd do
  let env ← getEnv
  let nine : List (Name × Nat) :=
    [ (``accum_block_on_pendingBlock, 29), (``accum_block_on_pendingBlockContent, 34),
      (``accum_block_on_pendingContent, 33), (``accum_content_on_pendingMapValue_indented, 14),
      (``colon_open_map, 24), (``flowKeyRoute_of_root, 24), (``indicator_open_map, 26),
      (``question_open_map, 23), (``question_open_map, 24) ]
  if nine.length != expectedCoreTerminal.length then
    throwError "item 225's shortlist is no longer nine rows"
  let got := nine.map (fun (c, i) =>
    let bn := (optBinders (env.find? c).get!.type).1.findSome?
      (fun q => if q.1 == i then some q.2 else none) |>.getD `_
    let ts := (chaseP env 30 c i).toList.mergeSort (fun a b => a < b)
    s!"{c.getString!}#{i} ({bn}) => {String.intercalate ", " ts}")
  if got != expectedNineResolved then
    throwError "the resolved nine moved.\nexpected:\n{
      String.intercalate "\n" expectedNineResolved}\ngot:\n{
      String.intercalate "\n" got}"
  -- …and re-derived, the shortlist is EMPTY, asserted as a count — item 360
  -- had `colon_open_map_explicit.h_outer` and `compact_open_map.h_outer` on it
  -- (conditional carriers whose only reader is their own `Or.elim`), and item 380
  -- (PR #146 review) reads that `Or.elim` as the site's two-arm split, so the two
  -- are READ and the peeled shortlist is empty again.
  let mut core : Nat := 0
  for (nm, ci) in env.constants.toList do
    -- Filter the USER name: the library's generated auxiliaries are private under
    -- the module system, so their real names read `_private.<module>.0.<name>`,
    -- which `isInternal` and the prefix test both reject.  Authored privates stay
    -- excluded -- they were mangled before the migration too.
    let nmU := Lean.privateToUserName nm
    if nmU.isInternal then continue
    if Lean.isPrivateName nm && !nmU.isInternalDetail then continue
    if !(`L4YAML).isPrefixOf nmU then continue
    if (`L4YAML.Tests).isPrefixOf nmU then continue
    if isMechanism env nm then continue
    for (i, _) in (optBinders ci.type).1 do
      if verdictP env nm i != "RELAY" then continue
      if (chaseP env 30 nm i).toList.all (fun t => !isLibTerminal t) then
        core := core + 1
  if core != 0 then
    throwError "the peeled core-terminal shortlist is not empty: {core}"
  let refT := (chaseP env 30 ``content_dispatch_routed 24).toList.mergeSort
    (fun a b => a < b)
  if refT != expectedRefTerminalsP then
    throwError "h_ref's peeled terminals moved.\nexpected:\n{
      String.intercalate "\n" expectedRefTerminalsP}\ngot:\n{
      String.intercalate "\n" refT}"

/-! ## §5  Item 225's §7, decided

`Or.elim` reads and `Or.imp_left` re-states, and with the pipe peeled the
census says so: the read RELAYS into a constant that eliminates, the
re-statement RETURNS the premise weakened.  Item 225's debt row is retired.
Item 380 (PR #146 review) made `Or.elim` a two-arm split, so the read is a
READ at the site now; the re-statement still RETURNS. -/

def expectedDistinguished : String :=
  "reads_by_elim#3=READ restates_by_imp#3=RETURN"

run_cmd do
  let env ← getEnv
  let got := s!"reads_by_elim#3={verdictP env ``reads_by_elim 3} restates_by_imp#3={
    verdictP env ``restates_by_imp 3}"
  if got != expectedDistinguished then
    throwError "§5's two relays are no longer distinguished.\nexpected: {
      expectedDistinguished}\ngot:      {got}"
  if expectedDistinguished == expectedIndistinguishable then
    throwError "the peeled and blind walks agree on §7's exhibits, so one of \
      the two pins has been edited to match the other"

/-! ## §6  The dead-parameter fixpoint

ALIVE is the least fixpoint, so DEAD never calls a read premise dead.  The
`inTy`/`usedLaterInType` clause is the one a census does not need and a DROP
does: item 225's walk peels the telescope before it walks, so it cannot see a
binder named in a LATER binder's type. -/

structure Node where
  c : Name
  i : Nat
deriving BEq, Hashable, Inhabited

def nkey (n : Node) : String := s!"{n.c}#{n.i}"

/-- Does binder `i` of `c` occur in a later binder's type or in the conclusion? -/
def usedLaterInType (env : Environment) (c : Name) (i : Nat) : Bool :=
  match env.find? c with
  | none => true
  | some ci => Id.run do
      let mut t := ci.type
      for _ in [0:i+1] do
        match t with
        | .forallE _ _ b _ => t := b
        | _ => return true
      return t.hasLooseBVar 0

/-- `(base-ALIVE, relay targets)`.  No accessible value means ALIVE: the
    fixpoint calls a binder alive when it cannot call it dead. -/
def baseOf (env : Environment) (n : Node) : Bool × Array Node :=
  match binderUsesP env n.c n.i with
  | none => (true, #[])
  | some us =>
      if usedLaterInType env n.c n.i then (true, #[]) else
      Id.run do
        let mut b := false
        let mut tg : Array Node := #[]
        for u in us do
          match u with
          | .relay g j => tg := tg.push ⟨g, j⟩
          | _ => b := true
        return (b, tg)

abbrev Graph := Std.HashMap String (Node × Bool × Array Node)

partial def build (env : Environment) : List Node → Graph → Graph
  | [], g => g
  | n :: rest, g =>
      if g.contains (nkey n) then build env rest g
      else
        let (b, tg) := baseOf env n
        build env (tg.toList ++ rest) (g.insert (nkey n) (n, b, tg))

/-- The least fixpoint, by reverse-edge propagation. -/
def aliveSet (g : Graph) : Std.HashSet String := Id.run do
  let mut rev : Std.HashMap String (Array String) := {}
  let mut alive : Std.HashSet String := {}
  let mut queue : Array String := #[]
  for (k, (_, b, tg)) in g do
    for t in tg do
      let tk := nkey t
      rev := rev.insert tk ((rev.getD tk #[]).push k)
    if b then
      alive := alive.insert k
      queue := queue.push k
  let mut idx := 0
  while h : idx < queue.size do
    let k := queue[idx]
    idx := idx + 1
    for s in rev.getD k #[] do
      if !alive.contains s then
        alive := alive.insert s
        queue := queue.push s
  return alive

/-- Nineteen dead binders in the whole explored closure, eighteen `UNUSED` and one a `RELAY`
    chased to an unused binder (item 315: `entryPropsKeyPack_of_dispatch`'s content dispatch,
    relayed to the promised `PackAlt.step_content`).  Eighteen are `StreamAccum`'s own — item 225's `expectedUnused`, which the peel
    does not move, eight of them the named alternative's stubs and promised wrappers (item
    311: `PackAlt.ofRefused`, `PackAltG.ofPark`, `PackAlt.ofGateClose`; item 313:
    `PackAlt.step_content`'s three; item 314: `PackAlt.step_dispatch`'s two — each `trivial`
    until its promise or its lane is its body, so its binders are dead by construction) —
    and the nineteenth is one module over. -/
-- Item 287: the wrapper reads its premises off the dispatch, so `_h_res` is its
-- thirteenth binder.
-- 2026-10-21 (item 318): seven rows added — `PackAlt.step_blockEntry`'s three `_`-binders and `PackAlt.step_value`'s four,
-- `lane stub` like the other promised wrappers; regenerated from the census's own `got` rows.
-- 2026-10-21 (item 324): two rows added — `PackAlt.step_preprocess`'s `_h_preprocess`/`_h`, `lane stub` like the other promised
-- wrappers (`deadReason` lists them); rows from the guard's own `got`.
-- 2026-10-23 (item 349): PEELED constants 1420 → 1424, decls 1130 → 1132, READ 1206 → 1207, RELAY 2222 → 2233 (the two
-- dispatch bridges; `h_sound`/`h_dead` relayed through the content step); DEAD set 32 → 31, see the reason table.
-- 2026-10-24 (B3 [66] col-0 threading): 32 → 33 — `question_open_map#15` left (its `_h_noflow_disp` is
-- spent); `gate_of_peek#3`, `park_gate_of_peek#2` enter; the
-- promised-step binders shift with the new park fields.
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-354 base.
def expectedDead : List String :=
  ["L4YAML.Proofs.StreamAccum.PackAlt.ofGateClose#2 (_h) [lane stub]",
   "L4YAML.Proofs.StreamAccum.PackAlt.ofRefused#1 (_h) [lane stub]",
   "L4YAML.Proofs.StreamAccum.PackAlt.step_blockEntry#3 (_h_preprocess) [lane stub]",
   "L4YAML.Proofs.StreamAccum.PackAlt.step_blockEntry#4 (_h_dispatch) [lane stub]",
   "L4YAML.Proofs.StreamAccum.PackAlt.step_blockEntry#5 (_h) [lane stub]",
   "L4YAML.Proofs.StreamAccum.PackAlt.step_content#4 (_h_preprocess) [lane stub]",
   "L4YAML.Proofs.StreamAccum.PackAlt.step_content#5 (_h_dispatch) [lane stub]",
   "L4YAML.Proofs.StreamAccum.PackAlt.step_content#6 (_h) [lane stub]",
   "L4YAML.Proofs.StreamAccum.PackAlt.step_dispatch#3 (_h_dispatch) [lane stub]",
   "L4YAML.Proofs.StreamAccum.PackAlt.step_dispatch#4 (_h) [lane stub]",
   "L4YAML.Proofs.StreamAccum.PackAlt.step_preprocess#3 (_h_preprocess) [lane stub]",
   "L4YAML.Proofs.StreamAccum.PackAlt.step_preprocess#4 (_h) [lane stub]",
   "L4YAML.Proofs.StreamAccum.PackAlt.step_value#3 (_h_preprocess) [lane stub]",
   "L4YAML.Proofs.StreamAccum.PackAlt.step_value#4 (_h_dispatch) [lane stub]",
   "L4YAML.Proofs.StreamAccum.PackAlt.step_value#5 (_h_noflow) [lane stub]",
   "L4YAML.Proofs.StreamAccum.PackAlt.step_value#6 (_h) [lane stub]",
   "L4YAML.Proofs.StreamAccum.PackAltG.ofPark#2 (_h) [lane stub]",
   "L4YAML.Proofs.StreamAccum.accum_content_on_noPending#18 (h_alt) [family uniformity]",
   "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_inline#12 (_h_res) [class marker]",
   "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack#10 (_h_src) [class marker]",
   "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack#11 (_h_indent) [class marker]",
   "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack#12 (_h_park) [class marker]",
   "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol#11 (_h_src) [class marker]",
   "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol#12 (_h_indent) [class marker]",
   "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol#13 (_h_ne) [class marker]",
   "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch#28 (h_alt) [promised step]",
   "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch#31 (h_alt) [promised step]",
   "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch#32 (h_dispatch) [promised step]",
   "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close#11 (_) [conclusion binder]",
   "L4YAML.Proofs.StreamAccum.gate_of_peek#3 (_) [family uniformity]",
   "L4YAML.Proofs.StreamAccum.park_gate_of_peek#2 (_) [family uniformity]",
   "L4YAML.Proofs.StructureCoupling.scanTagDirective_corr#2 (_hcorr) [family uniformity]"]

/-- Why each dead binder is there.  The reading is a JUDGEMENT read off the
    source and it is written down so a later reader can disagree with it; what
    is measured is the set, not the reasons. -/
def deadReason : String → String
  | "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_inline#12"
  | "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack#10"
  | "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack#11"
  | "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack#12"
  | "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol#11"
  | "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol#12"
  | "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol#13" => "class marker"
  | "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close#11" => "conclusion binder"
  -- Item 315: relayed to `PackAlt.step_content`, whose own step binder is unused while its promise is not yet
  -- its body — so the chase ends at a dead binder; alive the moment `PackAlt` is the predicate.
  | "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch#31"
  -- Item 340: the flip's premise `h_alt : PackAlt _` on the four lemmas that relay it into their packs through
  -- `PackAlt.step_dispatch`/`step_content`/`step_preprocess` — the same chase, ending at the same unused step binder.
  -- Item 349: `content_dispatch_routed#29` left the set (its `h_alt` is read at the `k = 0` payment's `dif`);
  -- `accum_content_on_noPending`'s `h_alt` moved to #17 behind `h_dead` and reads as family uniformity.
  | "L4YAML.Proofs.StreamAccum.content_dispatch_routed#29"
  | "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch#28"
  | "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch#32"
  | "L4YAML.Proofs.StreamAccum.accum_content_on_noPending#17" => "promised step"
  | "L4YAML.Proofs.StreamAccum.PackAlt.ofRefused#1"
  | "L4YAML.Proofs.StreamAccum.PackAltG.ofPark#2"
  | "L4YAML.Proofs.StreamAccum.PackAlt.ofGateClose#2"
  | "L4YAML.Proofs.StreamAccum.PackAlt.step_content#4"
  | "L4YAML.Proofs.StreamAccum.PackAlt.step_content#5"
  | "L4YAML.Proofs.StreamAccum.PackAlt.step_content#6"
  | "L4YAML.Proofs.StreamAccum.PackAlt.step_dispatch#3"
  | "L4YAML.Proofs.StreamAccum.PackAlt.step_dispatch#4"
  -- Item 318: the block lane's two promised wrappers (three implicit states precede their binders).
  | "L4YAML.Proofs.StreamAccum.PackAlt.step_blockEntry#3"
  | "L4YAML.Proofs.StreamAccum.PackAlt.step_blockEntry#4"
  | "L4YAML.Proofs.StreamAccum.PackAlt.step_blockEntry#5"
  | "L4YAML.Proofs.StreamAccum.PackAlt.step_value#3"
  | "L4YAML.Proofs.StreamAccum.PackAlt.step_value#4"
  | "L4YAML.Proofs.StreamAccum.PackAlt.step_value#5"
  | "L4YAML.Proofs.StreamAccum.PackAlt.step_value#6"
  -- Item 324: the preprocess transport's promised wrapper (two implicit states and `{c}` precede its binders).
  | "L4YAML.Proofs.StreamAccum.PackAlt.step_preprocess#3"
  | "L4YAML.Proofs.StreamAccum.PackAlt.step_preprocess#4" => "lane stub"
  | _ => "family uniformity"

-- 2026-10-21 (item 315): `dead` 18 → 19, `RELAY` 0 → 1 — `entryPropsKeyPack_of_dispatch`'s new `h_dispatch` is relayed to
-- the promised wrapper and chased to its unused step binder.
-- 2026-10-21 (item 318): `dead` 19 → 26, `UNUSED` 18 → 25 — the seven lane-stub binders above.
-- 2026-10-21 (item 324): `dead` 26 → 28, `UNUSED` 25 → 27 — `PackAlt.step_preprocess`'s two lane-stub binders above.
-- 2026-10-22 (item 340): `dead` 28 → 32, `RELAY` 1 → 5 — the four `h_alt` premises above, relayed to the promised
-- wrappers; `entryPropsKeyPack_of_dispatch`'s `h_dispatch` moved from #30 to #31 behind the new binder.
-- 2026-10-23 (item 349): `dead` 32 → 31, `RELAY` 5 → 4 — `content_dispatch_routed#29 (h_alt)` is read at the `k = 0` payment.
-- 2026-10-24 (B3 [66] col-0 threading): dead 33 → 32 — `content_dispatch_routed#29 (h_alt)` is read on the item-354 base.
def expectedDeadTally : String := "dead=32 RELAY=4 UNUSED=28 RELAY=4"  -- 2026-10-24 (B3): see `expectedDead`

run_cmd do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? ``colon_fires_implicit_key
  let mut q : Array Node := #[]
  for (nm, ci) in env.constants.toList do
    -- Filter the USER name: the library's generated auxiliaries are private under
    -- the module system, so their real names read `_private.<module>.0.<name>`,
    -- which `isInternal` and the prefix test both reject.  Authored privates stay
    -- excluded -- they were mangled before the migration too.
    let nmU := Lean.privateToUserName nm
    if nmU.isInternal then continue
    if Lean.isPrivateName nm && !nmU.isInternalDetail then continue
    if env.getModuleIdxFor? nm == modIdx then
      for (i, _) in ← propBinders nm do q := q.push ⟨nm, i⟩
    if (`L4YAML).isPrefixOf nm && !(`L4YAML.Tests).isPrefixOf nm
        && !isMechanism env nm then
      for (i, _) in (optBinders ci.type).1 do q := q.push ⟨nm, i⟩
  let g := build env q.toList {}
  let alive := aliveSet g
  let mut dead : Array String := #[]
  let mut tally : Std.HashMap String Nat := {}
  for (k, (n, _, _)) in g do
    if alive.contains k then continue
    let v := verdictP env n.c n.i
    tally := tally.insert v ((tally.getD v 0) + 1)
    let bn := match env.find? n.c with
      | none => `_
      | some ci => Id.run do
          let mut t := ci.type
          for _ in [0:n.i] do
            match t with | .forallE _ _ b _ => t := b | _ => return `_
          match t with | .forallE nm _ _ _ => return nm | _ => return `_
    dead := dead.push s!"{n.c} ({shownName bn}) [{deadReason k}]"
  let got := (dead.qsort (· < ·)).toList
  -- the rows carry the constant and the binder name; re-attach the index
  let gotIdx := ((g.toList.filterMap (fun (k, (n, _, _)) =>
      if alive.contains k then none else some (k, n))).mergeSort
      (fun a b => a.1 < b.1)).map (fun (k, n) =>
    let bn := match env.find? n.c with
      | none => `_
      | some ci => Id.run do
          let mut t := ci.type
          for _ in [0:n.i] do
            match t with | .forallE _ _ b _ => t := b | _ => return `_
          match t with | .forallE nm _ _ _ => return nm | _ => return `_
    s!"{k} ({shownName bn}) [{deadReason k}]")
  if gotIdx != expectedDead then
    throwError "the DEAD set moved.\nexpected ({expectedDead.length}):\n{
      String.intercalate "\n" expectedDead}\ngot ({gotIdx.length}):\n{
      String.intercalate "\n" gotIdx}"
  if got.length != expectedDead.length then
    throwError "dead row count disagreement"
  let body := String.intercalate " " ((tally.toList.mergeSort
    (fun a b => a.1 < b.1)).map (fun (k, v) => s!"{k}={v}"))
  let gotT := s!"dead={gotIdx.length} {body} RELAY={tally.getD "RELAY" 0}"
  if gotT != expectedDeadTally then
    throwError "the DEAD tally moved.\nexpected: {expectedDeadTally}\ngot:      {gotT}"

/-! ## §7  Why the optional lane is free, in one line

`A ∨ True` is unconditionally inhabited, so a premise of that shape constrains
nothing and a consumer takes it for free.  This is item 225's §6 corollary —
*a premise whose type is unconditionally inhabited has no reader at any price*
— applied to the population item 225 had just censused and did not apply it to.

`isOptTy` is the selector items 212–225 have used throughout, so the 163 rows
those censuses count are definitionally the rows these lemmas discharge — and
item 227 measures what that selector MISSES, which is two rows and one
definition. -/

/-- The whole of the optional-context lane, as a proposition. -/
lemma opt_is_unconditional (A : Prop) : A ∨ True := Or.inr trivial

/-- …so a consumer that takes one proves its goal without it. -/
lemma opt_premise_buys_nothing {A P : Prop} (k : A ∨ True → P) : P :=
  k (opt_is_unconditional A)

/-- …and the lemma that takes one is the lemma that does not, which is what
    the substitution probe verifies at the level of the PROOF rather than the
    statement. -/
lemma opt_premise_is_no_premise {A P : Prop} : (A ∨ True → P) ↔ P :=
  ⟨fun k => opt_premise_buys_nothing k, fun p _ => p⟩

/-- The population the three lemmas above cover: every binder items 212–225
    census is selected BY the shape they discharge, and there are ~~163 of
    them~~ **163 that `isOptTy` can SEE**.

    **Corrected at item 227.**  `isOptTy` is a test on the syntax, so a
    `∨ True` behind a definition is invisible to it, and `ResumeKeyCtx` is one:
    two further binders carry an optional context this selector does not
    report, so **the optional population is 165**.  The pin below is right —
    it pins what `isOptTy` finds, and it still passes unedited — and so is
    every measurement items 212–226 took over the 163, because each of them
    measured the 163.  What was wrong is this sentence, which called the 163
    the population.  `Tests.Guards.NarrowingWorthCensus` §6 runs the two
    selectors against each other and gates the difference.

    The pin is the count, because a selector that matched nothing would make
    the sentence above true and empty. -/
-- Item 287: `accum_block_on_closeThenBlock`'s `h_vslot` left the `_ ∨ True`
-- population.  Item 288: and `PendingNode.pendingMapValue.h_vslot`, a field.
-- 2026-10-20 (item 309): `optTy` 163 → 158 — the three generic helpers' five `∨ alt` binders are no `∨ True`
-- to this census (their callers instantiate the alternative).
-- 2026-10-21 (item 311): `optTy` 158 → 156 — `colon_open_map_implicit` states the family's alternative generically
-- (`{alt : Prop}`), so its two `∨ alt` premises leave the literal-optional population, as the three generic helpers'
-- did at item 309; `total` stands at 163.
-- 2026-10-26 (item 369): total=165 → total=166, optTy=157 → optTy=158 — `accum_block_on_pendingBlock.h_closeF_old` (the `-` park's frames, read at the `:`/`?` landing for `h_res_land`).
def expectedOptPopulation : String :=
  -- 2026-10-24 (item 350): total 163 → 159, optTy 156 → 153, ctorFields 33 → 31 — as above.
  "total=166 optTy=158 ctorFields=31"

run_cmd do
  let env ← getEnv
  let mut total := 0
  let mut optTy := 0
  let mut ctorFields := 0
  for (nm, ci) in env.constants.toList do
    -- Filter the USER name: the library's generated auxiliaries are private under
    -- the module system, so their real names read `_private.<module>.0.<name>`,
    -- which `isInternal` and the prefix test both reject.  Authored privates stay
    -- excluded -- they were mangled before the migration too.
    let nmU := Lean.privateToUserName nm
    if nmU.isInternal then continue
    if Lean.isPrivateName nm && !nmU.isInternalDetail then continue
    if !(`L4YAML).isPrefixOf nmU then continue
    if (`L4YAML.Tests).isPrefixOf nmU then continue
    if isMechanism env nm then continue
    let mut t := ci.type
    let mut j := 0
    for (i, _) in (optBinders ci.type).1 do
      total := total + 1
      if isCtor env nm then ctorFields := ctorFields + 1
      while j < i do
        t := match t with | .forallE _ _ b _ => b | x => x
        j := j + 1
      if (match t with | .forallE _ a _ _ => isOptTy a | _ => false) then
        optTy := optTy + 1
  let got := s!"total={total} optTy={optTy} ctorFields={ctorFields}"
  if got != expectedOptPopulation then
    throwError "the optional population moved.\nexpected: {
      expectedOptPopulation}\ngot:      {got}"

end Tests.Guards.PremiseNecessityCensus
