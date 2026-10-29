import Tests.Guards.Proofs.ArmDemandLedger
import Tests.Guards.Proofs.RelaySupplyCensus

/-!
# The spend census: who can READ the conjunct (item 224)

Item 222 built the STRENGTH LADDER, a census of PRODUCERS.  Item 223 built the
DEMAND LEDGER, a census of PARAMETERS, and closed its own record with the debt
this file pays:

> the demand ledger is a signature census, not a spend census — it counts which
> consumers ASK for the weak form, and nothing counts how many of the eight
> would actually USE the conjunct if they had it, so a loose parameter that no
> proof would read is indistinguishable here from one that is throwing strength
> away.

The two are not the same question and they do not have the same answer.  A
consumer that asks loose is **throwing strength away** only if its proof could
spend the strength; if it could not, the loose parameter is the RIGHT type and
the ledger row is not a debt at all.  Distinguishing them needs an instrument
that reads proofs rather than signatures, and there are two here.

## The instrument, part one: the arm binder resolved by TYPE

Item 223's ledger was assembled by grepping the loose literal and listing the
tight side by hand.  §1 below reads both off the ELABORATED types instead, by
matching the arm's exact shape — `ska = true ∨ R` and
`(ska = true ∧ poss = false) ∨ R`.  It finds **22** binders where the ledger
recorded twelve consumers.  The eight LOOSE ones are item 223's eight exactly;
the tight side is not four but fourteen, of which six are the park constructors
(the supply, correctly outside a demand census) and **four are consumers the
ledger never listed**: `block_dispatch_deferred` and its three stamp siblings.

## The instrument, part two: the WEAKENING PROBE

A flip patch tightens a binder and counts what breaks.  Its dual LOOSENS one
that is already tight and counts who screams, and that is the spend census: an
error inside the weakened lemma's own proof is a READ, and an error at a call
site is PLUMBING.  Run one binder at a time — eight builds, so that two
weakened lemmas which feed each other cannot mask one another — it reads:

| tight consumer | self-errors | verdict |
|---|---|---|
| `block_dispatch_deferred` | 1 | CONDUIT → `PendingNode.pendingFlow`'s field |
| `block_dispatch_deferred_stamp_offcol` | 1 | CONDUIT → `block_dispatch_deferred` |
| `block_dispatch_deferred_stamp_nopack` | 1 | CONDUIT → `block_dispatch_deferred` |
| `block_dispatch_deferred_inline` | 1 | CONDUIT → `block_dispatch_deferred` |
| `accum_block_on_closeThenBlock` | 2 | PLUMBING — a stale `Or.imp_left` and its `refine` |
| `colon_fires_implicit_key` | 2 | **READ** — `⟨_, h_poss_f⟩` refutes the branch |
| `accum_block_on_pendingContent` | 3 | CONDUIT → the two above |
| `accum_block_on_pendingBlockContent` | 2 | CONDUIT + one stale projection |

**One reader.**  Of the eight tight consumers exactly one destructures the
conjunct, twice, and both times to kill a branch outright — and it takes
`⟨_, h_poss_f⟩`, discarding the FLAG.  The landings are its mirror: they read
the flag and can never read the conjunct.  The arm is not one datum every
consumer shares, it is a PAIR whose two halves have disjoint readers.

## What that says about the eight loose rows

They are not a debt.  Nothing behind a landing reads the conjunct — the one
reader takes its arm from a park constructor's field through two relays
(§2's `FIELD`/`RELAY` edges), never through a landing, whose conclusions are
about the LANDED state.  And §4 shows the tight form of each landing is a
one-line corollary of the loose one, available at any call site that ever wants
it, at no cost to the library.  **The ledger counted corollaries as debt.**

The rule this item adds: **a demand row is a debt only if the consumer can
spend it; a census of who ASKS for strength is not a census of who READS it,
and to price a tightening you loosen what is already tight and count who
screams.**  Its corollary, which is the reason the two are not interchangeable:
**tightening a consumer that cannot read the conjunct buys only plumbing, and
plumbing is one `imp_left` away in either direction.**

## The projection count, re-measured

Item 223's record says `accum_block_on_closeThenBlock` "projects it away FOUR
TIMES" to reach the landings.  Resolved by the elaborator there are **nine**
`Or.imp_left` relays into the two landings, four at `closeThenBlock` and five
at `accum_block_on_pendingBlockContent` — the count was taken at one caller and
carried as if it were the total.  §2 pins all eighty-five arm payment edges so
it cannot be taken at one caller again.
-/

namespace Tests.Guards.ArmSpendCensus

set_option autoImplicit false

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs

open Lean Elab Command
open L4YAML.Tests.Guards.RelaySupplyCensus

/-! ## §1  The arm binder, read off the elaborated type

`s.simpleKeyAllowed = true` and `s.simpleKey.possible = false` are matched as
shapes, so the census sees the arm wherever it is written and under whichever
state variable — the two readings item 221 said a literal census cannot join. -/

/-- `s.simpleKeyAllowed = true`, for any `s`. -/
def isSkaTrue (e : Expr) : Bool :=
  e.isAppOfArity ``Eq 3 &&
  (e.getArg! 1).isAppOfArity ``L4YAML.Scanner.ScannerState.simpleKeyAllowed 1 &&
  (e.getArg! 2).isConstOf ``Bool.true

/-- `s.simpleKey.possible = false`, for any `s`. -/
def isPossFalse (e : Expr) : Bool :=
  e.isAppOfArity ``Eq 3 &&
  ((e.getArg! 1).find? (fun x =>
      x.isAppOfArity ``L4YAML.Scanner.ScannerState.simpleKey 1)).isSome &&
  (e.getArg! 2).isConstOf ``Bool.false

/-- `some tight?` when the type is an ARM — the loose `ska = true ∨ R` or the
    tight `(ska = true ∧ poss = false) ∨ R` — and `none` otherwise.  The right
    disjunct is deliberately unconstrained: the family pays against a column at
    eight carriers and against `inFlow` at `noPending`, and both are arms. -/
def armKind (e : Expr) : Option Bool :=
  if e.isAppOfArity ``Or 2 then
    let l := e.getArg! 0
    if isSkaTrue l then some false
    else if l.isAppOfArity ``And 2 && isSkaTrue (l.getArg! 0) && isPossFalse (l.getArg! 1)
      then some true
    else none
  else none

/-- Every arm binder of a type: its index, its name, and whether it is tight. -/
def armBinders (ty : Expr) : Array (Nat × Name × Bool) := Id.run do
  let mut out := #[]; let mut t := ty; let mut i := 0
  repeat match t with
    | .forallE n a b _ =>
        match armKind a with
        | some tg => out := out.push (i, n, tg)
        | none => pure ()
        i := i + 1; t := b
    | _ => break
  return out

/-- The arm binders in `OptMap` shape, so item 212's `walk` resolves them. -/
def armMap : CommandElabM OptMap := do
  let env ← getEnv
  let mut mm : OptMap := {}
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    let obs := armBinders ci.type
    if obs.isEmpty then continue
    mm := mm.insert nm (obs.map (fun (i, n, _) => (i, n)))
  return mm

/-- Every PAYMENT of an arm binder made inside the module declaring `anchor`,
    resolved through the pipes and splits item 214–217 taught `resolve` to
    cross.  This is the census `payers.py` could not be: a text scan reads the
    first `Or.inl` in a three-line window and attributes it to whichever
    parameter is nearest, which at `flowKeyRoute_of_open` is the wrong one. -/
def armEdges (anchor : Name) : CommandElabM (Array Edge × Nat) := do
  let env ← getEnv
  let m ← armMap
  let modIdx := env.getModuleIdxFor? anchor
  let mut acc : Array Edge := #[]
  let mut skipped := 0
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    if isMechanism env nm then continue
    let some v := ci.value? (allowOpaque := true) | continue
    let (_, n) := optBinders ci.type
    if lamDepth v < n then skipped := skipped + 1; continue
    acc := walk env m nm n #[] v acc
  return (acc, skipped)

/-- The ~~twenty-two~~ twenty-one arm binders, tight first by sort order.  Six
    of the ~~fourteen~~ thirteen tight rows are the park CONSTRUCTORS — the
    supply, which a demand census is right to exclude and which item 223's
    twelve therefore did.  The other ~~eight~~ seven are consumers, and item
    223's ledger named four of them.  DOCS item 287: the inline wrapper reads
    its arm off the dispatch, so its `h_arm` row is gone, and three
    `accum_block_on_*` read their `h_park` two binders earlier, past the
    retired `sp_block_ctx` and `h_stream_fallback`.

    **Item 293: twenty-five.**  Two rows leave because two binders narrowed to
    what their producers pay — `accum_content_on_noPending`'s `h_park` to the
    flag, and `pendingDocStart`'s `h_arm` to the armed conjunction.  Six rows
    join that are not arms: the escape park's `flag ∨ live` (`h_live0`) on
    `pendingFlow`, the escape, its two stamp wrappers, `content_live0` and
    `preprocess_possible_of_live0`.  The census reads every
    `simpleKeyAllowed = true ∨ …` binder as a loose arm — the shape, not the
    role. -/
-- 2026-10-21 (item 311): `flowKeyRoute_of_open` #14 → #15 and `flowKeyRoute_of_root` #9 → #10 — both take the flow
-- frame's gate `{g : Option ScannerState}` as an implicit binder now (their conclusions carry the frame's named
-- alternative `PackAltG g`); `h_park` is the same binder one index later.
-- 2026-10-24 (B3 [66] col-0 threading): nine binder indices shift, no row changes class — the
-- parks gain `sp_gram`/`h_run`/`h_gate`/`h_next` and the step frames read from `sp_gram`.
def expectedBinders : List String :=
  [ "loose accum_block_on_noPending#14 (h_arm)",
    "loose block_dispatch_deferred#9 (h_live0)",
    "loose block_dispatch_deferred_stamp_nopack#14 (h_live0)",
    "loose block_dispatch_deferred_stamp_offcol#15 (h_live0)",
    "loose content_live0#4 (h_live0)",
    "loose flowKeyRoute_of_open#15 (h_park)",
    "loose flowKeyRoute_of_root#11 (h_park)",
    "loose keyctx_of_preprocess#15 (h_park)",
    "loose landing_or_park_save#6 (h_park)",
    "loose landing_or_park_ska#6 (h_park)",
    "loose pendingFlow#8 (h_live0)",
    "loose preprocess_flow_thread#10 (h_park)",
    "loose preprocess_possible_of_live0#3 (h_live0)",
    "tight accum_block_on_closeThenBlock#16 (h_park)",
    "tight accum_block_on_pendingBlockContent#24 (h_park)",
    "tight accum_block_on_pendingContent#24 (h_park)",
    "tight block_dispatch_deferred#5 (h_arm)",
    "tight block_dispatch_deferred_stamp_nopack#7 (h_arm)",
    "tight block_dispatch_deferred_stamp_offcol#8 (h_arm)",
    "tight colon_fires_implicit_key#11 (h_arm)",
    "tight noPending#4 (h_arm)",
    "tight pendingBlockContent#11 (h_arm)",
    "tight pendingContent#10 (h_arm)",
    "tight pendingDocEnd#6 (h_arm)",
    "tight pendingFlow#5 (h_arm)" ]

/-- The payments, by kind.  **PAY=8** is every literal `Or.inl` that funds an
    arm anywhere in `StreamAccum`; a term census sees those and nothing else,
    and they are under a tenth of the traffic.  **RELAY=23** is the cascade —
    an argument forwarded from the caller's own arm binder, which is why
    tightening two landings drags three more consumers with them.  **VIA=32**
    names a lemma (`content_park_arm`, `arm_tight_of_block_dispatch`) and
    **FIELD=6** is a park constructor's own field read through `casesOn`, which
    is the supply route to the one reader.  `skipped` is `RelaySupplyCensus`'s
    counter over the same module, and it moved 31 → 30 for that file's reason:
    v4.34.0 no longer generates the derived enum's `FrameTail.toCtorIdx`, the
    one refused constant that left the module.

    **Item 284 adds one edge, a DECLINE**: the props arm's column-0 landing
    reads the landing's flag once more, through `landing_or_park_ska`'s
    `h_park`, paid `Or.inr h_col0_p` exactly as its two neighbours there pay
    it — the gate `slotGateAt_of_propsPark` spends.  It is the one arm-binder
    consumer whose application count changed (13 → 14).

    **Item 285 adds one more**: `slot_ride` builds the open's `noPending` park
    exactly as `drop_ride` does, paying its tight `h_arm` with
    `Or.inr (inFlow_of_flowLevel_eq h_fl1)`.

    **Item 287 takes two out**: the inline wrapper reads its arm off the
    dispatch, so its `h_arm` binder is gone and with it the two `VIA` edges
    its old applications paid (`arm_tight_of_block_dispatch`) and the `RELAY`
    it handed `block_dispatch_deferred`; the wrapper's own derivation is one
    `VIA` edge in their place.  91 → 89, `RELAY` 25 → 24, `VIA` 32 → 31.

    **Item 293: 89 → 102**, every edge named by a diff against item 292's tree
    (`scratchpad/l4yaml-row12-steps/362-armspend-edges.log`: 18 gained, 5
    lost).  Fifteen are the supply of the six `flag ∨ live` binders — the six
    stamp-wrapper calls and the inline wrapper paying `Or.inl` off the
    dispatch (`PAY` 7), the escape relaying to its park and the two wrappers
    and `content_live0` relaying onward (`RELAY` 4), `content_live0` into the
    escape (`VIA` 1), the two park fields read through `casesOn` (`FIELD` 2),
    and the props arm's `Or.inr` of the run's key (`DECLINE` 1).  The two
    narrowings take five out and put two back: `pendingDocStart.h_arm`'s two
    producer `PAY`s and `accum_content_on_noPending.h_park`'s caller `PAY`
    leave with their binders, and the two consumers that read a narrowed field
    on to a disjunctive binder now pay it with `Or.inl` (a `RELAY` and a
    `FIELD` each become a `PAY`).  The last is a second application of
    `landing_or_park_ska`, at the props park's landing (`DECLINE` 1).
    `skipped` 30 → 31 is `live_of_dispatch`, as at `RelaySupplyCensus`.

    **Item 295: 102 → 104, `PAY` 15 → 17.**  `accum_flow_open_depth0`'s
    `h_park` is `h_pending.arm_or_col`, a `VIA PendingNode.arm_or_col` edge at
    every use.  The `pendingBlock` and `pendingMapValue` arms pay
    `flowKeyRoute_of_open`'s `h_park` with the park's own flag now
    (`Or.inl h_sk_old`, `Or.inl h_sk_mv`), so two `VIA` edges become `PAY`;
    and `slot_ride` and the props arm's fallback apply `flowKeyRoute_of_root`,
    each reading `h_park`, two `VIA` edges in their place. -/
-- 2026-10-24 (B3 [66] col-0 threading): skipped 31 → 38 — eight new gate lemmas (`ParkFloor.stacked`,
-- `gate_of_blockEntry`, `gate_of_key`, `gate_of_value`, `blockScalar_park_gate`, `noPending_gate_of_inFlow`,
-- `PendingNode.nil_gate_of_allowDirectives`, `FlowBaseRoutes.value`) return functions, so their values
-- have fewer leading lambdas than their types have binders; the census refuses to read them, by design.
-- 2026-10-29 (item 389): skipped 39 → 40 — the landed birth's `nv < k` mapping-top term (`dite` over `s_prep.currentIndent < k` inside `Or.inl`) is a shape the census skips; no edge moved.
-- 2026-10-29 (item 394, option B): skipped 41 → 42 — the mapping arm's valueF supply is an
-- `Or.elim` over the park's cover (informative → carried, punted → declined), a shape the
-- arm-payment reader skips (RelaySupply's tally skipped 41 → 42 the same way).
def expectedTally : String :=
  "edges=106 skipped=42 DECLINE=21 FIELD=7 PAY=17 RELAY=29 VIA=32"

run_cmd do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if (`L4YAML.Tests).isPrefixOf nm then continue
    for (i, bn, tg) in armBinders ci.type do
      let lbl := if tg then "tight" else "loose"
      rows := rows.push s!"{lbl} {nm.getString!}#{i} ({bn})"
  let got := (rows.qsort (· < ·)).toList
  if got != expectedBinders then
    throwError "the ARM BINDER census moved.\nexpected ({expectedBinders.length}):\n{
      String.intercalate "\n" expectedBinders}\ngot ({got.length}):\n{
      String.intercalate "\n" got}"
  let (es, sk) ← armEdges ``L4YAML.Proofs.StreamAccum.landing_or_park_ska
  let mut t : Std.HashMap String Nat := {}
  for e in es do
    let k := (e.how.splitOn " ").head!
    t := t.insert k (t.getD k 0 + 1)
  let parts := (t.toList.map (fun (a, b) => a ++ "=" ++ toString b)).mergeSort (· ≤ ·)
  let gotTally := s!"edges={es.size} skipped={sk} {String.intercalate " " parts}"
  if gotTally != expectedTally then
    throwError "the ARM PAYMENT census moved.\nexpected: {expectedTally}\ngot:      {gotTally}"

/-- The nine `Or.imp_left` relays into the two landings, by caller — item 223's
    "FOUR TIMES" is the four at `closeThenBlock`, and the other five are next
    door.  A projection is invisible to a census of `Or.inl`, which is why this
    row needs the resolver and not a grep. -/
def expectedProjections : List String :=
  [ "4 accum_block_on_closeThenBlock", "8 accum_block_on_pendingBlockContent" ]

run_cmd do
  let (es, _) ← armEdges ``L4YAML.Proofs.StreamAccum.landing_or_park_ska
  let lands := es.filter (fun e =>
    (e.callee == ``L4YAML.Proofs.StreamAccum.landing_or_park_save
      || e.callee == ``L4YAML.Proofs.StreamAccum.landing_or_park_ska)
    && e.pipes == ["Or.imp_left"])
  let mut m : Std.HashMap String Nat := {}
  for e in lands do
    let k := e.caller.getString!
    m := m.insert k (m.getD k 0 + 1)
  let got := (m.toList.map (fun (a, b) => toString b ++ " " ++ a)).mergeSort (· ≤ ·)
  if got != expectedProjections then
    throwError "the PROJECTION census moved.\nexpected ({expectedProjections.length}):\n{
      String.intercalate "\n" expectedProjections}\ngot ({got.length}):\n{
      String.intercalate "\n" got}"

/-! ## §2  The one read, and the refutation that the loose arm cannot state

`colon_fires_implicit_key` spends the conjunct twice, at the two places its
pack's guard meets a park that preprocessing did not re-save.  Both are the
same three lines, and this is them: the conjunct says the park carried no
save, the branch supposes it carried one, so the branch is dead. -/

lemma conjunct_refutes_save {sc : ScannerState} {sp_scan : SurfPos}
    (h_arm : (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨
      0 < sp_scan.col)
    (h_col : sp_scan.col = 0) (h_poss : sc.simpleKey.possible = true) : False := by
  rcases h_arm with ⟨_, h_poss_f⟩ | h_colpos
  · exact absurd h_poss (by rw [h_poss_f]; exact Bool.false_ne_true)
  · omega

/-- **And the loose arm provably cannot.**  This is what makes the weakening
    probe's error a fact about the ARM rather than about the proof that broke:
    there is a state with the flag UP and a save PENDING at column 0, so the
    loose reading leaves the branch alive.  The witness is built, not asserted. -/
lemma loose_arm_cannot_refute_save :
    ¬ ∀ (sc : ScannerState) (sp_scan : SurfPos),
        (sc.simpleKeyAllowed = true ∨ 0 < sp_scan.col) →
        sp_scan.col = 0 → sc.simpleKey.possible = true → False := by
  intro h
  exact h { ScannerState.mk' "" with
              simpleKeyAllowed := true, simpleKey := { possible := true } }
    ⟨[], 0⟩ (Or.inl rfl) rfl rfl

/-! ## §3  Why the landings can never read it

The landings' left branch routes through `saveSimpleKey`, and outside a flow
`saveSimpleKey` branches on `simpleKeyAllowed` alone: armed, it OVERWRITES the
save without consulting the one it replaces.  So two states differing only in
`simpleKey` leave it agreeing, and no conclusion downstream of an armed save
can depend on the conjunct.  That is the spend census's answer for the two
consumers the plan named, and it is a fact about the FUNCTION, not about the
proof that happens to sit above it. -/

lemma saveSimpleKey_armed_indep {s : ScannerState} (k₁ k₂ : SimpleKeyState)
    (h_fl : s.inFlow = false) (h_a : s.simpleKeyAllowed = true) :
    saveSimpleKey { s with simpleKey := k₁ } = saveSimpleKey { s with simpleKey := k₂ } := by
  have h0 : ¬ (s.flowLevel > 0) := by simpa [ScannerState.inFlow] using h_fl
  unfold saveSimpleKey
  simp [ScannerState.inFlow, ScannerState.currentPos, h0, h_a]

/-! ## §4  The eight loose rows are corollaries, not debt

If a caller ever holds the tight arm and wants a landing, it does not need the
landing tightened: the tight statement follows from the loose lemma by one
`imp_left`, here, once, for every caller there will ever be.  Nothing in the
library changes and no cascade is paid.  These two are the rows item 223's
NEXT called "the cheapest next reading"; they are cheaper still unbought. -/

lemma landing_or_park_save_tight {sc s_prep : ScannerState} {sp_scan : SurfPos}
    {c : Char}
    (h_noflow : s_prep.inFlow = false)
    (h_larm : sp_scan.col ≠ 0 → s_prep.inFlow = false →
      s_prep.simpleKey.possible = true ∧ s_prep.simpleKey.pos.col = s_prep.col ∧
      s_prep.simpleKeyAllowed = true ∧
      (s_prep.currentIndent ≤ (s_prep.col : Int) ∨ s_prep.indents.size ≤ 1))
    (h_park : (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨
      0 < sp_scan.col)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    s_prep.simpleKey.pos.col = s_prep.col :=
  landing_or_park_save h_noflow h_larm (h_park.imp_left And.left) h_preprocess

lemma landing_or_park_ska_tight {sc s_prep : ScannerState} {sp_scan : SurfPos}
    {c : Char}
    (h_noflow : s_prep.inFlow = false)
    (h_larm : sp_scan.col ≠ 0 → s_prep.inFlow = false →
      s_prep.simpleKey.possible = true ∧ s_prep.simpleKey.pos.col = s_prep.col ∧
      s_prep.simpleKeyAllowed = true ∧
      (s_prep.currentIndent ≤ (s_prep.col : Int) ∨ s_prep.indents.size ≤ 1))
    (h_park : (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨
      0 < sp_scan.col)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    s_prep.simpleKeyAllowed = true :=
  landing_or_park_ska h_noflow h_larm (h_park.imp_left And.left) h_preprocess

/-! ## §5  The family reading has no library reader

Item 223 put `PendingNode.arm_tight_or_col` in the library and reduced item
78's nine-arm `arm_or_col` to one `And.left` off it.  That `And.left` is its
only library call site: the tight family reading is projected back to loose one
line after it is stated, and every other use of it is in a guard module.  The
one reader of the conjunct does not go through it at all — §1's `FIELD=6` is
the route, a park constructor's own field taken by `casesOn` inside
`accum_block_pending` and relayed twice.

That is not an argument for deleting it.  It is the measurement item 223's
pricing could not make, because the ladder counts what a carrier CAN state and
nothing counted whether anything downstream reads what it states. -/

example {sc : ScannerState} {sp_start sp_block sp_scan : SurfPos}
    (h_noflow : sc.inFlow = false)
    (h : PendingNode sc false sp_start sp_block sp_scan) :
    sc.simpleKeyAllowed = true ∨ 0 < sp_scan.col :=
  (PendingNode.arm_tight_or_col h_noflow h).imp_left And.left

end Tests.Guards.ArmSpendCensus
