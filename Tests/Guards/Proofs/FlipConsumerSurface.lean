import L4YAML.Proofs.Production.StreamAccum

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The `[210]` narrowing's consumer surface, pinned (DOCS item 183)

Row 19's 1c ends by narrowing `[211] l-yaml-stream`'s implicit-continuation
slot from `GOpt SLAnyDocument` to `GOpt SLExplicitDocument`.  The narrowing
instrument — flip the constructor, build — reports FIVE errors, at
`topLevelFlowResumeSep`, `rootMapRoute`, `rootMapRouteF`, `bareNodeRoute` and
`structural_dispatch_to_pending`, and has reported those same five since item
166.  That number does not move when a payment lands, because the five are the
flip's WORK: the four raw routes it deletes and the one `SLAnyDocument.explicit`
wrapper it unwraps.  What a payment moves is the surface BELOW them — who still
reaches a raw route — and this file pins that.

**What is counted.**  Every non-internal constant of
`L4YAML/Proofs/Production/StreamAccum.lean` whose value applies one of the four
raw routes, or one of the five guards that stand in front of them
(`rootMapRoute_or_refused`, `rootMapRouteF_or_refused`, `bareNodeRoute_or_refused`,
`bareNodeRoute_or_refused_content`, `topLevelFlowResumeSep_or_refused`), with
its application count.  The guards themselves are excluded from their own
census — they are where the raw term is written, not where it is spent.

**The denominator is the module, not the environment.**  Other
`Tests/Guards/Proofs/` files apply the routes and the guards too, in worked
examples that document their interfaces (`StreamBlockLandingRefusal`,
`StreamMarkerLandingFace`); those are prose, not accumulation, and the module
filter is what keeps them out of the number.  A new consumer inside
`StreamAccum` — the direction that matters — fails this gate.

**Why the guards and not the raw routes alone.**
`Scratch/CensusRawRoutes.lean` counts the four raw terms and skips the guards,
which is what says each raw term is written once; it reads TWO holders and has
since item 181.  It cannot see a payment that removes a guard application,
which is every payment row 19 has left.  So this census counts both, and the
number it pins is the one future items have to move.

**And the escape the flip runs into.**  `block_dispatch_deferred` is
`PendingNode.pendingFlow`'s only producer, and `pendingFlow` is the one park
that offers the landing faces NO arm to take: its `CompletedTail` is FALSE by
construction (the token behind it is a `-`/`?`/`:`), it carries no suffix run,
no marker route, no document-prefix witness and no resume frames.  Every door
that reaches a raw route reaches it through that park among others, so the
deferral's own census is pinned here beside the flip's — R3's deletion is what
empties these arms, and the two numbers move together.

**By CLASS, since item 184; by ROUTE, since item 185.**  The deferral's
applications are partitioned in the source by the branch that reaches them.
Item 184 read three classes — the undecided stamp source (**9**), the mid-line
inline residue (**2**), and `pendingFlow`'s own arm (**1**).  Item 185 measured
the nine and found them three QUESTIONS with three different prices: the park's
pack stands off the landing's column (**3**), the park carries no pack at all
(**4**), or the fill is COMPACT and the stamp is the only thing that funds it
(**2**).  So the DEFERRAL lane counts five names rather than one and a class
emptying shows as a wrapper leaving the list.  The PACK PUNT lane beside it
counts ~~what empties the inline class: `KeyPackPunt`'s two surviving reasons~~
the punt's reasons, which are five of the inline class's seven arms (DOCS item
286; the other two are the no-key arm and the value park whose slot declines).
Items 288 and 289 refuted the value park's arm and the props consumer's `tab`,
so the reasons are four of the five arms left — and item 293 refuted the no-key
arm, so they are all four.
Both partitions and the input families they serve are documented at
[`BlockDeferralClasses`](BlockDeferralClasses.lean).

**Item 186 took the first site out, and a whole ROW with it.**  Twelve
applications across five consumer lemmas are now ~~**ELEVEN across FOUR**~~
**NINE across FOUR** (item 209 deleted `block_dispatch_deferred_stamp_compact`,
whose class is refuted, and with it two of the eleven):
`accum_block_on_noPending` reached the escape once, on the undecided stamp
source, and `noPending`'s new `h_noek` — a virgin block-context park is the
stream's seed, so its explicit-key register is dead — decides that source
instead of splitting on it.  A row leaving this census is what a class
emptying looks like, which is the shape item 184 built the lane for.

**Re-derived from cold at item 210**, independently of this module:
`scripts/park_nic0_price.py sites` threads a premise through the escape and each
of its wrappers and reads the census off the failures — **9 applications across
4 consumer lemmas**, 3 `accum_block_on_closeThenBlock`, 3
`…_pendingBlockContent`, 2 `…_pendingBlock`, 1 `accum_content_pending`.  That
mode had been broken since item 209 (a control pinning the wrapper COUNT) and
mis-anchored since item 208 (a cascade collapse built for the park modes), so
the deletion this docstring records went two items without an instrument able to
confirm it. -/

namespace L4YAML.Tests.Guards.FlipConsumerSurface

open Lean Elab Command

/-- Occurrences of each of `tgts` in an elaborated term, accumulated
    positionally.  ONE traversal for every target: these values are whole
    accumulation proofs and a traversal per name costs minutes. -/
partial def tally (tgts : Array Name) : Expr → Array Nat → Array Nat
  | .const n _, acc =>
      match tgts.findIdx? (· == n) with
      | some i => acc.set! i (acc[i]! + 1)
      | none => acc
  | .app f a, acc => tally tgts a (tally tgts f acc)
  | .lam _ t b _, acc => tally tgts b (tally tgts t acc)
  | .forallE _ t b _, acc => tally tgts b (tally tgts t acc)
  | .letE _ t v b _, acc => tally tgts b (tally tgts v (tally tgts t acc))
  | .mdata _ e, acc => tally tgts e acc
  | .proj _ _ e, acc => tally tgts e acc
  | _, acc => acc

def ns : Name := `L4YAML.Proofs.StreamAccum

/-- The four terms that hand `[211]`'s implicit continuation a BARE document —
    the ones the flip deletes. -/
def raws : List Name :=
  [`rootMapRoute, `rootMapRouteF, `bareNodeRoute, `topLevelFlowResumeSep]

/-- The five guards that stand in front of them, each with §9.2's landing
    refusal (and, at the content landing, its dangling reading) taken out of
    the raw route's domain.  **Item 296: the two entry pack producers apply
    `rootMapRoute_or_refused` and `rootMapRouteF_or_refused` once each**, on the
    dedent branch's frameless exit, with `h_ref` declined: a landing that
    dedents emits a `blockEnd` first, which completes no value, so §9.2's
    check stands aside.  They go through the guards so that RAW ROUTES keeps
    its one row.  **Item 297: the `w ∉ ks` exit applies the same pair**, so
    each producer reads two of each. -/
def guards : List Name :=
  [`rootMapRoute_or_refused, `rootMapRouteF_or_refused,
   `bareNodeRoute_or_refused, `bareNodeRoute_or_refused_content,
   `topLevelFlowResumeSep_or_refused]

/-- `pendingFlow`'s only producer, and the four wrappers that partition its
    applications by the branch that reaches them (items 184–185): the stamp
    source's three ROUTES — the pack off the landing's column, no pack at all,
    and the compact fill — the mid-line inline residue, and, through the bare
    name, `pendingFlow`'s own arm, which the escape produces and which goes
    with the constructor.  The counts here are the DOMAIN's classes, so a class
    emptying shows as a wrapper leaving the list rather than as a total
    drifting. -/
def deferral : List Name :=
  [`block_dispatch_deferred,
   `block_dispatch_deferred_stamp_offcol,
   `block_dispatch_deferred_stamp_nopack,
   -- ~~`block_dispatch_deferred_stamp_compact`~~ — **the wrapper LEFT the list
   -- at item 209**, which is the shape the docstring above named: a class does
   -- not empty by its total drifting, it empties by its wrapper going away.
   -- Both of its sites are now `compact_deferral_refuted … |>.elim`.
   `block_dispatch_deferred_inline]

/-- What empties the inline-residue class: the implicit-key pack's punt
    reasons (item 102 — the mid-line `:` composes whenever
    `colon_fires_implicit_key` gets a pack, so the residue IS the punt).

    ~~The other two reasons are refuted at their consumers and have no producer
    left.~~  **Item 211: neither half holds, and this lane's own walk says so
    the moment it is asked.**  `tab` is produced twice
    (`entryKeyPack_of_dispatch`, `entryPropsKeyPack_of_dispatch`) and
    `implicitValue` three times.  And they are refuted at ONE consumer rather
    than at their consumers: at `colon_fires_props_key` the `tab` arm RIDES the
    caller's deferral exactly as `dedent` and `noKeyContext` do — three
    unconditionally, and `implicitValue` on its break branch besides — so the
    inline class has at least THREE surviving reasons there and two at its
    sibling.  The lane
    counts all four now, which is what it would have had to do to see either.
    **Item 289: `tab` is refuted at both consumers**, the reason carrying the
    saved key's possibility and line, so two reasons ride at each — `dedent`
    and `noKeyContext`.  (No break branch rides it either, since item 287:
    each refutes the residue, `sslComments_refutes_inline_residue`.)

    `keyPackPunt_transport` is skipped for the same reason the wrappers are: it
    re-WRITES a reason it was handed rather than spending one. -/
def packPunt : List Name :=
  -- Item 297 deletes `KeyPackPunt.dedent`: both pack exits key a fresh document.
  -- Item 300 adds `KeyPackPunt.markerLine`, the stamp's twin over the `docStartLine` field.
  [`KeyPackPunt.tab, `KeyPackPunt.implicitValue, `KeyPackPunt.markerLine,
   `KeyPackPunt.noKeyContext]

/-- One census: the targets counted, and the definitions where the term is
    WRITTEN rather than spent, excluded. -/
structure Lane where
  tag : String
  targets : List Name
  skip : List Name
  deriving Inhabited

/-- `name: target=count …` for every StreamAccum constant that applies one of
    each lane's targets, sorted.  All lanes share ONE walk of the environment —
    the module's values are large and a walk per lane costs minutes.
    `allowOpaque := true` is required or every theorem reads as valueless and
    the census silently returns nothing. -/
def surface (lanes : Array Lane) : CommandElabM (Array (Array String)) := do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? (ns ++ `bareNodeRoute)
  -- every lane's targets, once, so one walk serves all of them
  let names : Array Name := lanes.flatMap (fun l => l.targets.toArray)
  let quals : Array Name := names.map (ns ++ ·)
  let zero : Array Nat := names.map (fun _ => 0)
  let mut rows : Array (Array String) := lanes.map (fun _ => #[])
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    if env.getModuleIdxFor? n != modIdx then continue
    let some v := ci.value? (allowOpaque := true) | continue
    let counts := tally quals v zero
    let mut base := 0
    for i in [0:lanes.size] do
      let lane := lanes[i]!
      let mut out := ""
      if !lane.skip.contains n then
        for j in [0:lane.targets.length] do
          let c := counts[base + j]!
          if c > 0 then out := out ++ s!" {lane.targets[j]!}={c}"
      base := base + lane.targets.length
      if out != "" then rows := rows.set! i (rows[i]!.push s!"{n.getString!}:{out}")
  return rows.map (·.qsort)

/-- The gate: each census must be its pinned list, row for row. -/
def pin (lanes : Array (Lane × List String)) : CommandElabM Unit := do
  let got ← surface (lanes.map Prod.fst)
  for i in [0:lanes.size] do
    let (lane, expected) := lanes[i]!
    if got[i]!.toList != expected then
      throwError "{lane.tag} moved.\nexpected ({expected.length}):\n{
        String.intercalate "\n" expected}\ngot ({got[i]!.size}):\n{
        String.intercalate "\n" got[i]!.toList}"

/-! ## §1  The raw routes' direct holders

ONE definition, ONE application.  Item 181 deleted the two crossed-window
payments and took this from three holders to two; item 182's runtime floor left
it untouched, because that item's kit lands below every one of these.  The
survivor is the INDENTED content landing, whose three callers park on
`pendingBlock`, `pendingMapValue` and `pendingProps` — item 156 measured that
none of the three is refutable (`danglingNodePos?` reads `none` at all of them
and all three inputs parse), so what is missing there is a ROUTE, the enclosing
park's own, and not a guard. -/

/-! ## §2  The guards' holders — the surface a payment moves

SEVEN definitions, FOURTEEN applications, one row per door:

| door | guard(s) | what still reaches the raw arm |
|---|---|---|
| `accum_block_on_closeThenBlock` | `bareNodeRoute_or_refused` | the `-` lane's on-level landing — a `[183]` already open at this column (`- - a⏎- b`, `a:⏎- x⏎- y`, item 166): a missing ROUTE, the open sequence's continuation |
| `accum_content_pending` ×2 | `bareNodeRoute_or_refused_content` | `pendingFlow`'s break-crossed landings ALONE (item 174) — both `h_op` halves refute for a park with a completed tail |
| `accum_flow_open_depth0` | `topLevelFlowResumeSep_or_refused` | the two content parks at `h_op = true`, whose inputs the scanner REFUSES (§7 of `StreamFlipRemainderMap`), plus `pendingFlow` |
| `colon_open_map`, `question_open_map` | `rootMapRoute(F)_or_refused` | the sibling `:`/`?` landing whose park pays no resume face (item 173's cascade covers the rest) |
| `content_dispatch_routed` ×2 | `rootMapRoute(F)_or_refused` | the same, at the content landing's key side |
| `flowKeyRoute_of_root` | `rootMapRoute(F)_or_refused` | the sibling flow key whose park pays no frame (item 176's cascade covers the rest) |

Each `rootMapRoute_or_refused` row is paired with its entries-level twin
`rootMapRouteF_or_refused`, which is why those counts come in twos. -/

/-! ## §3  The deferral beside it

~~FOUR~~ **SEVEN** definitions, ~~ELEVEN~~ ~~NINE~~ ~~FIFTEEN~~ ~~FOURTEEN~~ ~~THIRTEEN~~ **TWELVE** applications
(item 186 — five and twelve before it; item 209 — the compact wrapper's two,
refuted and gone; **item 287** — the inline wrapper's two became eight, one at
each arm of DOCS item 286's measurement: `dedent`, `noKeyContext` and the
no-key arm at `colon_fires_implicit_key`, `tab`, `dedent` and `noKeyContext` at
`colon_fires_props_key`, and `accum_block_pending`'s frameless value park and
dead `pendingFlow` arm).  The count rose and the domain did not: the five
crossed-break arms that reached the old two sites are refuted now.  **Item
288** refutes the frameless value park's, which holds the stamp, and **item
289** the props consumer's `tab`, whose reason carries the saved key's
possibility and line, and **item 293** the implicit consumer's `¬ possible`,
on the content parks' `h_live`.
`pendingFlow` is not a `[210]`
construction site and never appears in the flip's five errors — it is the park
whose arms have nothing to pay the landing faces WITH, so it keeps the guards'
fallback arms alive wherever it can reach them.  Pinning it here is what makes
that dependency checkable rather than remembered: R3's deletion empties arms
this census counts, and a change to either number should be read against the
other.

The rows below are the DOMAIN's shape, not the module's: each landed-`:`
consumer contributes one `offcol` and one `nopack` because its `by_cases` on
the park's pack has exactly those two stuck arms, and the two consumers with a
compact-fill arm contribute a `compact` each.  The asymmetric row was
`accum_block_on_noPending`'s, and item 186 removed it: that park carries no
pack because it carries nothing at all, and the register face it does carry
now says the class-A branch cannot reach it.

Item 187 left the counts where they are and re-priced what emptying the
`nopack` row would cost: not the 23 payments a one-ring flip reported, but a
surface of **31 pack punts across 16 declarations** — the count this census
cannot see, because the punts are a field's alternative rather than a
definition's application.  The two instruments are complements, and
`BlockDeferralClasses` §6 carries the one this file does not.

Item 188 PAID the first of those 31 — the `?` frame's key, filled by a landed
sequence — and the counts below do not move by so much as a row.  That is the
expected reading and the reason to state it: a payment against an escape
narrows the DOMAIN of a stuck arm, and an arm with a narrower domain is still
an arm.  This census will register R3's progress only at the step where an arm
becomes unreachable and its wrapper is deleted; until then a flat table here is
evidence of nothing either way, and `BlockDeferralClasses` §7 carries what the
step actually bought.

Item 189 paid the second — the same slot filled by a landed MAPPING, where the
obstacle was not a missing carrier but a SHADOWED one — and again no lane
moves.  It adds one optional parameter to `accum_block_on_closeThenBlock` and
one to the two map openers, which this census does not count either: the DEFERRAL
lane counts applications of the escape, and a new punting parameter is neither
an application nor a pack punt.  `BlockDeferralClasses` §8 carries the
measurement, including the arm-swap that shows the shadowing was a policy.

Item 190 paid the COMPACT twin at the remaining two `_stamp_offcol` sites, and
this census stays flat for a THIRD reason worth separating from the other two.
It is not that the payment is small: the item adds a constructor field to
`pendingMapValue`, `pendingBlock` and `pendingBlockContent`, and touches every
producer of all three.  It is that none of what it adds is in any lane's
vocabulary — a new punting FIELD is not an application of the escape and not a
`KeyPackPunt` constructor, so all three lanes are blind to constructor growth
by construction.  The instrument that does see it is the per-field flip, and
`BlockDeferralClasses` §9 carries four readings of it taken at one commit: each
new field against the field it twins.  A census reports the surface it was
built to report, and saying which questions it cannot answer is part of
reporting it.

Item 191 paid the residue item 190 named — a landing two or more frames up —
and this census is flat again, now for a FOURTH reason, and it is the sharpest
of them.  The item adds no application, no parameter and no field: it changes
the TYPE of three fields item 190 already added, from `∃ nv` to `∃ ns : List Nat`
with a membership test at the landing.  Every lane here counts occurrences of
something, and a generalization in place occurs nowhere.  Even the per-field
flip cannot see it — re-run at this commit, `pendingMapValue.h_explUp` reads
7 declarations / 9 errors and `pendingBlock.h_kslotUp` reads 6 / 22, both
exactly item 190's numbers, because widening a field moves no PUNT.  What does
see it is the composed derivation: `BlockDeferralClasses` §10 builds the chain
through two `?` landings and answers two different landings from ONE funder,
which is the thing `∃ nv` cannot do and the thing no count reports.

Item 192 carried the chain across a CONSTRUCT — the flow open, close and the
park it re-parks as — and this census is flat a FIFTH time, for item 191's
reason.  What is new is at the other instrument, and it is a caution about
reading it across a refactor.  The per-field flip's DECLARATION counts hold
(`FlowBaseRoutes.vslot` 3, `pendingContent.h_vpack` 5, unchanged by the
widening) but its ERROR counts FALL — 17 → 11 and 35 → 23 — after a payment
that strictly added reach.  The cause is that the item introduces a combinator
(`frameChainUnion`), and a combinator's argument type does not mention the
field: the punts that used to sit in a preference `match`'s branches now sit
inside the helper's arguments, so flipping the field breaks one result position
per SITE where it used to break every branch.  Item 188 warned that an error
count is not monotone in the domain; this says something narrower and sharper —
an error count is not comparable across a change that alters how the punts are
nested.  Declaration counts still are, which is why they are the number to
carry forward.

Item 193 threaded the chain to the entry park's landed `?`, and this census is
flat a SIXTH time for item 191's reason.  What is new is that the per-field flip
was flat for a reason of its own, and the reason is worth separating from the
five readings before it: **a constructor FIELD's flip and the LEMMA PARAMETER
that carries it are two different surfaces.**  The field's flip deletes an
optional constructor argument, so what errors is the PRODUCERS — every site that
builds the constructor and must now supply the datum.  The parameter's flip
deletes an optional argument of a consuming lemma, so what errors is the uses
INSIDE it.  A payment that adds a consumer therefore moves the second and leaves
the first exactly where it was: `pendingBlock.h_kslotUp` reads 7 declarations /
23 errors at this commit and 7 / 23 at the parent, while the parameter of the
same name on `accum_block_on_pendingBlock` goes 5 → **6** errors over the two
declarations it reaches — 4 → 5 inside that lemma itself.  Five items of "the
census is flat" were all taken on the producer surface.

And one correction to our own record, found by re-running rather than by
reading.  Item 191's table reports `pendingBlock.h_kslotUp` at 6 / 22.  That was
true when written and went stale one item later: item 192 made
`accum_flow_open_depth0` a consumer of the field (0 → 3 mentions of the binder)
and re-ran the two FLOW fields instead of this pair, so the stale number rode
forward into item 192's entry as "flat".  The reading at both `a16a5566` and
here is 7 / 23.

Item 194 paid a punt that had waited on a PARAMETER LIST rather than on a
carrier, and its numbers refine item 193's sentence rather than repeating it.
The field surface is NOT flat this time: `pendingBlockContent.h_closeF` reads
3 declarations / 21 errors at `ffc5ef65` and **4 / 22** here, the new one being
`accum_block_pending` — the `match` that binds the field and hands it to the
lemma.  So a field's flip counts every site whose TERM changes type, which is
the producers that punt it AND the relays that pass it on; item 193 observed the
first half, because the item it was measuring added no relay.  The payment's own
surface is the parameter, which did not exist at the parent: `h_closeF_old` on
`accum_block_on_pendingBlockContent` reads **2 declarations / 2 errors**, one in
the lemma (the payment) and one at the caller.  A number that jumped because the
item introduced a new KIND of site is not evidence of reach, and the reach here
is the guards file's §13, not either count.

Item 195 separates two instruments that had been read as one, and then finds the
DECLARATION count blind to its own payment.

A FLIP deletes a field's `∨ True` and counts who can no longer punt.  A WIDENING
(`∃ nv : Nat` → `∃ ns : List Nat, ∀ nv ∈ ns`) leaves the escape in place, so
`Or.inr trivial` still elaborates and only the sites whose TERM changes type
move.  On `pendingMapValue.h_kslot` at `f113d701` the flip reads **9
declarations / 16 errors** and the widening **6 / 22**; the difference is exactly
the three PUNTERS (`colon_open_map`, `colon_open_map_explicit`,
`compact_open_map`), so a flip over-states a widening's surface — here by half.
The widening also has a wave structure the flip has not: its sixth declaration
was the RELAY `accum_content_pending`, whose one error was the field handed to a
still-narrow lemma parameter, and widening that parameter swapped in
`accum_content_on_pendingMapValue_indented` at 13 errors while the count stayed
at 6.  **A widen census reports one wave; a relay boundary hides the next**, and
the count is a price only once it is iterated to a fixpoint.

And this item's own payment is invisible to the declaration count.
`pendingMapValue.h_explUp` reads **8 declarations / 10 errors** at `f113d701` and
**8 / 11** here — flat where item 194's field moved 3 → 4 — because the new site
sits INSIDE `accum_block_pending`, which the field already reached on the slot
lane twenty lines away.  A declaration census answers "which proofs read this
field", not "which of their lanes do"; a lane that was never served is
indistinguishable in it from one that was.  The payment's reach is §14's
membership arithmetic, not this count.

Item 211 asked this lane for the one number the campaign had been carrying by
hand — `dedent` 7 sites in 5 declarations and `noKeyContext` 6 in 5, item 184's
reading, copied verbatim through twenty-two NEXT lists — and BOTH reproduce,
row for row, at every build since.  Three things around them do not.

**The lane's own ground was wrong.**  It counted two of four reasons because the
other two "have no producer left"; asked for all four, the same walk reads `tab`
at 2 productions and `implicitValue` at 3.  A census restricted on a claim it is
itself able to test is a census that cannot correct its author.

**The two instruments agree on the two reasons that were measured and not on
the third.**  `lake run punt-price` is item 184's other half as an
artifact — delete a constructor, build, group by declaration.  It reads `dedent`
7/5 and `noKeyContext` 6/5, agreeing; it reads `tab` at **7** where this lane
reads **5**, because `tab` is written `refine Or.inr (KeyPackPunt.tab ?_ ...)`
and the orphaned goal is a second error at each of its two productions.  Item
189 wrote the reason down in passing — "a `match` costs more to break than an
`Or.inr trivial`" — and never matched it to the agreement item 184 had recorded.

**And the number's UNIT glues two kinds of site.**  `dedent`'s 7 is 4
PRODUCTIONS and 3 CONSUMER ARMS; `noKeyContext`'s 6 is 3 and 3.  A production
hands the reason over and is emptied by a proof about the input; a consumer arm
is the `cases` label that spends it, and it goes when the last production does.
What R3 has to pay is seven productions, not thirteen sites — and this lane
cannot make that split, because an application is an application.
`lake run punt-price -- split` does, from the source, against this lane's own
site list.

**Item 296: `dedent` reads 5 sites, two productions and three consumer arms.**
The dedent branch's frameless exit keys a fresh document at the landing in both
entry pack producers, so each writes `dedent` once, on its `w ∉ ks` exit.
**Item 297 deletes it**: the `w ∉ ks` exit keys a fresh document too, and the
three consumer arms go with the constructor. -/

/-! ## The gate

All three lanes, in one walk of the module. -/

#eval show CommandElabM Unit from
  pin #[
    ⟨⟨"RAW ROUTES", raws, raws.map (ns ++ ·) ++ guards.map (ns ++ ·)⟩,
      ["content_dispatch_after_close: bareNodeRoute=1"]⟩,
    ⟨⟨"GUARDS", guards, guards.map (ns ++ ·)⟩,
      ["accum_block_on_closeThenBlock: bareNodeRoute_or_refused=1",
       "accum_content_pending: bareNodeRoute_or_refused_content=2",
       "accum_flow_open_depth0: topLevelFlowResumeSep_or_refused=1",
       "colon_open_map: rootMapRoute_or_refused=1 rootMapRouteF_or_refused=1",
       "content_dispatch_routed: rootMapRoute_or_refused=2 rootMapRouteF_or_refused=2",
       -- Items 296/297: the dedent branch's two exits, in both pack producers.
       -- Item 372 (2026-10-27): the `w ∉ ks` exit spells the bare-document
       -- fallback in its three unpaid cases (unpopped / uncovered / below the
       -- floor) and pays the `SeqTopKey` face in the fourth — four spellings,
       -- the same two application LINES item 368 counted.
       "entryKeyPack_of_dispatch: rootMapRoute_or_refused=4 rootMapRouteF_or_refused=2",
       "entryPropsKeyPack_of_dispatch: rootMapRoute_or_refused=2 rootMapRouteF_or_refused=2",
       "flowKeyRoute_of_root: rootMapRoute_or_refused=1 rootMapRouteF_or_refused=1",
       "question_open_map: rootMapRoute_or_refused=1 rootMapRouteF_or_refused=1"]⟩,
    ⟨⟨"DEFERRAL", deferral, deferral.map (ns ++ ·)⟩,
      ["accum_block_on_closeThenBlock: block_dispatch_deferred_stamp_offcol=1 block_dispatch_deferred_stamp_nopack=1",
       "accum_block_on_pendingBlock: block_dispatch_deferred_stamp_offcol=1 block_dispatch_deferred_stamp_nopack=1",
       "accum_block_on_pendingBlockContent: block_dispatch_deferred_stamp_offcol=1 block_dispatch_deferred_stamp_nopack=1",
       -- Item 288: the value park's frameless arm is refuted; the dead
       -- `pendingFlow` arm's application is the one left here.
       "accum_block_pending: block_dispatch_deferred_inline=1",
       "accum_content_pending: block_dispatch_deferred=1",
       -- Item 293: the `¬ possible` arm refutes, on the park's `h_live`.
       -- Item 297: the `dedent` arm goes with the constructor.
       "colon_fires_implicit_key: block_dispatch_deferred_inline=1",
       -- Item 289: the `tab` arm refutes, on the saved key's possibility and
       -- line the reason carries.  Item 297: the `dedent` arm goes with the
       -- constructor.
       "colon_fires_props_key: block_dispatch_deferred_inline=1"]⟩,
    ⟨⟨"PACK PUNT", packPunt,
       [ns ++ `keyPackPunt_transport,
        -- the type's own generated eliminators, which mention every
        -- constructor by construction and spend none
        ns ++ `KeyPackPunt.casesOn, ns ++ `KeyPackPunt.recOn]⟩,
      -- Item 297: no `dedent` row anywhere — the constructor is deleted.
      -- Item 300: `markerLine` — written at its two producers
      -- (`content_dispatch_routed`'s two cascades, `flowKeyPack_of_close`'s
      -- base slot), and read at the three consumers' `cases`; the flow open
      -- cases the run's punt twice now (stamp and marker), so its rows double.
      ["accum_flow_open_depth0: KeyPackPunt.tab=2 KeyPackPunt.implicitValue=2 KeyPackPunt.markerLine=2 KeyPackPunt.noKeyContext=2",
       "colon_fires_implicit_key: KeyPackPunt.tab=1 KeyPackPunt.implicitValue=1 KeyPackPunt.markerLine=1 KeyPackPunt.noKeyContext=1",
       "colon_fires_props_key: KeyPackPunt.tab=1 KeyPackPunt.implicitValue=1 KeyPackPunt.markerLine=1 KeyPackPunt.noKeyContext=1",
       "content_dispatch_routed: KeyPackPunt.markerLine=2 KeyPackPunt.noKeyContext=2",
       "entryKeyPack_of_dispatch: KeyPackPunt.tab=1 KeyPackPunt.implicitValue=1",
       "entryPropsKeyPack_of_dispatch: KeyPackPunt.tab=1 KeyPackPunt.implicitValue=1",
       "flowKeyPack_of_close: KeyPackPunt.implicitValue=1 KeyPackPunt.markerLine=1 KeyPackPunt.noKeyContext=1"]⟩]

end L4YAML.Tests.Guards.FlipConsumerSurface
