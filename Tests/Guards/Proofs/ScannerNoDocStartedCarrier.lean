module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The "no document started" carrier (DOCS item 116)

Item 110 measured 1c's constructor tightening and found all 16 breaking
sites blocked by the same missing datum: `rootMapRoute` and its kin append a
completed top-level node to the accumulated stream as a fresh bare document
via `[211]`'s `implicitContinue`, which is honest only when the stream has
started none — and `SLYamlStream sp_start sp` does not record that.  The
props landing (the other named prerequisite) was paid at item 111; this item
pays the record itself.

**The build is one field in `noPending`'s own style.**  The constructor has
exactly eight producers, and
~~`h_nodoc : inFlow = false → documentEverStarted = false → GStar
SLDocumentPrefix sp_start sp`~~ **`h_nodoc : inFlow = false → GStar
SLDocumentPrefix sp_start sp`** (the flag premise came off at item 135, where
the field was first spent: no producer used it and no consumer could discharge
it) splits them the way `h_col`'s disjunction
does: the seven flow-interior sites refute the premise with the
`inFlow_of_flowLevel_eq h_fl1` they already pay the other two fields with
(`nodoc_of_flowLevel_succ`), and the seed pays the real witness — `[202]`'s
byte order mark if there is one, nothing else — ignoring it.  A
`---` parks `pendingDocStart` and raises the flag, a `...` parks
`pendingDocEnd`, a directive parks the `true`-indexed `pendingDirective`,
and every content and indicator dispatch runs behind the wrapper that raises
the flag — so a block-context `noPending` with the flag still down stands on
prefixes alone.  The spend the tightening will make is landed beside
`rootMapRoute`: `nodocMapRoute`/`nodocMapRouteF` derive the stream from the
witness via `single`, whose `l-any-document?` slot 1c leaves untouched, and
`ssl_comments_extend_prefixes` carries the witness from the park to the
landing.  Nothing changes hands today — the 16 sites still spend
`implicitContinue`, and the constructor migration stays LAST.  (First spent at
item 135, which also re-measured the 16 as NINE; see §6.)

§1 is the family at the runtime; §2–§5 are the carrier, the payments, the
landing extension and the spend at their types; §6 is what this item does
not close. -/

namespace L4YAML.Tests.Guards.ScannerNoDocStartedCarrier

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
  L4YAML.Proofs.NodeProduction

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

-- §1 The family the carrier records.  A bare document with nothing before it
-- (the seed's `GStar.nil` witness)…
#guard emits "a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
-- …behind comment lines (the witness extended by `[202] l-comment*` — the
-- same `[79] s-l-comments` the landing crosses)…
#guard emits "# c1\n# c2\na: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
-- …behind the byte order mark (the seed's one REAL prefix — the witness
-- `initial_stream_and_prefix` now returns beside the stream)…
#guard emits "﻿a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
-- …behind both…
#guard emits "﻿# c\na: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
-- …and behind blank lines.
#guard emits "\n\na: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
-- A top-level flow node is the same family: the base routes are built at the
-- `[`, off the same park the carrier now decorates.
#guard emits "[1, 2]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]
#guard emits "# c\n[1, 2]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]

-- The flag's own producers: a `---` raises `documentEverStarted` at
-- `scanDocumentStart`, so the explicit document never asks this carrier.
#guard emits "---\na: 1\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "%YAML 1.2\n---\na: 1\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]

-- The directive region never coexists with a virgin block-context park at
-- content time: directives without `---` are §9.1.5 [209]'s refusal, so no
-- reachable `noPending` stands behind a consumed directive.
#guard refuses "%YAML 1.2\na: 1\n"
#guard refuses "%YAML 1.2\n"

-- A zero-document stream is the seed witness spent as the WHOLE derivation:
-- `single(prefix*, none, nil)`, no carrier needed at any landing.
#guard emits "# just a comment\n" ["+STR", "-STR"]
#guard emits "" ["+STR", "-STR"]

-- §1-residue: the SUFFIX state.  `...` neither raises the flag nor parks
-- `noPending` — it parks `pendingDocEnd`, whose close spends
-- `suffixContinue` with its document slot already empty — so a bare document
-- after a suffix run still rides `implicitContinue`'s bare slot (the
-- over-approximation), and its honest carrier (`suffixContinue`'s own open
-- `l-any-document?`) is the mirror item this one does not build.  Pinned as
-- ACCEPTED: these are 1c's residue families, not refusals.
-- (The mirror carrier CLOSED by item 117 — `SuffixRun` + the landing
-- skeleton's `h_sfx` face; see `ScannerSuffixRunCarrier`.)
#guard emits "...\na: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "...\n...\na: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "a: 1\n...\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC ...",
   "+DOC", "+MAP", "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]

/-! ## §2 The carrier: the virgin park holds the witness

The constructor's arity, stated: a block-context park with nothing pending
carries, beside its column and its armed save, the fact that there are
document prefixes and nothing else behind it.  The field is MANDATORY — no
`∨ True` — because its premise already names the two producer families: the
seed pays, the seven flow sites refute.  (Item 135 dropped the second
premise, `documentEverStarted = false`; the block-context park IS the seed,
so the flag added nothing the `inFlow` premise did not already carry, and
asking for it made the field uncashable at every consumer.)

**Item 186 added the SCANNER-side twin.**  `h_noek` says the same thing about
the same eight producers on the other side of the coupling: behind a virgin
block-context park nothing has been scanned, so the explicit-key register is
dead.  It is paid by the same split — the seed writes `none` in
`ScannerState.mk'`, the seven flow sites refute the premise — and what it buys
is a REFUTATION at the landed `:`, which used to split on a stamp source it
could not decide and now reads it off the park.  See `BlockDeferralClasses`
§5. -/

example {sc : ScannerState} {sp_start sp : SurfPos}
    (h_col : sp.col = 0 ∨ sc.inFlow = true)
    (h_arm : (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨ sc.inFlow = true)
    (h_nodoc : sc.inFlow = false → GStar SLDocumentPrefix sp_start sp)
    (h_noek : sc.inFlow = false → sc.explicitKeyLine = none)
    -- Item 208: and the STACK face, the third of the same shape.
    (h_ntop : sc.inFlow = false → sc.currentIndent < 0)
    (h_gate : sc.inFlow = false → sp.col ≠ 0 → ¬(Proofs.ScannerCoupling.CommentOk sc ∧ sc.peek? = some '#')) :
    PendingNode sc false sp_start sp sp :=
  PendingNode.noPending sp_start sp h_col h_arm h_nodoc h_noek h_ntop h_gate

-- The flow producers' payment is the refutation, from the one fact all
-- seven sites hold: depth ≥ 1 makes the face's `inFlow = false` premise
-- refute itself — and it pays BOTH faces, which is what says the two fields
-- have the same producer split rather than merely the same shape.
example {sc : ScannerState} {n : Nat} {sp_start sp : SurfPos}
    (h_fl1 : sc.flowLevel = n + 1) :
    sc.inFlow = false → GStar SLDocumentPrefix sp_start sp :=
  nodoc_of_flowLevel_succ h_fl1

example {sc : ScannerState} {n : Nat} (h_fl1 : sc.flowLevel = n + 1) :
    sc.inFlow = false → sc.explicitKeyLine = none :=
  noek_of_flowLevel_succ h_fl1

/-! ## §3 The seed's payment

`initial_stream_and_prefix` returns the witness beside the stream it always
built — the byte order mark's prefix in the BOM branch, `GStar.nil` in the
other — and the seed park pays `h_nodoc` with it unconditionally, both
premises ignored. -/

example (input : String) :
    ∃ sp, GStar SLDocumentPrefix ⟨input.toList, 0⟩ sp ∧
          SLYamlStream ⟨input.toList, 0⟩ sp := by
  obtain ⟨sp, h_stream, -, -, h_prefix⟩ := initial_stream_and_prefix input
  exact ⟨sp, h_prefix, h_stream⟩

/-! ## §4 The landing extension

The comment lines a landing crosses are `[202] l-document-prefix`'s own, so
the witness travels from the park to the landing over the same
`[79] s-l-comments` that `ssl_comments_extend_stream` absorbs into the
stream. -/

example {sp_start sp sp_land : SurfPos}
    (h_pre : GStar SLDocumentPrefix sp_start sp)
    (h_ssl : SSLComments sp sp_land)
    (h_col0 : sp.col = 0) :
    GStar SLDocumentPrefix sp_start sp_land :=
  ssl_comments_extend_prefixes h_pre h_col0 h_ssl

/-! ## §5 The spend: `rootMapRoute`'s interface with no stream anywhere

The tightening's route, end to end: the face fired by the two flags, the
witness carried to the landing, and both of `rootMapRoute`'s faces — the
route and its resume twin — derived via `single`, whose document slot 1c
leaves untouched.  No `SLYamlStream` appears in the premises: where
`rootMapRoute` EXTENDS a stream it cannot interrogate, this derivation
REBUILDS it from the carrier, which is what makes the bare document the
stream's first rather than `[211]`'s unmarked continuation. -/

example {sc : ScannerState} {sp_start sp sp_land sp_key : SurfPos} {k : Nat}
    (h_nodoc : sc.inFlow = false → GStar SLDocumentPrefix sp_start sp)
    (h_block : sc.inFlow = false)
    (h_ssl : SSLComments sp sp_land)
    (hcol0 : sp_land.col = 0)
    (h_ind : SIndent k sp_land sp_key)
    (h_col0 : sp.col = 0) :
    (∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v) ∧
    (∀ sp_v, SBlockMapEntry k sp_key sp_v →
     ∀ sp_e, SCompactMapTail k sp_v sp_e →
     ResumeFrames (SLYamlStream sp_start) [] sp_e) :=
  ⟨nodocMapRoute hcol0
      (ssl_comments_extend_prefixes (h_nodoc h_block) h_col0 h_ssl) h_ind,
   nodocMapRouteF hcol0
      (ssl_comments_extend_prefixes (h_nodoc h_block) h_col0 h_ssl) h_ind⟩

/-! ## §6 What this item does NOT close

* The SUFFIX state.  `pendingDocEnd` carries no carrier of its own, and its
  close spends `suffixContinue` with the document slot already empty — so
  `...⏎a: 1` and its twins (§1's last three pins) still give the bare
  document to `implicitContinue`.  The mirror carrier — the suffix run held
  open so the next document lands in `suffixContinue`'s own
  `l-any-document?` — is its own item.  (CLOSED by item 117 — the landing
  skeleton's `h_sfx` face, spent through `suffixMapRoute`/`suffixMapRouteF`/
  `suffixNodeRoute`; the content-dispatch landings route through the open
  arm now.)
* The raised-flag side.  `sc.allowDirectives = false → sc.documentEverStarted
  = true` is a scanner-state invariant nothing threads; the tightening's
  case split at a raised flag will be served by the suffix carrier and the
  scanner's refusals, not by this witness.
* The 16 sites.  `rootMapRoute`, `rootMapRouteF`, ~~`flowSeq_extends_stream`~~
  and their kin still spend `implicitContinue`'s bare slot; the constructor
  (`GOpt SLAnyDocument` → explicit-only continuation) is the migration's
  LAST step (item 110), now with both of its measured prerequisites paid
  (the props landing at item 111, the carrier here).
  (**16 is now NINE**, re-measured at item 135, which deleted the two dead
  flow extenders — `flowSeq_extends_stream` among them — turned
  `pendingDocStart`'s document builder into a route, and spent THIS field at
  `accum_block_on_noPending`'s two root-sequence faces, the carrier's first
  consumer.  ~~`nodocMapRoute`/`nodocMapRouteF` are still unspent: the seed's
  sequence reaches `single` inline, and the map faces wait on the landing's
  three-way disjunction.~~  **Spent at item 136**, which gave the landing face
  its HEAD arm and paid it at the park's other three landings — the block
  `:`/`?` through `nodocMapRoute`/`nodocMapRouteF`, the content dispatch
  through the new `nodocNodeRoute`, and the flow open through the new
  `nodocFlowResumeSep` and `flowKeyRoute_of_root`'s head arm.  See
  `StreamRouteSwapSurface` and `StreamHeadLandingFace`.)
* The compact branches' resume twins on both key packs (item 99's
  fused-closure residue) and the flow frame's rider
  (`FlowBaseRoutes.key`, 67b) are untouched — different rows of the same
  ledger. -/

end L4YAML.Tests.Guards.ScannerNoDocStartedCarrier

end Blanket
