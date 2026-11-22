module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The park's face, built and spent (DOCS item 157)

Item 141 named the face and priced it; item 156 derived the reading the
producer has to hand over and left the consumer side unnamed.  This item builds
the consumer side, threads it, and spends it.

The face is a PREMISE on `pendingContent.h_closable` and on
`PendingNode.close_with_ssl`: a park whose completed node is a §9.2-DANGLING
run has no `[211]` reading at all, so the close is offered only to a consumer
that can say the landing already refused one.  Two readings pay it —
`dangling_none_of_check` at a landing that crossed a break, and
`dangling_none_of_eof` at end of input — and one lemma transports the
producer's half across preprocessing (`preprocess_danglingPred`).

What it BUYS is `bareNodeRoute_or_refused_content`: at a content landing off a
completed node, BOTH halves of item 139's discriminator are now refuted — the
landing at no open level by `bareDocument_refutes_landing` (item 139), the
landing ON one by `danglingPark_refutes_route` (this item) — so the
bare-document reading has no input to serve at all.

§1 is the face at its type, with the gating asymmetry measured.  §2 is the
transport, with the popping half's witness.  §3 is what the face buys, stated
as a refutation and counted at the routes.  §4 is item 156's named obstacle,
dissolved.  §5 is what is left: the property lane. -/

namespace L4YAML.Tests.Guards.DanglingParkFace

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

private def posStr : Option YamlPos → String
  | some p => s!"{p.line},{p.col}"
  | none => "none"

private def stepN (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | n + 1 =>
    match scanNextToken s with
    | .ok (some s') => stepN s' n
    | _ => none

/-- The gate, read off the real scanner at the landing `n` steps in: the
    character that landed, the flag `scanNextToken_checkDanglingNode` is gated
    on, the park's own reading, and the check's verdict. -/
private def gateAt (input : String) (n : Nat) : String :=
  match stepN ((ScannerState.mk' input).emit .streamStart) n with
  | none => "no-state"
  | some s =>
    match scanNextToken_preprocess s with
    | .ok (some (s1, c)) =>
      s!"c={c} ska={s1.simpleKeyAllowed} park={posStr (danglingNodePos? s)} chk=" ++
        (match scanNextToken_checkDanglingNode s s1 with
         | .ok _ => "ok"
         | .error e => s!"{repr e}")
    | .ok none =>
      s!"EOF park={posStr (danglingNodePos? s)} chk=" ++
        (match scanLoop_checkDanglingNode s with
         | .ok _ => "ok"
         | .error e => s!"{repr e}")
    | _ => "no-landing"

/-- The transport's own reading: the PARK's last real token, the LANDING's, and
    whether preprocessing's unwind popped between them. -/
private def transportAt (input : String) (n : Nat) : String :=
  match stepN ((ScannerState.mk' input).emit .streamStart) n with
  | none => "no-state"
  | some s =>
    match scanNextToken_preprocess s with
    | .ok (some (s1, _)) =>
      let nameOf (ts : Array (Positioned YamlToken)) : String :=
        match prevRealIdx? ts ts.size with
        | some j => if ts[j]!.val == .blockEnd then "blockEnd"
                    else if ts[j]!.val.completesFlowValue then "completesValue"
                    else if ts[j]!.val.isNodeProperty then "property"
                    else if ts[j]!.val.offersNodeSlot then "slot" else "other"
        | none => "none"
      s!"park={nameOf s.tokens} land={nameOf s1.tokens} " ++
        (if s1.indents.size < s.indents.size then "POPPED" else "same")
    | _ => "no-landing"

private def parseOk (input : String) : String :=
  match Events.streamToEvents input with
  | .ok _ => "PARSE-OK"
  | .error e => s!"PARSE-ERR {repr e}"

private def scanOk (input : String) : String :=
  match scan input with
  | .ok _ => "SCAN-OK"
  | .error e => s!"SCAN-ERR {repr e}"

/-! ## §1  The face, and the flag it is gated on

The two readings that pay it are the two §9.2 checks, and they are not alike:
the mid-stream one is gated on the break the landing crossed, the end-of-input
one on nothing.  That is the whole asymmetry, and it is what decides WHERE the
premise can be discharged. -/

example {s_run s_land : ScannerState}
    (h_dn : scanNextToken_checkDanglingNode s_run s_land = .ok ())
    (h_ska : s_land.simpleKeyAllowed = true) :
    danglingNodePos? s_run = none :=
  dangling_none_of_check h_dn h_ska

example {s : ScannerState} (h_dn : scanLoop_checkDanglingNode s = .ok ()) :
    danglingNodePos? s = none :=
  dangling_none_of_eof h_dn

-- The premise's home: every `PendingNode` still closes on `[79] s-l-comments`,
-- but a `pendingContent` park now states what its close is a reading OF.
example {sc : ScannerState} {sp_start sp_block sp_scan sp_mid : SurfPos}
    (h_pending : PendingNode sc false sp_start sp_block sp_scan)
    (h_stream : SLYamlStream sp_start sp_block)
    (h_nd : danglingNodePos? sc = none)
    -- Item 275: §8.1's silence, carried beside it.
    (h_ui : underIndentedFlowValuePos? sc = none)
    (h_ssl : SSLComments sp_scan sp_mid)
    (h_noflow : sc.inFlow = false) :
    SLYamlStream sp_start sp_mid :=
  h_pending.close_with_ssl h_stream h_nd h_ui h_noflow h_ssl

-- **Item 159 puts the same premise on the ENTRY park.**  A completed node
-- inside a block entry parks as `pendingBlockContent`, not `pendingContent`
-- (`- a`, `- "x"`, `- &p a`), and until now that park's `h_closable` was the
-- one content close that said nothing about what it was a reading of — even
-- though `- a⏎b` is the same second bare document as `a: 1⏎b`.  The example
-- above already covers it: `close_with_ssl` takes any `PendingNode` and the
-- consumer is the same one, which is why the premise cost its ten producers
-- nothing.
#guard ["- a\nb\n", "- \"x\"\nb\n", "k:\n  - a\n  b\n", "- a\n- b\n"].map scanOk
  == ["SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "SCAN-ERR L4YAML.ScanError.invalidBareDocument 2 2",
      "SCAN-OK"]

-- **The gating asymmetry, measured.**  Five landings, each read at the state
-- the park stands in.  The two that pay the face are the ones whose flag is
-- UP — a landing across a break, and the end of the stream — and both REFUSE.
-- The three with the flag down succeed on a state whose reading is `some`:
-- there is nothing to discharge there, which is exactly why those landings
-- resolve the run as a KEY instead of closing the park.
#guard [("k:\n  a: 1\nb: 2\n", 6), ("a: 1\nb: 2\n", 4), ("a: 1\nb\nc: 2\n", 4),
        ("a: 1\nb", 4), ("a: &x 1\n*x : 2\n", 5)].map
    (fun (p : String × Nat) => gateAt p.1 p.2)
  == ["c=: ska=false park=2,0 chk=ok",
      "c=: ska=false park=1,0 chk=ok",
      "c=c ska=true park=1,0 chk=L4YAML.ScanError.invalidBareDocument 1 0",
      "EOF park=1,0 chk=L4YAML.ScanError.invalidBareDocument 1 0",
      "c=: ska=false park=1,0 chk=ok"]

-- The three flag-down rows are accepted inputs, and the two flag-up ones are
-- refused at exactly the column their park reads.
#guard ["k:\n  a: 1\nb: 2\n", "a: 1\nb: 2\n", "a: &x 1\n*x : 2\n"].map scanOk
  == ["SCAN-OK", "SCAN-OK", "SCAN-OK"]

#guard ["a: 1\nb\nc: 2\n", "a: 1\nb"].map parseOk
  == ["PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 0"]

/-! ## §2  The transport, and why the premise is a `prevRealIdx?` fact

`danglingNodePos?` is read at the PARK's state; the route is refuted at the
LANDING's, one preprocessing later.  Three writers stand between them and the
STACK decides all three: `skipToContent` writes no token, the save reserves two
placeholders that `prevRealIdx?` walks past, and the unwind emits `blockEnd`.

`CompletedTail` does NOT survive that third writer — a `blockEnd` completes no
value — which is why item 156 stated the producer's premise at the reading it
spends rather than as a completed tail.  `DanglingPred` does survive, because a
`blockEnd` offers the coming run no slot either. -/

example {ts : Array (Positioned YamlToken)} {p : Positioned YamlToken}
    (h_ph : p.val ≠ .placeholder)
    (h_prop : p.val.isNodeProperty = false)
    (h_slot : p.val.offersNodeSlot = false) :
    DanglingPred (ts.push p) :=
  danglingPred_push_real h_ph h_prop h_slot

example {ts : Array (Positioned YamlToken)} {p : Positioned YamlToken}
    (h_ph : p.val = .placeholder) (h : DanglingPred ts) :
    DanglingPred (ts.push p) :=
  danglingPred_push_placeholder h_ph h

example {sc s_prep : ScannerState} {c : Char}
    (h_tail : CompletedTail sc)
    (h : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    DanglingPred s_prep.tokens :=
  preprocess_danglingPred (CompletedTail.danglingPred h_tail) h

-- The `blockEnd` half of the transport is neither a property nor a slot, which
-- is the whole content of the popping case.
#guard (YamlToken.blockEnd.isNodeProperty, YamlToken.blockEnd.offersNodeSlot,
        YamlToken.blockEnd.completesFlowValue) == (false, false, false)

-- **The popping half, with its witness.**  `k:⏎␣␣a: 1⏎b: 2` is an accepted
-- input whose landing DEDENTS: the park's last real token completes a value,
-- the LANDING's is the `blockEnd` the unwind emitted, and the stack shrank.
-- Read as a `CompletedTail` the premise is lost at that landing; read as a
-- `DanglingPred` it survives — and the second row shows the no-pop case for
-- contrast.
#guard [("k:\n  a: 1\nb: 2\n", 5), ("a: 1\nb: 2\n", 3)].map
    (fun (p : String × Nat) => transportAt p.1 p.2)
  == ["park=completesValue land=blockEnd POPPED",
      "park=completesValue land=completesValue same"]

/-! ## §3  What the face buys: the bare-document route, refuted

Item 139 halved `bareNodeRoute`'s domain at the content landing: a completed
node at NO open level is a second bare document, and
`scanNextToken_checkBareDocument` fires AT that landing.  The other half — the
landing that rests ON an open level — is the DANGLING one, and the check that
refuses it cannot see the run until it is scanned.  The park carries the
refusal forward and the face brings it back.

So for a park that finished a node and a landing that completes a value, the
route has no domain left at all.  That is one statement and it needs no case
split on the stack: -/

example {sc s_prep s' : ScannerState} {c : Char}
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow : s_prep.inFlow = false)
    (h_ska : s_prep.simpleKeyAllowed = true)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc)
    (h_tail : CompletedTail sc)
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s')
    (h_flow' : s'.inFlow = false)
    (h_nd : danglingNodePos? s' = none) :
    False := by
  cases h_op : (s_prep.indents.any fun e => e.column == (s_prep.col : Int)) with
  | false => exact bareDocument_refutes_landing h_bare h_pre h_noflow h_ska h_base h_op h_tail
  | true =>
    exact danglingPark_refutes_route h_nd h_pre h_tail h_dispatch h_flow' h_op

-- The gate is what carries that refutation into a route the props arm shares.
-- (Item 158 took `c ≠ '&' ∧ c ≠ '!'` off the left disjunct: the refutation is
-- character-uniform.  ~~`&`/`!` park as `pendingProps`, which has no reading to
-- hand over, and take the right one.~~ **Item 165 gave `pendingProps.h_route`
-- the reading, and the right disjunct is DELETED** — the gate is the reading,
-- for every content character alike.)
example {s' : ScannerState} {c : Char} (h_nd : danglingNodePos? s' = none) :
    ContentRouteGate s' c := h_nd

/-! ### The route census after the halving

`bareNodeRoute` is applied at three places in `StreamAccum`, and after this item
they are three different strengths:

| site | form | what is left of its domain |
|---|---|---|
| `accum_content_pending` ×2 (the content landing) | `bareNodeRoute_or_refused_content` | ~~the `&`/`!` gate, and~~ parks with no completed tail (item 165) |
| `accum_block_on_closeThenBlock` (the block landing) | `bareNodeRoute_or_refused` | ~~item 139's `h_op = true` half, whole~~ ~~the open sequence's next entry, and parks with no completed tail (item 166)~~ ~~the open sequence's next entry where NO PARK NAMES it, and parks with no completed tail (item 167)~~ the open sequence's next entry where no park names it — which after item 168 means the landings crossing TWO open mapping levels, the compact cascade carrying one width — and parks with no completed tail |
| `content_dispatch_after_close` (row 19's 1c) | `bareNodeRoute` | a ROUTE, not a refutation (item 156) |

The `[210]` constructor flip still reports FIVE errors, at the same five lemma
definitions — `topLevelFlowResumeSep`, `rootMapRoute`, `rootMapRouteF`,
`bareNodeRoute` and `structural_dispatch_to_pending`.  The routes have not
moved; their DOMAINS have. -/

/-! ## §4  Item 156's named obstacle, dissolved

Item 156 recorded `accum_block_pending` as the face's one obstacle, and named
two repairs: move its `h_close_pending` into the arms that spend it, or stop
`accum_block_on_closeThenBlock`'s `:` fallback taking an unconditional stream.
Neither was needed, and the reason is precise.

The premise RIDES with the closure — `h_close_pending` has the face in its own
type — so the `have` before the case split costs nothing, and the premise is
discharged where the close is SPENT.  And `accum_block_on_closeThenBlock` spends
it in exactly one place: the branch where preprocessing produced a landing, and
there `landing_or_park_ska` supplies the flag.  The no-break `:` takes a
different parameter, `h_stream_fallback`, and never reaches the park's close.

Item 141's wall is real about the shape it measured — a DISJUNCT on the
conclusion has to be discharged wherever the conclusion is used — and empty
about the shape item 156 chose.  The witness makes that concrete: -/

#guard gateAt "a: &x 1\n*x : 2\n" 5 == "c=: ska=false park=1,0 chk=ok"
#guard transportAt "a: &x 1\n*x : 2\n" 5 == "park=completesValue land=completesValue same"
#guard scanOk "a: &x 1\n*x : 2\n" == "SCAN-OK"
#guard parseOk "a: &x 1\n*x : 2\n" == "PARSE-OK"

/-! ## §5  What is left: the property lane

The gate's right disjunct is the whole remaining domain of the content
landing's route, and it names the next item exactly: `&` and `!` park as
`pendingProps`, which carries its stream route as a FIELD and has no face.

~~The lane is refutable — `danglingNodePos?` reads a `[96]` property run as a
node run, so a run behind a completed node at an open level is dangling by the
same reading, and the scanner already refuses all three shapes below.  What is
missing is the constructor's own premise and the producer lemma behind it
(`dispatchContent_tokens_push`'s property twin).~~

**Item 158 struck that.**  The producer lemma landed and the refutation is
character-uniform now, so the four witnesses below are refused as a theorem
rather than as a measurement.  But "the scanner already refuses" is true only
of the BLOCK-bodied lane: a property run whose body is a flow collection scans
CLEAN (`a: 1⏎&p [b]`), so the field cannot simply be added.  The lane's two
halves, and what the second one costs, are measured in
`Tests/Guards/Proofs/PropsParkDangling.lean`.

**And item 159 closed the second half.**  `[161] ns-flow-node` offers a flow
collection where a scalar stands, so `trailingNodeRun?` reads a trailing close
back to its matching open and `a: 1⏎&p [b]` is a scanner error at `1,0` now —
the two halves are one lane again.  What is still missing is a premise shape
that relays through a PROPERTY push; see
`Tests/Guards/Proofs/FlowRunDanglingClosed.lean` §5. -/

#guard ["a: 1\n&p b\n", "k:\n  a: 1\n  &p b\n", "- a\n&p b\n", "a: 1\n!!str b\n"].map scanOk
  == ["SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "SCAN-ERR L4YAML.ScanError.invalidBareDocument 2 2",
      "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"]

-- …and the positions are the RUN's start, not the body's — which is what says
-- the property heads the dangling run and therefore what the props face has to
-- be stated about.
#guard [("a: 1\n&p b\n", 4), ("a: 1\n&p b\n", 5),
        ("k:\n  a: 1\n  &p b\n", 6), ("k:\n  a: 1\n  &p b\n", 7)].map
    (fun (p : String × Nat) => gateAt p.1 p.2)
  == ["c=b ska=false park=1,0 chk=ok",
      "EOF park=1,0 chk=L4YAML.ScanError.invalidBareDocument 1 0",
      "c=b ska=false park=2,2 chk=ok",
      "EOF park=2,2 chk=L4YAML.ScanError.invalidBareDocument 2 2"]

end L4YAML.Tests.Guards.DanglingParkFace

end Blanket
