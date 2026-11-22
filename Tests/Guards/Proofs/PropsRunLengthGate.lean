module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # `[96]`'s LENGTH, and the gate it pays for (DOCS item 165)

Item 164 left row 1c with one gate site unpaid and one guard unbuilt, and named
them in that order: `accum_flow_open_depth0`'s props arm, then
`pendingProps.h_route` taking `danglingNodePos? sc = none`.  Building the second
first is what showed the order was wrong — the guard does not relay through a
run's own EXTENSION, and item 160 had priced that class as free.

**What blocked it.**  `trailingNodeRun?` walks back over at most TWO properties,
because `[96] c-ns-properties` derives at most one anchor and one tag.  A third
property therefore MOVES §9.2's start — from the run's first property to its
second — so the park's reading and the reading one push later are readings of
different tokens (`PropsRunReadingTransport` §1 measures the move).

**What unblocks it is the scanner, not the proof.**  Both §6.9 guards decide by
KIND and, outside a flow, read `trailingPropertyRunOnLine` — the current LINE's
run.  That is blind to a run crossing a break: at the `&b` of `&a⏎!t &b x` the
line's run is `[!t]`, which carries no anchor, so the third property was
accepted and only `TokenParser` refused the document.  `propertyRunFull` decides
by LENGTH and reads the RUN.

**Item 170 narrowed the block reading back to the cursor's line** — the
length-only form read a parent's full run, a break, and the first implicit
KEY's fresh run as ONE run and refused 9KAX — so the cross-line third-property
shapes are the parser's again, and the walk-back CAN reach its cap at a park
the scanner produces.  ~~The relay in §2 returns that window
(`PropsWindowCross`) instead of forcing the verdict through it, and
`pendingProps.h_routeX` — the route held without the verdict — serves it.~~
**Item 181: the window's states are scanner-refused** (§9.2's fourth clause,
item 180), so §2's relay is a plain implication again and the route it would
have needed is owed by nobody (`PropsCrossWindowRoute` is that story's own
guard).

§1 measures the check, §2 the relay it buys, §3 the props arm's own gate — the
tenth and last of item 161's ten — and §4 the residue that leaves:
`ContentRouteGate`'s right disjunct, DELETED. -/

namespace L4YAML.Tests.Guards.PropsRunLengthGate

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.CouplingBridge

private def scanOk (input : String) : String :=
  match scan input with
  | .ok _ => "SCAN-OK"
  | .error e => s!"SCAN-ERR {repr e}"

private def parseOk (input : String) : String :=
  match Events.streamToEvents input with
  | .ok _ => "PARSE-OK"
  | .error e => s!"PARSE-ERR {repr e}"

private def both (input : String) : String × String := (scanOk input, parseOk input)

/-! ## §1  The check: a SAME-LINE run is at most two properties long

**Item 170 narrowed the block-context reading to the cursor's line.**  A full
run whose tail closed on an EARLIER line may belong to a PARENT node whose
mapping's first implicit key carries the incoming property — 9KAX's
`&a4 !!map⏎&a5 !!str key5: v` is `[96]`-valid twice over and the two runs
stand adjacent in the array — so the cross-line shapes are the PARSER's now
(`invalidBareDocument` at the run's start, `TokenParser.validNextToken`'s own
§9.2), exactly as `a: 1⏎&p [b]` always was.  On one line, and in a flow, the
length still decides at the scanner. -/

-- Across ONE break: the PUSH still defers (the tail is on an earlier line,
-- and the scanner cannot tell a run continuation from a parent's run beside
-- a fresh key's — 9KAX below), but item 180's crossed-block clause refuses
-- the still-unresolved block at the next landing or EOF — at the same
-- position the parser reported, so the refusal moved STAGE only.
#guard both "&a\n!t &b x\n"
  == ("SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 3",
      "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 3")
#guard both "!t\n&a !u x\n"
  == ("SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 3",
      "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 3")
-- Across TWO: likewise.
#guard both "&a\n!t\n&b x\n"
  == ("SCAN-ERR L4YAML.ScanError.invalidBareDocument 2 0",
      "PARSE-ERR L4YAML.ScanError.invalidBareDocument 2 0")
-- On ONE line, and inside a flow, §6.9's KIND guards already answered — the
-- length check agrees with them rather than replacing them.
#guard scanOk "&a !t &b x\n"
  == "SCAN-ERR L4YAML.ScanError.invalidNodeProperties '&' 0 6"
#guard scanOk "[&a !t &b x]\n"
  == "SCAN-ERR L4YAML.ScanError.invalidNodeProperties '&' 0 7"

-- The families the narrowing RESTORES (both pipelines end to end): a parent
-- node's FULL run, a break, and the first implicit key's own fresh run.
#guard both "---\n&a4 !!map\n&a5 !!str key5: value4\n" == ("SCAN-OK", "PARSE-OK")
#guard both "&a !t\n&b x: 1\n" == ("SCAN-OK", "PARSE-OK")

-- The TWO-property run it stops at is untouched, in every shape: on a line,
-- across a break in either order, in a flow, and as a mapping value.
#guard both "&a !t x\n" == ("SCAN-OK", "PARSE-OK")
#guard both "&a\n!t x\n" == ("SCAN-OK", "PARSE-OK")
#guard both "!t\n&a x\n" == ("SCAN-OK", "PARSE-OK")
#guard both "[&a !t x]\n" == ("SCAN-OK", "PARSE-OK")
#guard both "k: &a !t v\n" == ("SCAN-OK", "PARSE-OK")

/-- The check, read back off a dispatch that succeeded — which is the form the
    accumulation spends: a park that took a third property had at most ONE
    trailing property, so the walk-back's cap is not reached. -/
example {s s' : ScannerState} (hok : scanNextToken_dispatchContent s '&' = .ok s') :
    propertyRunFull s = false :=
  propertyRunFull_false_of_anchor_dispatch hok

example {s s' : ScannerState} (hok : scanNextToken_dispatchContent s '!' = .ok s') :
    propertyRunFull s = false :=
  propertyRunFull_false_of_tag_dispatch hok

/-! ## §2  The relay it buys

`pendingProps.h_route` takes `danglingNodePos? sc = none` now, so every step
that carries the run forward has to hand the verdict back.  Both relays split
the same way, and the split is the LANDING's: a step that crossed a break has
already been refused by §9.2's own mid-stream check
(`scanNextToken_checkDanglingNode` reads the run at the park and the flag at the
landing), and a step that crossed none wrote neither a token nor an indent — the
park's own two DOWN flags are what make that total. -/

example {sc s_prep : ScannerState} {sp_scan : SurfPos} {c : Char}
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow_prep : s_prep.inFlow = false)
    (h_col0 : 0 < sp_scan.col)
    (h_nic : sc.needIndentCheck = false)
    (h_ska : sc.simpleKeyAllowed = false)
    (h_dn : scanNextToken_checkDanglingNode sc s_prep = .ok ()) :
    danglingNodePos? sc = none ∨
      (s_prep.tokens = sc.tokens ∧ s_prep.indents = sc.indents) :=
  propsPark_stale_dangling h_corr h_pre h_noflow_prep h_col0 h_nic h_ska h_dn

/-- The EXTENSION's relay.  ~~Item 170 reshaped it into a disjunction~~ —
    under the narrowed gate a property may stand below the run's tail across a
    break, and there the §9.2 window SLIDES under the push, so the verdict
    could not be transported and the lemma handed the window back.  **Item 181
    made it a relay again, and took two premises off with the disjunct**: §9.2
    refuses the crossed block itself now (item 180), so the branch that could
    not transport is the branch whose own premise is false — and neither the
    length check nor the tail's LINE is read any more. -/
example {sc s_prep s_ad s' : ScannerState} {sp_scan : SurfPos} {c : Char}
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow_sc : sc.inFlow = false) (h_noflow_prep : s_prep.inFlow = false)
    (h_col0 : 0 < sp_scan.col)
    (h_nic : sc.needIndentCheck = false) (h_ska : sc.simpleKeyAllowed = false)
    (h_dn : scanNextToken_checkDanglingNode sc s_prep = .ok ())
    (h_prop : ∃ k, prevRealIdx? sc.tokens sc.tokens.size = some k ∧
      sc.tokens[k]!.val.isNodeProperty = true)
    (h_ad_tok : s_ad.tokens = s_prep.tokens) (h_ad_ind : s_ad.indents = s_prep.indents)
    (h_ad_flow : s_ad.inFlow = s_prep.inFlow)
    (hc : c = '&' ∨ c = '!')
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s') :
    danglingNodePos? s' = none → danglingNodePos? sc = none :=
  propsPark_dangling_of_prop h_corr h_pre h_noflow_sc h_noflow_prep h_col0 h_nic h_ska
    h_dn h_prop h_ad_tok h_ad_ind h_ad_flow hc h_dispatch

/-- …and the CONTENT's, which needs no such premise: a body push leaves the
    walk-back's answer alone (item 160's row, now spendable). -/
example {sc s_prep s_ad s' : ScannerState} {sp_scan : SurfPos} {c : Char}
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow_sc : sc.inFlow = false) (h_noflow_prep : s_prep.inFlow = false)
    (h_col0 : 0 < sp_scan.col)
    (h_nic : sc.needIndentCheck = false) (h_ska : sc.simpleKeyAllowed = false)
    (h_dn : scanNextToken_checkDanglingNode sc s_prep = .ok ())
    (h_prop : ∃ k, prevRealIdx? sc.tokens sc.tokens.size = some k ∧
      sc.tokens[k]!.val.isNodeProperty = true)
    (h_ad_tok : s_ad.tokens = s_prep.tokens) (h_ad_ind : s_ad.indents = s_prep.indents)
    (h_ad_flow : s_ad.inFlow = s_prep.inFlow)
    (hna : c ≠ '&') (hnt : c ≠ '!')
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s')
    (h_nd : danglingNodePos? s' = none) : danglingNodePos? sc = none :=
  propsPark_dangling_of_body h_corr h_pre h_noflow_sc h_noflow_prep h_col0 h_nic h_ska
    h_dn h_prop h_ad_tok h_ad_ind h_ad_flow hna hnt h_dispatch h_nd

/-! ## §3  The props arm's own gate — item 161's tenth site

The arm does not open at ONE verdict.  Which park the gate names is the
LANDING's to decide, and the two cases pay differently: a landing that crossed a
break owes the route unconditionally (§9.2's check already fired ON the park), so
the frame opens at `none` and `GateOf none` is `True` by definition; a landing
that crossed none leaves `sc` itself as the state the bracket extends, so the
frame opens at `some sc` and the close hands the park's verdict straight back.

That is why no transport across preprocessing is needed: the arm where the two
states differ is the arm where the gate is not wanted. -/

example {sc s_prep s' : ScannerState} {sp_scan : SurfPos} {c : Char}
    {p : Positioned YamlToken}
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow_sc : sc.inFlow = false) (h_noflow_prep : s_prep.inFlow = false)
    (h_col0 : 0 < sp_scan.col)
    (h_nic : sc.needIndentCheck = false) (h_ska : sc.simpleKeyAllowed = false)
    (h_dn : scanNextToken_checkDanglingNode sc s_prep = .ok ())
    (h_prop : ∃ k, prevRealIdx? sc.tokens sc.tokens.size = some k ∧
      sc.tokens[k]!.val.isNodeProperty = true)
    (hop : p.val.isFlowOpen = true)
    (htok : s'.tokens = s_prep.tokens.push p)
    (hind : s'.indents = s_prep.indents)
    (hposs : s'.simpleKey.possible = false) :
    ∃ g : Option ScannerState, FlowBaseAnchor g s' 0 ∧
      (GateOf g → danglingNodePos? sc = none) :=
  propsPark_open_gate h_corr h_pre h_noflow_sc h_noflow_prep h_col0 h_nic h_ska h_dn
    h_prop hop htok hind hposs

/-- `ParkAnchor`'s fourth conjunct for a `[96]` park, read off the fields
    `pendingProps` already carries — the run is non-empty, a non-empty same-line
    run is headed by the last real token, and a real final slot is the one
    `prevRealIdx?` lands on.  Item 170: the derivation always held the tail's
    LINE too and used to drop it; the narrowed gate's relay spent it — and
    item 181's relay no longer does, so the conjunct is pinned here alone. -/
example {sc : ScannerState} {ha ht : Bool} {n : Nat} {sp_p sp_scan : SurfPos}
    (h_real : L4YAML.Proofs.FlowAdjacency.LastTokenReal sc.tokens)
    (h_run : PropsRun n .flowOut ha ht sp_p sp_scan)
    (h_anchor : ha = true →
      (trailingPropertyRunOnLine sc.tokens sc.line).any YamlToken.isAnchorProperty = true)
    (h_tag : ht = true →
      (trailingPropertyRunOnLine sc.tokens sc.line).any YamlToken.isTagProperty = true) :
    ∃ k, prevRealIdx? sc.tokens sc.tokens.size = some k ∧
      sc.tokens[k]!.val.isNodeProperty = true ∧
      sc.tokens[k]!.pos.line = sc.line :=
  propsPark_prevReal_prop h_real h_run h_anchor h_tag

-- The two futures the gate exists to separate (item 160's table, unchanged):
-- the collection heads an implicit KEY and is LEGAL; it closes as a VALUE and
-- is refused at the run's own start.
#guard both "a: 1\n&p [b]: c\n" == ("SCAN-OK", "PARSE-OK")
#guard scanOk "a: 1\n&p [b]\n" == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"

/-! ## §4  The residue, deleted

`ContentRouteGate` was `danglingNodePos? s' = none ∨ (c = '&' ∨ c = '!')`, and
item 158 measured what the right disjunct named: not two characters but a
missing FIELD — `pendingProps` carried no §9.2 face, so at `&`/`!` the landing
had no reading to hand over.  It has one now, so the gate is the reading, for
every content character alike.  (~~Item 170 widened `content_dispatch_routed`'s
route PREMISE with `PropsWindowCross`~~ — a different disjunct with a different
payer, and **item 181 narrowed it back**: §9.2 refuses the crossed window
itself, so the premise is the gate alone again.  The gate itself was never
moved by either.) -/

example {s' : ScannerState} {c : Char} :
    ContentRouteGate s' c ↔ danglingNodePos? s' = none := Iff.rfl

/-- What the gate buys at the content landing: at a park with a completed tail
    the bare-document route is refuted on BOTH halves of item 139's
    discriminator, with no character left standing between them. -/
example {sc s_prep s' : ScannerState} {c : Char} {sp_start sp_anchor : SurfPos}
    (h_stream : SLYamlStream sp_start sp_anchor)
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow : s_prep.inFlow = false)
    (h_ska : s_prep.simpleKeyAllowed = true)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc)
    (h_tail : CompletedTail sc ∨ True)
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s')
    (h_flow' : s'.inFlow = false)
    (h_nd : danglingNodePos? s' = none) :
    ∀ sp_m, SBlockNode 0 .blockIn sp_anchor sp_m → SLYamlStream sp_start sp_m :=
  bareNodeRoute_or_refused_content h_stream h_bare h_pre h_noflow h_ska h_base h_tail
    h_dispatch h_flow' h_nd

-- The character family the right disjunct used to carry, refused at the RUN's
-- start in every shape item 158 listed — the measurement that says the
-- refutation is character-uniform and the disjunct was never about characters.
#guard scanOk "a: 1\n&p b\n" == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"
#guard scanOk "k:\n  a: 1\n  &p b\n" == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 2 2"
#guard scanOk "- a\n&p b\n" == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"
#guard scanOk "a: 1\n!!str b\n" == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"

end L4YAML.Tests.Guards.PropsRunLengthGate

end Blanket
