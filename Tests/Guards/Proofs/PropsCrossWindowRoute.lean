module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The crossed tail window — the route it needed, and its RETIREMENT
    (DOCS items 170 and 181)

Item 165's `[96]` length gate read a parent node's FULL property run, a break,
and the first implicit KEY's fresh run as ONE run, and refused 9KAX — found
when the test matrix ran again at item 169.  The narrowing is measured and
small: in block context the gate fires only when all three properties share
the cursor's line (`PropsRunLengthGate` §1 has the runtime).

The narrowing's PRICE was this file's first subject.  With cross-line thirds
deferred, a `[96]` park's tail window can hold a property on an EARLIER line
below its tail, and there item 165's verdict relay is not hard but FALSE:
§9.2's walk-back is capped at `[96]`'s arity, so a property push SLIDES the
window, and the park's verdict and the pushed state's are readings of
different columns.  §1 pins the slide at the runtime, where it still holds.

Item 170 answered it with a second route — `PropsWindowCross` naming the
window, `pendingProps.h_routeX` carrying a construction that never read the
verdict, and a same-line extension refuting the premise.  **Item 181 deletes
all three.**  What retires them is not a better relay but an empty domain: the
push that slides the window puts a THIRD property adjacent to two others, and
`[96]` admits one anchor and one tag — so a kind repeats, §9.2's fourth clause
(item 180) reads the excess, and `danglingNodePos?` returns `some` at exactly
the states the window named.  The relay's premise is refuted there; the branch
that could not transport a verdict is the branch that has none to transport.

§1 pins the slide and the refusal at the runtime, §2 the pigeonhole the
retirement rests on, §3 the pieces at the proof's own types, §4 the record.
-/

namespace L4YAML.Tests.Guards.PropsCrossWindowRoute

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.CouplingBridge

private def stepN (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | n + 1 =>
    match scanNextToken s with
    | .ok (some s') => stepN s' n
    | _ => none

/-- §9.2's verdict `n` tokens in. -/
private def dangAt (input : String) (n : Nat) : String :=
  match stepN ((ScannerState.mk' input).emit .streamStart) n with
  | none => "no-state"
  | some s =>
    match danglingNodePos? s with
    | none => "none"
    | some p => s!"some({p.line},{p.col})"

private def scanOk (input : String) : String :=
  match scan input with
  | .ok _ => "SCAN-OK"
  | .error e => s!"SCAN-ERR {repr e}"

private def parseOk (input : String) : String :=
  match Events.streamToEvents input with
  | .ok _ => "PARSE-OK"
  | .error e => s!"PARSE-ERR {repr e}"

/-! ## §1  The slide, at the runtime — and the two floors in front of it

When this file was written (item 170), `a:⏎!t⏎&b⏎␣␣!s &c x` scanned clean:
every landing passed §9.2's mid-stream check, the gate deferred every `&`/`!`,
and only `TokenParser` refused.  Five tokens in, the array ended `[.., &b, !s]`
and the window started at `&b` — column 0, AT the open level; one property
push later it started at `!s` — column 2, at no level.  So the pushed state's
verdict could not relay the park's, which is why `h_routeX` carried the window
instead.

Item 178's floor now stands IN FRONT of the slide for this family: the first
property lands at the awaiting level's own column, and the first BREAK after
it is `danglingNodePos?`'s own refusal (the slot-offered exemption no longer
covers a `[96]`-headed run), so the scan dies three tokens in — at the same
run start `TokenParser` used to name — and the sliding windows behind it are
no longer reachable states.  The verdict three tokens in is still the some
the relay could not carry, pinned below.

What survived for the crossed-window arms was the family with no offered slot
in front — the ROOT's (`&a⏎!t &b x`), where §9.2 read `none` at every window
(no level is open) and the route never needed a verdict at all.  **Item 180's
fourth clause reads that family too**, and item 181 spends the shrinkage. -/

#guard dangAt "a:\n!t\n&b\n  !s &c x\n" 3 == "some(1,0)"
#guard dangAt "a:\n!t\n&b\n  !s &c x\n" 5 == "no-state"
#guard scanOk "a:\n!t\n&b\n  !s &c x\n"
  == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"
#guard parseOk "a:\n!t\n&b\n  !s &c x\n"
  == "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 0"
#guard dangAt "&a\n!t &b x\n" 2 == "none"
-- Item 180: the crossed-block clause reads the excess property, so the
-- verdict four tokens in is SOME at `&b` — and the whole family refuses at
-- the SCANNER now (EOF, same constructor and position the parser reported).
-- The crossed-window arms' scanner-reachable domain is EMPTY.
#guard dangAt "&a\n!t &b x\n" 4 == "some(1,3)"
#guard scanOk "&a\n!t &b x\n"
  == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 3"
#guard parseOk "&a\n!t &b x\n"
  == "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 3"

/-! ## §2  The pigeonhole, exhaustively

`[96] c-ns-properties` admits at most one anchor and one tag, so THREE
adjacent property tokens always duplicate a kind.  All eight assignments,
against the reader item 180 landed — the excess index is the first token, in
token order, whose kind already occurs below it.  The two-property controls
say the reader is not simply counting: `&!` and `!&` are one legal run. -/

private def pos3 (l c : Nat) : YamlPos := ⟨l * 8 + c, l, c⟩

private def anchorTok (l : Nat) : Positioned YamlToken :=
  ⟨pos3 l 0, .anchor "x", pos3 l 0⟩

private def tagTok (l : Nat) : Positioned YamlToken :=
  ⟨pos3 l 0, .tag "!" "t", pos3 l 0⟩

/-- `true` = anchor, `false` = tag; the list is read bottom-up, as the array is. -/
private def excessOf (kinds : List Bool) : String :=
  let ts := (kinds.zipIdx.map fun (b, i) => if b then anchorTok (i + 1) else tagTok (i + 1))
  match crossedPropsExcessIdx? ts.toArray with
  | none => "none"
  | some j => s!"some {j}"

#guard excessOf [true, true, true] == "some 1"
#guard excessOf [true, true, false] == "some 1"
#guard excessOf [true, false, true] == "some 2"
#guard excessOf [true, false, false] == "some 2"
#guard excessOf [false, true, true] == "some 2"
#guard excessOf [false, true, false] == "some 2"
#guard excessOf [false, false, true] == "some 1"
#guard excessOf [false, false, false] == "some 1"
-- …and two are a run exactly when the kinds differ.
#guard excessOf [true, true] == "some 1"
#guard excessOf [true, false] == "none"
#guard excessOf [false, true] == "none"
#guard excessOf [false, false] == "some 1"

/-! ## §3  The pieces, at the proof's own types -/

/-- The pigeonhole as the proof spends it: a property pushed onto a tail whose
    own predecessor is a property leaves an excess in the block. -/
example {ts : Array (Positioned YamlToken)} {p : Positioned YamlToken} {k j : Nat}
    (hp : p.val.isNodeProperty = true)
    (hk : prevRealIdx? ts ts.size = some k)
    (hkp : ts[k]!.val.isNodeProperty = true)
    (hj : prevRealIdx? ts k = some j)
    (hjp : ts[j]!.val.isNodeProperty = true) :
    crossedPropsExcessPos? (ts.push p) ≠ none :=
  crossedPropsExcessPos?_push_prop_three hp hk hkp hj hjp

/-- …and the step from the excess to the verdict: a run that STARTS on a
    property clears the slot exemption, so both remaining branches report. -/
example {s : ScannerState} {st : Nat} {pred : Option Nat}
    (hflow : s.inFlow = false)
    (hrun : trailingNodeRun? s.tokens = some (st, pred))
    (hstp : s.tokens[st]!.val.isNodeProperty = true)
    (hx : crossedPropsExcessPos? s.tokens ≠ none) :
    danglingNodePos? s ≠ none :=
  danglingNodePos?_ne_none_of_crossed hflow hrun hstp hx

/-- The relay, RETIRED to a plain implication (item 181).  Where the window
    crossed a break the conclusion is vacuous, not transported — and neither
    the `[96]` length check nor the tail's line is a premise any more. -/
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

/-- …and the landing's route premise, narrowed back to the gate alone. -/
example {s' : ScannerState} {c : Char} {sp_start sp_anchor : SurfPos}
    (h : ContentRouteGate s' c →
      ∀ sp_m, SBlockNode 0 .blockIn sp_anchor sp_m → SLYamlStream sp_start sp_m)
    (h_nd : danglingNodePos? s' = none) :
    ∀ sp_m, SBlockNode 0 .blockIn sp_anchor sp_m → SLYamlStream sp_start sp_m :=
  h h_nd

/-! ## §4  The record

* **What item 181 deletes.**  `PropsWindowCross` (the window), its refutation
  `propsWindowCross_push_refute`, and `pendingProps.h_routeX` (the route held
  without the verdict) — with the six payments the field cost: two landed
  births, the entry and value slots' re-handed closers, and the two same-line
  extensions' refutations.  `content_dispatch_routed`'s route premise is
  `ContentRouteGate` alone again, and `propsPark_dangling_of_prop` loses its
  disjunct, its `propertyRunFull` premise and the tail-line conjunct with it.

* **What it buys.**  `accum_content_pending`'s two `bareNodeRoute` fallbacks —
  the arms the crossed window rode — are gone, so the raw-route census drops
  from THREE holders to TWO: `bareNodeRoute_or_refused_content` (2) and
  `content_dispatch_after_close` (1).  At the content landing the refined
  route is now the ONLY construction.

* **No refusal weakens, and none is added.**  This item edits no runtime file:
  the refusal it spends is item 180's, already measured against PyYAML and
  already in the matrix.  The gated `h_route` and both `_or_refused`
  refinements are untouched; `ContentRouteGate` is unchanged.

* **The gate stays as measured.**  The slide is a fact about §9.2's READER
  (`trailingNodeRun?`'s `[96]`-arity cap), not about item 170's narrowed
  `propertyRunFull`, and it is still true — §1 pins it.  What changed is that
  the states it describes are refused before any route is owed. -/

end L4YAML.Tests.Guards.PropsCrossWindowRoute

end Blanket
