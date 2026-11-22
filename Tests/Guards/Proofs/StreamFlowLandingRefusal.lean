module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # §9.2's landing refusal at the FLOW open (DOCS item 143)

Items 139 and 142 threaded `scanNextToken_checkBareDocument`'s success to the
content landing and then to the block landing.  `accum_step_flow` was the only
step left without it, and this item closes that: `h_bare` now reaches every
dispatcher `scanNextToken` runs.

What it guards is the flow open's two fallbacks — the collection's own route
(`topLevelFlowResumeSep`, `[1]⏎[2]`) and the mapping that collection may key
(`rootMapRoute` inside `flowKeyRoute_of_root`, `[1]⏎[2]: b`).  Both are reached
from the LANDING arm only; the no-break arm of each is a park at a line start,
which is not a landing and keeps its route unguarded.

§1 is the half the refusal closes, measured on the real scanner.  §2 is the
half it does not — and at this dispatcher that half has a second refusal of its
own, because §8.1's floor (item 66) already runs here.  §3 is the guarded flow
route.  §4 is the enrichment that made the flag reachable.  §5 is the key side.
§6 is what remains.

No runtime file is touched, so every verdict below is the one the pipelines
already gave. -/

namespace L4YAML.Tests.Guards.StreamFlowLandingRefusal

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.CouplingBridge

/-! ## §1  The half §9.2 closes

`fires` walks the real `scanNextToken` and reports which §9.2 check fired, at
which landing, and at what indent-stack size.  `verdict` separates the three
refusals this dispatcher can produce: §9.2's (`scan-bare`), §8.1's floor
(`scan-flowfloor`), and the parser's alone (`parse-bare`). -/

private def fireAt (s : ScannerState) (n : Nat) : Nat → String
  | 0 => "fuel"
  | fuel + 1 =>
    match scanNextToken_preprocess s with
    | .error _ => "preprocess-error"
    | .ok none =>
      match scanLoop_checkDanglingNode s with
      | .error _ => s!"eof-dangling@{n}"
      | .ok _ => "clean"
    | .ok (some (s1, _)) =>
      match scanNextToken_checkDanglingNode s s1 with
      | .error _ => s!"dangling@{n}"
      | .ok _ =>
        match scanNextToken_checkBareDocument s1 with
        | .error _ => s!"bare@{n} sz={s1.indents.size}"
        | .ok _ =>
          match scanNextToken s with
          | .ok (some s') => fireAt s' (n + 1) fuel
          | .ok none => "no-step"
          | .error _ => s!"step-error@{n}"

private def fires (input : String) : String :=
  fireAt (ScannerState.mk' input) 0 40

/-- Stops at the first dispatched `[`/`{` and reports the two readings the two
    checks compare: §8.1's `currentIndent` against the bracket's column, and
    §9.2's indent-stack size against the sentinel. -/
private def atOpenAt (s : ScannerState) : Nat → String
  | 0 => "fuel"
  | fuel + 1 =>
    match scanNextToken_preprocess s with
    | .error _ => "preprocess-error"
    | .ok none => "eof"
    | .ok (some (s1, c)) =>
      if c == '[' || c == '{' then
        s!"ci={s1.currentIndent} col={s1.col} sz={s1.indents.size}"
      else
        match scanNextToken s with
        | .ok (some s') => atOpenAt s' fuel
        | _ => "no-step"

private def atOpen (input : String) : String :=
  atOpenAt (ScannerState.mk' input) 40

private def verdict (input : String) : String :=
  match scan input with
  | .error (.invalidBareDocument l c) => s!"scan-bare {l},{c}"
  | .error (.underIndentedFlowContent l c) => s!"scan-flowfloor {l},{c}"
  | .error e => s!"scan {toString (repr e)}"
  | .ok _ =>
    match Events.streamToEvents input with
    | .error (.invalidBareDocument l c) => s!"parse-bare {l},{c}"
    | .error e => s!"parse {toString (repr e)}"
    | .ok _ => "OK"

-- **A completed value, a break, and a `[`/`{` at the sentinel alone.**  This
-- is the arm `topLevelFlowResumeSep` serves in `accum_flow_open_depth0`'s
-- shared `main`, and the scanner refuses all of it AT the landing — before the
-- bracket's own token exists.
#guard ["\"x\"\n[1, 2]\n", "'x'\n{a: 1}\n"].map fires
  == ["bare@1 sz=1", "bare@1 sz=1"]

-- A completed FLOW collection is a completed value too, and the refusal is at
-- the landing after its closing bracket.
#guard (fires "[1]\n[2]\n", fires "{a: 1}\n[2]\n") == ("bare@3 sz=1", "bare@5 sz=1")

-- The plain scalar is absent from this family for item 142's reason: it
-- ABSORBS the line, so `a⏎[1, 2]` is one multi-line plain scalar and there is
-- no landing at all.  A comment stops the run, and then the landing appears.
#guard (fires "a\n[1, 2]\n", fires "a\n# c\n[1, 2]\n") == ("clean", "bare@1 sz=1")
#guard (fires "&p a\n[1]\n", verdict "&p a\n[1]\n") == ("clean", "OK")

-- The landing is at column 0; the BRACKET need not be.  An indented open after
-- the same break is refused at the same landing, and the position reported is
-- the bracket's.
#guard (verdict "\"x\"\n  [1, 2]\n", verdict "[1]\n  [2]\n")
  == ("scan-bare 1,2", "scan-bare 1,2")

-- The KEY side — `flowKeyRoute_of_root`'s landing arm, where the collection
-- turns out to be a mapping key.  Same refusal, same landing.
#guard (fires "\"x\"\n[1]: b\n", fires "[1]\n[2]: b\n")
  == ("bare@1 sz=1", "bare@3 sz=1")

-- The verdicts, and they are the SCANNER's.
#guard ["\"x\"\n[1, 2]\n", "'x'\n{a: 1}\n", "[1]\n[2]\n", "{a: 1}\n[2]\n",
        "\"x\"\n[1]: b\n", "[1]\n[2]: b\n"].map verdict
  == ["scan-bare 1,0", "scan-bare 1,0", "scan-bare 1,0", "scan-bare 1,0",
      "scan-bare 1,0", "scan-bare 1,0"]
#guard verdict "a\n# c\n[1, 2]\n" == "scan-bare 2,0"

/-! ## §2  The half it does not

The discriminator is the indent stack, as at the other two landings.  What is
new here is that the above-sentinel half is not all parser-only: §8.1's floor
(item 66) runs at this dispatcher and takes the part of it that sits at or left
of the enclosing block collection. -/

-- Item 172 defers §8.1's floor to the close, so the OPEN's step succeeds and
-- the landing scans through the collection; what refuses these is the EOF
-- gate, and the reading is §9.2's — the completed value (`1`, `"a"`) holds
-- the slot, so the trailing flow node is a dangling run read back to its
-- open, `invalidBareDocument` at the open's own position.
#guard (fires "a: 1\n[1, 2]\n", verdict "a: 1\n[1, 2]\n")
  == ("eof-dangling@8", "scan-bare 1,0")
#guard (fires "- \"a\"\n[1, 2]\n", verdict "- \"a\"\n[1, 2]\n")
  == ("eof-dangling@7", "scan-bare 1,0")

-- **The residue this item recorded as the parser's alone**: a completed value
-- met by a flow open MORE indented than the enclosing collection, with a level
-- still open.  §8.1 stands aside (the bracket is past the floor), and §9.2
-- stood aside too, because its first conjunct was the stack's SIZE.  [Item 145
-- reads the landing's COLUMN: none of these four brackets stands at an open
-- level, so all four are the scanner's refusal now, at the positions
-- `TokenParser` used to report.]
#guard ["k:\n  \"a\"\n  [1, 2]\n", "k:\n  \"a\"\n    [1, 2]\n",
        "k:\n  [1]\n  [2]\n", "- \"a\"\n  [1, 2]\n"].map fires
  == ["bare@3 sz=2", "bare@3 sz=2", "bare@5 sz=2", "bare@2 sz=2"]
#guard ["k:\n  \"a\"\n  [1, 2]\n", "k:\n  \"a\"\n    [1, 2]\n",
        "k:\n  [1]\n  [2]\n", "- \"a\"\n  [1, 2]\n"].map verdict
  == ["scan-bare 2,2", "scan-bare 2,4", "scan-bare 2,2", "scan-bare 1,2"]

-- …and the refusal lands BEFORE the bracket's own token, so the array the
-- parser used to receive (twenty-one tokens) is never built.
#guard (match scan "k:\n  \"a\"\n  [1, 2]\n" with
        | .ok ts => ts.size | .error _ => 0) == 0

-- The two floors, read at the bracket itself.  `atOpen` stops at the first
-- dispatched `[`/`{` and reports what §8.1 compares (`currentIndent` against
-- the bracket's column) and the stack size §9.2 compared before item 145 —
-- which is why every row but the last reads `sz=2` and the rows still split.
-- This is the whole discrimination of §1 and §2 in one table.
#guard ["k:\n  \"a\"\n    [1, 2]\n", "k:\n  \"a\"\n  [1, 2]\n",
        "a: 1\n[1, 2]\n", "- \"a\"\n[1, 2]\n", "- \"a\"\n  [1, 2]\n",
        "\"x\"\n[1, 2]\n"].map atOpen
  == ["ci=0 col=4 sz=2", "ci=0 col=2 sz=2", "ci=0 col=0 sz=2",
      "ci=0 col=0 sz=2", "ci=0 col=2 sz=2", "ci=-1 col=0 sz=1"]

-- The key side of the same residue.
#guard (fires "k:\n  \"a\"\n    [1]: b\n", verdict "k:\n  \"a\"\n    [1]: b\n")
  == ("bare@3 sz=2", "scan-bare 2,4")

-- A plain scalar absorbs the line at an open level too, so these are accepted
-- outright rather than left to the parser.
#guard (fires "k:\n  a\n  [1, 2]\n", verdict "k:\n  a\n  [1, 2]\n") == ("clean", "OK")

-- The faces above this fallback are untouched: a virgin park, a `...` park and
-- a `---` park all take their own route and none of them is a landing behind a
-- completed value.
#guard ["[1, 2]\n", "# c\n[1, 2]\n", "...\n[1, 2]\n", "---\n[1, 2]\n",
        "- [1, 2]\n", "&a [b]\n"].map verdict
  == ["OK", "OK", "OK", "OK", "OK", "OK"]

-- Not every refusal at this landing is §9.2's: a plain scalar met by a flow
-- key on the next line is an implicit-key failure, and the bare-document check
-- reports `ok` on the way past.
#guard fires "a\n[1]: b\n" == "step-error@1"

/-! ## §3  The flow route, guarded

`topLevelFlowResumeSep` is `bareNodeRoute`'s flow-side twin: the completed
collection as a fresh bare document on a stream that has already finished one.
It is the same reading row 19's 1c deletes, and the guard takes the half of its
domain the scanner has already refused out of it. -/

/-- The route itself. -/
example {sp_start sp_mid sp_br : SurfPos}
    (h_stream : SLYamlStream sp_start sp_mid)
    (h_sep : SSeparateLines 0 sp_mid sp_br) :
    ∀ sp_ne sp_m, SFlowContent 0 .flowOut sp_br sp_ne →
      SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m :=
  topLevelFlowResumeSep h_stream h_sep

/-- …and the same route with §9.2's landing refusal taken out of its domain. -/
example {sc s_prep : ScannerState} {c : Char} {sp_start sp_mid sp_br : SurfPos}
    (h_ref : BareLandingFacts sc s_prep c ∨ True)
    (h_stream : SLYamlStream sp_start sp_mid)
    (h_sep : SSeparateLines 0 sp_mid sp_br) :
    ∀ sp_ne sp_m, SFlowContent 0 .flowOut sp_br sp_ne →
      SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m :=
  topLevelFlowResumeSep_or_refused h_ref h_stream h_sep

/-- A park with no `CompletedTail` still gets the route: the guard is a
    NARROWING, not a deletion.  Of the four parks that reach `main`, the two
    that punt are `pendingFlow` (the deferred state, whose tail is a block
    indicator) and `pendingDocEnd` (which takes the suffix arm above this one);
    the other five parks the flow open splits on build their own result and
    reach neither fallback. -/
example {sp_start sp_mid sp_br : SurfPos}
    (h_stream : SLYamlStream sp_start sp_mid)
    (h_sep : SSeparateLines 0 sp_mid sp_br) :
    ∀ sp_ne sp_m, SFlowContent 0 .flowOut sp_br sp_ne →
      SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m :=
  topLevelFlowResumeSep_or_refused (sc := ScannerState.mk' "")
    (s_prep := ScannerState.mk' "") (c := 'x') (Or.inr trivial) h_stream h_sep

/-- Resting ON an open level the check stands aside by its own reading, which is
    what makes the guard a narrowing rather than a deletion. -/
example (s : ScannerState)
    (h : (s.indents.any fun e => e.column == (s.col : Int)) = true) :
    scanNextToken_checkBareDocument s = .ok () := by
  unfold scanNextToken_checkBareDocument
  rw [ite_eq_right (by simp [h])]

/-! ## §4  The reading `preprocess_flow_thread` was dropping

Item 139 appended `simpleKeyAllowed` to `preprocess_some_ssl_comments_anyCol`'s
landed arm.  `preprocess_flow_thread` is the coarsening the flow open splits
on, and it was discarding that third component — so the flag could not be read
inside `main`.  It carries it now, and both of its first arm's sub-cases can
answer: a park already at a line start crossed nothing and hands its own flag
forward, and a park off one reached the landing across a break, which re-arms
it. -/

example {sc s_prep : ScannerState} {sp_scan sp_prep : SurfPos} {c : Char}
    (h_corr : ScannerSurfCorr sc sp_scan)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow : s_prep.inFlow = false)
    (h_park : sc.simpleKeyAllowed = true ∨ 0 < sp_scan.col)
    (h_gate : sc.col ≠ 0 → ¬(Proofs.ScannerCoupling.CommentOk sc ∧ sc.peek? = some '#')) :
    (∃ sp_mid, SSLComments sp_scan sp_mid ∧ GStar SSWhite sp_mid sp_prep ∧
      s_prep.simpleKeyAllowed = true) ∨
    (sp_scan.col ≠ 0 ∧ GStar SSWhite sp_scan sp_prep) :=
  preprocess_flow_thread sc sp_scan sp_prep s_prep c h_corr hcorr_prep h_pre h_noflow h_park (GStar.nil _)
    (fun _ => h_gate)

/-- …which is all `main` needs to assemble item 142's bundle. -/
example {sc s_prep : ScannerState} {c : Char}
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow : s_prep.inFlow = false)
    (h_ska : s_prep.simpleKeyAllowed = true)
    (h_tail : CompletedTail sc)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc) :
    BareLandingFacts sc s_prep c :=
  ⟨h_bare, h_pre, h_noflow, h_ska, h_tail, h_base⟩

/-! ## §5  The key side

`flowKeyRoute_of_root` hands the collection the entry route it will need if the
collection turns out to be a mapping key.  Its landing arm falls back to
`rootMapRoute`, and item 142's guard is what that arm takes now; its no-break
arm is the park at a line start, which is not a landing and keeps the route
it had. -/

example {sc s_prep : ScannerState} {c : Char} {sp_start sp_land sp_key : SurfPos} {k : Nat}
    (h_ref : BareLandingFacts sc s_prep c ∨ True)
    (hcol0 : sp_land.col = 0)
    (h_stream : SLYamlStream sp_start sp_land)
    (h_ind : SIndent k sp_land sp_key) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v :=
  rootMapRoute_or_refused h_ref hcol0 h_stream h_ind

/-- And spent: at a landing that stands at no open level, the landing does not
    exist. -/
example {sc s_prep : ScannerState} {c : Char}
    (h : BareLandingFacts sc s_prep c)
    (h_op : (s_prep.indents.any fun e => e.column == (s_prep.col : Int)) = false) :
    False :=
  h.refutes h_op

/-! ## §6  What remains

The `[210]` flip is UNCHANGED at five errors, and that is this item's shape:
the flip counts CONSTRUCTION sites, and this item removes none — it removes
callers from one site's reachable domain.  `topLevelFlowResumeSep`,
`rootMapRoute`, `rootMapRouteF`, `bareNodeRoute` and
`structural_dispatch_to_pending` all still build `[211]`'s implicit
continuation; what changed is that the flow dispatcher can no longer reach the
first two at a sentinel landing.

Two lanes are left.  The CONTENT dispatch's own key and node routes —
`content_dispatch_routed`'s two `rootMapRoute`/`rootMapRouteF` pairs and
`content_dispatch_after_close`'s `bareNodeRoute` — take no guard yet; item
139's thread reaches that step but stops at the landing skeleton.  And
`structural_dispatch_to_pending` is the fifth site, which builds an EXPLICIT
document and so is not this refusal's business at all.

What no refusal reaches stays §2's second measurement, now with a flow witness:
`k:⏎␣␣"a"⏎␣␣␣␣[1, 2]` scans clean and only `TokenParser` refuses it. -/

end L4YAML.Tests.Guards.StreamFlowLandingRefusal

end Blanket
