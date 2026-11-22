module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # §9.2's landing refusal at the CONTENT landing's KEY routes (DOCS item 144)

Item 139 threaded `scanNextToken_checkBareDocument`'s success to the content
dispatch and guarded the NODE route it spends; items 142 and 143 carried the
same bundle to the block landing and the flow open.  What all three left behind
is the content dispatch's own KEY cascade: `content_dispatch_routed`'s
last-resort arm applied `rootMapRoute` and `rootMapRouteF` RAW, twice apiece —
once in the props pack's cascade, once in the content pack's.  A landed key at
the sentinel takes that arm, and `"x"⏎b: 2` is refused before its `:` exists.

This item guards those four and measures the one raw site it deliberately
leaves standing: `content_dispatch_after_close`'s `bareNodeRoute`, whose
refutable half is EMPTY.

§1 is the half the refusal closes, read at the KEY side.  §2 is the half it does
not.  §3 is the empty site, and the two DIFFERENT reasons its three callers give
for being empty.  §4 is the guarded routes and the narrowing at their types.
§5 is what remains.

No runtime file is touched, so every verdict below is the one the pipelines
already gave. -/

namespace L4YAML.Tests.Guards.StreamContentLandingRefusal

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

/-! ## §1  The half §9.2 closes, at the key side

`fires` walks the real `scanNextToken` and reports which §9.2 check fired, at
which landing, and at what indent-stack size.  `verdict` separates the scanner's
refusal from the parser's. -/

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

private def verdict (input : String) : String :=
  match scan input with
  | .error (.invalidBareDocument l c) => s!"scan-bare {l},{c}"
  | .error (.invalidImplicitKey l) => s!"scan-implicitkey {l}"
  | .error e => s!"scan {toString (repr e)}"
  | .ok _ =>
    match Events.streamToEvents input with
    | .error (.invalidBareDocument l c) => s!"parse-bare {l},{c}"
    | .error e => s!"parse {toString (repr e)}"
    | .ok _ => "OK"

-- **A completed top-level node, a break, and a landed KEY at the sentinel.**
-- This is the arm the root fallback serves inside `content_dispatch_routed`,
-- and the scanner refuses all of it AT the landing — before the key's own `:`
-- is scanned, and so before the mapping the route would build exists.
#guard ["\"x\"\nb: 2\n", "'x'\nb: 2\n"].map fires == ["bare@1 sz=1", "bare@1 sz=1"]

-- A completed FLOW collection is a completed value too, and the refusal is at
-- the landing after its closing bracket.
#guard (fires "[1, 2]\nb: 2\n", fires "{a: 1}\nb: 2\n") == ("bare@5 sz=1", "bare@5 sz=1")

-- **The plain scalar needs a comment line to reach this family at all**, and it
-- is refused by a DIFFERENT check without one: `a⏎b` is ONE multi-line
-- `[131] ns-plain`, and an implicit key is restricted to a single line.  So the
-- two refusals partition the plain-scalar shape rather than overlapping.
#guard verdict "a\nb: 2\n" == "scan-implicitkey 1"
#guard (fires "a\n# c\nb: 2\n", verdict "a\n# c\nb: 2\n") == ("bare@1 sz=1", "scan-bare 2,0")

-- The property run's own scalar completes the node, and the run's tokens push
-- the landing two steps out.
#guard (fires "&p a\n# c\nb: 2\n", verdict "&p a\n# c\nb: 2\n") == ("bare@2 sz=1", "scan-bare 2,0")

-- The verdicts, at the two landings the family splits between.
#guard ["\"x\"\nb: 2\n", "'x'\nb: 2\n", "[1, 2]\nb: 2\n", "{a: 1}\nb: 2\n"].map verdict
  == ["scan-bare 1,0", "scan-bare 1,0", "scan-bare 1,0", "scan-bare 1,0"]
#guard verdict "\"x\"\n# c\nb: 2\n" == "scan-bare 2,0"

/-! ## §2  The half it does not

A level still open at the landing is a SIBLING entry, not a second document, and
the check stands aside by its own indent-stack reading.  The last input is the
residue: §9.2 never reaches an indented landing, so the refusal stays in the
parser — the content lane's copy of item 143's `k:⏎␣␣"a"⏎␣␣[1, 2]`. -/

#guard ["a: 1\nb: 2\n", "k: [1, 2]\nb: 2\n"].map fires == ["clean", "clean"]
#guard ["a: 1\nb: 2\n", "k: [1, 2]\nb: 2\n"].map verdict == ["OK", "OK"]

-- …and a marker between them makes the second document legal outright.
#guard (fires "a: 1\n...\nb: 2\n", fires "a: 1\n---\nb: 2\n") == ("clean", "clean")
#guard (verdict "a: 1\n...\nb: 2\n", verdict "a: 1\n---\nb: 2\n") == ("OK", "OK")

-- THE INDENTED LANDING.  Item 144 recorded this as the parser's alone — the
-- scanner was clean because the stack was not the sentinel.  Item 145 reads the
-- landing's COLUMN instead: level 2 was never pushed, so `"x"` fills `k`'s slot
-- and `b` stands at no open level.  Same error, same position, one layer up.
#guard (fires "k:\n  \"x\"\n  b: 2\n", verdict "k:\n  \"x\"\n  b: 2\n")
  == ("bare@3 sz=2", "scan-bare 2,2")

/-! ## §3  The raw site this item leaves, and why its refutable half is empty

`content_dispatch_after_close` still applies `bareNodeRoute` raw.  Its three
callers park on `pendingBlock`, `pendingMapValue` and `pendingProps`, and
`tails` reads what §9.2 would have to read at each of their landings: the indent
stack, and whether the park's last real token completes a value.

**The three are empty for two different reasons**, which is the measurement.
The `-` and `:` parks stand aside on the STACK (`sz=3` at the indented levels
their callers serve).  The props park stands AT the sentinel (`sz=1`) and §9.2
stands aside anyway, on the TOKEN — an anchor is not a completed value.  So no caller can produce the `CompletedTail` the
guard needs to bite, and guarding here would add a parameter nobody pays. -/

private def tagOf : YamlToken → String
  | .placeholder => "placeholder"
  | .blockEntry => "blockEntry"
  | .value => "value"
  | .anchor _ => "anchor"
  | .tag _ _ => "tag"
  | .scalar _ _ => "scalar"
  | t => toString (repr t)

private def tailAt (s : ScannerState) : Nat → List String
  | 0 => ["fuel"]
  | fuel + 1 =>
    match scanNextToken_preprocess s with
    | .error _ => ["preprocess-error"]
    | .ok none => []
    | .ok (some (s1, c)) =>
      let bare := match scanNextToken_checkBareDocument s1 with
        | .error _ => "BARE" | .ok _ => "-"
      let tl := match lastRealTokenVal? s1.tokens with
        | none => "none:false"
        | some t => s!"{tagOf t}:{t.completesFlowValue}"
      let row := s!"{c}|sz={s1.indents.size}|{tl}|{bare}"
      match scanNextToken s with
      | .ok (some s') => row :: tailAt s' fuel
      | _ => [row]

private def tails (input : String) : List String :=
  tailAt (ScannerState.mk' input) 40

-- The `-` park at an INDENTED level.  `accum_content_on_pendingBlock_indented`
-- is the arm the `pendingBlock` case takes at `n_old = k+1`, and it is the
-- first of the three callers; the tail at its landing is `blockEntry`.
#guard tails "k:\n  -\n    b\n"
  == ["k|sz=1|placeholder:false|-", ":|sz=1|scalar:true|-",
      "-|sz=2|value:false|-", "b|sz=3|blockEntry:false|-"]

-- The `:` park at an indented level, the second caller; its tail is `value`.
#guard tails "k:\n  a:\n    b\n"
  == ["k|sz=1|placeholder:false|-", ":|sz=1|scalar:true|-", "a|sz=2|value:false|-",
      ":|sz=2|scalar:true|-", "b|sz=3|value:false|-"]

-- The same two parks at the ROOT, where the stack is shallower and the TOKEN
-- reading is unchanged.  (`n_old = 0` takes the non-`_indented` twins, which
-- build their own result and reach this route not at all.)
#guard (tails "-\n  b\n", tails "k:\n  b\n")
  == (["-|sz=1|placeholder:false|-", "b|sz=2|blockEntry:false|-"],
      ["k|sz=1|placeholder:false|-", ":|sz=1|scalar:true|-", "b|sz=2|value:false|-"])

-- **The props park is the interesting one**: it lands AT the sentinel, and the
-- check still stands aside — on the token reading alone.
#guard tails "&p\n  b\n"
  == ["&|sz=1|placeholder:false|-", "b|sz=1|anchor:false|-"]
#guard tails "&p\n# c\nb\n"
  == ["&|sz=1|placeholder:false|-", "b|sz=1|anchor:false|-"]

/-- What a caller would have to produce for the guard to bite — and what none of
    the three parks records.  Their tails are measured above; all three read
    `completesFlowValue = false`. -/
example {sc : ScannerState} (h : CompletedTail sc) :
    ∃ t, lastRealTokenVal? sc.tokens = some t ∧ t.completesFlowValue = true := h.2

/-! ## §4  The guarded key routes, and the narrowing at their types

The fallback is a narrowing, not a deletion: with nothing completed behind the
park the guarded route still delivers the raw one's conclusion. -/

example {sc s_prep : ScannerState} {c : Char}
    {sp_start sp_land sp_key : SurfPos} {k : Nat}
    (h_ref : BareLandingFacts sc s_prep c ∨ True)
    (hcol0 : sp_land.col = 0)
    (h_stream : SLYamlStream sp_start sp_land)
    (h_ind : SIndent k sp_land sp_key) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v :=
  rootMapRoute_or_refused h_ref hcol0 h_stream h_ind

example {sc s_prep : ScannerState} {c : Char}
    {sp_start sp_land sp_key : SurfPos} {k : Nat}
    (h_ref : BareLandingFacts sc s_prep c ∨ True)
    (hcol0 : sp_land.col = 0)
    (h_stream : SLYamlStream sp_start sp_land)
    (h_ind : SIndent k sp_land sp_key) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v →
    ∀ sp_e, SCompactMapTail k sp_v sp_e →
    ResumeFrames (SLYamlStream sp_start) [] sp_e :=
  rootMapRouteF_or_refused h_ref hcol0 h_stream h_ind

/-- THE NARROWING.  `Or.inr` keeps the raw route, so a park that finished no
    node loses nothing — the route is reachable at any scanner state at all. -/
example {sp_start sp_land sp_key : SurfPos} {k : Nat}
    (hcol0 : sp_land.col = 0)
    (h_stream : SLYamlStream sp_start sp_land)
    (h_ind : SIndent k sp_land sp_key) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v :=
  rootMapRoute_or_refused (sc := ScannerState.mk' "") (s_prep := ScannerState.mk' "")
    (c := 'x') (Or.inr trivial) hcol0 h_stream h_ind

/-- The bundle spent: at a landing that stands at no open level, this landing
    does not exist. -/
example {sc s_prep : ScannerState} {c : Char}
    (h : BareLandingFacts sc s_prep c)
    (h_op : (s_prep.indents.any fun e => e.column == (s_prep.col : Int)) = false) :
    False :=
  h.refutes h_op

/-- The bundle assembled, as the two landing arms of `accum_content_pending`'s
    skeleton assemble it: the check's verdict at the landing, the park's own
    preprocessing, the block context, the re-armed flag, the park's completed
    tail, and the stack's base. -/
example {sc s_prep : ScannerState} {c : Char}
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow : s_prep.inFlow = false)
    (h_ska : s_prep.simpleKeyAllowed = true)
    (h_tail : CompletedTail sc)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc) :
    BareLandingFacts sc s_prep c :=
  ⟨h_bare, h_pre, h_noflow, h_ska, h_tail, h_base⟩

/-! ## §5  What remains

Every landing consumer that can PAY the guard now spends a guarded route — §3's
site is the one that cannot, and it is empty rather than pending.  What the
§9.2 checks do NOT reach at all is the INDENTED landing — `k:⏎␣␣"x"⏎␣␣b: 2` above,
clean at the scanner and refused only by the parser — and that half is item
141's park face, priced at a converging 32 sites.  The two raw applications left
in the module are both measured rather than pending: this file's §3 site, whose
callers cannot pay, and `flowKeyRoute_of_root`'s no-break arm, which is a park at
a line start and not a landing at all. -/

end L4YAML.Tests.Guards.StreamContentLandingRefusal

end Blanket
