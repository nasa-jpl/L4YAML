module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # §9.2's landing refusal at the BLOCK landing (DOCS item 142)

Item 139 threaded `scanNextToken_checkBareDocument`'s success to the CONTENT
landing and measured that it refutes exactly half of the bare-document
fallback's domain.  Item 141 priced the other half and found the ordering
wrong: the block landing is not a peer of the dangling window but its
prerequisite.  This item threads the same success to the block landing.

Three things change, and each is pinned below:

* `accum_block_on_closeThenBlock` built `[211]`'s implicit continuation INLINE —
  the sixth `[210]` construction site, and the one item 139's `bareNodeRoute`
  did not collapse.  It is that lemma now, guarded;
* `rootMapRoute`/`rootMapRouteF`, the key-side siblings the `:`/`?` openers
  fall back to, take the refusal as a fifth route arm;
* the thread itself: `h_bare` runs from `scanNextToken_accum_step` through
  `accum_step_block` to every park the block dispatch splits on, and
  `BareLandingFacts` is the bundle that carries it the last two lemmas.

§1 is the half the refusal closes, measured on the real scanner.  §2 is the
half it does not, with the discriminator and one input the scanner accepts and
only the parser refuses.  §3 is the bundle at its type.  §4 is the flag twin.
§5 is the two guarded key routes, with the narrowing shown to be a narrowing.
§6 is what remains.

No runtime file is touched, so every verdict below is the one the pipelines
already gave. -/

namespace L4YAML.Tests.Guards.StreamBlockLandingRefusal

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

/-! ## §1  The half §9.2 closes

`fires` walks the real `scanNextToken` and reports which §9.2 check fired, at
which landing, and at what indent-stack size; `verdict` separates the SCANNER's
verdict from the parser's, because the difference between them is what item 140
was about and what §2 below measures again. -/

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
  | .error e => s!"scan {toString (repr e)}"
  | .ok _ =>
    match Events.streamToEvents input with
    | .error (.invalidBareDocument l c) => s!"parse-bare {l},{c}"
    | .error e => s!"parse {toString (repr e)}"
    | .ok _ => "OK"

-- **Every head shape, met by a block indicator across a break, at the
-- sentinel alone.**  This is the fallback arm `rootMapRoute` serves at
-- `colon_open_map`/`question_open_map` and `bareNodeRoute` serves at the `-`,
-- and the scanner refuses all of it AT the landing — before the collection
-- the indicator opens is ever accumulated.
#guard ["a\n: v\n", "\"x\"\n: v\n", "'x'\n: v\n"].map fires
  == ["bare@1 sz=1", "bare@1 sz=1", "bare@1 sz=1"]

#guard ["[1, 2]\n: v\n", "{a: 1}\n: v\n"].map fires
  == ["bare@5 sz=1", "bare@5 sz=1"]

-- A property run completes at its SCALAR, so the refusal is one landing later
-- than the `&`.
#guard fires "&p a\n: v\n" == "bare@2 sz=1"

-- The `-` and `?` reach the same refusal — but only where the plain run has
-- stopped.  A comment line stops it; a bare next line does not, because the
-- plain scalar absorbs its own continuation (item 139's own reading, re-read
-- at the block landing).
#guard (fires "a\n# c\n- b\n", fires "a\n- b\n") == ("bare@1 sz=1", "clean")
#guard (fires "a\n# c\n: v\n", fires "a\n? k\n") == ("bare@1 sz=1", "clean")

-- The verdicts, and they are the SCANNER's.
#guard ["a\n: v\n", "\"x\"\n: v\n", "'x'\n: v\n", "[1, 2]\n: v\n", "{a: 1}\n: v\n",
        "&p a\n: v\n"].map verdict
  == ["scan-bare 1,0", "scan-bare 1,0", "scan-bare 1,0", "scan-bare 1,0",
      "scan-bare 1,0", "scan-bare 1,0"]

#guard (verdict "a\n# c\n: v\n", verdict "a\n# c\n- b\n")
  == ("scan-bare 2,0", "scan-bare 2,0")

/-! ## §2  The half it does not

The discriminator is the indent stack, exactly as at the content landing:
resting ON an open level the same shapes are legal (`a: 1⏎: v` is the root
mapping's second entry) or belong to a different refusal.  [Item 145 moved the
boundary: the check reads the landing's own COLUMN, so the indented `:` below
is refused by the scanner now and this section's residue is the `-`'s alone.] -/

-- A level open: the landing is an ordinary sibling and nothing refuses it.
#guard ["a: 1\n: v\n", "a: 1\n? k\n", "k:\n  a: 1\n  ? k\n"].map fires
  == ["clean", "clean", "clean"]
#guard ["a: 1\n: v\n", "a: 1\n? k\n", "k:\n  a: 1\n  ? k\n"].map verdict
  == ["OK", "OK", "OK"]

-- **A completed value met by a `:` at its own column, one level in.**  The
-- run IS offered a slot (`k:` is its predecessor), so the dangling check stands
-- aside.  The bare-document check stood aside too until item 145 — the stack is
-- size 2, which was its first conjunct — and reads the landing's COLUMN now:
-- level 2 was never pushed, so the `:` stands at no open level and the refusal
-- is the scanner's, at the position the parser used to report.
#guard (fires "k:\n  a\n  : v\n", verdict "k:\n  a\n  : v\n")
  == ("bare@3 sz=2", "scan-bare 2,2")

-- …and the refusal lands BEFORE the `:`'s own token, so nothing is scanned
-- past it: the array the parser used to receive (seventeen tokens) is never
-- built.
#guard (match scan "k:\n  a\n  : v\n" with | .ok ts => ts.size | .error _ => 0) == 0

-- The `-` at an open level is refused by the dispatch's own indent check, not
-- by §9.2 — so the check reports `ok` and the STEP is what fails.
#guard (fires "a: 1\n- b\n", verdict "a: 1\n- b\n") == ("step-error@3", "scan-bare 1,0")

/-- Resting ON an open level the check stands aside by its own reading, whatever
    the tail says.  This is why the guard below is a NARROWING and not a
    deletion. -/
example (s : ScannerState)
    (h : (s.indents.any fun e => e.column == (s.col : Int)) = true) :
    scanNextToken_checkBareDocument s = .ok () := by
  unfold scanNextToken_checkBareDocument
  rw [ite_eq_right (by simp [h])]

/-! ## §3  The bundle

`BareLandingFacts` holds the readings `bareDocument_refutes_landing` spends,
minus the indent stack — the discriminator stays with the consumer that splits
on it.  One hypothesis is what crosses `indicator_open_map` and
`colon_open_map` without turning a route's signature into a scanner state. -/

example {sc s_prep : ScannerState} {c : Char}
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow : s_prep.inFlow = false)
    (h_ska : s_prep.simpleKeyAllowed = true)
    (h_tail : CompletedTail sc)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc) :
    BareLandingFacts sc s_prep c :=
  ⟨h_bare, h_pre, h_noflow, h_ska, h_tail, h_base⟩

/-- …and spent: at a landing that stands at no open level, the landing does not
    exist. -/
example {sc s_prep : ScannerState} {c : Char}
    (h : BareLandingFacts sc s_prep c)
    (h_op : (s_prep.indents.any fun e => e.column == (s_prep.col : Int)) = false) :
    False :=
  h.refutes h_op

/-! ## §4  The flag, from the park or from the break

`landing_or_park_save` (item 77) made the landed `:`'s SAVE unconditional from
two sources; §9.2 reads the FLAG that save is gated on, and the same two
sources answer for it. -/

example {sc s_prep : ScannerState} {sp_scan : SurfPos} {c : Char}
    (h_noflow : s_prep.inFlow = false)
    (h_larm : sp_scan.col ≠ 0 → s_prep.inFlow = false →
      s_prep.simpleKey.possible = true ∧ s_prep.simpleKey.pos.col = s_prep.col ∧
      -- Item 147: the landed arm carries a FOURTH reading now — the landing's
      -- own floor — and these two consumers project past it exactly as they
      -- project past item 139's flag.
      s_prep.simpleKeyAllowed = true ∧
      (s_prep.currentIndent ≤ (s_prep.col : Int) ∨ s_prep.indents.size ≤ 1))
    (h_park : sc.simpleKeyAllowed = true ∨ 0 < sp_scan.col)
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    s_prep.simpleKeyAllowed = true :=
  landing_or_park_ska h_noflow h_larm h_park h_pre

/-- The first source on its own: an armed park hands its flag forward, because
    every writer preprocessing has moves it UP. -/
example {sc s_prep : ScannerState} {c : Char}
    (h_arm : sc.simpleKeyAllowed = true)
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    s_prep.simpleKeyAllowed = true :=
  preprocess_simpleKeyAllowed_mono h_arm h_pre

/-! ## §5  The two key routes, guarded

`rootMapRoute` is what `colon_open_map`/`question_open_map` fall back to when
the park behind the landing is neither a `...`, nor virgin, nor a `---`; it
appends the landed entry's mapping to a FINISHED stream as a second bare
document, which is the reading row 19's 1c deletes. -/

/-- The route itself. -/
example {sp_start sp_land sp_key : SurfPos} {k : Nat}
    (hcol0 : sp_land.col = 0)
    (h_stream : SLYamlStream sp_start sp_land)
    (h_ind : SIndent k sp_land sp_key) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v :=
  rootMapRoute hcol0 h_stream h_ind

/-- …and the same route with §9.2's landing refusal taken out of its domain. -/
example {sc s_prep : ScannerState} {c : Char} {sp_start sp_land sp_key : SurfPos} {k : Nat}
    (h_ref : BareLandingFacts sc s_prep c ∨ True)
    (hcol0 : sp_land.col = 0)
    (h_stream : SLYamlStream sp_start sp_land)
    (h_ind : SIndent k sp_land sp_key) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v :=
  rootMapRoute_or_refused h_ref hcol0 h_stream h_ind

/-- The entries-level twin, refuted at the same landings. -/
example {sc s_prep : ScannerState} {c : Char} {sp_start sp_land sp_key : SurfPos} {k : Nat}
    (h_ref : BareLandingFacts sc s_prep c ∨ True)
    (hcol0 : sp_land.col = 0)
    (h_stream : SLYamlStream sp_start sp_land)
    (h_ind : SIndent k sp_land sp_key) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v →
    ∀ sp_e, SCompactMapTail k sp_v sp_e →
    ResumeFrames (SLYamlStream sp_start) [] sp_e :=
  rootMapRouteF_or_refused h_ref hcol0 h_stream h_ind

/-- A park with no `CompletedTail` still gets the route: the guard is a
    NARROWING, not a deletion.  Those parks are `pendingProps` (a `[96]` run),
    `pendingFlow` (a block indicator) and `pendingMapValue` (the `:` that
    opened it) — the three places `completesFlowValue` is false by
    construction. -/
example {sp_start sp_land sp_key : SurfPos} {k : Nat}
    (hcol0 : sp_land.col = 0)
    (h_stream : SLYamlStream sp_start sp_land)
    (h_ind : SIndent k sp_land sp_key) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v :=
  rootMapRoute_or_refused (sc := ScannerState.mk' "") (s_prep := ScannerState.mk' "")
    (c := 'x') (Or.inr trivial) hcol0 h_stream h_ind

/-- The block landing's NODE route, which was the sixth `[210]` construction
    site until this item: `bareNodeRoute` under item 139's own guard, where
    `accum_block_on_closeThenBlock` wrote `implicitContinue` out by hand. -/
example {sc s_prep : ScannerState} {c : Char} {sp_start sp_anchor : SurfPos}
    (h_stream : SLYamlStream sp_start sp_anchor)
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow : s_prep.inFlow = false)
    (h_ska : s_prep.simpleKeyAllowed = true)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc)
    (h_tail : CompletedTail sc ∨ True) :
    ∀ sp_m, SBlockNode 0 .blockIn sp_anchor sp_m → SLYamlStream sp_start sp_m :=
  bareNodeRoute_or_refused h_stream h_bare h_pre h_noflow h_ska h_base h_tail

/-! ## §6  What remains

The `[210]` flip reports FIVE errors after this item, down from six:
`topLevelFlowResumeSep`, `rootMapRoute`, `rootMapRouteF`, `bareNodeRoute` and
`structural_dispatch_to_pending`.  Two of those five are the flow lane, which
is the next item — `topLevelFlowResumeSep` is this fallback for a completed
FLOW collection and `accum_flow_open_depth0`'s shared `main` is where its
landing spends it — and the three block-lane ones are now guarded at every
caller the block dispatch reaches.

What no refusal reaches is §2's second measurement: a completed value met by an
indicator at its own column with a level still open.  §9.2 has no check for it
(the run is offered a slot, and the stack is not the sentinel), and the park
face item 141 priced is where it has to be carried rather than refuted. -/

end L4YAML.Tests.Guards.StreamBlockLandingRefusal

end Blanket
