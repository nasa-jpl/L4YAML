module

public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx
public meta import L4YAML.Output.EventsIx
public import L4YAML.Proofs.Production.StreamAccum

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # `ResumeFrames.one` instantiated (DOCS item 371, Rule 2)

Item 371 restated every value-line pack's conclusion from the fused stream to
one still-open mapping level, `ResumeFrames (SLYamlStream sp_start)
[FrameLevel.map nv] sp_v`, built by the new `ResumeFrames.one` from a TAIL
ROUTE `∀ sp_end, SCompactMapTail k sp sp_end → P sp_end`.  Priority 39 reads
the parser's verdicts; this file instantiates the lemma itself, at the term
level, on the boundary cases Rule 2 names:

* §1 the width `k` at 0 / 1 / 2 and the frame list it leaves (exactly one level);
* §2 the hypothesis is load-bearing: the `nil` tail is always available, so
  the route must already hold at `sp` — a bottom nothing satisfies refutes
  the construction, and `close` is the `nil` instance of the route;
* §3 the spend: `resumeAt` at the level's own width pops to the EMPTY stack
  and continues through one compact entry (`? a⏎:⏎b: 1`'s `b: 1`), while
  any other width is not a member — the dedent arm's whole decision;
* §4 the singleton beneath a deeper stack (an enclosing level over it), and
  the two ways the item's consumers spend the pack (`close` for the fused
  spenders, the tail for the sibling);
* §5 the parser's reading of the same four shapes, so the term-level rows and
  the executable rows name the same inputs.
-/

namespace L4YAML.Tests.Guards.ResumeFramesOne

open L4YAML L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.IndentStackCover (FrameLevel)

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

/-! ## §1 Width 0 / 1 / 2, one level -/

example {P : SurfPos → Prop} {sp : SurfPos}
    (h : ∀ sp_end, SCompactMapTail 0 sp sp_end → P sp_end) :
    ResumeFrames P [FrameLevel.map 0] sp := ResumeFrames.one h

example {P : SurfPos → Prop} {sp : SurfPos}
    (h : ∀ sp_end, SCompactMapTail 1 sp sp_end → P sp_end) :
    ResumeFrames P [FrameLevel.map 1] sp := ResumeFrames.one h

example {P : SurfPos → Prop} {sp : SurfPos}
    (h : ∀ sp_end, SCompactMapTail 2 sp sp_end → P sp_end) :
    ResumeFrames P [FrameLevel.map 2] sp := ResumeFrames.one h

/-- The list is the one level and nothing beneath it: `h_lt` is vacuous, which
    is what lets the singleton sit at the bottom of ANY deeper stack (§4). -/
example : ∀ fr ∈ ([] : List FrameLevel), fr.width < 0 :=
  fun _ h => absurd h List.not_mem_nil

/-! ## §2 The hypothesis is load-bearing -/

/-- `close` is the route at the `nil` tail — the value's mapping goes on with
    NO sibling (`? a⏎:⏎`), and the bottom holds where the pack ended. -/
example {P : SurfPos → Prop} {k : Nat} {sp : SurfPos}
    (h : ∀ sp_end, SCompactMapTail k sp sp_end → P sp_end) :
    (ResumeFrames.one h).close = h sp (SCompactMapTail.nil k sp) := rfl

/-- A bottom nothing satisfies cannot be built: the `nil` tail is always
    there, so the route would already have to pay `P sp`. -/
example {k : Nat} {sp : SurfPos} :
    ¬ (∀ sp_end, SCompactMapTail k sp sp_end → False) :=
  fun h => h sp (SCompactMapTail.nil k sp)

/-- …and conversely a singleton over an impossible bottom is itself
    uninhabited, so the conclusion is not vacuous (§7: the informative side). -/
example {k : Nat} {sp : SurfPos} :
    ResumeFrames (fun _ => False) [FrameLevel.map k] sp → False :=
  fun h => h.close

/-- The route must hold at every tail end, not only at `sp`: a bottom that
    pins the position refutes the construction as soon as one compact entry
    is read. -/
example {k : Nat} {sp sp_i sp_v : SurfPos}
    (h_ind : SIndent k sp sp_i) (h_entry : SBlockMapEntry k sp_i sp_v)
    (h : ResumeFrames (fun sp' => sp' = sp) [FrameLevel.map k] sp)
    (h_ne : sp_v ≠ sp) : False :=
  match h with
  | .level _ _ _ _ h_cont =>
      h_ne (h_cont sp_v
        (SCompactMapTail.cons k sp sp_i sp_v sp_v h_ind h_entry (SCompactMapTail.nil k sp_v))).close

/-! ## §3 The spend -/

/-- The positional reading's exactness (item 473; a test-side reader): one level resumed at its own
    width leaves nothing. -/
private lemma resumeWidths_nil_of_singleton {e : FrameLevel} {ks' : List FrameLevel} {j : Nat}
    (h : ResumeWidths [e] ks' j) : ks' = [] := by
  obtain ⟨_, pre, e', heq, _, _⟩ := h
  cases pre with
  | nil => exact (List.cons.inj heq).2.symm
  | cons p pre' =>
      exact absurd (List.cons.inj heq).2.symm
        (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))



/-- `resumeAt` at the level's own width: the popped stack is EMPTY — `ks'`
    has no member, because every survivor would have to be `map k` with
    width below `k`. -/
example {P : SurfPos → Prop} {k : Nat} {sp : SurfPos}
    (h : ∀ sp_end, SCompactMapTail k sp sp_end → P sp_end) :
    ∃ ks', ks' = [] ∧
      (∀ sp_end, SCompactMapTail k sp sp_end → ResumeFrames P ks' sp_end) :=
  match (ResumeFrames.one h).resumeAt (List.mem_singleton.mpr rfl) with
  | ⟨ks', h_w, cont⟩ =>
      ⟨ks', resumeWidths_nil_of_singleton h_w, cont⟩

/-- One compact entry after the value (`? a⏎:⏎b: 1`'s `b: 1`), then the bottom:
    the sibling's tail is exactly what the route was asked to pay. -/
example {P : SurfPos → Prop} {k : Nat} {sp sp_i sp_v : SurfPos}
    (h : ∀ sp_end, SCompactMapTail k sp sp_end → P sp_end)
    (h_ind : SIndent k sp sp_i) (h_entry : SBlockMapEntry k sp_i sp_v) :
    P sp_v :=
  match (ResumeFrames.one h).resumeAt (List.mem_singleton.mpr rfl) with
  | ⟨_, _, cont⟩ =>
      (cont sp_v (SCompactMapTail.cons k sp sp_i sp_v sp_v h_ind h_entry
        (SCompactMapTail.nil k sp_v))).close

/-- Any OTHER width is not a member of the singleton — a landing that is not at
    the value's mapping column cannot resume it (`x:⏎  ? a⏎  :⏎y: 2`'s `y` is
    the enclosing level's business, item 372+, not this pack's). -/
example : FrameLevel.map 0 ∉ [FrameLevel.map 2] := by decide
example : FrameLevel.map 1 ∉ [FrameLevel.map 2] := by decide
example : FrameLevel.map 3 ∉ [FrameLevel.map 2] := by decide
example : FrameLevel.map 2 ∈ [FrameLevel.map 2] := by decide

/-! ## §4 Beneath a deeper stack, and the two spends -/

/-- The singleton is the bottom of a two-level stack: an enclosing mapping at
    0 whose own tail then pays a singleton at 2. -/
example {P : SurfPos → Prop} {sp : SurfPos}
    (route : ∀ sp_e, SCompactMapTail 2 sp sp_e →
      ∀ sp_end, SCompactMapTail 0 sp_e sp_end → P sp_end) :
    ResumeFrames P [FrameLevel.map 2, FrameLevel.map 0] sp :=
  ResumeFrames.level 2 [FrameLevel.map 0] sp
    (fun fr hfr => by rw [List.mem_singleton.mp hfr]; decide)
    (fun sp_e h_tail => ResumeFrames.one (route sp_e h_tail))

/-- The item's value-line pack, spent as the fused spenders do: `close`
    reaches the stream (every `.close` site item 371 added). -/
example {sp_start sp_v : SurfPos} {nv : Nat}
    (pack : ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v) :
    SLYamlStream sp_start sp_v := pack.close

/-- …and as `colon_open_map_explicit`'s park now does: the value's mapping
    may go on with a sibling before the stream is reached. -/
example {sp_start sp_v sp_i sp_s : SurfPos} {nv : Nat}
    (pack : ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v)
    (h_ind : SIndent nv sp_v sp_i) (h_entry : SBlockMapEntry nv sp_i sp_s) :
    SLYamlStream sp_start sp_s :=
  match pack.resumeAt (List.mem_singleton.mpr rfl) with
  | ⟨_, _, cont⟩ =>
      (cont sp_s (SCompactMapTail.cons nv sp_v sp_i sp_s sp_s h_ind h_entry
        (SCompactMapTail.nil nv sp_s))).close

/-! ## §5 The parser on the same shapes -/

-- §2's `nil` tail: no sibling, the entry closes its mapping.
#guard emits "? a\n:\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :", "-MAP", "-DOC", "-STR"]
-- §3's one compact entry at the value's width (0).
#guard emits "? a\n:\nb: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :", "=VAL :b", "=VAL :1", "-MAP",
   "-DOC", "-STR"]
-- §1's width 2: the same tail inside an enclosing mapping.
#guard emits "x:\n  ? a\n  :\n  b: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :x", "+MAP", "=VAL :a", "=VAL :", "=VAL :b",
   "=VAL :1", "-MAP", "-MAP", "-DOC", "-STR"]
-- §4's two-level stack: the landing at 0 is the ENCLOSING level's tail, not a
-- member of the singleton at 2 (parser verdict; the enclosing frame is item 372+).
#guard emits "x:\n  ? a\n  :\ny: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :x", "+MAP", "=VAL :a", "=VAL :", "-MAP",
   "=VAL :y", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- A width that is no open level at all is refused before any pack is spent.
#guard refuses "x:\n  ? a\n  :\n y: 2\n"

end L4YAML.Tests.Guards.ResumeFramesOne
