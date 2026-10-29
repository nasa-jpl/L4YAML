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

/-! # The key packs carry their column (DOCS item 79)

Item 28 gave `ImplicitKeyPack` a column conjunct and wrote it `∨ True`, for
Reflection 653's reason: a producer that cannot take the measurement should cost
a field value rather than a call site.  Items 59, 63, 75 and 78 answered one
producer each, and this item removes the last of the reason.

Two things were still optional and neither had to be.

* **The mask's base slot.**  `KmSound` promised the bottom tracked slot's column
  `∨ True` because an empty mask has no bottom.  That is a statement about the
  mask, so the mask can carry it: the promise is conditional on `0 < km.size`,
  and every frame's mask is nonempty (`FlowOpenStack.km_pos`).  So
  `KmSound.back_col` and `close_col_of_base` return the column.  (The empty
  mask the `∨ True` was written for was the collapsed stack's; item 126
  deleted that constructor, and `KmSound.empty` is now the only state with no
  bottom slot — nothing in the accumulation hands it.)
* **The compact route's width.**  `entryKeyPack_of_dispatch` took the compact
  frame and the park's column as two options, and all six call sites read them
  off the same field — item 78's observation at the flow open, applied to the
  block dispatch.  Bundled, the arm that has the route has the width to measure
  against.

With those, all four producers measure, `PropsKeyPack`'s column and
`ImplicitKeyPack`'s are equations, and the props park's own flag (`h_ska`) turns
the run's two transports from punts into refutations.

§1–§3 are the compile-time witnesses; §4 is the measurement that says the mask's
promise is the one the scanner actually keeps — at every depth-0 close the key
restored sits at the column the matching open held. -/

namespace Tests.Guards.MaskBaseColumn

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

/-! ## §1  An empty mask promises nothing, and no frame has one -/

/-- The empty mask costs nothing: it promises no base slot, and says so by its
    own size rather than by a disjunct. -/
example (sc : ScannerState) (kc : Nat) : KmSound sc #[] kc := KmSound.empty sc kc

/-- …and no `FlowOpenStack` carries one — the two base constructors write a
    one-bit mask and the two nests push onto one.  This is what discharges the
    base-open premise at a NESTED open. -/
example {s0 : ScannerState} {sp_start : SurfPos} {n kc fl : Nat} {ks km : Array Bool}
    {tl : FrameTail} {a b : SurfPos}
    (h : FlowOpenStack sp_start n kc none s0 fl ks km tl a b) : 0 < km.size := h.km_pos

/-! ## §2  So the outermost close reads a column, not an option -/

/-- `KmSound.back_col`: a mask of exactly one bit discharges the promise's own
    premise, so the slot the close restores comes back with its column — and,
    since item 103, with the open's stamp reading beside it; since item 300,
    with the marker's line too. -/
example {sc : ScannerState} {km : Array Bool} {kc : Nat}
    (h : KmSound sc km kc) (h1 : km.size = 1) :
    ∃ key, sc.simpleKeyStack.back? = some key ∧ key.pos.col = kc ∧
      (sc.implicitValueLine = some key.pos.line ∨ True) ∧
      (sc.docStartLine = some key.pos.line ∨ True) :=
  h.back_col h1

/-! ## §3  …and both packs carry an equation

The pack's column used to be the one thing a consumer had to case on before it
could measure a floor.  It is a projection now. -/

example {sc : ScannerState} {sp_start sp_scan : SurfPos}
    (h : ImplicitKeyPack sc sp_start sp_scan) :
    ∃ k : Nat, sc.simpleKey.pos.col = k := by
  obtain ⟨k, _, _, _, _, _, h_col, _⟩ := h
  exact ⟨k, h_col⟩

example {sc : ScannerState} {sp_start sp_p sp_scan : SurfPos}
    (h : PropsKeyPack sc sp_start sp_p sp_scan) :
    ∃ k : Nat, sc.simpleKey.pos.col = k := by
  obtain ⟨⟨k, _, h_col, _⟩, _⟩ := h
  exact ⟨k, h_col⟩

/-- The flow close's producer, with the COLUMN an equation: nothing in this
    pack is decided by a case split on a measurement.  What stays optional is
    the key ROUTE — a fact about the enclosing construct — and, beside the
    column, the open's stamp reading, which is a fact about the input (item
    103) and is what names the punt where the route is absent. -/
-- Item 311: the flow frame's alternative is the gate's (`PackAltG g`); these probes name an ungated frame.
example {sc : ScannerState} {kc : Nat} {sp_start sp_br sp_tok sp_key : SurfPos}
    (route : ∀ sp_v, SBlockMapEntry kc sp_key sp_v → SLYamlStream sp_start sp_v)
    (head : ∀ sp_end, SFlowContent 0 .flowOut sp_br sp_end →
      ImplicitKeyHead sp_key sp_end ∨ True)
    (h_kc : sc.simpleKey.pos.col = kc)
    (h_park : StalePark sc)
    (h_content : SFlowContent 0 .flowOut sp_br sp_tok) :
    sc.simpleKey.possible = true → sc.simpleKey.pos.line = sc.line →
      ImplicitKeyPack sc sp_start sp_tok ∨ KeyPackPunt sc :=
  flowKeyPack_of_close (g := none) (Or.inl ⟨kc, sp_key, route, head, rfl, Or.inr trivial,
      Or.inr trivial, Or.inr trivial⟩)
    -- Item 300: the base slot's third reading, the marker's line, declined here.
    ⟨h_kc, Or.inr trivial, Or.inr trivial⟩ h_park h_content

/-! ## §4  The promise, measured on the scanner

`closeMatchesOpen` walks the token scanner and, at every `]`/`}` that returns the
flow level to 0, compares the key the close RESTORES against the key the matching
open held.  That comparison IS the mask's base slot: nothing between the two
positions can be read off the closing state, because the interior pushes and pops
the key stack freely and the restore reaches past all of it. -/

private def closeLoop (s : ScannerState) (fuel : Nat) (opened : Option Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    match scanNextToken_preprocess s with
    | .error _ => true
    | .ok none => true
    | .ok (some (sp, c)) =>
      match scanNextToken s with
      | .error _ => true
      | .ok none => true
      | .ok (some s') =>
        let isOpen := (c == '[' || c == '{') && s.flowLevel == 0
        let isClose := (c == ']' || c == '}') && s.flowLevel == 1
        (!isClose || opened == some s'.simpleKey.pos.col) &&
          closeLoop s' fuel' (if isOpen then some sp.simpleKey.pos.col else opened)

private def closeMatchesOpen (input : String) : Bool :=
  closeLoop ((ScannerState.mk' input).emit .streamStart) (input.utf8ByteSize + 2) none

/-- …and the same walk reporting whether a depth-0 close was REACHED, so the
    check above is not vacuous on the shape it is there to measure. -/
private def closeSeenLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match scanNextToken_preprocess s with
    | .error _ => false
    | .ok none => false
    | .ok (some (_, c)) =>
      ((c == ']' || c == '}') && s.flowLevel == 1) ||
        (match scanNextToken s with
         | .error _ => false
         | .ok none => false
         | .ok (some s') => closeSeenLoop s' fuel')

private def closeSeen (input : String) : Bool :=
  closeSeenLoop ((ScannerState.mk' input).emit .streamStart) (input.utf8ByteSize + 2)

-- The five parks that reach a depth-0 open with a key route to offer…
#guard closeMatchesOpen "[1]: b\n" && closeSeen "[1]: b\n"
#guard closeMatchesOpen "- [1]: b\n" && closeSeen "- [1]: b\n"
#guard closeMatchesOpen "k:\n  [1]: b\n" && closeSeen "k:\n  [1]: b\n"
#guard closeMatchesOpen "&a [1]: b\n" && closeSeen "&a [1]: b\n"
#guard closeMatchesOpen "? [1]\n: v\n" && closeSeen "? [1]\n: v\n"
-- …the landings…
#guard closeMatchesOpen "# c\n[1]: b\n" && closeSeen "# c\n[1]: b\n"
#guard closeMatchesOpen "...\n[1]: b\n" && closeSeen "...\n[1]: b\n"
#guard closeMatchesOpen "&a\n[1]: b\n" && closeSeen "&a\n[1]: b\n"
-- …the value openings, which offer no key at all…
#guard closeMatchesOpen "[1]\n" && closeMatchesOpen "{a: b}\n"
#guard closeMatchesOpen "- [1]\n" && closeMatchesOpen "k: {a: b}\n"
#guard closeMatchesOpen "&a [1]\n"
-- …the indented and doubly-compact openers, where the column is not 0…
#guard closeMatchesOpen "  [1]: b\n" && closeSeen "  [1]: b\n"
#guard closeMatchesOpen "- - [1]: b\n" && closeSeen "- - [1]: b\n"
-- …and the NESTED interiors, which is where the mask's push/pop carries the
-- base slot past levels that stack and restore keys of their own.
#guard closeMatchesOpen "[[1], 2]: b\n" && closeSeen "[[1], 2]: b\n"
#guard closeMatchesOpen "[{a: b}]: b\n" && closeSeen "[{a: b}]: b\n"
#guard closeMatchesOpen "[1, [2, [3]]]: b\n" && closeSeen "[1, [2, [3]]]: b\n"
#guard closeMatchesOpen "[]: b\n" && closeMatchesOpen "{}: b\n"

/-! ## §5  The readings the column is FOR, held fixed -/

private def bothEvents (input : String) : Option String × Option String :=
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  bothEvents input == (e, e)

#guard emits "[[1], 2]: b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :2", "-SEQ",
   "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "  [1]: b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "- - [1]: b\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b",
   "-MAP", "-SEQ", "-SEQ", "-DOC", "-STR"]

end Tests.Guards.MaskBaseColumn

end Blanket
