module

public import L4YAML.Proofs.Production.StreamAccum

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # `pendingMapValue`'s floor is unconditional (DOCS item 82)

Reflection 653 §3 priced the field optional because the implicit `:` pushes at
the RESOLVED key's column, which the producer could not measure.  Items 79–81
made it measurable — the pack's column is an equation, the inherit is the
consumer's derivation, and `[197]`'s clear dies on `KeysBehindCursor` — so the
field is `IndentFloor sc n` outright: all six producers pay it, and the flow
OPEN's under-run arms refute from it directly, DELETING the two drop rides
`pendingMapValue` still carried there (`k:⏎  b:⏎[1]`'s run-end half and its
tab half).  What still rides at the open is `pendingFlow`'s opaque resume (R3)
and the props park's two arms (the next item's).

§1 pins the types; §2 measures the floor's inequality at every implicit `:`.
-/

namespace Tests.Guards.MapValueFloorUnconditional

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.PreprocessIndentStable L4YAML.Proofs.FlowAdjacency

/-! ## §1  The field and its feeder are unconditional -/

/-- Building the pending demands a REAL floor — no `Or.inl` in sight.
    Item 179: the awaited node and the floor both read at the SHIFTED index
    `n + 1`, `n` staying the entry column. -/
example {sc : ScannerState} {sp_start sp_block sp_scan : SurfPos} {n : Nat}
    -- 2026-10-29 (item 388): the park's value route is typed `.blockOut` (the grammar's `[187]` context).
    (h_close : ∀ sp_mid, SBlockNode (n + 1) .blockOut sp_scan sp_mid →
      SLYamlStream sp_start sp_mid)
    (h_floor : IndentFloor sc (n + 1))
    -- Item 402: the park's top at or left of its level (`h_top`), beside the floor.
    (h_top : sc.currentIndent ≤ (n : Int))
    (h_nic : sc.needIndentCheck = false)
    (h_real : LastTokenReal sc.tokens)
    (h_sk : sc.simpleKeyAllowed = true)
    (h_col0 : 0 < sp_scan.col)
    -- Item 125: `h_ivl` is stamp-or-FACE now, so this pin carries a stamp;
    -- the floor it is about is still the unconditional field beside it.
    (h_ivl : sc.implicitValueLine = some sc.line)
    -- Item 138: and the park's directive face, which every park past the
    -- structural dispatch carries.
    (h_nodir : sc.allowDirectives = false)
    -- Item 284: and the offer the indicator it stands on records.
    (h_offer : OfferPred sc.tokens) 
    -- Item 350: the two `?`-entry faces take the "not a `?` park" fact instead.
    (h_nq : NotQuestionPark sc)
    (h_alt : PackAlt sc)
    (h_next : sc.inFlow = false → NextIsSep sc) :
    PendingNode sc false sp_start sp_block sp_scan :=
  PendingNode.pendingMapValue (h_next := h_next) (h_offer := h_offer) sp_start sp_block sp_scan n h_close h_floor h_top
    -- Item 288: the slot's decline names the stamp this pin carries.
    h_nic h_real (Or.inl h_ivl) (Or.inr h_nq) (Or.inr h_ivl)
    h_sk h_col0 (Or.inr trivial) (Or.inr h_alt)
    (Or.inr trivial) (Or.inr trivial)
    (Or.inr h_alt) (Or.inr h_alt) h_nodir
    -- Item 168: this guard is about the FLOOR; the sequence face punts.
    (Or.inr trivial)
    -- Item 190: and so does the entry route's up-frame twin.
    (Or.inr h_nq)

/-- ...and `colon_open_map_implicit`'s slot asks for exactly that. -/
example {s' : ScannerState} {k : Nat} (h : IndentFloor s' k) :
    IndentFloor s' k := h

/-! ## §2  The measurement: the push lands at or above the resolved key

At every block-context `:` that resolves a live same-line key at column `k`,
the state after the scan has `k ≤ currentIndent` — `scanValue_key_col_le`'s
inequality, read off the running scanner.  `floorSeen` counts the states
where the premise fires, so the check is measured, not vacuous. -/

private def floorAtKeyLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    let stepOk :=
      match scanNextToken_preprocess s with
      | .error _ => true
      | .ok none => true
      | .ok (some (s_prep, c)) =>
        !(c == ':' && !s_prep.inFlow && s_prep.simpleKey.possible &&
            s_prep.simpleKey.pos.line == s_prep.line) ||
          (match scanNextToken s with
           | .ok (some s') => (s_prep.simpleKey.pos.col : Int) ≤ s'.currentIndent
           | _ => true)
    stepOk &&
      match scanNextToken s with
      | .error _ => true
      | .ok none => true
      | .ok (some s') => floorAtKeyLoop s' fuel'

private def floorAtKey (input : String) : Bool :=
  floorAtKeyLoop (ScannerState.mk' input) 128

private def floorSeenLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    let fires :=
      match scanNextToken_preprocess s with
      | .error _ => false
      | .ok none => false
      | .ok (some (s_prep, c)) =>
        c == ':' && !s_prep.inFlow && s_prep.simpleKey.possible &&
          s_prep.simpleKey.pos.line == s_prep.line
    fires ||
      match scanNextToken s with
      | .error _ => false
      | .ok none => false
      | .ok (some s') => floorSeenLoop s' fuel'

private def floorSeen (input : String) : Bool :=
  floorSeenLoop (ScannerState.mk' input) 128

#guard floorSeen "a: 1\n"
#guard floorSeen "k:\n  a: 1\n"
#guard floorSeen "[1]: b\n"
#guard floorAtKey "a: 1\nb: 2\n"
#guard floorAtKey "k:\n  a: 1\n  b: 2\n"
#guard floorAtKey "- a: 1\n- b: 2\n"
#guard floorAtKey "&x a: 1\n"
#guard floorAtKey "k:\n  a: |\n   x\n"
#guard floorAtKey "[1]: b\n"
#guard floorAtKey "{a: b}: c\n"
#guard floorAtKey "? a : b\n: v\n"
#guard floorAtKey "k: |\n a\n: v\n"
#guard floorAtKey "k:\n  a: \"p\n    q\"\n"

end Tests.Guards.MapValueFloorUnconditional

end Blanket
