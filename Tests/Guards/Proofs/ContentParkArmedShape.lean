module

public import L4YAML.Proofs.Production.StreamAccum

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The content park's armed shape (DOCS item 80)

Item 77 said every content scan parks ARMED or off a line start; what it did
not say is what an armed park has in hand.  The one armed content scan is the
block scalar, and §8.1 clears the saved key on its way out
(`scanBlockScalar_simpleKey_false`) — so an armed content park and a LIVE
implicit-key pack cannot coexist, and the same-line `:` at a content park can
answer the RE-SAVE question instead of punting on it:

* ARMED refutes the pack's own guard (`simpleKey.possible = true` is false);
* MID-LINE makes the `:` the park's inline residue, whose stale tail carries
  the flag DOWN — and a down flag across no break INHERITS
  (`preprocess_some_ssl_comments_anyCol`'s stale conjunct), so the key the `:`
  resolves IS the pack's.

With the question answered at the consumers (`colon_fires_implicit_key` spends
the park's `h_stale`/`h_arm`, `colon_fires_props_key` the props park's
`h_nic`/`h_ska`), `implicit_key_floor` takes the inherit as a PREMISE
(`h_inh`) instead of casing `preprocess_some_savedKey_shape` and punting on
its fresh arm.  (Item 81 then closed the one remaining punt — the explicit-key
clear — so the lemma is TOTAL now; §2 of `KeysBehindCursorFloor` pins that.)

§1 pins the strengthened types; §2 pins the consumer's two moves; §3 pins the
runtime invariant the armed shape states; §4 pins the inherit the consumers
now derive.
-/

namespace Tests.Guards.ContentParkArmedShape

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.LineOpenGuard L4YAML.Proofs.PreprocessIndentStable

/-! ## §1  The armed park's key is down — as a type

The scan-level funder, and the floor's new premise.  Neither statement has an
`∨ True` where the re-save used to punt. -/

/-- The block scalar ends armed AND cleared — the pair item 80 records. -/
example {s s' : ScannerState} (hok : scanBlockScalar s = .ok s') :
    s'.simpleKeyAllowed = true ∧ s'.simpleKey.possible = false :=
  ⟨scanBlockScalar_simpleKeyAllowed hok, scanBlockScalar_simpleKey_false hok⟩

/-- `implicit_key_floor` takes the inherit as a premise (`h_inh`) — the
    re-save case is the caller's to refute, not this lemma's to punt on.
    (Stated here as the item-80 shape; item 81 made the conclusion total, and
    the weaker disjunction below is the projection every optional field still
    accepts.) -/
example {sc s_prep s' : ScannerState} {k : Nat}
    (h_poss : sc.simpleKey.possible = true)
    (h_kcol : sc.simpleKey.pos.col = k)
    (h_inh : s_prep.simpleKey = sc.simpleKey)
    (h_kline : s_prep.simpleKey.pos.line = s_prep.line)
    (h_behind : s_prep.simpleKey.pos.offset ≠ s_prep.offset)
    (h_noflow : s_prep.inFlow = false)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, ':')))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) ':' = .ok (some s')) :
    -- Item 179: at the SHIFTED index — the push is at the key's column.
    IndentFloor s' (k + 1) ∨ True :=
  Or.inl (implicit_key_floor h_poss h_kcol h_inh h_kline h_behind h_noflow
    h_preprocess h_dispatch)

/-! ## §2  The consumer's two moves

A live pack FORCES the mid-line reading — that is the whole of what the
strengthened field buys, stated as the one-step derivation
`colon_fires_implicit_key` performs. -/

example {sc : ScannerState} {sp_scan : SurfPos}
    (h_arm : (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨
      0 < sp_scan.col)
    (h_poss : sc.simpleKey.possible = true) :
    0 < sp_scan.col := by
  rcases h_arm with ⟨_, h_poss_f⟩ | h_colpos
  · exact absurd h_poss (by rw [h_poss_f]; exact Bool.false_ne_true)
  · exact h_colpos

/-- ...and off the mid-line reading, the stale tail's flag half is what the
    no-break transport asks for: the two premises compose. -/
example {sc : ScannerState} {sp_scan : SurfPos}
    (h_stale : InlineResidue sp_scan ':' → StaleNodeTail sc)
    (h_res : InlineResidue sp_scan ':')
    (h_transport : sc.needIndentCheck = false → sc.simpleKeyAllowed = false →
      True) : True :=
  h_transport (h_stale h_res).1 (h_stale h_res).2.1

/-! ## §3  The measurement: an armed line-start state has no live key

Step the scanner over whole inputs and check every reachable post-token state:
`simpleKeyAllowed = true` at column 0 implies `simpleKey.possible = false`.
The block scalar is the one content scan that parks there armed, and §8.1's
clear is what the invariant observes.  `armedSeen` is the non-vacuity witness:
the armed line-start state is REACHED on the block-scalar inputs, so the
invariant is measured, not merely never applicable. -/

private def armedClearLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    match scanNextToken s with
    | .error _ => true
    | .ok none => true
    | .ok (some s') =>
      (!(s'.simpleKeyAllowed && s'.col == 0) || !s'.simpleKey.possible) &&
        armedClearLoop s' fuel'

private def armedClear (input : String) : Bool :=
  armedClearLoop (ScannerState.mk' input) 64

private def armedSeenLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match scanNextToken s with
    | .error _ => false
    | .ok none => false
    | .ok (some s') =>
      (s'.simpleKeyAllowed && s'.col == 0) || armedSeenLoop s' fuel'

private def armedSeen (input : String) : Bool :=
  armedSeenLoop (ScannerState.mk' input) 64

-- The armed line-start park is reached (block scalars), and the key is down
-- there every time.
#guard armedSeen "k: |\n a\n"
#guard armedSeen "- |\n a\nb: 1\n"
#guard armedClear "k: |\n a\n"
#guard armedClear "k: |\n a\n: b\n"
#guard armedClear "- |\n a\nb: 1\n"
#guard armedClear "k: >\n a\n b\nc: 2\n"
#guard armedClear "a: 1\nb: 2\n"
#guard armedClear "&x a: 1\n"
#guard armedClear "*x : 1\n"
#guard armedClear "\"q\": 1\n"
#guard armedClear "- a: 1\n- b: 2\n"
#guard armedClear "? k\n: v\n"
#guard armedClear "---\nk: v\n...\n"

/-! ## §4  The measurement: a down flag across no break inherits

At every state about to dispatch a `:` — `scanNextToken_preprocess` lands on
`':'` with no break crossed — where the park's shape holds (key live on the
current line, flag down, indent check clear), the preprocessed state carries
the SAME saved key: preprocessing re-saved nothing.  This is `h_inh`, measured.
`inheritSeen` counts the states where the premise actually fires. -/

private def inheritLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    let stepOk :=
      match scanNextToken_preprocess s with
      | .error _ => true
      | .ok none => true
      | .ok (some (s_prep, c)) =>
        !(c == ':' && s.simpleKey.possible && s.simpleKey.pos.line == s.line &&
          !s.simpleKeyAllowed && s.needIndentCheck == false &&
          s_prep.line == s.line) ||
          (s_prep.simpleKey == s.simpleKey)
    stepOk &&
      match scanNextToken s with
      | .error _ => true
      | .ok none => true
      | .ok (some s') => inheritLoop s' fuel'

private def inherits (input : String) : Bool :=
  inheritLoop (ScannerState.mk' input) 64

private def inheritSeenLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    let fires :=
      match scanNextToken_preprocess s with
      | .error _ => false
      | .ok none => false
      | .ok (some (_, c)) =>
        c == ':' && s.simpleKey.possible && s.simpleKey.pos.line == s.line &&
          !s.simpleKeyAllowed && s.needIndentCheck == false
    fires ||
      match scanNextToken s with
      | .error _ => false
      | .ok none => false
      | .ok (some s') => inheritSeenLoop s' fuel'

private def inheritSeen (input : String) : Bool :=
  inheritSeenLoop (ScannerState.mk' input) 64

-- The premise fires on every implicit-key shape below, and the key inherits
-- at each firing.
#guard inheritSeen "a: 1\n"
#guard inheritSeen "- a: 1\n"
#guard inheritSeen "&x a: 1\n"
#guard inherits "a: 1\nb: 2\n"
#guard inherits "- a: 1\n- b: 2\n"
#guard inherits "&x a: 1\n"
#guard inherits "*x : 1\n"
#guard inherits "\"q\": 1\n"
#guard inherits "k:\n  a: 1\n  b: 2\n"
#guard inherits "? k\n: v\nother: 1\n"
#guard inherits "k: |\n a\nnext: 1\n"

end Tests.Guards.ContentParkArmedShape

end Blanket
