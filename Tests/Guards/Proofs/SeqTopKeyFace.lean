module

public import L4YAML.Scanner.Scanner
public meta import L4YAML.Scanner.Scanner
public import L4YAML.Proofs.Production.StreamAccum
public meta import L4YAML.Proofs.Production.StreamAccum

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # `SeqTopKey` instantiated (DOCS item 372, Rule 2)

Item 372 put `SeqTopKey sc` — the saved key sits at the column of the scanner's
top level and that level is a sequence — on `ImplicitKeyPack`'s route conjunct,
transported it with `SeqTopKey.of_eq` and refuted it at the `:` with
`seqTopKey_refuted_at_colon`.  Priority 40 reads the parser's verdicts; this
file instantiates the two lemmas themselves on concrete scanner states:

* §1 the face on literal states: a sequence top at the key's column holds it, a
  mapping top, a sequence at another column, an empty stack and a key at a
  different column do not;
* §2 `SeqTopKey.of_eq`: the face rides a step that moves the cursor, the line,
  the tokens and the key's offset but keeps `indents` and the key's column; each
  of its two premises is load-bearing (a changed key column or a changed stack
  loses the face);
* §3 `seqTopKey_refuted_at_colon` on REAL states: the scanner paused at the `:`
  of `a: 1`, `k:⏎  a: 1`, `- a: 1` and `k:⏎  - a⏎b: 1` satisfies the four
  side premises and dispatches, so the lemma yields `¬ SeqTopKey`, and the
  face is read false on the same state;
* §4 the inapplicable samples, classified by WHICH premise fails: the explicit
  `:` of `? a⏎: b` (a fresh key saved AT the `:`: `h_behind`), the flow `:` of
  `{a: b}` (`inFlow`), and
  the item's own input `- a⏎b: 1`, where the face HOLDS and the dispatch is
  refused — the lemma's `h_dispatch` is exactly the premise that fails.
-/

namespace L4YAML.Tests.Guards.SeqTopKeyFace

open L4YAML L4YAML.Scanner L4YAML.Proofs.StreamAccum

/-- The states at which the scanner's preprocessing hands a `:` to the block dispatcher
    while scanning `input`, in scan order, after the directive reset the `:` producers
    dispatch over — the lemma's `s`.  (A pause is read off `scanNextToken_preprocess`,
    not off the raw cursor: the explicit `:` of `? a⏎: b` sits behind a line break.) -/
private def colonPauses (input : String) (fuel : Nat := 64) : Array ScannerState := Id.run do
  let mut s := ScannerState.mk' input
  let mut acc : Array ScannerState := #[]
  for _ in [:fuel] do
    match scanNextToken_preprocess s with
    | .ok (some (sp, c)) =>
      if c == ':' then
        acc := acc.push (if sp.allowDirectives then
          { sp with allowDirectives := false, documentEverStarted := true } else sp)
    | _ => break
    match scanNextToken s with
    | .ok (some s') => s := s'
    | _ => break
  return acc

/-- The `i`-th pause; every use below is guarded by a pause-count pin, so a missing
    pause is a build failure, not a silent fallback to the initial state. -/
private def pauseAt (input : String) (i : Nat) : ScannerState :=
  ((colonPauses input)[i]?).getD (ScannerState.mk' input)

#guard (colonPauses "a: 1").size == 1
#guard (colonPauses "k:\n  a: 1").size == 2
#guard (colonPauses "- a: 1").size == 1
#guard (colonPauses "k:\n  - a\nb: 1").size == 2
#guard (colonPauses "- a\nb: 1").size == 1
#guard (colonPauses "-\nb: 1").size == 1
#guard (colonPauses "? a\n: b").size == 1
#guard (colonPauses "{a: b}").size == 1

private def seqTop (col : Int) : IndentEntry := { column := col, isSequence := true }
private def mapTop (col : Int) : IndentEntry := { column := col, isSequence := false }

/-- A key saved at `(offset, line, col)`. -/
private def keyAt (offset line col : Nat) : SimpleKeyState :=
  { possible := true, pos := { offset := offset, line := line, col := col } }

/-- `- a⏎b: 1` with the cursor on `b`: the root sequence is the top, the key at
    its column. -/
private def sFace : ScannerState :=
  { ScannerState.mk' "- a\nb: 1" with
    offset := 4
    line := 1
    col := 0
    indents := #[mapTop (-1), seqTop 0]
    simpleKey := keyAt 4 1 0 }

private def isOkSome : Except ScanError (Option ScannerState) → Bool
  | .ok (some _) => true
  | _ => false

/-! ## §1 The face on literal states -/

example : SeqTopKey sFace := by unfold SeqTopKey; decide
-- A mapping top at the key's column is not the face (`k:⏎  a: 1`'s shape).
example : ¬ SeqTopKey { sFace with indents := #[mapTop (-1), mapTop 0] } := by
  unfold SeqTopKey; decide
-- A sequence top at ANOTHER column is not the face (`- - a⏎  b: 1`'s `b` is at
-- the inner sequence's column 2, the outer at 0 is beneath it).
example : ¬ SeqTopKey { sFace with indents := #[mapTop (-1), seqTop 0, seqTop 2] } := by
  unfold SeqTopKey; decide
example : SeqTopKey { sFace with
    indents := #[mapTop (-1), seqTop 0, seqTop 2]
    simpleKey := keyAt 8 1 2 } := by
  unfold SeqTopKey; decide
-- The sentinel alone: no sequence anywhere.
example : ¬ SeqTopKey { sFace with indents := #[mapTop (-1)] } := by unfold SeqTopKey; decide
-- The empty stack: `back?` is `none`.
example : ¬ SeqTopKey { sFace with indents := #[] } := by unfold SeqTopKey; decide
-- The key one column in (`- a⏎  b: 1` before the fold): not the face.
example : ¬ SeqTopKey { sFace with simpleKey := keyAt 6 1 2 } := by unfold SeqTopKey; decide
-- `possible` is not read: the face is about the saved position, the consumers
-- supply `possible = true` separately.
example : SeqTopKey { sFace with simpleKey := { keyAt 4 1 0 with possible := false } } := by
  unfold SeqTopKey; decide

/-! ## §2 `SeqTopKey.of_eq` -/

/-- The content dispatch the producer transports across: cursor, line, tokens
    and the key's OFFSET move, `indents` and the key's column stay. -/
private def sMoved : ScannerState :=
  { sFace with
    offset := 9
    line := 2
    col := 3
    simpleKey := keyAt 7 2 0
    tokens := #[]
    simpleKeyAllowed := false }

example : SeqTopKey sMoved := SeqTopKey.of_eq (s := sFace) rfl rfl (by unfold SeqTopKey; decide)
-- Both premises are load-bearing: the same step with the key column moved, or
-- with the sequence level popped, has no face to transport.
example : ¬ SeqTopKey { sMoved with simpleKey := keyAt 7 2 1 } := by unfold SeqTopKey; decide
example : ¬ SeqTopKey { sMoved with indents := #[mapTop (-1)] } := by unfold SeqTopKey; decide
-- Transport is symmetric in the two fields: a state agreeing on them with a
-- NON-face state has no face either.
example (h : ¬ SeqTopKey { sFace with indents := #[mapTop (-1), mapTop 0] }) :
    ¬ SeqTopKey { sMoved with indents := #[mapTop (-1), mapTop 0] } :=
  fun hf => h (SeqTopKey.of_eq rfl rfl hf)

/-! ## §3 `seqTopKey_refuted_at_colon` on the scanner's own states -/

/-- The lemma applied at a real pause: its four side premises are read off the
    state by `decide`, `h_dispatch` by evaluating the dispatcher. -/
private lemma refutedAt (s : ScannerState)
    (hok : isOkSome (scanNextToken_dispatchBlockIndicators s ':') = true)
    (h_noflow : s.inFlow = false) (h_poss : s.simpleKey.possible = true)
    (h_behind : s.simpleKey.pos.offset ≠ s.offset)
    (h_kline : s.simpleKey.pos.line = s.line) : ¬ SeqTopKey s := by
  cases h : scanNextToken_dispatchBlockIndicators s ':' with
  | ok o =>
    cases o with
    | none => rw [h] at hok; simp [isOkSome] at hok
    | some s' => exact seqTopKey_refuted_at_colon h h_noflow h_poss h_behind h_kline
  | error e => rw [h] at hok; simp [isOkSome] at hok

-- `a: 1`: the root key, the stack is the sentinel.
example : ¬ SeqTopKey (pauseAt "a: 1" 0) :=
  refutedAt _ (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
example : ¬ SeqTopKey (pauseAt "a: 1" 0) := by unfold SeqTopKey; native_decide
-- `k:⏎  a: 1`: the second `:`, a mapping top at the key's column.
example : ¬ SeqTopKey (pauseAt "k:\n  a: 1" 1) :=
  refutedAt _ (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
example : ¬ SeqTopKey (pauseAt "k:\n  a: 1" 1) := by unfold SeqTopKey; native_decide
-- `- a: 1`: the key INSIDE the entry — the sequence is beneath the mapping top.
example : ¬ SeqTopKey (pauseAt "- a: 1" 0) :=
  refutedAt _ (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
example : ¬ SeqTopKey (pauseAt "- a: 1" 0) := by unfold SeqTopKey; native_decide
-- `k:⏎  - a⏎b: 1`: Priority 40's accepted neighbour — the dedent popped the
-- sequence, `b` resumes the root mapping's level.
example : ¬ SeqTopKey (pauseAt "k:\n  - a\nb: 1" 1) :=
  refutedAt _ (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
example : ¬ SeqTopKey (pauseAt "k:\n  - a\nb: 1" 1) := by unfold SeqTopKey; native_decide

/-! ## §4 The inapplicable samples, by failing premise -/

-- `- a⏎b: 1`: the item's input.  The face HOLDS at the `:` and the dispatcher
-- refuses — `h_dispatch` is the premise that fails, as the lemma says it must.
example : SeqTopKey (pauseAt "- a\nb: 1" 0) := by unfold SeqTopKey; native_decide
example : isOkSome (scanNextToken_dispatchBlockIndicators (pauseAt "- a\nb: 1" 0) ':') = false := by
  native_decide
-- …and the other three side premises hold there, so no other premise explains the refusal.
example : (pauseAt "- a\nb: 1" 0).inFlow = false := by native_decide
example : (pauseAt "- a\nb: 1" 0).simpleKey.possible = true := by native_decide
example : (pauseAt "- a\nb: 1" 0).simpleKey.pos.line = (pauseAt "- a\nb: 1" 0).line := by native_decide
-- `-⏎b: 1`: the empty entry, same classification.
example : SeqTopKey (pauseAt "-\nb: 1" 0) := by unfold SeqTopKey; native_decide
example : isOkSome (scanNextToken_dispatchBlockIndicators (pauseAt "-\nb: 1" 0) ':') = false := by
  native_decide
-- `? a⏎: b`: the explicit `:`.  REFUTED expectation, kept: I predicted "no simple
-- key" (`h_poss` fails); the scanner saves a fresh simple key AT the `:` (the
-- `:` could start a key), so `possible` holds and it is `h_behind` (the key is
-- not strictly behind the cursor) that fails.  The `?` register is live; the
-- face is not asserted.
example : (pauseAt "? a\n: b" 0).simpleKey.possible = true := by native_decide
example : (pauseAt "? a\n: b" 0).simpleKey.pos.offset = (pauseAt "? a\n: b" 0).offset := by
  native_decide
example : (pauseAt "? a\n: b" 0).simpleKey.pos.line = (pauseAt "? a\n: b" 0).line := by
  native_decide
example : (pauseAt "? a\n: b" 0).explicitKeyLine = some 0 := by native_decide
example : ¬ SeqTopKey (pauseAt "? a\n: b" 0) := by unfold SeqTopKey; native_decide
-- `{a: b}`: the flow `:` — `h_noflow` fails; the block dispatcher is never
-- consulted there, and the stack is the sentinel.
example : (pauseAt "{a: b}" 0).inFlow = true := by native_decide
example : ¬ SeqTopKey (pauseAt "{a: b}" 0) := by unfold SeqTopKey; native_decide

end L4YAML.Tests.Guards.SeqTopKeyFace
