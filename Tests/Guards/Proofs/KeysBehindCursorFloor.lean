module

public import L4YAML.Proofs.Production.StreamAccum

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The saved keys sit strictly behind the cursor (DOCS item 81)

`scanValueClearKey` — `[197]`'s explicit-key arm — was the implicit-key
floor's last punt.  Its two branches both demand coordinates a live same-line
key cannot supply: branch (2) a key from the `?`'s own EARLIER line (refuted
by the pack's `pos.line = line`), branch (1) a key saved AT the `:` itself.
The second refutation is `KeysBehindCursor` (`ScannerCorrectness`): every
reachable saved key — the current one AND every stacked one, because a flow
close restores from the stack — sits strictly behind the cursor.  Vacuous at
`mk'`; preprocessing weakens it to `≤` (a fresh save is AT the cursor) and the
dispatch's own strict advance restores `<`
(`scanNextToken_preserves_KeysBehindCursor`, on `scanNextToken_progress`'s
skeleton).

The invariant rides `scanLoop_grammar_prod` as one threaded conjunct — no
constructor gained a field — and the floor chain is TOTAL:
`scanValue_key_col_le` → `value_key_floor` → `implicit_key_floor`, whose
`∨ True` is gone.  Both `colon_open_map_implicit` and `colon_open_map_props`
now hand `pendingMapValue` a REAL floor (`Or.inl`).

§1 pins the invariant and its preservation; §2 pins the total floor chain;
§3 measures the invariant over stepped runs; §4 measures that the clear is a
no-op at every live same-line `:`.
-/

namespace Tests.Guards.KeysBehindCursorFloor

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.ScannerCorrectness

/-! ## §1  The invariant, established and preserved -/

example (input : String) : KeysBehindCursor (ScannerState.mk' input) :=
  KeysBehindCursor.initial input

example {s s' : ScannerState} (h : scanNextToken s = .ok (some s'))
    (h_kbc : KeysBehindCursor s) : KeysBehindCursor s' :=
  scanNextToken_preserves_KeysBehindCursor s s' h h_kbc

/-- The current-key half is exactly what refutes the phantom clear. -/
example {s : ScannerState} (h_kbc : KeysBehindCursor s)
    (h_poss : s.simpleKey.possible = true) :
    s.simpleKey.pos.offset ≠ s.offset :=
  fun h_eq => absurd (h_eq ▸ h_kbc.1 h_poss) (Nat.lt_irrefl _)

/-! ## §2  The floor chain is total — no `∨ True` anywhere in it -/

example {s s' : ScannerState} {k : Nat}
    (h_noflow : s.inFlow = false)
    (h_poss : s.simpleKey.possible = true)
    (h_kline : s.simpleKey.pos.line = s.line)
    (h_behind : s.simpleKey.pos.offset ≠ s.offset)
    (h_key : (k : Int) ≤ (s.simpleKey.pos.col : Int))
    (hok : scanValue s = .ok s') :
    (k : Int) ≤ s'.currentIndent :=
  scanValue_key_col_le h_noflow h_poss h_kline h_behind h_key hok

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
    IndentFloor s' (k + 1) :=
  implicit_key_floor h_poss h_kcol h_inh h_kline h_behind h_noflow
    h_preprocess h_dispatch

/-! ## §3  The measurement: every reachable saved key is strictly behind

Step the scanner over whole inputs and check, at every post-token state, the
CURRENT key and every STACKED key against the cursor.  `liveSeen` witnesses
that live keys (and, on the flow shapes, restored ones) are reached. -/

private def stackBehind (s : ScannerState) : Bool :=
  s.simpleKeyStack.all (fun k => !k.possible || k.pos.offset < s.offset)

private def behindLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    match scanNextToken s with
    | .error _ => true
    | .ok none => true
    | .ok (some s') =>
      (!s'.simpleKey.possible || s'.simpleKey.pos.offset < s'.offset) &&
        stackBehind s' && behindLoop s' fuel'

private def behind (input : String) : Bool :=
  behindLoop (ScannerState.mk' input) 128

private def liveSeenLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match scanNextToken s with
    | .error _ => false
    | .ok none => false
    | .ok (some s') =>
      (s'.simpleKey.possible && s'.simpleKey.pos.line == s'.line) || liveSeenLoop s' fuel'

private def liveSeen (input : String) : Bool :=
  liveSeenLoop (ScannerState.mk' input) 128

#guard behind "a: 1\n"
#guard behind "- a: 1\n"
#guard behind "&x a: 1\n"
#guard behind "*x : 1\n"
#guard behind "\"q\": 1\n"
#guard behind "[1]: b\n"
#guard behind "{a: b}: c\n"
#guard behind "[[1], 2]: b\n"
#guard behind "[1, [2, [3]]]: b\n"
#guard behind "  [1]: b\n"
#guard behind "- - [1]: b\n"
#guard behind "? a\n: b\n"
#guard behind "? a : b\n: v\n"
#guard behind "? earth: blue\n: moon: white\n"
#guard behind "k: |\n a\nnext: 1\n"
#guard behind "a b\nc d\n"
#guard behind "? [a, b]\n: v\n"
#guard behind "{? a: b}: v\n"
#guard behind "[? a, b: c]\n"
#guard behind "---\nk: v\n...\n"
#guard behind "k: \"multi\n line\": w\n"
#guard behind "? a\n? b\n: v\n"
#guard behind "[a: b, c: d]: e\n"
#guard liveSeen "a: 1\n"
#guard liveSeen "[1]: b\n"
#guard liveSeen "{a: b}: c\n"
#guard liveSeen "&x a: 1\n"

/-! ## §4  The measurement: the clear is a no-op behind the cursor

At every state about to dispatch a `:` whose saved key is live on the current
line AND strictly behind the cursor, `scanValueClearKey` preserves the key —
both branches' conditions fail, which is what the total floor rides.  The
BEHIND premise is load-bearing and this file measured it so: a `:` at which
preprocessing just re-saved carries a key AT the cursor, and there the phantom
branch legitimately fires (`? a : b⏎: v`'s second `:`) — which is why the
floor's callers derive the INHERIT first (item 80) and only then read the
clear.  `clearArmSeen` witnesses the outer branch is EXERCISED: states with an
open explicit key (`explicitKeyLine` some) and a live behind same-line key are
reached (`? a : b`'s compact key). -/

private def clearNoopLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    let stepOk :=
      match scanNextToken_preprocess s with
      | .error _ => true
      | .ok none => true
      | .ok (some (s_prep, c)) =>
        !(c == ':' && s_prep.simpleKey.possible &&
            s_prep.simpleKey.pos.line == s_prep.line &&
            s_prep.simpleKey.pos.offset != s_prep.offset) ||
          ((scanValueClearKey s_prep).simpleKey == s_prep.simpleKey)
    stepOk &&
      match scanNextToken s with
      | .error _ => true
      | .ok none => true
      | .ok (some s') => clearNoopLoop s' fuel'

private def clearNoop (input : String) : Bool :=
  clearNoopLoop (ScannerState.mk' input) 128

private def clearArmSeenLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    let fires :=
      match scanNextToken_preprocess s with
      | .error _ => false
      | .ok none => false
      | .ok (some (s_prep, c)) =>
        c == ':' && s_prep.simpleKey.possible &&
          s_prep.simpleKey.pos.line == s_prep.line &&
          s_prep.simpleKey.pos.offset != s_prep.offset &&
          s_prep.explicitKeyLine.isSome
    fires ||
      match scanNextToken s with
      | .error _ => false
      | .ok none => false
      | .ok (some s') => clearArmSeenLoop s' fuel'

private def clearArmSeen (input : String) : Bool :=
  clearArmSeenLoop (ScannerState.mk' input) 128

#guard clearNoop "a: 1\nb: 2\n"
#guard clearNoop "- a: 1\n- b: 2\n"
#guard clearNoop "&x a: 1\n"
#guard clearNoop "[1]: b\n"
#guard clearNoop "{a: b}: c\n"
#guard clearNoop "? a : b\n: v\n"
#guard clearNoop "? earth: blue\n: moon: white\n"
#guard clearNoop "? k\n: v\nother: 1\n"
#guard clearNoop "k: |\n a\nnext: 1\n"
#guard clearArmSeen "? a : b\n"
#guard clearArmSeen "? earth: blue\n: moon: white\n"

end Tests.Guards.KeysBehindCursorFloor

end Blanket
