module

public import L4YAML.Proofs.Production.StreamAccum

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # `pendingProps`' floor is unconditional (DOCS item 83)

The `[96]` run's park inherits the ENTRY's floor — a props scan writes tokens,
not indents — and every opener measures now: the root parks at 0
(`IndentFloor.zero`), the indented openers inherit through
`indentedValue_reads_at_any_indent`'s props arm (the INLINE step off the
stability, the LANDED step off the landing's own `s-indent(n)` via
`preprocess_some_floor_at_landing` — the derivation that lemma already
performed and then threw away), and the run extension transports its own.
The degenerate landing that blocked totality demands a column-0 park, which
no caller's park is (`h_col0`).

With the field real, the flow OPEN's props arms refute both halves of the
under-run outright — the LAST two floor-gated drop rides are DELETED, and
what rides the open now is `pendingFlow`'s opaque resume alone (R3's own
`drop_ride`, one textual use).

§1 pins the field; §2 measures the floor's two transport premises on the
running scanner.
-/

namespace Tests.Guards.PropsFloorUnconditional

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.PreprocessIndentStable L4YAML.Proofs.FlowAdjacency

/-! ## §1  The field is real -/

/-- Building the props pending demands a REAL floor. -/
example {sc : ScannerState} {sp_start sp_block sp_scan sp_node sp_p : SurfPos}
    {n : Nat}
    (h_sep : SSeparateLines n sp_node sp_p)
    (h_run : PropsRun n .flowOut true false sp_p sp_scan)
    (h_nic : sc.needIndentCheck = false)
    (h_real : LastTokenReal sc.tokens)
    (h_anchor : (trailingPropertyRunOnLine sc.tokens sc.line).any
      YamlToken.isAnchorProperty = true)
    -- Item 165: the run's route takes §9.2's verdict now.
    (h_route : danglingNodePos? sc = none →
      ∀ sp_m, SBlockNode n .blockIn sp_node sp_m → SLYamlStream sp_start sp_m)
    (h_floor : IndentFloor sc n)
    (h_col0 : 0 < sp_scan.col)
    (h_ska : sc.simpleKeyAllowed = false)
    -- Item 138: and the park's directive face.  (~~Item 170: and the crossed
    -- tail window's UNGATED route~~ — RETIRED at item 181, with the window.)
    (h_nodir : sc.allowDirectives = false)
    -- Item 284: and the run's slot face, gated as `h_route` is.
    (h_slot : danglingNodePos? sc = none → sc.indents.size ≤ 1 ∨ SlotFace sc.tokens)
    -- Item 293: and the run's saved key, live.
    (h_poss : sc.simpleKey.possible = true) 
    (h_alt : PackAlt sc)
    (h_next : sc.inFlow = false → NextIsSep sc) :
    PendingNode sc false sp_start sp_block sp_scan :=
  PendingNode.pendingProps (h_next := h_next) (h_poss := h_poss) (h_slot := h_slot) sp_start sp_block sp_scan true false sp_node sp_p n
    h_sep h_run h_nic h_real (fun _ => h_anchor) (fun h => nomatch h) h_route
    -- Item 102: the key field's `True` became `KeyPackPunt`, so a pin that
    -- offers no pack has to NAME why — here, a caller with no key context.
    (Or.inr KeyPackPunt.noKeyContext) h_floor h_col0 (Or.inr trivial) h_ska
    (Or.inr h_alt)
    -- Item 114: the five resume faces are optional too — a pin with no
    -- enclosing holdings punts them all.  Item 199: SIX, since the entry face
    -- got its value-line twin and the census closed.
    (Or.inr h_alt) (Or.inr h_alt) (Or.inr trivial) (Or.inr trivial)
    (Or.inr h_alt) h_nodir (Or.inr h_alt)

/-! ## §2  The measurement: the floor's transport premises

A `[96]` scan writes tokens, not indents — `s'.indents = s_prep.indents` at
every `&`/`!` step — and leaves the indent-check flag DOWN, which are the two
halves the park's `IndentFloor` rides on.  Measured over inline runs, landed
runs (`k:⏎  &a x: 1` — the arm whose floor came from the landing), and nested
landed runs.  `propsSeen` witnesses the steps fire. -/

private def propsStepLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    let stepOk :=
      match scanNextToken_preprocess s with
      | .error _ => true
      | .ok none => true
      | .ok (some (s_prep, c)) =>
        !((c == '&' || c == '!') && !s_prep.inFlow) ||
          (match scanNextToken s with
           | .ok (some s') =>
             s'.indents == s_prep.indents && s'.needIndentCheck == false
           | _ => true)
    stepOk &&
      match scanNextToken s with
      | .error _ => true
      | .ok none => true
      | .ok (some s') => propsStepLoop s' fuel'

private def propsStep (input : String) : Bool :=
  propsStepLoop (ScannerState.mk' input) 128

private def propsSeenLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    let fires :=
      match scanNextToken_preprocess s with
      | .error _ => false
      | .ok none => false
      | .ok (some (s_prep, c)) => (c == '&' || c == '!') && !s_prep.inFlow
    fires ||
      match scanNextToken s with
      | .error _ => false
      | .ok none => false
      | .ok (some s') => propsSeenLoop s' fuel'

private def propsSeen (input : String) : Bool :=
  propsSeenLoop (ScannerState.mk' input) 128

#guard propsSeen "&a x: 1\n"
#guard propsSeen "k:\n  &a x: 1\n"
#guard propsSeen "k:\n  - \n    &a x: 1\n"
#guard propsStep "&a x: 1\n"
#guard propsStep "!!str x: 1\n"
#guard propsStep "&a !t x: 1\n"
#guard propsStep "k:\n  &a x: 1\n"
#guard propsStep "k:\n  - \n    &a x: 1\n"
#guard propsStep "- &a x\n- *a\n"
#guard propsStep "k:\n  &a |\n   text\n"

end Tests.Guards.PropsFloorUnconditional

end Blanket
