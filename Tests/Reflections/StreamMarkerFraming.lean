import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity

/-!
# Reflection 584 — BIRTH PROBE for Front B's span-locality producer, FIRST scanner step (§5.14)

Reflections 579–583 peeled every *emission-only* prerequisite off Front B's brick-3 producer. R583's
"Next step" named the first scanner sub-link as: each in-stream `(emit v).toList` segment "scans to the
standalone `scanFiltered (emit v)` token run". **Reflection 584 applies the inhabitation-debt discipline
([[ref-probe-deferred-universal-before-producing]]) to that target BEFORE producing against it — and an
`#eval` probe shows it is literally FALSE.**

The scanner opens every run with `.streamStart` and closes it with `.streamEnd` (`scanLoop`), and BOTH
pass the `.placeholder` filter, so a *standalone* `scanFiltered` is bracketed by stream markers a
*mid-stream* segment can never carry:

  `scanFiltered (emit a)` vals = `[.streamStart, .scalar "a" .., .streamEnd]`   (3 tokens, WITH markers)
  in-stream segment for that element = `[.scalar "a" ..]`                       (1 token, NO markers)

So the producer's true contract is "segment = the **marker-stripped core** of `scanFiltered (emit v)`",
not the whole token run. `ContentFidelity.lean` §5.14 lands that correction as the stream-marker framing
of any successful `scanFiltered`:

* `scanFiltered_first_is_streamStart` / `scanFiltered_last_is_streamEnd` — first/last filtered token is
  `.streamStart`/`.streamEnd` (lifted from `scan_first_is_streamStart` / `scan_last_is_streamEnd`
  through the `.placeholder` filter); and
* `scanFiltered_stream_framing` / `scanFiltered_vals_stream_framing` — the decomposition
  `ft.toList = t0 :: (core ++ [tlast])` (resp. its `.val`-map `.streamStart :: coreVals ++ [.streamEnd]`)
  exposing the marker-free `core`/`coreVals` the eventual segment-equality targets.

## Why this probe (inhabitation debt: probe the deferred target's TRUTH before producing)

The §5.14 lemmas are equations, so Lean verifies them — they carry no inhabitation debt of their own.
The debt is on the *deferred producer target* R583 stated, which a producer would have spent effort
proving had the probe not surfaced its falsity first:

1. **Probe-the-target ([[ref-probe-deferred-universal-before-producing]]).** `standalone_a_vals` /
   `standalone_seq_vals` `native_decide` the REAL standalone token-value runs and exhibit the stream
   markers; `core_a_eq_segment` / `core_seq_eq_segment` `native_decide` that the marker-stripped core
   (`drop 1 |>.dropLast` of the vals) is exactly the in-stream segment value run. Together they prove
   "segment = standalone" is false but "segment = core" holds — the producer's corrected contract.
2. **Non-vacuity (rule 2-flavoured).** The corrected framing lemma is APPLIED on real emission output
   (`framing_fires_on_emit_a` / `framing_fires_on_emit_seq` instantiate `scanFiltered_vals_stream_framing`
   at `emit a` / a real flow sequence, discharging the `2 ≤ ft.size` premise by `native_decide`), and the
   structural splitter fires on a concrete list — so the contract is genuinely consumable, not orphan
   scaffolding.

The `#print axioms` audits certify the four source lemmas + the splitter at `[propext, Classical.choice,
Quot.sound]` — sorry-free. `Classical.choice` enters via the core `Array`/`List`/`String` simp lemmas,
not from any `Except` monad reasoning — same lesson as §5.11–§5.13: `#print axioms` it, never assume.
-/

namespace StreamMarkerFraming

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures: plain scalars and a flow sequence (so `emit` is the bare double-quoted content). -/

def a : YamlValue := .scalar { content := "a", style := .plain }
def b : YamlValue := .scalar { content := "b", style := .plain }
def seqAB : YamlValue := .sequence .flow #[a, b] none none

/-! ## Rule 5 grounding + falsity surfacing: the standalone scan CARRIES stream markers the in-stream
    segment cannot, and the marker-stripped core IS the segment value run. -/

/-- Standalone `scanFiltered (emit a)` vals = `[streamStart, scalar "a", streamEnd]` — markers present. -/
theorem standalone_a_vals :
    ((scanFiltered (emit a)).toOption.map (fun ft => ft.toList.map (·.val)))
      = some [YamlToken.streamStart, YamlToken.scalar "a" .doubleQuoted, YamlToken.streamEnd] := by
  native_decide

/-- The marker-stripped core (`drop 1 |>.dropLast`) of those vals = the in-stream segment for `a`. -/
theorem core_a_eq_segment :
    ((((scanFiltered (emit a)).toOption.map (fun ft => ft.toList.map (·.val))).getD []).drop 1).dropLast
      = [YamlToken.scalar "a" .doubleQuoted] := by native_decide

/-- Standalone `scanFiltered (emit seqAB)` vals — the bracketed body, again bracketed by stream markers. -/
theorem standalone_seq_vals :
    ((scanFiltered (emit seqAB)).toOption.map (fun ft => ft.toList.map (·.val)))
      = some [YamlToken.streamStart, YamlToken.flowSequenceStart,
              YamlToken.scalar "a" .doubleQuoted, YamlToken.flowEntry,
              YamlToken.scalar "b" .doubleQuoted, YamlToken.flowSequenceEnd,
              YamlToken.streamEnd] := by native_decide

/-- The marker-stripped core of the sequence scan = its in-stream body token-value run. -/
theorem core_seq_eq_segment :
    ((((scanFiltered (emit seqAB)).toOption.map (fun ft => ft.toList.map (·.val))).getD []).drop 1).dropLast
      = [YamlToken.flowSequenceStart, YamlToken.scalar "a" .doubleQuoted, YamlToken.flowEntry,
         YamlToken.scalar "b" .doubleQuoted, YamlToken.flowSequenceEnd] := by native_decide

/-! ## Non-vacuity: the corrected value-framing lemma FIRES on real emission output (the `2 ≤ ft.size`
    premise discharged by `native_decide`), exposing the marker-free `coreVals` existentially. -/

theorem framing_fires_on_emit_a :
    ∃ coreVals, ((scanFiltered (emit a)).toOption.getD #[]).toList.map (·.val)
      = YamlToken.streamStart :: (coreVals ++ [YamlToken.streamEnd]) := by
  have hsz : 2 ≤ ((scanFiltered (emit a)).toOption.getD #[]).size := by native_decide
  rcases hh : scanFiltered (emit a) with err | ft
  · rw [hh] at hsz; simp [Except.toOption] at hsz
  · rw [hh] at hsz
    simp only [Except.toOption, Option.getD] at hsz ⊢
    exact scanFiltered_vals_stream_framing (emit a) ft hh hsz

theorem framing_fires_on_emit_seq :
    ∃ coreVals, ((scanFiltered (emit seqAB)).toOption.getD #[]).toList.map (·.val)
      = YamlToken.streamStart :: (coreVals ++ [YamlToken.streamEnd]) := by
  have hsz : 2 ≤ ((scanFiltered (emit seqAB)).toOption.getD #[]).size := by native_decide
  rcases hh : scanFiltered (emit seqAB) with err | ft
  · rw [hh] at hsz; simp [Except.toOption] at hsz
  · rw [hh] at hsz
    simp only [Except.toOption, Option.getD] at hsz ⊢
    exact scanFiltered_vals_stream_framing (emit seqAB) ft hh hsz

/-- The structural head/middle/last splitter fires on a concrete list (`[1,2,3] = 1 :: ([2] ++ [3])`). -/
theorem split_concrete : ∃ a core b, ([1, 2, 3] : List Nat) = a :: (core ++ [b]) :=
  list_split_head_mid_last [1, 2, 3] (by decide)

/-! ## Abstract residual contract: the marker framing holds for ANY input whose `scanFiltered` succeeds
    with `≥ 2` tokens (the caller discharges that for `emit v`). -/

theorem first_is_streamStart_shape (input : String) (ft : Array (Positioned YamlToken))
    (h : scanFiltered input = .ok ft) (h_size : ft.size > 0) :
    (ft[0]'h_size).val = YamlToken.streamStart :=
  scanFiltered_first_is_streamStart input ft h h_size

theorem last_is_streamEnd_shape (input : String) (ft : Array (Positioned YamlToken))
    (h : scanFiltered input = .ok ft) (h_size : ft.size > 0) :
    (ft[ft.size - 1]'(by omega)).val = YamlToken.streamEnd :=
  scanFiltered_last_is_streamEnd input ft h h_size

theorem vals_framing_shape (input : String) (ft : Array (Positioned YamlToken))
    (h : scanFiltered input = .ok ft) (h_size : 2 ≤ ft.size) :
    ∃ coreVals, ft.toList.map (·.val)
      = YamlToken.streamStart :: (coreVals ++ [YamlToken.streamEnd]) :=
  scanFiltered_vals_stream_framing input ft h h_size

/-! ## Axiom audit: the four §5.14 lemmas + the structural splitter are sorry-free
    (`[propext, Classical.choice, Quot.sound]`). `Classical.choice` enters via the core
    `Array`/`List`/`String` simp lemmas, NOT from `Except` reasoning — `#print axioms` it, never assume. -/

/-- info: 'L4YAML.Proofs.EmitterScannability.list_split_head_mid_last' depends on axioms: [propext] -/
#guard_msgs in
#print axioms list_split_head_mid_last

/-- info: 'L4YAML.Proofs.EmitterScannability.scanFiltered_first_is_streamStart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scanFiltered_first_is_streamStart

/-- info: 'L4YAML.Proofs.EmitterScannability.scanFiltered_last_is_streamEnd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scanFiltered_last_is_streamEnd

/-- info: 'L4YAML.Proofs.EmitterScannability.scanFiltered_stream_framing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scanFiltered_stream_framing

/-- info: 'L4YAML.Proofs.EmitterScannability.scanFiltered_vals_stream_framing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scanFiltered_vals_stream_framing

end StreamMarkerFraming
