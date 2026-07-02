import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# `seqWindowRecSeqBody` DEEP-FIELD probe — its `FlowBodyContentDeep` hypothesis is ALSO too strong

The SMALLEST-FIRST de-risk mandated BEFORE authoring the `h_seq_rec` producer
(`(i'-b-B2c-(d)-seq-rec-producer)`, after R412), per [[ref-probe-deferred-universal-before-producing]] /
[[ref-minimal-pair-extracts-the-gate]].  R412 confirmed the narrow-gate *navigator-locator*
`nestedSeq_recseqbody_of_locator` cannot serve `h_seq_rec` (its `SeqPathAllSeq` fails on a map-enclosed
window).  The blueprint's redirect named the STOP-AT-EDGE producer `seqWindowRecSeqBody` (R323) as the
right `h_seq_rec` producer, on the read that it needs only the TOP-only `SeqEnclosed` (not the whole-path
tag) so it is "enclosure-blind".  This probe reads `seqWindowRecSeqBody`'s ACTUAL signature
(`SeqInteriorSeparators.lean:2678`) and finds a SECOND too-strong hypothesis the enclosure analysis
missed: it consumes **`FlowBodyContentDeep tokens lo hi`** — the all-depth content guard whose
`openerContentStart` fires at EVERY `flowBracketDelta = 1` opener, including a flow-MAP `{`.  R392
(`flowBodyContentDeep_root_seed_false`) already proved that field FALSE on real output; R393 re-scoped it
to the seq-only `FlowBodyContentDeepSeq` (opener keyed on `.flowSequenceStart` + `≠ ]`) which is TRUE
everywhere.  But **`seqWindowRecSeqBody` was never re-scoped onto the parallel R393 type** — it still
consumes the OLD, map-FALSE `FlowBodyContentDeep`.

So `seqWindowRecSeqBody` is NOT a one-line `h_seq_rec` producer: `h_seq_rec` quantifies over EVERY
seq-body window with the weak bracket guard — including a seq window whose direct entry is a MAP
(`[{a: b}]`) — and at such a window the producer's own `FlowBodyContentDeep` premise is UNSATISFIABLE.

The MINIMAL PAIR (one window, the two parallel deep-content types disagree) on real scanned output:

* `[{a: b}]` scans to `streamStart [ { key "a" value "b" } ] streamEnd` (size 10).  The seq BODY
  window is `[lo, hi) = [2, 8)` (`tokens[1] = .flowSequenceStart` opener, `tokens[8] = .flowSequenceEnd`
  close, `flowBracketBalance 2 8 = 0`) — it PASSES the weak bracket guard `h_seq_rec` quantifies over.
* `FlowBodyContentDeep tokens 2 8` is **FALSE**: its `openerContentStart` fires at the `{` at `k = 2`
  (`flowBracketDelta .flowMappingStart = 1`, `k + 1 = 3 < 8`), demanding `isFlowContentStart tokens[3]`
  — but `tokens[3] = .key`, not a content start.  So the producer's premise cannot be supplied here.
* `FlowBodyContentDeepSeq tokens 2 8` is **TRUE**: its `openerContentStart` is keyed on
  `.flowSequenceStart` (the `{` is `.flowMappingStart`, so the field is VACUOUS at `k = 2`), its
  `feContentStart` on `.flowEntry` (none in the window, VACUOUS), and `headContentStart` holds because
  `tokens[2] = .flowMappingStart` is itself a content start (the map disjunct).

**Conclusion.**  The `h_seq_rec` producer is NOT `seqWindowRecSeqBody tokens … h_deep …` as written.  Its
residual beyond the weak guard is: (R1) the ROOT CARRIER `SeqInteriorSeparators tokens 2 (size-2)`;
(R2) **re-scope the producer from `FlowBodyContentDeep` onto the R393 `FlowBodyContentDeepSeq`** — NOT a
mere signature swap, because `recseqentry_window_dispatch` RELIES on the false `openerContentStart` to
EXCLUDE the empty-bracket leaf (R392's unsoundness note), so the dispatch must be redesigned to HANDLE
empty `[ ]` / `{ }` entries; (R3) the re-scoped field's three sub-fields per window — `openerContentStart`
is already the R411 provider `seqWindowOpenerAdj_of_emit`, `headContentStart` derives from the global
opener-adjacency at `k = lo - 1`, but `feContentStart` (separator→non-`.key`→content-start) needs a NEW
GLOBAL SEPARATOR-adjacency fact that does not yet exist (only the OPENER adjacency `GlobalFlowSeqOpenerAdj`
is built).  `SeqEnclosed` (top-only) and `FlowBodyWindow` reduce from the weak guard (R390).  Surfacing
this BEFORE authoring averts a doomed one-line wiring that would wall at the `[{a: b}]` window.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqHseqRecDeepFieldProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance flowBracketDelta isFlowContentStart)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-- `[{a: b}]` — a flow sequence whose single entry is a flow MAP.  Its body window `[2, 8)` is a valid
    `h_seq_rec` window (passes the weak bracket guard) yet contains a `{` opener. -/
def mapVal2 : YamlValue := .sequence .flow #[.mapping .flow #[(sc "a", sc "b")]]
def Q : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapVal2) with | .ok ts => ts | .error _ => #[]
-- layout: 0:SS 1:[ 2:{ 3:key 4:"a" 5:value 6:"b" 7:} 8:] 9:SE

#guard Q.size == 10

/-- The WEAK bracket-only window guard `h_seq_rec` is quantified over, as a Bool. -/
def weakGuard (T : Array (Positioned YamlToken)) (lo hi : Nat) : Bool :=
  (2 ≤ lo) && (lo < hi) && (hi ≤ T.size - 2) && (hi < T.size) &&
  (T[hi]!.val == .flowSequenceEnd) && (flowBracketBalance T lo hi == 0) &&
  (T[lo-1]!.val == .flowSequenceStart)

-- the body window `[2, 8)` IS in `h_seq_rec`'s domain.
#guard weakGuard Q 2 8

-- Concrete token facts of the closed scan (the body window `[2, 8)` interior).
theorem q2 : Q[2]!.val = .flowMappingStart := by native_decide
theorem q3 : Q[3]!.val = .key := by native_decide
theorem q4 : Q[4]!.val = .scalar "a" .doubleQuoted := by native_decide
theorem q5 : Q[5]!.val = .value := by native_decide
theorem q6 : Q[6]!.val = .scalar "b" .doubleQuoted := by native_decide

/-- **NEGATIVE — the OLD `FlowBodyContentDeep` that `seqWindowRecSeqBody` consumes is FALSE on this
    `h_seq_rec` window.**  Its `openerContentStart` fires at the `{` (delta 1) and demands `tokens[3] = .key`
    be a content start.  So the stop-at-edge producer's premise is UNSATISFIABLE here — it cannot serve
    `h_seq_rec` as written. -/
theorem flowBodyContentDeep_false_on_map_window : ¬ FlowBodyContentDeep Q 2 8 := by
  intro hd
  have h_delta : flowBracketDelta Q[2]!.val = 1 := by rw [q2]; exact flowBracketDelta_flowMappingStart
  have h_cs : isFlowContentStart Q[3]!.val :=
    hd.openerContentStart 2 (Nat.le_refl 2) (by omega) h_delta
  rw [q3] at h_cs
  simp only [isFlowContentStart] at h_cs
  rcases h_cs with ⟨c, s, h⟩ | h | h
  · exact YamlToken.noConfusion h
  · exact YamlToken.noConfusion h
  · exact YamlToken.noConfusion h

/-- **POSITIVE — the R393 re-scoped `FlowBodyContentDeepSeq` HOLDS on the SAME window.**  The opener field
    is keyed on `.flowSequenceStart` (vacuous at the `{`), the separator field on `.flowEntry` (none in the
    window), and the head `tokens[2] = .flowMappingStart` is a content start.  So the re-scoped type is the
    right producer target — the discriminator between the two is EXACTLY the opener keying. -/
theorem flowBodyContentDeepSeq_holds_on_map_window : FlowBodyContentDeepSeq Q 2 8 := by
  refine ⟨?_, ?_, ?_⟩
  · -- headContentStart: tokens[2] = .flowMappingStart is content-start.
    rw [q2]; exact Or.inr (Or.inr rfl)
  · -- openerContentStart: vacuous — no `.flowSequenceStart` opener in [2, 8).
    intro k hk1 hk2 hopen _hne
    exfalso
    have hk : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · rw [q2] at hopen; exact YamlToken.noConfusion hopen
    · rw [q3] at hopen; exact YamlToken.noConfusion hopen
    · rw [q4] at hopen; exact YamlToken.noConfusion hopen
    · rw [q5] at hopen; exact YamlToken.noConfusion hopen
    · rw [q6] at hopen; exact YamlToken.noConfusion hopen
  · -- feContentStart: vacuous — no `.flowEntry` separator in [2, 8).
    intro k hk1 hk2 hfe _hne
    exfalso
    have hk : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · rw [q2] at hfe; exact YamlToken.noConfusion hfe
    · rw [q3] at hfe; exact YamlToken.noConfusion hfe
    · rw [q4] at hfe; exact YamlToken.noConfusion hfe
    · rw [q5] at hfe; exact YamlToken.noConfusion hfe
    · rw [q6] at hfe; exact YamlToken.noConfusion hfe

end L4YAML.Proofs.EmitterScannability.SeqHseqRecDeepFieldProbe
