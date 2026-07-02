import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Empty-bracket ARM probe — the (R2) dispatch redesign needs NO new infra; the arm already exists

The SMALLEST-FIRST de-risk the blueprint queued for the `h_seq_rec` producer migration
(`(i'-b-B2c-(d)-seq-rec-producer)`, residual **(R2)**): "probe whether
`recseqentry_window_dispatch`'s empty-exclusion can be replaced by an explicit empty-entry ARM
BEFORE the full migration."  R413 (`SeqHseqRecDeepFieldProbe`) established that
`seqWindowRecSeqBody` consumes the map-FALSE `FlowBodyContentDeep`, and that
`recseqentry_window_dispatch` uses that guard's `openerContentStart` to EXCLUDE the empty-bracket
leaf — a REAL case (`[[]]`), so the exclusion is unsound and the migration onto the R393
`FlowBodyContentDeepSeq` (whose opener field is vacuous at an empty `[]`) requires the dispatch to
HANDLE empty `[ ]` / `{ }` entries rather than exclude them.  The open question (R2): does HANDLING
the empty case need NEW machinery, or does the deliverable's classify already carry the arm?

**Finding — the arm already exists; the redesign is a `by_cases`, not new infra.**  The deliverable
`RecSeqEntry` was built COMPLETE: its `seqEmpty` constructor (`NonemptyStructure.lean:475`) is the
empty `[ ]` entry, and `recseqentry_classify`'s SECOND head disjunct (`:5876`) is exactly the empty
sequence head — routed to `recseqentry_seqempty_dispatch` (`:5912`), which produces the `seqEmpty`
entry.  So the producer's false guard was suppressing an arm the classify ALREADY HANDLES.  The
dispatch redesign is: in the `[`-headed branch, `by_cases tokens[lo+1]!.val = .flowSequenceEnd`;
TRUE routes to classify's 2nd disjunct (the empty arm), FALSE keeps the existing
`recseqentry_seqbracket_located` path — and crucially the FALSE branch supplies exactly the
`tokens[lo+1] ≠ .flowSequenceEnd` premise that `FlowBodyContentDeepSeq.openerContentStart` /
`flowBodyContentDeepSeq_descend` (`:4818`) is keyed on.  The empty arm's only non-trivial input —
the successor `(lo+2 = hi ∨ tokens[lo+2]! = .flowEntry)` — is sourced from the SAME
`FlowBodyContent.bodySucc` field (`:4547`, called at `k = lo+1`) the scalar arm already uses.

**Witness (richer than the minimal `[[]]`):** `[[], "x"]` — a flow sequence whose FIRST entry is an
empty `[]` and whose SECOND is a scalar, so the empty entry is NOT last and its successor is a real
`.flowEntry` (the `bodySucc` case), and `FlowBodyContentDeepSeq.feContentStart` fires NON-vacuously.
It scans to `streamStart [ [ ] , "x" ] streamEnd` (size 8); the body window is `[lo, hi) = [2, 6)`
(`tokens[1] = [` opener, `tokens[6] = ]` close, balance `0`) — it PASSES the weak bracket guard.

* `FlowBodyContentDeep Q 2 6` is **FALSE** — its `openerContentStart` at the empty `[` (`k = 2`,
  delta `1`, `k+1 = 3 < 6`) demands `isFlowContentStart tokens[3]`, but `tokens[3] = ]`.  (Same
  unsoundness R413 found at a `{`, here at an empty `[]`.)
* `FlowBodyContentDeepSeq Q 2 6` **HOLDS** non-vacuously — opener field vacuous at `k = 2` (its
  `tokens[3] ≠ ]` premise fails), `feContentStart` FIRES at the `,` (`k = 4`: `tokens[5] = "x"` is a
  content start, the migration target's separator field doing real work).
* `recseqentry_classify Q 2 6 …` ROUTES the empty arm through its 2nd disjunct, producing the real
  `∃ m, … ∧ RecSeqEntry ((Q.toList.take m).drop 2)` — with the NON-trivial `.flowEntry` successor —
  using only EXISTING infra.  The (R2) blocker dissolves: no new lemma, a `by_cases` in the dispatch.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqEmptyEntryArmProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance flowBracketDelta isFlowContentStart)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-- `[[], "x"]` — a flow sequence whose FIRST entry is an empty `[]` and whose second is a scalar.
    The empty entry is NOT last, so its successor is a real `.flowEntry`. -/
def emptyThenScalar : YamlValue := .sequence .flow #[.sequence .flow #[], sc "x"]
def Q : Array (Positioned YamlToken) :=
  match scanFiltered (emit emptyThenScalar) with | .ok ts => ts | .error _ => #[]
-- layout: 0:SS 1:[ 2:[ 3:] 4:, 5:"x" 6:] 7:SE   (size 8); body window [2, 6)

#guard Q.size == 8

/-- The WEAK bracket-only window guard `h_seq_rec` is quantified over, as a Bool. -/
def weakGuard (T : Array (Positioned YamlToken)) (lo hi : Nat) : Bool :=
  (2 ≤ lo) && (lo < hi) && (hi ≤ T.size - 2) && (hi < T.size) &&
  (T[hi]!.val == .flowSequenceEnd) && (flowBracketBalance T lo hi == 0) &&
  (T[lo-1]!.val == .flowSequenceStart)

-- the body window `[2, 6)` IS in `h_seq_rec`'s domain (empty `[]` as its first entry).
#guard weakGuard Q 2 6
-- the empty arm's classify-2nd-disjunct head shape holds, with a NON-trivial `.flowEntry` successor.
#guard (2 + 1 < Q.size) && (Q[2]!.val == .flowSequenceStart) &&
  (Q[3]!.val == .flowSequenceEnd) && (Q[4]!.val == .flowEntry)

-- Concrete token facts of the closed scan (the body window `[2, 6)` interior).
theorem q2 : Q[2]!.val = .flowSequenceStart := by native_decide
theorem q3 : Q[3]!.val = .flowSequenceEnd := by native_decide
theorem q4 : Q[4]!.val = .flowEntry := by native_decide
theorem q5 : Q[5]!.val = .scalar "x" .doubleQuoted := by native_decide

/-- **NEGATIVE — the OLD `FlowBodyContentDeep` that `seqWindowRecSeqBody` consumes is FALSE on this
    `h_seq_rec` window** — at the EMPTY `[]` opener, not a `{` (R413's witness).  Its
    `openerContentStart` fires at the `[` (`k = 2`, delta `1`) and demands `tokens[3] = ]` be a
    content start.  This is the unsound empty-EXCLUSION the dispatch leans on, made visible. -/
theorem flowBodyContentDeep_false_on_empty_window : ¬ FlowBodyContentDeep Q 2 6 := by
  intro hd
  have h_delta : flowBracketDelta Q[2]!.val = 1 := by rw [q2]; exact flowBracketDelta_flowSequenceStart
  have h_cs : isFlowContentStart Q[3]!.val :=
    hd.openerContentStart 2 (Nat.le_refl 2) (by omega) h_delta
  rw [q3] at h_cs
  simp only [isFlowContentStart] at h_cs
  rcases h_cs with ⟨c, s, h⟩ | h | h
  · exact YamlToken.noConfusion h
  · exact YamlToken.noConfusion h
  · exact YamlToken.noConfusion h

/-- **POSITIVE — the R393 re-scoped `FlowBodyContentDeepSeq` HOLDS on the SAME window, NON-vacuously.**
    The opener field is vacuous at the empty `[` (its `tokens[3] ≠ ]` premise fails — exactly the
    empty case the `by_cases` carves out), but `feContentStart` FIRES at the depth-`0` `,` (`k = 4`:
    `tokens[5] = "x"` is a content start).  So the migration target is satisfiable here AND its
    separator field is load-bearing. -/
theorem flowBodyContentDeepSeq_holds_on_empty_window : FlowBodyContentDeepSeq Q 2 6 := by
  refine ⟨?_, ?_, ?_⟩
  · -- headContentStart: tokens[2] = .flowSequenceStart is content-start.
    rw [q2]; exact Or.inr (Or.inl rfl)
  · -- openerContentStart: k ∈ {2,3,4}.  k=2 vacuous (tokens[3] = ] fails `≠ ]`); k=3,4 not `[`.
    intro k hk1 hk2 hopen hne
    have hk : k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk with rfl | rfl | rfl
    · exact absurd q3 hne
    · rw [q3] at hopen; exact YamlToken.noConfusion hopen
    · rw [q4] at hopen; exact YamlToken.noConfusion hopen
  · -- feContentStart: k ∈ {2,3,4}.  Only k=4 is a `.flowEntry` — and there tokens[5] = "x" is content.
    intro k hk1 hk2 hfe _hne
    have hk : k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk with rfl | rfl | rfl
    · rw [q2] at hfe; exact YamlToken.noConfusion hfe
    · rw [q3] at hfe; exact YamlToken.noConfusion hfe
    · rw [q5]; exact Or.inl ⟨"x", .doubleQuoted, rfl⟩

/-- **HEADLINE — the empty arm routes through the EXISTING `recseqentry_classify`.**  Feeding its
    SECOND head disjunct (the empty-sequence `[ ]` shape) on the real window `[2, 6)` produces the
    located first entry `∃ m, … ∧ RecSeqEntry ((Q.toList.take m).drop 2)` — with the NON-trivial
    `.flowEntry` successor (`tokens[4]`, since `lo+2 = 4 ≠ 6 = hi`).  No new lemma: the (R2) dispatch
    redesign is a `by_cases tokens[lo+1] = .flowSequenceEnd` routing to this disjunct, exactly the
    `≠ .flowSequenceEnd` key that `FlowBodyContentDeepSeq.openerContentStart` already consumes. -/
theorem empty_window_routes_through_classify :
    ∃ m, 2 < m ∧ m ≤ 6 ∧ flowBracketBalance Q 2 m = 0 ∧
      (m = 6 ∨ Q[m]!.val = .flowEntry) ∧
      (∀ k, 2 < k → k < m →
        ¬ (flowBracketBalance Q 2 k = 0 ∧ (k = 6 ∨ Q[k]!.val = .flowEntry))) ∧
      RecSeqEntry ((Q.toList.take m).drop 2) :=
  recseqentry_classify Q 2 6 (by native_decide) (by native_decide) (by native_decide)
    (Or.inr (Or.inl ⟨by native_decide, by native_decide, by native_decide, Or.inr (by native_decide)⟩))

end L4YAML.Proofs.EmitterScannability.SeqEmptyEntryArmProbe
