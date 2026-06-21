/-!
# Reflection 481 — a GENERIC-discriminant premise underdetermines a TYPE-SPECIFIC output:
# surface the refinement as an explicit hypothesis, don't try to derive it.

Self-contained (core Lean, no `L4YAML` import) toy recording what R481 discovered while landing the (α)
`enclosingLocate` assemble `seqEnclosingLocate_of_seqOpener_at_depth`
(`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`).

**The setup.**  `seqWidthEnc_of_enclosingLocate_and_recIH` (R475) consumes an `enclosingLocate` hypothesis
whose located-opener premise is the GENERIC discriminant `flowBracketDelta tokens[p]!.val = 1` — "`p` is
SOME opener".  But `delta = 1` is satisfied by BOTH `.flowSequenceStart` (`[`) and `.flowMappingStart`
(`{`).  The assemble's OUTPUT, on the seq side, is type-SPECIFIC: `FlowBodyContent tokens p hiE` encodes a
`.flowSequenceEnd` close, and the close locator (R478) needs `tokens[p]!.val = .flowSequenceStart` to
guarantee the matching close is a `]`.  So when the assemble is written, the gap appears: the seq output
CANNOT be built from `delta = 1` alone — a `{`-opener satisfies the premise yet has a map child, not a seq
child.

**The brick — surface the refinement, don't derive it.**  The type-specific refinement
(`.flowSequenceStart`) is provably NOT derivable from the generic discriminant (`delta = 1`).  The honest
move is to take it as an EXPLICIT hypothesis of the assemble; that retypes the residual from "build
`enclosingLocate`" to the strictly smaller "at the located `p`, discharge seq-opener-type (+ depth-0)" —
pure boundary facts, no further structure.  The assemble's job is to SURFACE the irreducible refinement as
a named consume-side residual, not to invent a derivation that cannot exist.  (Same shape as the
head-blind / end-free gate findings, but on the CONSUMER's supplied premise rather than the producer's
precondition: a too-generic discriminant admits inhabitants the deliverable cannot represent.)

This toy abstracts the bracket as a 3-way tag: `isOpener` (the generic `delta = 1`, admits `seqOpen` and
`mapOpen`) versus `isSeqOpener` (the refinement, admits only `seqOpen`); `SeqChild` is the type-specific
output (a stand-in for `FlowBodyContent` / `.flowSequenceEnd`).
-/

namespace GenericDiscriminantUnderdeterminesOutput

set_option autoImplicit false

/-- A bracket opener tag.  `seqOpen` = `[`, `mapOpen` = `{`, `other` = a non-opener. -/
inductive Bracket where
  | seqOpen
  | mapOpen
  | other
  deriving DecidableEq

/-- **The GENERIC discriminant the consumer supplies** — `flowBracketDelta tokens[p]!.val = 1`, "`p` is
    some opener".  Admits BOTH bracket kinds. -/
def isOpener : Bracket → Prop
  | .seqOpen => True
  | .mapOpen => True
  | .other   => False

/-- **The TYPE-SPECIFIC refinement the seq output needs** — `tokens[p]!.val = .flowSequenceStart`,
    "`p` is specifically a `[`".  Admits ONLY `seqOpen`. -/
def isSeqOpener : Bracket → Prop
  | .seqOpen => True
  | _ => False

/-- The type-specific OUTPUT (a stand-in for `FlowBodyContent`, which encodes a `.flowSequenceEnd`
    close and so is inhabitable only by a `[`-headed child). -/
structure SeqChild (op : Bracket) : Prop where
  seq : op = .seqOpen

/-- **The "given seq opener" constructor — builds the seq output from the REFINEMENT** (mirrors feeding
    `h_open : tokens[p]!.val = .flowSequenceStart` to R478 + the seq child-bracket constructors). -/
theorem seqChild_of_seqOpener (op : Bracket) (h : isSeqOpener op) : SeqChild op := by
  cases op with
  | seqOpen => exact ⟨rfl⟩
  | mapOpen => simp [isSeqOpener] at h
  | other   => simp [isSeqOpener] at h

/-- **The generic discriminant ALONE cannot build the seq output.**  `mapOpen` (`{`) satisfies the
    generic `isOpener` premise yet has NO seq output — its child is a map.  So the refinement
    `isSeqOpener` is IRREDUCIBLE from `isOpener`: the assemble must surface it as a named consume-side
    residual, not derive it.  This is the exact gap R481 found between `enclosingLocate`'s `delta = 1`
    premise and the seq assemble's `.flowSequenceStart` need. -/
theorem generic_opener_underdetermines : isOpener .mapOpen ∧ ¬ SeqChild .mapOpen := by
  refine ⟨trivial, ?_⟩
  intro h
  exact absurd h.seq (by decide)

/-- The refinement is strictly STRONGER than the generic discriminant — it implies `isOpener`, never the
    reverse.  (So taking `.flowSequenceStart` as the assemble hypothesis loses nothing the consumer
    needed; it only adds what the typed output requires.) -/
theorem seqOpener_implies_opener (op : Bracket) (h : isSeqOpener op) : isOpener op := by
  cases op with
  | seqOpen => trivial
  | mapOpen => simp [isSeqOpener] at h
  | other   => simp [isSeqOpener] at h

/-- **The refinement IS recoverable once the OUTPUT already pins the type** — the converse direction.
    Where the assemble cannot derive `.flowSequenceStart` from `delta = 1` going IN, anything downstream
    holding the `SeqChild` output gets the refinement back for free.  The irreducibility is purely about
    the INPUT premise being too generic, not about the fact being unknowable. -/
theorem seqOpener_of_seqChild (op : Bracket) (h : SeqChild op) : isSeqOpener op := by
  rw [h.seq]; trivial

end GenericDiscriminantUnderdeterminesOutput
