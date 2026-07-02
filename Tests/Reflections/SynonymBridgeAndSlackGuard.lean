/-!
# Reflection 399 — a producer field and the consumer hypothesis it feeds can be the SAME
predicate under two module-local names: check definitional equality FIRST (the bridge is
`exact h`), and a consumer guard premise the producer asserts unconditionally is SLACK.

Self-contained core-Lean toy of L4YAML R399 — the head-bridge between R398's composite wrappers
and the value-induction. The producer (`EmitScansInFlowBlock`, `Block.lean`) carries a content-start
HEAD field `∃ hne : block ≠ [], ContentStartTok (block.head hne).val`; the consumer
(`OpenerAdj_wrap_seq`, `WellBracketed.lean`) wants `h_head : ∀ h0, (block[0]).val ≠ .flowSequenceEnd
→ isFlowContentStart (block[0]).val`. The wiring looked like a real lemma; it collapsed twice.

(1) SYNONYM: `ContentStartTok` (the emitter-scannability layer's name) and `isFlowContentStart`
   (the parser layer's name) are DEFINITIONALLY identical — declared independently in two modules,
   each coining a name for one notion. The bridge is `exact h`, not a structural proof.
(2) SLACK GUARD: the consumer's `≠ .flowSequenceEnd` premise is one the producer asserts
   UNCONDITIONALLY (line 107 holds for EVERY non-empty block) — so it is DISCARDED (`intro _`),
   not discharged. The same producer field feeds the UNGUARDED consumer just as well.

Here `Tok.content`/`Tok.opn` ~ content-start tokens, `Tok.cls` ~ `.flowSequenceEnd`.
`ContentStartP` ~ `ContentStartTok` (producer name), `IsContentStart` ~ `isFlowContentStart`
(consumer name), definitionally identical. `NotQuiteContentStart` is a genuine look-alike that is
NOT a synonym (only `.content`, not the opener) — the NEGATIVE that pins why the `exact h` shortcut
needs real definitional equality.
-/

namespace Tests.Reflections.SynonymBridgeAndSlackGuard

set_option autoImplicit false

/-- A content head, the seq opener, the close (~ `.flowSequenceEnd`), and a separator. -/
inductive Tok | content | opn | cls | sep
  deriving DecidableEq, Repr, BEq, Inhabited

/-- "Module A" (the PRODUCER layer) coins this name for a content-start. -/
def ContentStartP (t : Tok) : Prop := t = .content ∨ t = .opn

/-- "Module B" (the CONSUMER layer) independently coins THIS name — DEFINITIONALLY identical
    to `ContentStartP`, just a different identifier declared in a different module. -/
def IsContentStart (t : Tok) : Prop := t = .content ∨ t = .opn

/-- A genuine look-alike that only LOOKS like the synonym: `.content` alone, NOT the opener. -/
def NotQuiteContentStart (t : Tok) : Prop := t = .content

/-- **POSITIVE — the synonym bridge is `id`.**  No structural proof: `exact h` typechecks
    only because the two predicates are definitionally equal. -/
theorem synonym_fwd (t : Tok) (h : ContentStartP t) : IsContentStart t := h
theorem synonym_bwd (t : Tok) (h : IsContentStart t) : ContentStartP t := h

/-- **NEGATIVE — a look-alike is NOT a synonym, so the `exact h` shortcut is unavailable and
    the implication is in fact FALSE.**  `.opn` is a content-start (`IsContentStart`) but not
    `NotQuiteContentStart`.  This pins that the bridge shortcut requires real definitional
    equality — a predicate that merely resembles the field must be proved (and may not hold). -/
theorem lookalike_not_synonym : ¬ (∀ t, IsContentStart t → NotQuiteContentStart t) := by
  intro h
  have hh := h .opn (Or.inr rfl)
  simp only [NotQuiteContentStart] at hh
  exact absurd hh (by decide)

/-- **The head-bridge** (= `openerAdj_head_of_block_contentStart`).  Convert the producer field
    `∃ hne : block ≠ [], ContentStartP (block.head hne)` into the GUARDED consumer shape
    `∀ h0, block[0] ≠ .cls → IsContentStart block[0]`.  The `≠ .cls` guard is SLACK — the
    producer asserts the content-start head UNCONDITIONALLY — so it is DISCARDED (`intro _`). -/
theorem head_of_block_contentStart (block : List Tok)
    (h : ∃ (hne : block ≠ []), ContentStartP (block.head hne)) :
    ∀ (h0 : 0 < block.length), (block[0]'h0) ≠ .cls → IsContentStart (block[0]'h0) := by
  obtain ⟨hne, hcs⟩ := h
  intro h0 _
  rw [List.head_eq_getElem hne] at hcs
  exact hcs

/-- **The slack is real:** the SAME producer field feeds the UNGUARDED consumer
    (`∀ h0, IsContentStart block[0]`) — the `≠ .cls` premise added nothing. -/
theorem head_of_block_contentStart_unguarded (block : List Tok)
    (h : ∃ (hne : block ≠ []), ContentStartP (block.head hne)) :
    ∀ (h0 : 0 < block.length), IsContentStart (block[0]'h0) := by
  obtain ⟨hne, hcs⟩ := h
  intro h0
  rw [List.head_eq_getElem hne] at hcs
  exact hcs

/-- **POSITIVE — the bridge on a concrete block `[.content, .opn]`.** -/
theorem bridge_concrete :
    ∀ (h0 : 0 < ([Tok.content, .opn]).length),
      (([Tok.content, .opn])[0]'h0) ≠ .cls → IsContentStart (([Tok.content, .opn])[0]'h0) :=
  head_of_block_contentStart [.content, .opn] ⟨by decide, Or.inl rfl⟩

-- The producer field's head sits at index 0; the guard `≠ .cls` is incidental and unused.
#guard ([Tok.content, Tok.opn])[0]! == Tok.content
#guard ([Tok.opn, Tok.cls])[0]! == Tok.opn
-- The look-alike differs from the synonym exactly at `.opn` (witness of `lookalike_not_synonym`).
#guard (Tok.opn == Tok.content) == false

end Tests.Reflections.SynonymBridgeAndSlackGuard
