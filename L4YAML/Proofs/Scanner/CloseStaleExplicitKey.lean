module

public import L4YAML.Scanner.Scanner

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# `closeStaleExplicitKey` — the projection lemmas (item 333)

The last step of `scanNextToken_preprocess` (the indexed twin is in
`CloseStaleExplicitKeyIx`) ends a pending explicit key whose entry a sibling has closed.  It
writes `explicitKeyLine`/`explicitKeyCol` and NOTHING else, so every other
projection of the state passes through unchanged; the preprocess lemmas peel
it off the outside with these rewrites before reasoning about the key save.
-/

namespace L4YAML.Proofs.CloseStaleExplicitKey

open L4YAML L4YAML.Scanner

/-! ## Legacy scanner -/

/-- The hook is the identity or exactly the re-read of the register off the
    pending-key stack with the closed level's key cleared (item 335: an outer
    `?` survives, a lone `?` dies). -/
lemma closeStaleExplicitKey_cases (s : ScannerState) :
    closeStaleExplicitKey s = s ∨
    ∃ c, s.peek? = some c ∧ closeStaleExplicitKey s = (s.closeStaleAt c).readPendingKey := by
  unfold closeStaleExplicitKey
  split <;> (try split) <;> (try split) <;>
    first | exact Or.inl rfl | exact Or.inr ⟨_, by assumption, rfl⟩

/-- In flow context the hook is the identity. -/
lemma closeStaleExplicitKey_of_inFlow (s : ScannerState) (h : s.inFlow = true) :
    closeStaleExplicitKey s = s := by
  unfold closeStaleExplicitKey; simp [h]

/-- A dead register is left alone: the hook only ends a LIVE `?` entry. -/
lemma closeStaleExplicitKey_of_ek_none (s : ScannerState) (h : s.explicitKeyLine = none) :
    closeStaleExplicitKey s = s := by
  unfold closeStaleExplicitKey; rw [h]; split <;> rfl

/-- The register after the hook is what it was, or the innermost pending key
    below the closed level. -/
lemma closeStaleExplicitKey_explicitKeyLine (s : ScannerState) :
    (closeStaleExplicitKey s).explicitKeyLine = s.explicitKeyLine ∨
    ∃ c, s.peek? = some c ∧ (closeStaleExplicitKey s).explicitKeyLine =
      (s.closeStaleAt c).innermostPendingKey.1 := by
  rcases closeStaleExplicitKey_cases s with h | ⟨c, hc, h⟩ <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr ⟨c, hc, rfl⟩

@[simp] lemma closeStaleExplicitKey_input (s : ScannerState) :
    (closeStaleExplicitKey s).input = s.input := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_inputEnd (s : ScannerState) :
    (closeStaleExplicitKey s).inputEnd = s.inputEnd := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_offset (s : ScannerState) :
    (closeStaleExplicitKey s).offset = s.offset := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_line (s : ScannerState) :
    (closeStaleExplicitKey s).line = s.line := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_col (s : ScannerState) :
    (closeStaleExplicitKey s).col = s.col := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_indents (s : ScannerState) :
    (closeStaleExplicitKey s).indents = s.indents := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_flowLevel (s : ScannerState) :
    (closeStaleExplicitKey s).flowLevel = s.flowLevel := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_tokens (s : ScannerState) :
    (closeStaleExplicitKey s).tokens = s.tokens := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_simpleKey (s : ScannerState) :
    (closeStaleExplicitKey s).simpleKey = s.simpleKey := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_simpleKeyStack (s : ScannerState) :
    (closeStaleExplicitKey s).simpleKeyStack = s.simpleKeyStack := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_simpleKeyAllowed (s : ScannerState) :
    (closeStaleExplicitKey s).simpleKeyAllowed = s.simpleKeyAllowed := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_needIndentCheck (s : ScannerState) :
    (closeStaleExplicitKey s).needIndentCheck = s.needIndentCheck := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_allowDirectives (s : ScannerState) :
    (closeStaleExplicitKey s).allowDirectives = s.allowDirectives := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_seenYamlDirective (s : ScannerState) :
    (closeStaleExplicitKey s).seenYamlDirective = s.seenYamlDirective := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_directivesPresent (s : ScannerState) :
    (closeStaleExplicitKey s).directivesPresent = s.directivesPresent := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_documentEverStarted (s : ScannerState) :
    (closeStaleExplicitKey s).documentEverStarted = s.documentEverStarted := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_flowStack (s : ScannerState) :
    (closeStaleExplicitKey s).flowStack = s.flowStack := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_implicitValueLine (s : ScannerState) :
    (closeStaleExplicitKey s).implicitValueLine = s.implicitValueLine := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_docStartLine (s : ScannerState) :
    (closeStaleExplicitKey s).docStartLine = s.docStartLine := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_explicitKeyStack (s : ScannerState) :
    (closeStaleExplicitKey s).explicitKeyStack = s.explicitKeyStack := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_comments (s : ScannerState) :
    (closeStaleExplicitKey s).comments = s.comments := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_definedAnchors (s : ScannerState) :
    (closeStaleExplicitKey s).definedAnchors = s.definedAnchors := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_currentPos (s : ScannerState) :
    (closeStaleExplicitKey s).currentPos = s.currentPos := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_hasMore (s : ScannerState) :
    (closeStaleExplicitKey s).hasMore = s.hasMore := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_peek (s : ScannerState) :
    (closeStaleExplicitKey s).peek? = s.peek? := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_peekAt? (s : ScannerState) (n : Nat) :
    (closeStaleExplicitKey s).peekAt? n = s.peekAt? n := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_inFlow (s : ScannerState) :
    (closeStaleExplicitKey s).inFlow = s.inFlow := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKey_currentIndent (s : ScannerState) :
    (closeStaleExplicitKey s).currentIndent = s.currentIndent := by
  unfold closeStaleExplicitKey ScannerState.readPendingKey ScannerState.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

/-- Peel the item-333 hook off every projection in sight (goal and
    hypotheses) so a preprocess proof reads `saveSimpleKey` again. -/
macro "peel_stale" : tactic =>
  `(tactic| simp only [closeStaleExplicitKey_input, closeStaleExplicitKey_inputEnd, closeStaleExplicitKey_offset, closeStaleExplicitKey_line, closeStaleExplicitKey_col, closeStaleExplicitKey_indents, closeStaleExplicitKey_flowLevel, closeStaleExplicitKey_tokens, closeStaleExplicitKey_simpleKey, closeStaleExplicitKey_simpleKeyStack, closeStaleExplicitKey_simpleKeyAllowed, closeStaleExplicitKey_needIndentCheck, closeStaleExplicitKey_allowDirectives, closeStaleExplicitKey_seenYamlDirective, closeStaleExplicitKey_directivesPresent, closeStaleExplicitKey_documentEverStarted, closeStaleExplicitKey_flowStack, closeStaleExplicitKey_implicitValueLine, closeStaleExplicitKey_docStartLine, closeStaleExplicitKey_explicitKeyStack, closeStaleExplicitKey_comments, closeStaleExplicitKey_definedAnchors, closeStaleExplicitKey_currentPos, closeStaleExplicitKey_hasMore, closeStaleExplicitKey_peek, closeStaleExplicitKey_inFlow, closeStaleExplicitKey_currentIndent] at *)

end L4YAML.Proofs.CloseStaleExplicitKey

end Blanket
