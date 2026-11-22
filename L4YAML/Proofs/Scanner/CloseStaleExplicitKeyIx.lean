module

public import L4YAML.Scanner.IndexedDispatch

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# `closeStaleExplicitKeyIx` — the projection lemmas (item 333)

The last step of `scanNextTokenIx_preprocess` and `scanNextTokenIx_preprocessWC` ends a pending explicit key whose entry a sibling has closed.  It
writes `explicitKeyLine`/`explicitKeyCol` and NOTHING else, so every other
projection of the state passes through unchanged; the preprocess lemmas peel
it off the outside with these rewrites before reasoning about the key save.
-/

namespace L4YAML.Proofs.CloseStaleExplicitKeyIx

open L4YAML L4YAML.Scanner L4YAML.Scanner.Indexed

/-! ## Indexed scanner -/

lemma closeStaleExplicitKeyIx_cases {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx = s ∨
    ∃ c, s.peek? = some c ∧ s.closeStaleExplicitKeyIx = (s.closeStaleAt c).readPendingKey := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx
  split <;> (try split) <;> (try split) <;>
    first | exact Or.inl rfl | exact Or.inr ⟨_, by assumption, rfl⟩

lemma closeStaleExplicitKeyIx_of_inFlow {input : String} (s : ScannerStateIx input)
    (h : s.inFlow = true) : s.closeStaleExplicitKeyIx = s := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx; simp [h]

lemma closeStaleExplicitKeyIx_of_ek_none {input : String} (s : ScannerStateIx input)
    (h : s.explicitKeyLine = none) : s.closeStaleExplicitKeyIx = s := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx; rw [h]; split <;> rfl

lemma closeStaleExplicitKeyIx_explicitKeyLine {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.explicitKeyLine = s.explicitKeyLine ∨
    ∃ c, s.peek? = some c ∧ s.closeStaleExplicitKeyIx.explicitKeyLine =
      (s.closeStaleAt c).innermostPendingKey.1 := by
  rcases closeStaleExplicitKeyIx_cases s with h | ⟨c, hc, h⟩ <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr ⟨c, hc, rfl⟩

@[simp] lemma closeStaleExplicitKeyIx_cursor {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.cursor = s.cursor := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_indents {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.indents = s.indents := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_flowLevel {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.flowLevel = s.flowLevel := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_tokens {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.tokens = s.tokens := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_simpleKey {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.simpleKey = s.simpleKey := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_simpleKeyStack {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.simpleKeyStack = s.simpleKeyStack := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_simpleKeyAllowed {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.simpleKeyAllowed = s.simpleKeyAllowed := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_needIndentCheck {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.needIndentCheck = s.needIndentCheck := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_allowDirectives {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.allowDirectives = s.allowDirectives := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_seenYamlDirective {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.seenYamlDirective = s.seenYamlDirective := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_directivesPresent {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.directivesPresent = s.directivesPresent := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_documentEverStarted {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.documentEverStarted = s.documentEverStarted := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_flowStack {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.flowStack = s.flowStack := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_implicitValueLine {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.implicitValueLine = s.implicitValueLine := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_docStartLine {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.docStartLine = s.docStartLine := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_explicitKeyStack {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.explicitKeyStack = s.explicitKeyStack := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_definedAnchors {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.definedAnchors = s.definedAnchors := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_comments {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.comments = s.comments := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_hasMore {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.hasMore = s.hasMore := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_peek {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.peek? = s.peek? := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_inFlow {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.inFlow = s.inFlow := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

@[simp] lemma closeStaleExplicitKeyIx_currentIndent {input : String} (s : ScannerStateIx input) :
    s.closeStaleExplicitKeyIx.currentIndent = s.currentIndent := by
  unfold ScannerStateIx.closeStaleExplicitKeyIx ScannerStateIx.readPendingKey ScannerStateIx.closeStaleAt
  split <;> (try split) <;> (try split) <;> rfl

/-- Indexed twin of `peel_stale`. -/
macro "peel_stale_ix" : tactic =>
  `(tactic| simp only [closeStaleExplicitKeyIx_cursor, closeStaleExplicitKeyIx_indents, closeStaleExplicitKeyIx_flowLevel, closeStaleExplicitKeyIx_tokens, closeStaleExplicitKeyIx_simpleKey, closeStaleExplicitKeyIx_simpleKeyStack, closeStaleExplicitKeyIx_simpleKeyAllowed, closeStaleExplicitKeyIx_needIndentCheck, closeStaleExplicitKeyIx_allowDirectives, closeStaleExplicitKeyIx_seenYamlDirective, closeStaleExplicitKeyIx_directivesPresent, closeStaleExplicitKeyIx_documentEverStarted, closeStaleExplicitKeyIx_flowStack, closeStaleExplicitKeyIx_implicitValueLine, closeStaleExplicitKeyIx_docStartLine, closeStaleExplicitKeyIx_explicitKeyStack, closeStaleExplicitKeyIx_definedAnchors, closeStaleExplicitKeyIx_comments, closeStaleExplicitKeyIx_hasMore, closeStaleExplicitKeyIx_peek, closeStaleExplicitKeyIx_inFlow, closeStaleExplicitKeyIx_currentIndent] at *)

end L4YAML.Proofs.CloseStaleExplicitKeyIx

end Blanket
