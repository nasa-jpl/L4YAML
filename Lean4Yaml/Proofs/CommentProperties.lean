/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types
import Lean4Yaml.Grammar
import Lean4Yaml.Emitter
import Lean4Yaml.TokenParser

/-!
# Comment Properties (Phase G3)

Properties of the comment side-channel architecture (YAML 1.2.2 §6.6).

Comments live on `YamlDocument.comments` as `Array (YamlPos × Comment)`,
separate from the value tree (`YamlValue`). This module proves that:

1. **Compose preserves comments** — alias resolution + anchor stripping
   does not touch the comment side-channel.
2. **Strip-comments preserves structure** — removing comments does not
   affect the value tree, directives, or anchors.
3. **Commutativity** — compose and stripComments commute; the value tree
   is the same regardless of operation order.
4. **Idempotence** — stripping comments twice is the same as once.

These lemmas are foundations for G5 (specification predicates modulo
comments), G6 (round-trip), and G7 (structural equivalence).

## Zero Axioms

All theorems are `rfl` — they hold by definitional reduction of struct
updates. No `sorry`, no `axiom`, no `partial`.
-/

namespace Lean4Yaml.Proofs.CommentProperties

open Lean4Yaml

/-! ## §1  Compose preserves comments

`YamlDocument.compose` uses `{ doc with value := ..., anchors := #[] }`,
which preserves all other fields including `comments`.
-/

/-- Composing a document preserves its comments. -/
theorem compose_preserves_comments (doc : YamlDocument) :
    doc.compose.comments = doc.comments := rfl

/-- Composing a document preserves its directives. -/
theorem compose_preserves_directives (doc : YamlDocument) :
    doc.compose.directives = doc.directives := rfl

/-! ## §2  Strip-comments preserves structure

`YamlDocument.stripComments` uses `{ doc with comments := #[] }`,
which preserves `value`, `directives`, and `anchors`.
-/

/-- Stripping comments preserves the value tree. -/
theorem stripComments_value_eq (doc : YamlDocument) :
    doc.stripComments.value = doc.value := rfl

/-- Stripping comments preserves directives. -/
theorem stripComments_directives_eq (doc : YamlDocument) :
    doc.stripComments.directives = doc.directives := rfl

/-- Stripping comments preserves anchors. -/
theorem stripComments_anchors_eq (doc : YamlDocument) :
    doc.stripComments.anchors = doc.anchors := rfl

/-- Stripping comments produces empty comments. -/
theorem stripComments_comments_eq (doc : YamlDocument) :
    doc.stripComments.comments = #[] := rfl

/-! ## §3  Idempotence

Stripping comments twice is the same as stripping once —
both produce `{ doc with comments := #[] }`.
-/

/-- `stripComments` is idempotent. -/
theorem stripComments_idem (doc : YamlDocument) :
    doc.stripComments.stripComments = doc.stripComments := rfl

/-! ## §4  Commutativity of compose and stripComments

Both operations use `{ doc with ... }` on orthogonal fields:
- `compose` modifies `value` and `anchors`
- `stripComments` modifies `comments`

They commute: the final document is the same regardless of order.
-/

/-- Compose then strip = strip then compose. -/
theorem compose_stripComments_comm (doc : YamlDocument) :
    doc.compose.stripComments = doc.stripComments.compose := rfl

/-- The value tree is the same whether comments are stripped before
    or after composition. -/
theorem stripComments_compose_value_eq (doc : YamlDocument) :
    doc.stripComments.compose.value = doc.compose.value := rfl

/-! ## §5  Value-independence of comments (YAML §6.6)

YAML 1.2.2 §6.6: "Comments are a presentation detail and must not be
used to convey content information."

Since comments live in a side-channel (`YamlDocument.comments`) and not
in the value tree (`YamlValue`), the value is automatically independent
of comments. This formalizes §6.6 at the type level.
-/

/-- Stripping comments from a composed document yields the same value
    as composing then stripping — both equal the composed value. -/
theorem value_independent_of_comments (doc : YamlDocument) :
    doc.compose.stripComments.value = doc.compose.value := rfl

/-- Two documents with the same value and anchors but (possibly) different
    comments or directives have the same composed value. Directives are
    not needed: `compose` only rewrites `value` and `anchors`. -/
theorem compose_value_eq_of_comments_eq
    (d1 d2 : YamlDocument)
    (hv : d1.value = d2.value)
    (ha : d1.anchors = d2.anchors) :
    d1.compose.value = d2.compose.value := by
  unfold YamlDocument.compose
  simp only []
  rw [hv, ha]

/-! ## §6  Specification predicates modulo comments (Phase G5)

All grammar validity predicates (`Scannable`, `Grammable`, `ValidNode`,
`ValidYaml`) are defined on `YamlValue`, which does not contain comments
(G2b side-channel design). `YamlDocument.stripComments` only touches the
`comments` field, leaving `value` identical. Therefore every predicate
that holds on `doc.value` automatically holds on `doc.stripComments.value`
and vice versa.

This section formalizes that comment-agnosticism with explicit theorems
so downstream proofs can rewrite through `stripComments` transparently.
-/

/-- `Grammable` is comment-agnostic: stripping comments from a document
    does not affect whether its value is grammable. -/
theorem grammable_stripComments_iff (doc : YamlDocument) (inFlow : Bool) :
    Grammar.Grammable doc.stripComments.value inFlow ↔
    Grammar.Grammable doc.value inFlow := by
  constructor <;> (intro h; exact h)

/-- `Scannable` is comment-agnostic: stripping comments from a document
    does not affect whether its value is scannable. -/
theorem scannable_stripComments_iff (doc : YamlDocument) (inFlow : Bool) :
    Grammar.Scannable doc.stripComments.value inFlow ↔
    Grammar.Scannable doc.value inFlow := by
  constructor <;> (intro h; exact h)

/-- Stripping comments preserves `Grammable` (forward direction). -/
theorem grammable_of_stripComments (doc : YamlDocument) (inFlow : Bool)
    (h : Grammar.Grammable doc.value inFlow) :
    Grammar.Grammable doc.stripComments.value inFlow := h

/-- Stripping comments preserves `Scannable` (forward direction). -/
theorem scannable_of_stripComments (doc : YamlDocument) (inFlow : Bool)
    (h : Grammar.Scannable doc.value inFlow) :
    Grammar.Scannable doc.stripComments.value inFlow := h

/-! ## §7  YamlPath resolution properties (Phase G5b)

`YamlValue.resolve` navigates the value tree by `YamlPath`. Since paths
operate on `YamlValue` (not `YamlDocument`), and `stripComments` only
touches `YamlDocument.comments`, resolution is automatically independent
of comments.
-/

/-- Empty path resolves to the value itself. -/
theorem resolve_nil (v : YamlValue) : v.resolve #[] = some v := rfl

/-- Stripping comments does not affect path resolution. -/
theorem resolve_stripComments_eq (doc : YamlDocument) (path : YamlPath) :
    doc.stripComments.value.resolve path = doc.value.resolve path := rfl

/-- Path resolution is deterministic — resolving the same path twice
    yields the same result (trivially, since `resolve` is a `def`). -/
theorem resolve_deterministic (v : YamlValue) (path : YamlPath) :
    v.resolve path = v.resolve path := rfl

/-! ## §8  Node position properties (Phase G5c)

`nodePositions` is a side-channel on `YamlDocument`, orthogonal to
`value`, `directives`, `anchors`, and `comments`. The same struct-update
independence pattern applies: `stripPositions`, `stripComments`, and
`compose` operate on disjoint fields.
-/

/-- Stripping positions preserves the value tree. -/
theorem stripPositions_value_eq (doc : YamlDocument) :
    doc.stripPositions.value = doc.value := rfl

/-- Stripping positions preserves comments. -/
theorem stripPositions_comments_eq (doc : YamlDocument) :
    doc.stripPositions.comments = doc.comments := rfl

/-- Stripping positions preserves directives. -/
theorem stripPositions_directives_eq (doc : YamlDocument) :
    doc.stripPositions.directives = doc.directives := rfl

/-- Stripping positions preserves anchors. -/
theorem stripPositions_anchors_eq (doc : YamlDocument) :
    doc.stripPositions.anchors = doc.anchors := rfl

/-- stripPositions is idempotent. -/
theorem stripPositions_idem (doc : YamlDocument) :
    doc.stripPositions.stripPositions = doc.stripPositions := rfl

/-- stripPositions and stripComments commute. -/
theorem stripPositions_stripComments_comm (doc : YamlDocument) :
    doc.stripPositions.stripComments = doc.stripComments.stripPositions := rfl

/-- commentsFor on a document with no comments returns empty. -/
theorem commentsFor_stripComments (doc : YamlDocument) (path : YamlPath) :
    doc.stripComments.commentsFor path = #[] := by
  simp only [YamlDocument.stripComments, YamlDocument.commentsFor]
  split <;> simp [Array.filterMap]

/-- Stripping positions does not affect path resolution. -/
theorem resolve_stripPositions_eq (doc : YamlDocument) (path : YamlPath) :
    doc.stripPositions.value.resolve path = doc.value.resolve path := rfl

/-- Compose preserves nodePositions. -/
theorem compose_preserves_nodePositions (doc : YamlDocument) :
    doc.compose.nodePositions = doc.nodePositions := rfl

/-- Stripping comments preserves nodePositions. -/
theorem stripComments_preserves_nodePositions (doc : YamlDocument) :
    doc.stripComments.nodePositions = doc.nodePositions := rfl

/-! ## §9  Comment text properties and emitter round-trip (Phase G6)

`commentTexts` extracts just the text strings from a document's comments,
independent of byte positions. `emitWithComments` serializes a document
with comments as `#text` lines followed by the canonical value.

These properties establish the algebraic foundations for comment round-trip:
the new functions compose predictably with `stripComments`, `stripPositions`,
`compose`, etc.
-/

/-- Stripping positions does not affect comment texts. -/
theorem commentTexts_stripPositions_eq (doc : YamlDocument) :
    doc.stripPositions.commentTexts = doc.commentTexts := rfl

/-- Stripping comments yields empty comment texts. -/
theorem commentTexts_stripComments_eq (doc : YamlDocument) :
    doc.stripComments.commentTexts = #[] := by
  simp [YamlDocument.stripComments, YamlDocument.commentTexts, Array.map]

/-- Compose preserves comment texts. -/
theorem commentTexts_compose_eq (doc : YamlDocument) :
    doc.compose.commentTexts = doc.commentTexts := rfl

/-- A document with no comments emits as just the value. -/
theorem emitWithComments_no_comments (doc : YamlDocument)
    (h : doc.comments = #[]) :
    Emit.emitWithComments doc = Emit.emit doc.value := by
  unfold Emit.emitWithComments Emit.emitCommentLines
  rw [h]
  simp [Array.foldl]

/-- Stripping positions does not affect emitWithComments output
    (positions are not used during emission). -/
theorem emitWithComments_stripPositions_eq (doc : YamlDocument) :
    Emit.emitWithComments doc.stripPositions = Emit.emitWithComments doc := rfl

/-- Stripping comments makes emitWithComments emit just the value. -/
theorem emitWithComments_stripComments_eq (doc : YamlDocument) :
    Emit.emitWithComments doc.stripComments = Emit.emit doc.value := by
  unfold Emit.emitWithComments Emit.emitCommentLines
  simp [YamlDocument.stripComments, Array.foldl]

/-- commentTexts is empty iff comments is empty. -/
theorem commentTexts_empty_iff (doc : YamlDocument) :
    doc.commentTexts = #[] ↔ doc.comments = #[] := by
  constructor
  · intro h
    unfold YamlDocument.commentTexts at h
    exact Array.eq_empty_of_map_eq_empty h
  · intro h
    unfold YamlDocument.commentTexts
    rw [h]
    simp [Array.map]

/-! ## §10  Structural equivalence modulo comments and positions (Phase G7)

YAML 1.2.2 §6.6: "Comments are a presentation detail and must not be
used to convey content information." Source positions are likewise
presentation-only metadata.

Under the G2b side-channel design, `stripComments`, `stripPositions`,
and `compose` operate on orthogonal struct fields of `YamlDocument`:
- `compose` modifies `value` (alias resolution) and `anchors` (cleared)
- `stripComments` modifies `comments` (cleared)
- `stripPositions` modifies `nodePositions` (cleared)

Because these fields are independent, stripping comments or positions
before or after composition yields the same value tree. These theorems
formalize §6.6 at the structural level: presentation details (comments
and positions) have no effect on the serialization/representation tree.

The first three theorems accept `parseYaml` output as hypothesis but
do not actually use it — the properties hold for *all* `YamlDocument`s.
The hypothesis is kept for documentation: these theorems are meaningful
precisely because the parser produces `YamlDocument` values.
-/

/-- Structural parse results are unchanged by comment presence.
    Stripping comments before composing yields the same value tree. -/
theorem parse_value_independent_of_comments (_input : String)
    (docs : Array YamlDocument)
    (_h : TokenParser.parseYaml _input = .ok docs) :
    ∀ i : Fin docs.size,
      docs[i].stripComments.compose.value = docs[i].compose.value := by
  intro i; rfl

/-- Positions do not affect the value tree either. -/
theorem parse_value_independent_of_positions (_input : String)
    (docs : Array YamlDocument)
    (_h : TokenParser.parseYaml _input = .ok docs) :
    ∀ i : Fin docs.size,
      docs[i].stripPositions.compose.value = docs[i].compose.value := by
  intro i; rfl

/-- Stripping both comments and positions still yields the same value. -/
theorem parse_value_independent_of_presentation (_input : String)
    (docs : Array YamlDocument)
    (_h : TokenParser.parseYaml _input = .ok docs) :
    ∀ i : Fin docs.size,
      docs[i].stripComments.stripPositions.compose.value = docs[i].compose.value := by
  intro i; rfl

/-- Resolution by YamlPath is independent of comments and positions. -/
theorem resolve_independent_of_presentation (doc : YamlDocument) (path : YamlPath) :
    doc.stripComments.stripPositions.value.resolve path = doc.value.resolve path := rfl

/-- Stripping order doesn't matter: comments-then-positions = positions-then-comments,
    and compose commutes with both. -/
theorem strip_order_compose_comm (doc : YamlDocument) :
    doc.stripComments.stripPositions.compose =
    doc.stripPositions.stripComments.compose := rfl

/-- Compose then strip-all produces the same value as strip-all then compose. -/
theorem compose_strip_all_comm (doc : YamlDocument) :
    doc.compose.stripComments.stripPositions.value =
    doc.stripComments.stripPositions.compose.value := rfl

end Lean4Yaml.Proofs.CommentProperties
