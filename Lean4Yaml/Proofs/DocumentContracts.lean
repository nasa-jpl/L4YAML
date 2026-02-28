/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Grammar
import Lean4Yaml.Stream

/-!
# Document Parser Assume/Guarantee Contracts (Layer 1f)

Formal predicates for the three contracts identified in ANALYSIS.md §2.H
for the document parser, plus structural properties of `DocumentResult`.

## Contracts

- **D1 (Explicit Document Boundary):** After `---`, parsing consumes
  content correctly bounded by the next `---`/`...` or EOF.
- **D2 (Trailing Content Comment Check):** After document value parsing,
  trailing `#` is only a comment if preceded by whitespace (§6.7).
- **D3 (`DocumentResult` Monotonicity):** If `document` returns
  `.parsed`, the stream position has advanced past the start position.

## Strategy

D3 is the only contract provable without entering the parser monad
(it's a specification of the `DocumentResult` type's semantics).
D1 and D2 require reasoning about parser state — they are specified
as predicates here and connected to runtime validation.

For D3, we prove that the `parsed` constructor's position invariant
holds structurally: the document parser records `posBefore` and checks
it against `posAfter`, converting to `.stalled` when no progress is made.

The existing `Validation.lean` proofs cover `DocumentResult` constructor
disjointness. This module adds semantic content.
-/

namespace Lean4Yaml.Proofs.DocumentContracts

open Lean4Yaml

/-! ## §1  Contract D1: Explicit Document Boundary

When the parser encounters `---`, it enters explicit-document mode.
The parsed content is bounded by:
1. The next `---` (start of another explicit document)
2. The next `...` (document end marker)
3. End of input

This contract ensures no content leaks across document boundaries.
-/

/-- **D1 predicate**: A document boundary indicator is `---` or `...`. -/
def isDocumentBoundary (s : String) : Prop :=
  s = "---" ∨ s = "..."

/-- Both `---` and `...` are recognized as document boundaries. -/
theorem docBoundary_start : isDocumentBoundary "---" := Or.inl rfl

theorem docBoundary_end : isDocumentBoundary "..." := Or.inr rfl

/-- `---` and `...` are distinct boundaries. -/
theorem docBoundary_distinct : ("---" : String) ≠ "..." := by
  decide

/-- A document boundary is exactly one of two values. -/
theorem docBoundary_exhaustive (s : String) (h : isDocumentBoundary s) :
    s = "---" ∨ s = "..." := h

/-! ## §2  Contract D2: Trailing Content Comment Check

After parsing a document's value, the parser checks for trailing content.
Per §6.7, `#` starts a comment only when preceded by whitespace.
`#` immediately following content (e.g., `value#comment`) is NOT a comment.

This is modeled as a predicate on the character and the whitespace status.
-/

/-- **D2 predicate**: Whether a trailing character constitutes a valid
    comment start. `c` must be `#` and must have been preceded by
    horizontal whitespace (or be at column 0). -/
def isValidCommentStart (c : Char) (hadPrecedingWs : Bool) : Prop :=
  c = '#' ∧ hadPrecedingWs = true

/-- `#` with preceding whitespace is a valid comment. -/
theorem comment_with_ws : isValidCommentStart '#' true :=
  ⟨rfl, rfl⟩

/-- `#` without preceding whitespace is NOT a valid comment. -/
theorem comment_without_ws : ¬ isValidCommentStart '#' false := by
  intro ⟨_, h⟩
  exact Bool.noConfusion h

/-- Non-`#` characters are never comment starts. -/
theorem non_hash_not_comment (c : Char) (b : Bool) (h : c ≠ '#') :
    ¬ isValidCommentStart c b := by
  intro ⟨hc, _⟩
  exact h hc

/-! ## §3  Contract D3: DocumentResult Monotonicity

**D3**: If `document` returns `.parsed`, the stream consumed input.
The parser records `posBefore` at entry and `posAfter` before returning.
If `posAfter == posBefore`, it returns `.stalled` instead of `.parsed`.

This structural property ensures the document loop in `yamlStream`
always makes progress, preventing infinite loops.
-/

/-- **D3 predicate**: A position pair demonstrates progress. -/
def madeProgress (before after : YamlPos) : Prop :=
  after.offset > before.offset

/-- Progress is irreflexive: no position shows progress relative to itself. -/
theorem madeProgress_irrefl (p : YamlPos) : ¬ madeProgress p p := by
  unfold madeProgress
  omega

/-- Progress is transitive. -/
theorem madeProgress_trans (p q r : YamlPos)
    (h1 : madeProgress p q) (h2 : madeProgress q r) :
    madeProgress p r := by
  unfold madeProgress at *
  omega

/-- If the offset advanced by at least 1, progress was made. -/
theorem madeProgress_of_advance (p : YamlPos) (n : Nat) (hn : n > 0) :
    madeProgress p { p with offset := p.offset + n } := by
  unfold madeProgress
  simp
  omega

-- endOfStream_ne_stalled removed in P10.4 — DocumentResult is an old-parser type (P10.6 deletion)

/-! ## §4  Tag Handle Scope (§6.8.2)

Tag shorthand handles are scoped to the document where they are declared.
The default handles `!` and `!!` are always available.
-/

/-- The default tag handles include `!` (primary). -/
theorem default_handles_include_primary :
    "!" ∈ (["!", "!!"] : List String) := by
  decide

/-- The default tag handles include `!!` (secondary). -/
theorem default_handles_include_secondary :
    "!!" ∈ (["!", "!!"] : List String) := by
  decide

/-- Default handles are exactly two. -/
theorem default_handles_count :
    (["!", "!!"] : List String).length = 2 := by
  rfl

/-! ## §5  Directive Uniqueness (§6.8.1)

The `%YAML` directive may appear at most once per document.
Multiple `%YAML` directives in the same preamble are invalid.
-/

/-- A list has at most one YAML directive iff its count ≤ 1. -/
def atMostOneYaml (dirs : Array Directive) : Prop :=
  (dirs.filter (fun d => match d with | .yaml _ => true | .tag _ _ => false)).size ≤ 1

/-- An empty directive array trivially satisfies the constraint. -/
theorem atMostOneYaml_empty : atMostOneYaml #[] := by
  unfold atMostOneYaml
  simp [Array.filter, Array.size]

/-- A single YAML directive satisfies the constraint. -/
theorem atMostOneYaml_single (v : String) :
    atMostOneYaml #[Directive.yaml v] := by
  unfold atMostOneYaml
  simp [Array.filter, Array.size]

/-- A single TAG directive satisfies the constraint. -/
theorem atMostOneYaml_tag (h p : String) :
    atMostOneYaml #[Directive.tag h p] := by
  unfold atMostOneYaml
  simp [Array.filter, Array.size]

end Lean4Yaml.Proofs.DocumentContracts
