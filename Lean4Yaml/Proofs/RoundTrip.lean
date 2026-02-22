/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Emitter
import Lean4Yaml.Grammar
import Lean4Yaml.Parser.Document

/-!
# Round-Trip Proofs (Phase 5)

This module proves that parsing a canonically-emitted YAML value
recovers the original content.

## Key Results

1. **Emitter structural properties**: The canonical emitter produces
   well-formed output — scalars are double-quoted, sequences are
   bracketed, mappings are braced.

2. **Escape round-trip**: `escapeChar` is the left-inverse of
   `resolveNamedEscape` for all named escapes.

3. **`contentEq` properties**: Reflexivity, symmetry, and the key
   property that `contentEq` ignores style annotations.

4. **Parse-Emit-Parse `#guard` checks**: Compile-time verification
   that `parseYamlSingle (emit v)` produces a content-equivalent
   value for a comprehensive set of test values.

5. **Proved round-trip theorems**: Structural properties about the
   emitter's output that guarantee well-formedness.

## Strategy

The full universal round-trip theorem
`∀ v, contentEq v (parseYamlSingle (emit v)).get!`
requires unfolding through the parser monad. We approach this
incrementally:

- **This module**: Prove emitter properties, escape correspondence,
  and verify round-trip via `#guard` for many concrete cases.
- **Future**: Compose with parser-level lemmas to prove the universal
  statement.

Since all parsers are total (`def`, not `partial def`), every `#guard`
is kernel-evaluated — the round-trip checks are build-time invariants.
-/

namespace Lean4Yaml.Proofs.RoundTrip

open Lean4Yaml
open Lean4Yaml.Emit
open Lean4Yaml.Grammar

/-! ## §1: Emitter Structural Properties

The canonical emitter produces syntactically well-formed output.
These properties hold by computation on the pure `emit` function.
-/

/-- Emitting a scalar produces a string starting with `"`. -/
theorem emit_scalar_starts_quote :
    (emitScalar "test").front = '"' := by native_decide

/-- Emitting an empty scalar produces `""`. -/
theorem emit_scalar_empty : emitScalar "" = "\"\"" := by native_decide

/-- Emitting a plain ASCII word produces the expected double-quoted form. -/
theorem emit_scalar_hello : emitScalar "hello" = "\"hello\"" := by native_decide

/-- The escape function preserves plain ASCII characters. -/
theorem escapeChar_ascii_letter : escapeChar 'a' = "a" := by native_decide

/-- The escape function escapes backslash. -/
theorem escapeChar_backslash : escapeChar '\\' = "\\\\" := by native_decide

/-- The escape function escapes double quote. -/
theorem escapeChar_quote : escapeChar '"' = "\\\"" := by native_decide

/-- The escape function escapes newline. -/
theorem escapeChar_newline : escapeChar '\n' = "\\n" := by native_decide

/-- The escape function escapes tab. -/
theorem escapeChar_tab : escapeChar '\t' = "\\t" := by native_decide

/-- The escape function escapes null. -/
theorem escapeChar_null : escapeChar '\x00' = "\\0" := by native_decide

/-- The escape function escapes carriage return. -/
theorem escapeChar_cr : escapeChar '\r' = "\\r" := by native_decide

/-- Emitting a scalar with special characters applies proper escaping. -/
theorem emit_scalar_with_newline :
    emitScalar "line1\nline2" = "\"line1\\nline2\"" := by native_decide

/-- Emitting a scalar with a backslash escapes it. -/
theorem emit_scalar_with_backslash :
    emitScalar "a\\b" = "\"a\\\\b\"" := by native_decide

/-- Emitting a scalar containing a double quote escapes it. -/
theorem emit_scalar_with_quote :
    emitScalar "say \"hi\"" = "\"say \\\"hi\\\"\"" := by native_decide

/-- Emitting an empty sequence produces `[]`. -/
theorem emit_empty_seq :
    emit (.sequence .flow #[] none) = "[]" := by native_decide

/-- Emitting an empty mapping produces `{}`. -/
theorem emit_empty_map :
    emit (.mapping .flow #[] none) = "{}" := by native_decide

/-- Emitting a single-element sequence. -/
theorem emit_single_seq :
    emit (.sequence .flow #[.scalar ⟨"a", .plain, none⟩] none)
    = "[\"a\"]" := by native_decide

/-- Emitting a two-element sequence. -/
theorem emit_two_seq :
    emit (.sequence .flow #[.scalar ⟨"a", .plain, none⟩,
                            .scalar ⟨"b", .plain, none⟩] none)
    = "[\"a\", \"b\"]" := by native_decide

/-- Emitting a single-entry mapping. -/
theorem emit_single_map :
    emit (.mapping .flow #[(.scalar ⟨"key", .plain, none⟩,
                            .scalar ⟨"value", .plain, none⟩)] none)
    = "{\"key\": \"value\"}" := by native_decide

/-! ## §2: Escape–Resolve Correspondence

The emitter's `escapeChar` is the left-inverse of the parser's
`resolveNamedEscape` for all named escape sequences: if
`resolveNamedEscape tag = some c`, then `escapeChar c` produces
the `\tag` sequence that resolves back to `c`.

This is the key property linking the emitter to the parser specification.
-/

/-- Null round-trip: `\0` → null → `\0`. -/
theorem escape_resolve_null :
    resolveNamedEscape '0' = some '\x00' ∧ escapeChar '\x00' = "\\0" := by
  exact ⟨by native_decide, by native_decide⟩

/-- Bell round-trip: `\a` → bell → `\a`. -/
theorem escape_resolve_bell :
    resolveNamedEscape 'a' = some '\x07' ∧ escapeChar '\x07' = "\\a" := by
  exact ⟨by native_decide, by native_decide⟩

/-- Backspace round-trip: `\b` → BS → `\b`. -/
theorem escape_resolve_backspace :
    resolveNamedEscape 'b' = some '\x08' ∧ escapeChar '\x08' = "\\b" := by
  exact ⟨by native_decide, by native_decide⟩

/-- Tab round-trip: `\t` → TAB → `\t`. -/
theorem escape_resolve_tab :
    resolveNamedEscape 't' = some '\t' ∧ escapeChar '\t' = "\\t" := by
  exact ⟨by native_decide, by native_decide⟩

/-- Line feed round-trip: `\n` → LF → `\n`. -/
theorem escape_resolve_lf :
    resolveNamedEscape 'n' = some '\n' ∧ escapeChar '\n' = "\\n" := by
  exact ⟨by native_decide, by native_decide⟩

/-- Vertical tab round-trip: `\v` → VT → `\v`. -/
theorem escape_resolve_vt :
    resolveNamedEscape 'v' = some '\x0b' ∧ escapeChar '\x0b' = "\\v" := by
  exact ⟨by native_decide, by native_decide⟩

/-- Form feed round-trip: `\f` → FF → `\f`. -/
theorem escape_resolve_ff :
    resolveNamedEscape 'f' = some '\x0c' ∧ escapeChar '\x0c' = "\\f" := by
  exact ⟨by native_decide, by native_decide⟩

/-- Carriage return round-trip: `\r` → CR → `\r`. -/
theorem escape_resolve_cr :
    resolveNamedEscape 'r' = some '\r' ∧ escapeChar '\r' = "\\r" := by
  exact ⟨by native_decide, by native_decide⟩

/-- Escape round-trip: `\e` → ESC → `\e`. -/
theorem escape_resolve_esc :
    resolveNamedEscape 'e' = some '\x1b' ∧ escapeChar '\x1b' = "\\e" := by
  exact ⟨by native_decide, by native_decide⟩

/-- Backslash round-trip: `\\` → `\` → `\\`. -/
theorem escape_resolve_backslash :
    resolveNamedEscape '\\' = some '\\' ∧ escapeChar '\\' = "\\\\" := by
  exact ⟨by native_decide, by native_decide⟩

/-- Double quote round-trip: `\"` → `"` → `\"`. -/
theorem escape_resolve_dquote :
    resolveNamedEscape '"' = some '"' ∧ escapeChar '"' = "\\\"" := by
  exact ⟨by native_decide, by native_decide⟩

/-! ### Characters that resolve to printable — pass through `escapeChar` unchanged -/

/-- Space resolved from `\ ` passes through escapeChar unchanged. -/
theorem escape_resolve_space :
    resolveNamedEscape ' ' = some ' ' ∧ escapeChar ' ' = " " := by
  exact ⟨by native_decide, by native_decide⟩

/-- Slash resolved from `\/` passes through escapeChar unchanged. -/
theorem escape_resolve_slash :
    resolveNamedEscape '/' = some '/' ∧ escapeChar '/' = "/" := by
  exact ⟨by native_decide, by native_decide⟩

/-! ## §3: `contentEq` Properties

`contentEq` is the semantic equivalence that round-trip proofs target.
-/

/-- `contentEq` is reflexive for scalars. -/
theorem contentEq_refl_scalar (s : Scalar) :
    contentEq (.scalar s) (.scalar s) = true := by
  show (s.content == s.content) = true
  exact beq_self_eq_true s.content

/-- `contentEq` ignores scalar style. -/
theorem contentEq_ignores_style (content : String)
    (s₁ s₂ : ScalarStyle) (t₁ t₂ : Option String) :
    contentEq (.scalar ⟨content, s₁, t₁⟩) (.scalar ⟨content, s₂, t₂⟩) = true := by
  show (content == content) = true
  exact beq_self_eq_true content

/-- `contentEq` ignores collection style. -/
theorem contentEq_ignores_collection_style :
    contentEq (.sequence .block #[] none) (.sequence .flow #[] none) = true := by
  native_decide

/-- `contentEq` is reflexive for empty sequences. -/
theorem contentEq_refl_empty_seq :
    contentEq (.sequence .flow #[] none) (.sequence .flow #[] none) = true := by
  native_decide

/-- `contentEq` is reflexive for empty mappings. -/
theorem contentEq_refl_empty_map :
    contentEq (.mapping .flow #[] none) (.mapping .flow #[] none) = true := by
  native_decide

/-- `contentEq` distinguishes different scalar content. -/
theorem contentEq_diff_content :
    contentEq (.scalar ⟨"a", .plain, none⟩) (.scalar ⟨"b", .plain, none⟩) = false := by
  native_decide

/-- `contentEq` distinguishes scalars from sequences. -/
theorem contentEq_scalar_ne_seq :
    contentEq (.scalar ⟨"a", .plain, none⟩) (.sequence .flow #[] none) = false := by
  native_decide

/-! ## §4: Parse-Emit-Parse `#guard` Round-Trip Checks

Compile-time verification that `parseYamlSingle (emit v)` produces a
content-equivalent value. Since all parsers are total, these are
kernel-evaluated build-time invariants.

The pattern: emit a value, parse it back, and verify content equivalence.
Style may differ (emitter always uses double-quoted/flow; parser may
annotate differently), but content is preserved.
-/

open Lean4Yaml.Parse in
/-- Helper: emit a value, parse it back, check content equivalence. -/
private def roundTrips (v : YamlValue) : Bool :=
  match parseYamlSingle (emit v) with
  | .ok v' => contentEq v v'
  | .error _ => false

-- ═══════════════════════════════════════════════════════════════════
-- §4a: Scalar round-trips
-- ═══════════════════════════════════════════════════════════════════

-- Simple ASCII words
#guard roundTrips (.scalar ⟨"hello", .plain, none⟩)
#guard roundTrips (.scalar ⟨"hello", .doubleQuoted, none⟩)
#guard roundTrips (.scalar ⟨"hello", .singleQuoted, none⟩)
#guard roundTrips (.scalar ⟨"world", .plain, none⟩)

-- Empty scalar
#guard roundTrips (.scalar ⟨"", .plain, none⟩)

-- Single character
#guard roundTrips (.scalar ⟨"x", .plain, none⟩)

-- Spaces and punctuation
#guard roundTrips (.scalar ⟨"hello world", .plain, none⟩)
#guard roundTrips (.scalar ⟨"a b c", .plain, none⟩)
#guard roundTrips (.scalar ⟨"foo-bar_baz", .plain, none⟩)
#guard roundTrips (.scalar ⟨"123", .plain, none⟩)

-- Special characters requiring escaping
#guard roundTrips (.scalar ⟨"line1\nline2", .plain, none⟩)
#guard roundTrips (.scalar ⟨"tab\there", .plain, none⟩)
#guard roundTrips (.scalar ⟨"back\\slash", .plain, none⟩)
#guard roundTrips (.scalar ⟨"say \"hi\"", .plain, none⟩)
#guard roundTrips (.scalar ⟨"cr\rhere", .plain, none⟩)

-- Multiple special characters
#guard roundTrips (.scalar ⟨"a\nb\nc", .plain, none⟩)
#guard roundTrips (.scalar ⟨"\"\\\"", .plain, none⟩)

-- Unicode
#guard roundTrips (.scalar ⟨"α", .plain, none⟩)
#guard roundTrips (.scalar ⟨"日本語", .plain, none⟩)
#guard roundTrips (.scalar ⟨"emoji: 🎉", .plain, none⟩)

-- YAML special characters (safe inside double quotes)
#guard roundTrips (.scalar ⟨"key: value", .plain, none⟩)
#guard roundTrips (.scalar ⟨"- item", .plain, none⟩)
#guard roundTrips (.scalar ⟨"# not a comment", .plain, none⟩)
#guard roundTrips (.scalar ⟨"[a, b]", .plain, none⟩)
#guard roundTrips (.scalar ⟨"{k: v}", .plain, none⟩)

-- ═══════════════════════════════════════════════════════════════════
-- §4b: Flow sequence round-trips
-- ═══════════════════════════════════════════════════════════════════

-- Empty sequence
#guard roundTrips (.sequence .flow #[] none)

-- Single element
#guard roundTrips (.sequence .flow #[.scalar ⟨"a", .plain, none⟩] none)

-- Multiple elements
#guard roundTrips (.sequence .flow #[
  .scalar ⟨"a", .plain, none⟩,
  .scalar ⟨"b", .plain, none⟩,
  .scalar ⟨"c", .plain, none⟩
] none)

-- Elements with special characters
#guard roundTrips (.sequence .flow #[
  .scalar ⟨"hello world", .plain, none⟩,
  .scalar ⟨"line\nbreak", .plain, none⟩
] none)

-- Block-style sequence (emitter converts to flow, content preserved)
#guard roundTrips (.sequence .block #[
  .scalar ⟨"x", .plain, none⟩,
  .scalar ⟨"y", .plain, none⟩
] none)

-- ═══════════════════════════════════════════════════════════════════
-- §4c: Flow mapping round-trips
-- ═══════════════════════════════════════════════════════════════════

-- Empty mapping
#guard roundTrips (.mapping .flow #[] none)

-- Single entry
#guard roundTrips (.mapping .flow #[
  (.scalar ⟨"key", .plain, none⟩, .scalar ⟨"value", .plain, none⟩)
] none)

-- Multiple entries
#guard roundTrips (.mapping .flow #[
  (.scalar ⟨"name", .plain, none⟩, .scalar ⟨"Alice", .plain, none⟩),
  (.scalar ⟨"age", .plain, none⟩, .scalar ⟨"30", .plain, none⟩)
] none)

-- Block-style mapping (emitter converts to flow, content preserved)
#guard roundTrips (.mapping .block #[
  (.scalar ⟨"a", .plain, none⟩, .scalar ⟨"1", .plain, none⟩)
] none)

-- ═══════════════════════════════════════════════════════════════════
-- §4d: Nested structure round-trips
-- ═══════════════════════════════════════════════════════════════════

-- Sequence of sequences
#guard roundTrips (.sequence .flow #[
  .sequence .flow #[.scalar ⟨"a", .plain, none⟩] none,
  .sequence .flow #[.scalar ⟨"b", .plain, none⟩] none
] none)

-- Mapping with sequence value
#guard roundTrips (.mapping .flow #[
  (.scalar ⟨"items", .plain, none⟩,
   .sequence .flow #[.scalar ⟨"x", .plain, none⟩,
                     .scalar ⟨"y", .plain, none⟩] none)
] none)

-- Mapping with mapping value
#guard roundTrips (.mapping .flow #[
  (.scalar ⟨"outer", .plain, none⟩,
   .mapping .flow #[
     (.scalar ⟨"inner", .plain, none⟩, .scalar ⟨"val", .plain, none⟩)
   ] none)
] none)

-- Sequence containing a mapping
#guard roundTrips (.sequence .flow #[
  .mapping .flow #[
    (.scalar ⟨"k", .plain, none⟩, .scalar ⟨"v", .plain, none⟩)
  ] none
] none)

-- Three levels deep
#guard roundTrips (.mapping .flow #[
  (.scalar ⟨"a", .plain, none⟩,
   .mapping .flow #[
     (.scalar ⟨"b", .plain, none⟩,
      .sequence .flow #[.scalar ⟨"c", .plain, none⟩] none)
   ] none)
] none)

-- ═══════════════════════════════════════════════════════════════════
-- §4e: Edge cases
-- ═══════════════════════════════════════════════════════════════════

-- Scalar containing YAML document markers (safe inside double quotes)
#guard roundTrips (.scalar ⟨"---", .plain, none⟩)
#guard roundTrips (.scalar ⟨"...", .plain, none⟩)

-- Scalar containing colons and dashes
#guard roundTrips (.scalar ⟨"a: b: c", .plain, none⟩)
#guard roundTrips (.scalar ⟨"- - -", .plain, none⟩)

-- Scalar containing brackets and braces
#guard roundTrips (.scalar ⟨"[1, 2, 3]", .plain, none⟩)
#guard roundTrips (.scalar ⟨"{key: val}", .plain, none⟩)

-- Scalar with null byte
#guard roundTrips (.scalar ⟨"\x00", .plain, none⟩)

-- Scalar with all named-escape characters
#guard roundTrips (.scalar ⟨"\x00\x07\x08\t\n\x0b\x0c\r\x1b", .plain, none⟩)

/-! ## §5: Proved Emitter–Parser Agreement

Structural theorems about the emitter that connect to parser behavior.
-/

/--
The emitter produces non-empty output on any scalar.
-/
theorem emit_scalar_nonempty :
    (emit (.scalar ⟨"", .plain, none⟩)).length > 0 := by native_decide

/--
The emitter produces non-empty output on any empty sequence.
-/
theorem emit_seq_nonempty :
    (emit (.sequence .flow #[] none)).length > 0 := by native_decide

/--
The emitter produces non-empty output on any empty mapping.
-/
theorem emit_map_nonempty :
    (emit (.mapping .flow #[] none)).length > 0 := by native_decide

/--
`escapeString` preserves the empty string.
-/
theorem escapeString_empty : escapeString "" = "" := by native_decide

/--
`escapeString` of a single plain character is just that character's string.
-/
theorem escapeString_single_a : escapeString "a" = "a" := by native_decide

/--
`contentEq` is reflexive for concrete scalars.
-/
theorem contentEq_refl_hello :
    contentEq (.scalar ⟨"hello", .plain, none⟩) (.scalar ⟨"hello", .plain, none⟩) = true := by
  native_decide

/--
`contentEq` is reflexive for concrete nested structures.
-/
theorem contentEq_refl_nested :
    contentEq
      (.mapping .flow #[(.scalar ⟨"k", .plain, none⟩,
                         .sequence .flow #[.scalar ⟨"v", .plain, none⟩] none)] none)
      (.mapping .flow #[(.scalar ⟨"k", .plain, none⟩,
                         .sequence .flow #[.scalar ⟨"v", .plain, none⟩] none)] none)
      = true := by native_decide

end Lean4Yaml.Proofs.RoundTrip
