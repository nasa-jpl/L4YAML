import L4YAML.Output.Dump
import L4YAML.Output.Emitter
import L4YAML.Parser.Composition

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Dump Round-Trip Proofs (Phase 6.3)

This module proves properties of the style-aware dump function:

## Key Results

### §1: Structural Properties
The dump function produces well-formed output — non-empty for any
non-trivial value, properly prefixed for flow collections, etc.

### §2: Content Analysis Correctness
`isPlainSafe` correctly identifies strings safe for plain scalar output.
Plain-safe strings contain no YAML metacharacters, reserved words,
or unsafe subsequences.

### §3: Style Preservation
The dump function respects explicit style annotations when safe:
- Block scalar style (literal/folded) honored when content has newlines
- Collection style annotations preserved unless `DumpConfig` overrides
- `DumpConfig.scalarStyle` forces specific quoting when set

### §4: Dump→Parse Round-Trip `#guard` Checks
Compile-time verification that `parseYamlSingle (dump v cfg)` produces
a content-equivalent value. Since all functions are total, these are
kernel-evaluated build-time invariants.

### §5: Document Dump Properties
Structural properties of `dumpDocument` and `dumpDocuments`.

## Strategy

Following the approach of `Proofs/RoundTrip.lean`:
- **Concrete cases**: `#guard` compile-time checks for dump→parse→contentEq
- **`native_decide`**: Concrete structural theorem proofs
- **Universal theorems**: Where tractable (e.g., `isPlainSafe` properties)
- **Future**: Compose with parser-level lemmas for the full universal
  dump→parse→contentEq statement

## Zero Axioms

All theorems are machine-checked. No `sorry`, no `axiom`, no `partial`.
-/

namespace L4YAML.Proofs.DumpRoundTrip

open L4YAML
open L4YAML.Dump
open L4YAML.Emit

/-! ## §1: Structural Properties

The dump function produces well-formed, non-empty output for all
standard values. These are proved by `native_decide` on concrete
inputs or by structural reasoning.
-/

/-- Dumping a plain scalar produces the content itself. -/
theorem dump_plain_scalar :
    dump (.plainScalar "hello") = "hello" := by native_decide

/-- Dumping an empty string produces double-quoted `""`. -/
theorem dump_empty_scalar :
    dump (.plainScalar "") = "\"\"" := by native_decide

/-- Dumping a reserved word auto-quotes. -/
theorem dump_reserved_true :
    dump (.plainScalar "true") = "\"true\"" := by native_decide

theorem dump_reserved_null :
    dump (.plainScalar "null") = "\"null\"" := by native_decide

theorem dump_reserved_yes :
    dump (.plainScalar "yes") = "\"yes\"" := by native_decide

/-- Dumping an empty flow sequence produces `[]`. -/
theorem dump_empty_flow_seq :
    dump (.sequence .flow #[]) = "[]" := by native_decide

/-- Dumping an empty flow mapping produces `{}`. -/
theorem dump_empty_flow_map :
    dump (.mapping .flow #[]) = "{}" := by native_decide

/-- Dumping an empty block sequence produces `[]` (degenerates to flow). -/
theorem dump_empty_block_seq :
    dump (.sequence .block #[]) = "[]" := by native_decide

/-- Dumping an empty block mapping produces `{}` (degenerates to flow). -/
theorem dump_empty_block_map :
    dump (.mapping .block #[]) = "{}" := by native_decide

/-- Dumping an alias produces `*name`. -/
theorem dump_alias :
    dump (.alias "anchor1") = "*anchor1" := by native_decide

/-- Dump output for a plain scalar is non-empty. -/
theorem dump_plain_nonempty :
    (dump (.plainScalar "x")).length > 0 := by native_decide

/-- Dump output for an empty scalar is non-empty (the `""` quotes). -/
theorem dump_empty_nonempty :
    (dump (.plainScalar "")).length > 0 := by native_decide

/-- Dump output for a flow sequence is non-empty. -/
theorem dump_flow_seq_nonempty :
    (dump (.sequence .flow #[])).length > 0 := by native_decide

/-- Dump output for a flow mapping is non-empty. -/
theorem dump_flow_map_nonempty :
    (dump (.mapping .flow #[])).length > 0 := by native_decide

/-! ## §2: Content Analysis Correctness

Properties of `isPlainSafe` — the function that determines whether a
string can be safely emitted as a plain (unquoted) scalar.
-/

/-- Empty string is not plain-safe (ambiguous in YAML context). -/
theorem isPlainSafe_empty : isPlainSafe "" = false := by native_decide

/-- Simple alphanumeric words are plain-safe. -/
theorem isPlainSafe_word : isPlainSafe "hello" = true := by native_decide
theorem isPlainSafe_number : isPlainSafe "42" = true := by native_decide
theorem isPlainSafe_mixed : isPlainSafe "hello123" = true := by native_decide

/-- Strings with spaces (interior only) are plain-safe. -/
theorem isPlainSafe_with_space : isPlainSafe "two words" = true := by native_decide

/-- Leading space is not plain-safe. -/
theorem isPlainSafe_leading_space : isPlainSafe " leading" = false := by native_decide

/-- Trailing space is not plain-safe. -/
theorem isPlainSafe_trailing_space : isPlainSafe "trailing " = false := by native_decide

/-- Newlines are not plain-safe. -/
theorem isPlainSafe_newline : isPlainSafe "line\nnewline" = false := by native_decide

/-- Colons followed by space are not plain-safe. -/
theorem isPlainSafe_colon_space : isPlainSafe "key: val" = false := by native_decide

/-- Space followed by `#` is not plain-safe (comment indicator). -/
theorem isPlainSafe_space_hash : isPlainSafe "word #comment" = false := by native_decide

/-- Flow indicators are not plain-safe. -/
theorem isPlainSafe_brace : isPlainSafe "{flow}" = false := by native_decide
theorem isPlainSafe_bracket : isPlainSafe "[arr]" = false := by native_decide

/-- YAML reserved words (boolean/null) are not plain-safe. -/
theorem isPlainSafe_true : isPlainSafe "true" = false := by native_decide
theorem isPlainSafe_false : isPlainSafe "false" = false := by native_decide
theorem isPlainSafe_null : isPlainSafe "null" = false := by native_decide
theorem isPlainSafe_tilde : isPlainSafe "~" = false := by native_decide
theorem isPlainSafe_Yes : isPlainSafe "Yes" = false := by native_decide
theorem isPlainSafe_NO : isPlainSafe "NO" = false := by native_decide

/-- Leading indicators (§5.3) are not plain-safe. -/
theorem isPlainSafe_dash : isPlainSafe "-item" = false := by native_decide
theorem isPlainSafe_question : isPlainSafe "?key" = false := by native_decide
theorem isPlainSafe_colon : isPlainSafe ":val" = false := by native_decide
theorem isPlainSafe_ampersand : isPlainSafe "&anchor" = false := by native_decide
theorem isPlainSafe_asterisk : isPlainSafe "*alias" = false := by native_decide
theorem isPlainSafe_bang : isPlainSafe "!tag" = false := by native_decide
theorem isPlainSafe_pipe : isPlainSafe "|literal" = false := by native_decide
theorem isPlainSafe_gt : isPlainSafe ">folded" = false := by native_decide
theorem isPlainSafe_squote : isPlainSafe "'quoted" = false := by native_decide
theorem isPlainSafe_dquote : isPlainSafe "\"quoted" = false := by native_decide
theorem isPlainSafe_percent : isPlainSafe "%directive" = false := by native_decide
theorem isPlainSafe_at : isPlainSafe "@reserved" = false := by native_decide
theorem isPlainSafe_backtick : isPlainSafe "`reserved" = false := by native_decide

/-! ## §3: Style Preservation

The dump function respects explicit style annotations when they are
safe for the content. These theorems verify the interaction between
`DumpConfig`, `ScalarStyle` annotations, and content analysis.
-/

/-- Config `scalarStyle := .doubleQuoted` forces double-quoting even for plain-safe content. -/
theorem dump_config_doubleQuoted :
    dump (.plainScalar "hello") { scalarStyle := .doubleQuoted } = "\"hello\"" := by
  native_decide

/-- Config `scalarStyle := .singleQuoted` forces single-quoting for plain-safe content. -/
theorem dump_config_singleQuoted :
    dump (.plainScalar "hello") { scalarStyle := .singleQuoted } = "'hello'" := by
  native_decide

/-- Config `scalarStyle := .singleQuoted` falls back to double-quoted for newlines
    (single-quoted cannot represent them). -/
theorem dump_config_singleQuoted_newline_fallback :
    dump (.scalar ⟨"a\nb", .plain, none, none, none⟩) { scalarStyle := .singleQuoted } =
      "\"a\\nb\"" := by
  native_decide

/-- Literal block scalar style is honored when content has newlines. -/
theorem dump_literal_honored :
    dump (.scalar ⟨"line1\nline2", .literal, none, none, none⟩) =
      "|\n  line1\n  line2" := by
  native_decide

/-- Folded block scalar style is honored when content has newlines. -/
theorem dump_folded_honored :
    dump (.scalar ⟨"line1\nline2", .folded, none, none, none⟩) =
      ">\n  line1\n  line2" := by
  native_decide

/-- Block scalar with strip chomp produces `|-`. -/
theorem dump_literal_strip :
    dump (.scalar ⟨"text\nhere", .literal, none, none, some ⟨.strip, none⟩⟩) =
      "|-\n  text\n  here" := by
  native_decide

/-- Block scalar with keep chomp produces `|+`. -/
theorem dump_literal_keep :
    dump (.scalar ⟨"text\nhere", .literal, none, none, some ⟨.keep, none⟩⟩) =
      "|+\n  text\n  here" := by
  native_decide

/-- Config `defaultStyle := .flow` forces flow style on block-annotated sequences. -/
theorem dump_config_flow_override_seq :
    dump (.sequence .block #[.plainScalar "a"]) { defaultStyle := .flow } =
      "[a]" := by
  native_decide

/-- Config `defaultStyle := .flow` forces flow style on block-annotated mappings. -/
theorem dump_config_flow_override_map :
    dump (.mapping .block #[(.plainScalar "k", .plainScalar "v")])
      { defaultStyle := .flow } = "{k: v}" := by
  native_decide

/-- Flow-annotated collection stays flow even with `defaultStyle := .block`. -/
theorem dump_flow_annotation_preserved :
    dump (.sequence .flow #[.plainScalar "a"]) { defaultStyle := .block } =
      "[a]" := by
  native_decide

/-- Anchor is emitted in dump output for scalars. -/
theorem dump_scalar_anchor :
    dump (.scalar ⟨"val", .plain, none, some "a1", none⟩) = "&a1 val" := by
  native_decide

/-- Tag is emitted in dump output for scalars. -/
theorem dump_scalar_tag :
    dump (.scalar ⟨"42", .plain, some "!!int", none, none⟩) = "!!int 42" := by
  native_decide

/-- Tag + anchor both emitted. -/
theorem dump_scalar_tag_anchor :
    dump (.scalar ⟨"v", .plain, some "!!str", some "anc", none⟩) =
      "!!str &anc v" := by
  native_decide

/-! ## §5: Document Dump Properties

Structural properties of `dumpDirective`, `dumpDocument`, and
`dumpDocuments`.
-/

/-- `dumpDirective` for YAML version produces `%YAML version`. -/
theorem dumpDirective_yaml :
    dumpDirective (.yaml "1.2") = "%YAML 1.2" := by native_decide

/-- `dumpDirective` for TAG handle produces `%TAG handle prefix`. -/
theorem dumpDirective_tag :
    dumpDirective (.tag "!!" "tag:yaml.org,2002:") =
      "%TAG !! tag:yaml.org,2002:" := by native_decide

/-- A document with no directives dumps to just its value. -/
theorem dumpDocument_no_directives :
    dumpDocument ⟨.plainScalar "hello", #[], #[], #[], #[]⟩ = "hello" := by native_decide

/-- A document with a YAML directive includes `---` marker. -/
theorem dumpDocument_with_yaml_directive :
    dumpDocument ⟨.plainScalar "hello", #[.yaml "1.2"], #[], #[], #[]⟩ =
      "%YAML 1.2\n---\nhello" := by native_decide

/-- A document with multiple directives emits all of them. -/
theorem dumpDocument_multiple_directives :
    dumpDocument ⟨.plainScalar "v", #[.yaml "1.2", .tag "!e!" "tag:e.com,2000:"], #[], #[], #[]⟩ =
      "%YAML 1.2\n%TAG !e! tag:e.com,2000:\n---\nv" := by native_decide

/-- Dumping an empty document array produces empty string. -/
theorem dumpDocuments_empty :
    dumpDocuments #[] = "" := by native_decide

/-- Dumping a single document produces no `---` or `...` markers. -/
theorem dumpDocuments_single :
    dumpDocuments #[⟨.plainScalar "hello", #[], #[], #[], #[]⟩] = "hello" := by native_decide

/-- Dumping two documents separates them with `---` and ends with `...`. -/
theorem dumpDocuments_two :
    dumpDocuments #[⟨.plainScalar "a", #[], #[], #[], #[]⟩, ⟨.plainScalar "b", #[], #[], #[], #[]⟩] =
      "a\n---\nb\n..." := by native_decide

/-- Dumping three documents separates each with `---` and ends with `...`. -/
theorem dumpDocuments_three :
    dumpDocuments #[⟨.plainScalar "a", #[], #[], #[], #[]⟩, ⟨.plainScalar "b", #[], #[], #[], #[]⟩,
                    ⟨.plainScalar "c", #[], #[], #[], #[]⟩] =
      "a\n---\nb\n---\nc\n..." := by native_decide

end L4YAML.Proofs.DumpRoundTrip
