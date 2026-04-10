/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Types

/-!
# Canonical YAML Emitter

A pure function `emit : YamlValue → String` that serializes a `YamlValue`
into canonical YAML. The canonical form uses:

- **Double-quoted scalars** for all scalar content (simplifies escaping)
- **Flow-style collections** (`[...]` and `{...}`) for all sequences and mappings

This form is a strict subset of valid YAML that the parser can always
round-trip: `parseYamlSingle (emit v) = .ok v'` where `v'` is
content-equivalent to `v` (same scalar content, same collection elements,
potentially different style annotations).

## Design Choices

Using a single canonical form rather than style-preserving emission
makes round-trip proofs tractable. The emitter is a pure function on
inductive types with no IO, no parser dependency, and no partial defs.

## Round-Trip Property

The key theorem target (proved in `Proofs/RoundTrip.lean`):

```
∀ v, contentEq v (parseYamlSingle (emit v)).get!
```

where `contentEq` compares values ignoring style and tag annotations.
-/

namespace L4YAML.Emit

open L4YAML

/-! ## Escape Handling

Escape characters for double-quoted YAML scalars (§5.7).
This is the *inverse* of the parser's `processEscape` function
and `Grammar.resolveNamedEscape` specification.
-/

/--
Convert a nibble (0–15) to its uppercase hex character.
-/
def hexNibble (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n)  -- '0'-'9'
  else Char.ofNat (0x41 + n - 10)        -- 'A'-'F'

/--
Emit a `\xHH` hex escape for a character in the range `x00-xFF`.
Used for non-printable characters that lack a named escape (§5.7 [59]).
-/
def escapeHex2 (c : Char) : String :=
  let n := c.val.toNat
  "\\" ++ "x" ++ (hexNibble (n / 16)).toString ++ (hexNibble (n % 16)).toString

/--
Escape a single character for inclusion in a double-quoted scalar.

Maps control characters to their YAML named escape sequences (§5.7)
and escapes `\` and `"` which have special meaning in double-quoted context.
Non-printable characters without a named escape are emitted as `\xHH` (§5.7 [59]).
All other characters (nb-json minus `\` and `"`) pass through unchanged.

**YAML 1.2.2 §5.1**: On output, characters outside `c-printable` must be
presented using escape sequences. **§7.3.1 [107]**: Inside double-quoted
scalars, only `nb-json` characters (minus `\` and `"`) or escape sequences
are valid.
-/
def escapeChar (c : Char) : String :=
  match c with
  | '\x00' => "\\0"    -- null
  | '\x07' => "\\a"    -- bell
  | '\x08' => "\\b"    -- backspace
  | '\t'   => "\\t"    -- horizontal tab
  | '\n'   => "\\n"    -- line feed
  | '\x0b' => "\\v"    -- vertical tab
  | '\x0c' => "\\f"    -- form feed
  | '\r'   => "\\r"    -- carriage return
  | '\x1b' => "\\e"    -- escape
  | '\\'   => "\\\\"   -- backslash
  | '"'    => "\\\"" -- double quote
  | c      => if c.val.toNat < 0x20 then escapeHex2 c  -- remaining C0 controls (§5.1)
              else c.toString

/--
Escape a string for inclusion in a double-quoted scalar.

Applies `escapeChar` to each character in the string. Produces the
*content* portion (without the surrounding `"` delimiters).
-/
def escapeString (s : String) : String :=
  s.foldl (fun acc c => acc ++ escapeChar c) ""

/--
Emit a scalar value as a double-quoted string.

Always uses double-quoted style regardless of the original scalar style.
This is the canonical form that ensures round-trip correctness:
any content (including empty strings, special characters, and multi-line
text) is faithfully preserved.
-/
def emitScalar (content : String) : String :=
  "\"" ++ escapeString content ++ "\""

/-! ## Canonical Emitter

The main `emit` function and its list-recursion helpers.
Uses `where`-clause helpers for structural recursion through
`List YamlValue` and `List (YamlValue × YamlValue)` (converted
from the `Array` fields of `YamlValue`).
-/

/--
Emit a `YamlValue` as canonical YAML.

- Scalars: double-quoted with escapes
- Sequences: flow-style `[a, b, c]`
- Mappings: flow-style `{"k": "v", "k2": "v2"}`

The output is always a single line (no block-style constructs),
which simplifies both parsing and proof.
-/
def emit : YamlValue → String
  | .scalar s => emitScalar s.content
  | .sequence _ items .. => "[" ++ emitList items.toList ++ "]"
  | .mapping _ pairs .. => "{" ++ emitPairList pairs.toList ++ "}"
  | .alias name => emitScalar ("*" ++ name)
where
  /-- Emit a list of values as comma-separated items. -/
  emitList : List YamlValue → String
    | [] => ""
    | [v] => emit v
    | v :: vs => emit v ++ ", " ++ emitList vs
  /-- Emit a list of key-value pairs as comma-separated entries. -/
  emitPairList : List (YamlValue × YamlValue) → String
    | [] => ""
    | [(k, v)] => emit k ++ ": " ++ emit v
    | (k, v) :: rest => emit k ++ ": " ++ emit v ++ ", " ++ emitPairList rest

/-! ## Content Equivalence

`contentEq` compares two `YamlValue`s ignoring style and tag annotations.
This is the semantic equivalence that round-trip proofs target: the parser
may change style from plain to double-quoted, but the content is preserved.
-/

/--
Content equivalence of YAML values, ignoring style and tag annotations.

Two values are content-equivalent if:
- Both are scalars with the same content string
- Both are sequences with pairwise content-equivalent elements
- Both are mappings with pairwise content-equivalent key-value pairs
-/
def contentEq : YamlValue → YamlValue → Bool
  | .scalar s₁, .scalar s₂ => s₁.content == s₂.content
  | .sequence _ items₁ .., .sequence _ items₂ .. =>
    items₁.size == items₂.size &&
    contentEqList items₁.toList items₂.toList
  | .mapping _ pairs₁ .., .mapping _ pairs₂ .. =>
    pairs₁.size == pairs₂.size &&
    contentEqPairList pairs₁.toList pairs₂.toList
  | .alias n₁, .alias n₂ => n₁ == n₂
  | _, _ => false
where
  /-- Pairwise content equivalence of value lists. -/
  contentEqList : List YamlValue → List YamlValue → Bool
    | [], [] => true
    | v₁ :: vs₁, v₂ :: vs₂ => contentEq v₁ v₂ && contentEqList vs₁ vs₂
    | _, _ => false
  /-- Pairwise content equivalence of key-value pair lists. -/
  contentEqPairList : List (YamlValue × YamlValue) → List (YamlValue × YamlValue) → Bool
    | [], [] => true
    | (k₁, v₁) :: rest₁, (k₂, v₂) :: rest₂ =>
      contentEq k₁ k₂ && contentEq v₁ v₂ && contentEqPairList rest₁ rest₂
    | _, _ => false

/-! ## Comment-Aware Emission

`emitWithComments` serializes a `YamlDocument` into a string that
includes both the value tree (in canonical form) and any collected
comments. Comments are emitted as `#text` lines before the value.

When re-parsed with `parseYamlWithComments`, the same comment texts
are recovered (though byte offsets will differ). This is the emitter
for comment round-trip verification.
-/

/-- Emit comment lines from a document's comment array.
    Each comment becomes `#text\n` (the scanner stores text without `#`). -/
def emitCommentLines (comments : Array (YamlPos × Comment)) : String :=
  comments.foldl (fun acc (_, c) => acc ++ "#" ++ c.text ++ "\n") ""

/-- Emit a YAML document with comments preserved.

    Comments are emitted as `#text` lines before the canonical value.
    When re-parsed by `parseYamlWithComments`, the same comment texts
    are recovered (byte offsets will shift but text content is stable).

    Uses the canonical emitter (`emit`) for the value tree, ensuring
    deterministic output. -/
def emitWithComments (doc : YamlDocument) : String :=
  emitCommentLines doc.comments ++ emit doc.value

end L4YAML.Emit
