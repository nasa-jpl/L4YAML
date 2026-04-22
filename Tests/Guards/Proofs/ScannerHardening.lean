/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Parser.Composition

/-!
# Scanner Hardening — Compile-Time Guards (v0.2.10)

Compile-time `#guard` checks for explicit key value resolution, flow explicit
keys, and validation strictness edge cases beyond yaml-test-suite coverage.
Each guard is evaluated by Lean's kernel at `lake build` time.

**Categories** (matching ExplicitKeyTests.lean §11–§20):
- Double/nested explicit keys (§11)
- Standalone `?` and empty key/value (§12)
- Nested structures as explicit keys (§13)
- Tags on explicit keys (§14)
- Flow explicit key edge cases (§15)
- Explicit key + block sequence nesting (§16)
- Explicit key with colons in plain scalars (§17)
- Explicit key + alias resolution (§18)
- Indented explicit keys (§19)
- Tab rejection (§20)
-/

namespace Tests.Guards.ScannerHardening

open L4YAML.TokenParser

-- §11: Double/nested explicit keys
-- ? ? a: b — mapping-as-key (valid YAML, unhashable in Python/libyaml)
#guard match parseYamlSingle "? ? a: b" with | .ok v => v.isMapping | .error _ => false
-- ? ? — double bare explicit key → nested null:null mapping as key
#guard match parseYamlSingle "? ?" with | .ok v => v.isMapping | .error _ => false
-- ? ?\n  a: b\n: outer — nested explicit key with outer value
#guard match parseYamlSingle "?\n  ? a: b\n: outer" with | .ok v => v.isMapping | .error _ => false

-- §12: Standalone ? and empty key/value
-- bare ? at EOF → mapping with null key and null value
#guard match parseYamlSingle "?" with | .ok v => v.isMapping | .error _ => false
-- ? with trailing space
#guard match parseYamlSingle "? " with | .ok v => v.isMapping | .error _ => false
-- ? with trailing newline
#guard match parseYamlSingle "?\n" with | .ok v => v.isMapping | .error _ => false
-- ---\n? under explicit document start
#guard match parseYamlSingle "---\n?" with | .ok v => v.isMapping | .error _ => false
-- ?\n:\n?\n: — two null:null entries
#guard match parseYamlSingle "?\n:\n?\n:" with
  | .ok v => match v.asPairs? with | some p => p.size == 2 | none => false
  | .error _ => false
-- ?\n: — bare explicit key + bare value
#guard match parseYamlSingle "?\n:" with | .ok v => v.isMapping | .error _ => false

-- §13: Nested structures as explicit keys
-- ? [1, 2]\n: value — flow sequence as key
#guard match parseYamlSingle "? [1, 2]\n: value" with
  | .ok v => match v.asPairs? with
    | some p => match p[0]? with
      | some (k, _) => k.isSequence
      | none => false
    | none => false
  | .error _ => false
-- ? {a: 1}\n: value — flow mapping as key (produces 2 entries)
#guard match parseYamlSingle "? {a: 1}\n: value" with
  | .ok v => match v.asPairs? with
    | some p => match p[0]? with
      | some (k, _) => k.isMapping
      | none => false
    | none => false
  | .error _ => false
-- ? [a, b]\n: {c: d} — sequence key → mapping value
#guard match parseYamlSingle "? [a, b]\n: {c: d}" with
  | .ok v => match v.asPairs? with
    | some p => match p[0]? with
      | some (k, val) => k.isSequence && val.isMapping
      | none => false
    | none => false
  | .error _ => false
-- {? [a]: b} — flow mapping with sequence as explicit key
#guard match parseYamlSingle "{? [a]: b}" with
  | .ok v => match v.asPairs? with
    | some p => match p[0]? with
      | some (k, _) => k.isSequence
      | none => false
    | none => false
  | .error _ => false

-- §14: Tags on explicit keys
-- ? !!str 123\n: numeric
#guard match parseYamlSingle "? !!str 123\n: numeric" with | .ok v => v.isMapping | .error _ => false
-- ? !tag key\n: value
#guard match parseYamlSingle "? !tag key\n: value" with | .ok v => v.isMapping | .error _ => false

-- §15: Flow explicit key edge cases
-- {? : v1, ? : v2} — duplicate null keys in flow
#guard match parseYamlSingle "{? : v1, ? : v2}" with | .ok v => v.isMapping | .error _ => false
-- {?, ?} — bare ? entries in flow
#guard match parseYamlSingle "{?, ?}" with | .ok v => v.isMapping | .error _ => false
-- {? , ? } — bare ? with spaces
#guard match parseYamlSingle "{? , ? }" with | .ok v => v.isMapping | .error _ => false
-- [? a : b, ? c : d] — multiple explicit entries in flow sequence
#guard match parseYamlSingle "[? a : b, ? c : d]" with
  | .ok v => match v.asArray? with
    | some a => a.size == 2
    | none => false
  | .error _ => false
-- [? a, ? b] — explicit keys without values in flow sequence
#guard match parseYamlSingle "[? a, ? b]" with
  | .ok v => match v.asArray? with
    | some a => a.size == 2 && a[0]!.isMapping && a[1]!.isMapping
    | none => false
  | .error _ => false

-- §16: Explicit key + block sequence nesting
-- - ? k1\n  : v1\n- ? k2\n  : v2 — sequence of explicit-key mappings
#guard match parseYamlSingle "- ? k1\n  : v1\n- ? k2\n  : v2" with
  | .ok v => match v.asArray? with
    | some a => a.size == 2 && a[0]!.isMapping && a[1]!.isMapping
    | none => false
  | .error _ => false

-- §17: Explicit key with colons in plain scalars
-- ? a:b:c\n: v — unspaced colons are part of key
#guard match parseYamlSingle "? a:b:c\n: v" with
  | .ok v => match v.asPairs? with
    | some p => match p[0]? with
      | some (k, _) => match k with
        | .scalar s => s.content == "a:b:c"
        | _ => false
      | none => false
    | none => false
  | .error _ => false
-- ? http://example.com\n: url — URL-like plain scalar key
#guard match parseYamlSingle "? http://example.com\n: url" with
  | .ok v => match v.asPairs? with
    | some p => match p[0]? with
      | some (k, _) => match k with
        | .scalar s => s.content == "http://example.com"
        | _ => false
      | none => false
    | none => false
  | .error _ => false

-- §18: Explicit key + alias resolution
-- ? &a k\n: *a — alias resolves to anchored value "k"
#guard match parseYamlSingle "? &a k\n: *a" with
  | .ok v => match v.asPairs? with
    | some p => match p[0]? with
      | some (_, val) => match val with
        | .scalar s => s.content == "k"
        | _ => false
      | none => false
    | none => false
  | .error _ => false

-- §19: Indented explicit keys
-- "  ? a\n  : b" — indented block explicit key
#guard match parseYamlSingle "  ? a\n  : b" with
  | .ok v => match v.asPairs? with
    | some p => match p[0]? with
      | some (k, val) => match k, val with
        | .scalar ks, .scalar vs => ks.content == "a" && vs.content == "b"
        | _, _ => false
      | none => false
    | none => false
  | .error _ => false

-- §20: Tab rejection in explicit keys
-- ?\t — tab after ? is forbidden in block context (§6.1)
#guard match parseYamlSingle "?\t" with | .ok _ => false | .error _ => true

-- Cross-category: explicit key across document boundary
#guard match parseYaml "? key\n: val\n---\n? key2\n: val2" with
  | .ok docs => docs.size == 2
  | .error _ => false
-- Document end after explicit key
#guard match parseYaml "---\n? key\n: val\n..." with
  | .ok docs => docs.size == 1
  | .error _ => false

-- Explicit key value resolution: ? a\n: b basic round-trip check
#guard match parseYamlSingle "? a\n: b" with
  | .ok v => match v.asPairs? with
    | some p => match p[0]? with
      | some (k, val) => match k, val with
        | .scalar ks, .scalar vs => ks.content == "a" && vs.content == "b"
        | _, _ => false
      | none => false
    | none => false
  | .error _ => false

-- Multiple explicit keys without values
#guard match parseYamlSingle "? a\n? b\n? c" with
  | .ok v => match v.asPairs? with
    | some p => p.size == 3
    | none => false
  | .error _ => false

-- Comment between ? and : (X8DW pattern)
#guard match parseYamlSingle "---\n? key\n# comment\n: value" with
  | .ok v => match v.asPairs? with
    | some p => match p[0]? with
      | some (k, val) => match k, val with
        | .scalar ks, .scalar vs => ks.content == "key" && vs.content == "value"
        | _, _ => false
      | none => false
    | none => false
  | .error _ => false

-- Anchor-only explicit key: ? &a\n: *a
#guard match parseYamlSingle "? &a\n: *a" with | .ok v => v.isMapping | .error _ => false

-- Mixed explicit + implicit keys
#guard match parseYamlSingle "? a\n: 1\nimplicit: 2" with
  | .ok v => match v.asPairs? with
    | some p => p.size == 2
    | none => false
  | .error _ => false

-- §8.2.2 [197]: misindented `:` after explicit key must be rejected.
-- `? a\n : b` has `:` at col 1 when mapping indent is 0.
#guard match parseYamlSingle "? a\n : b" with
  | .ok _ => false
  | .error _ => true

-- Legal version: `:` at col 0 (matching mapping indent)
#guard match parseYamlSingle "? a\n: b" with | .ok v => v.isMapping | .error _ => false

-- Deeper nesting: `? ? a\n  : inner\n: outer` — both `:` at correct indents
#guard match parseYamlSingle "? ? a\n  : inner\n: outer" with
  | .ok v => v.isMapping | .error _ => false

/-! ## §22: Same-line Explicit Key Content — §8.2.2 [196] -/

-- `? : x` — `:` on same line as `?` is implicit value for empty key
-- inside the explicit key's content (compact mapping): accept
#guard match parseYamlSingle "? : x" with | .ok v => v.isMapping | .error _ => false

-- `? :` — same-line `:` with empty value → compact mapping: accept
#guard match parseYamlSingle "? :" with | .ok v => v.isMapping | .error _ => false

-- `? ? : b` — nested explicit key, same-line `:` → compact mapping: accept
#guard match parseYamlSingle "? ? : b" with | .ok v => v.isMapping | .error _ => false

-- `? key : val` — `:` follows simple key on `?` line → accept
#guard match parseYamlSingle "? key : val" with | .ok v => v.isMapping | .error _ => false

-- `? key\n: val` — `:` on next line at correct indent → accept
#guard match parseYamlSingle "? key\n: val" with | .ok v => v.isMapping | .error _ => false

/-! ## §23: Block→Flow Underindent Rejection — §8.1 [187] (v0.2.11) -/

-- `a:\n{b: c}` — flow at col 0 as value of mapping at indent 0 → reject
#guard match parseYamlSingle "a:\n{b: c}" with | .ok _ => false | .error _ => true

-- `a:\n[1, 2]` — sequence at col 0 under mapping at indent 0 → reject
#guard match parseYamlSingle "a:\n[1, 2]" with | .ok _ => false | .error _ => true

-- `a:\n {b: c}` — flow at col 1 (indent+1) → accept
#guard match parseYamlSingle "a:\n {b: c}" with | .ok v => v.isMapping | .error _ => false

-- `a:\n [1, 2]` — sequence at col 1 (indent+1) → accept
#guard match parseYamlSingle "a:\n [1, 2]" with | .ok v => v.isMapping | .error _ => false

-- Root `{a: 1}` — no enclosing block (indent = -1) → accept
#guard match parseYamlSingle "{a: 1}" with | .ok v => v.isMapping | .error _ => false

-- Root `[1, 2]` — no enclosing block → accept
#guard match parseYamlSingle "[1, 2]" with | .ok v => v.isSequence | .error _ => false

end Tests.Guards.ScannerHardening
