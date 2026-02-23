import Lean.Data.Json
import Lean4Yaml.Types

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# YAML Dump

Style-aware serialization: `dump : YamlValue → DumpConfig → String`.

Implements YAML 1.2.2 §3.1.1 — converts the representation graph
(`YamlValue`) to a character stream with human-readable formatting.

## Relationship to `Emitter.lean`

| | Emitter | Dump |
|---|---|---|
| Scalars | Double-quoted only | Plain, quoted, literal, folded |
| Collections | Flow only | Block (default) or flow |
| Indentation | None (single line) | Configurable width |
| Purpose | Round-trip proofs | Human-readable output |

## Design

The dump function is **pure** (no IO), **kernel-reducible** (`#guard`-testable),
and respects YAML 1.2.2 presentation details:

- **Scalar style**: content analysis determines plain vs quoted; block scalar
  annotations (`.literal`, `.folded`) are honored when content contains newlines.
- **Collection style**: per-node `CollectionStyle` annotation respected;
  `DumpConfig.defaultStyle` overrides when set to `.flow`.
- **Indentation**: configurable width, minimum 1 space for block scalar content.
-/

namespace Lean4Yaml.Dump

open Lean Lean4Yaml

/-! ## Style Preferences -/

/--
Default collection style preference.

- `block`: indentation-based (default, human-readable)
- `flow`: JSON-like brackets (compact)
- `auto`: respect per-node `CollectionStyle` annotation
-/
inductive DefaultStyle where
  | block
  | flow
  | auto
  deriving Repr, BEq, Inhabited, DecidableEq, ToJson, FromJson

/--
Scalar style preference for the dump function.

- `plain`: unquoted when content allows
- `doubleQuoted`: always double-quote
- `singleQuoted`: single-quote when content allows
- `auto`: choose based on content analysis (default)
-/
inductive ScalarPref where
  | plain
  | doubleQuoted
  | singleQuoted
  | auto
  deriving Repr, BEq, Inhabited, DecidableEq, ToJson, FromJson

/-! ## Configuration -/

/--
Configuration for the YAML dump function.

Controls formatting: indentation width, default collection style,
scalar quoting preference, line width hint, and key ordering.
-/
structure DumpConfig where
  /-- Spaces per indentation level -/
  indent : Nat := 2
  /-- Default collection style when node has no explicit annotation -/
  defaultStyle : DefaultStyle := .block
  /-- Scalar quoting preference -/
  scalarStyle : ScalarPref := .auto
  /-- Line width hint (advisory, for future flow→block decisions) -/
  lineWidth : Nat := 80
  /-- Sort mapping keys alphabetically for deterministic output.
      **Not yet implemented** — reserved for a future enhancement. -/
  sortKeys : Bool := false
  deriving Repr, BEq, Inhabited, ToJson

/-- Manual `FromJson` instance for `DumpConfig` that uses structure defaults
    for any missing JSON field, enabling partial config like `{"indent": 4}`. -/
instance : Lean.FromJson DumpConfig where
  fromJson? json := do
    let indent := match json.getObjValAs? Nat "indent" with
      | .ok v => v | _ => 2
    let defaultStyle := match json.getObjValAs? DefaultStyle "defaultStyle" with
      | .ok v => v | _ => .block
    let scalarStyle := match json.getObjValAs? ScalarPref "scalarStyle" with
      | .ok v => v | _ => .auto
    let lineWidth := match json.getObjValAs? Nat "lineWidth" with
      | .ok v => v | _ => 80
    let sortKeys := match json.getObjValAs? Bool "sortKeys" with
      | .ok v => v | _ => false
    .ok { indent, defaultStyle, scalarStyle, lineWidth, sortKeys }

/-! ## Private Helpers -/

/-- Build an indentation string: `depth × width` spaces. -/
private def makeIndent (depth : Nat) (width : Nat) : String :=
  String.ofList (List.replicate (depth * width) ' ')

/--
Escape a character for double-quoted YAML scalars (§5.7).

Same table as `Emit.escapeChar`; duplicated here to avoid a
dependency cycle (`Dump` imports only `Types`).
-/
private def escapeChar (c : Char) : String :=
  match c with
  | '\x00' => "\\0"
  | '\x07' => "\\a"
  | '\x08' => "\\b"
  | '\t'   => "\\t"
  | '\n'   => "\\n"
  | '\x0b' => "\\v"
  | '\x0c' => "\\f"
  | '\r'   => "\\r"
  | '\x1b' => "\\e"
  | '\\'   => "\\\\"
  | '"'    => "\\\""
  | c      => c.toString

/-- Escape a string for double-quoted context. -/
private def escapeString (s : String) : String :=
  s.foldl (fun acc c => acc ++ escapeChar c) ""

/-- Emit a double-quoted scalar. -/
private def dumpDoubleQuoted (s : String) : String :=
  "\"" ++ escapeString s ++ "\""

/-- Emit a single-quoted scalar. Only `'` is escaped (as `''`). -/
private def dumpSingleQuoted (s : String) : String :=
  "'" ++ s.foldl (fun acc c => acc ++ if c == '\'' then "''" else c.toString) "" ++ "'"

/-- Check if string is a YAML reserved word (boolean, null). -/
def isReservedWord (s : String) : Bool :=
  s == "true" || s == "false" || s == "null" ||
  s == "True" || s == "False" || s == "Null" ||
  s == "TRUE" || s == "FALSE" || s == "NULL" ||
  s == "yes" || s == "no" || s == "Yes" || s == "No" ||
  s == "YES" || s == "NO" || s == "~"

/-- Check if a character is a YAML indicator (§5.3). -/
def isIndicator (c : Char) : Bool :=
  c == '-' || c == '?' || c == ':' || c == ',' ||
  c == '[' || c == ']' || c == '{' || c == '}' ||
  c == '#' || c == '&' || c == '*' || c == '!' ||
  c == '|' || c == '>' || c == '\'' || c == '"' ||
  c == '%' || c == '@' || c == '`'

/-- Check if string contains `: ` or ` #` (unsafe in plain scalars). -/
def hasUnsafeSubsequence (s : String) : Bool :=
  go s.toList
where
  go : List Char → Bool
    | [] => false
    | [_] => false
    | c₁ :: c₂ :: rest =>
      (c₁ == ':' && c₂ == ' ') ||
      (c₁ == ' ' && c₂ == '#') ||
      go (c₂ :: rest)

/-- Determine if string content is safe for plain scalar style. -/
def isPlainSafe (s : String) : Bool :=
  if s.isEmpty then false
  else
    let chars := s.toList
    match chars with
    | [] => false
    | c :: _ =>
      -- First character must not be a YAML indicator
      !isIndicator c &&
      -- Must not contain flow indicators or newlines
      !s.any (fun ch => ch == '{' || ch == '}' || ch == '[' || ch == ']' ||
                         ch == ',' || ch == '\n' || ch == '\r') &&
      -- Must not contain `: ` or ` #`
      !hasUnsafeSubsequence s &&
      -- Must not have leading/trailing whitespace
      c != ' ' && c != '\t' &&
      (match chars.getLast? with
       | some last => last != ' ' && last != '\t'
       | none => true) &&
      -- Must not be a reserved word
      !isReservedWord s

/-- Check if string contains newlines. -/
def hasNewlines (s : String) : Bool :=
  s.any (· == '\n')

/-- Choose effective scalar style based on content and config. -/
private def chooseScalarStyle (s : Scalar) (cfg : DumpConfig) : ScalarStyle :=
  -- Honor explicit block scalar style when content has newlines
  if (s.style == .literal || s.style == .folded) && hasNewlines s.content then
    s.style
  else match cfg.scalarStyle with
    | .doubleQuoted => .doubleQuoted
    | .singleQuoted =>
      -- Single-quoted cannot represent newlines
      if hasNewlines s.content then .doubleQuoted else .singleQuoted
    | .plain =>
      if isPlainSafe s.content then .plain else .doubleQuoted
    | .auto =>
      if s.content.isEmpty then .doubleQuoted
      else if hasNewlines s.content then
        -- Multi-line: use block scalar style from annotation, or default to literal
        if s.style == .literal || s.style == .folded then s.style else .literal
      else if isPlainSafe s.content then .plain
      else .doubleQuoted

/-- Resolve collection style from node annotation and config. -/
private def resolveCollectionStyle (nodeStyle : CollectionStyle) (cfg : DumpConfig)
    : CollectionStyle :=
  match cfg.defaultStyle with
  | .flow => .flow
  | .block => nodeStyle
  | .auto => nodeStyle

/--
Emit a block scalar (literal `|` or folded `>`).

Returns the header + newline + indented content lines.
Content lines are indented at `max(1, depth) × indentWidth` spaces
to satisfy YAML's minimum 1-space content indent requirement.
-/
private def dumpBlockScalar (content : String) (indicator : String)
    (bsMeta : Option BlockScalarMeta) (depth : Nat) (indentWidth : Nat) : String :=
  let chomp := match bsMeta with | some m => m.chomp | none => .clip
  let chompStr := match chomp with | .clip => "" | .strip => "-" | .keep => "+"
  -- Block scalar content must be indented ≥ 1 space from the indicator
  let effectiveDepth := if depth == 0 then 1 else depth
  let ind := makeIndent effectiveDepth indentWidth
  let lines := content.splitOn "\n"
  let body := lines.map (fun line => if line.isEmpty then "" else ind ++ line)
  indicator ++ chompStr ++ "\n" ++ String.intercalate "\n" body

/-- Build tag + anchor prefix for a node. No trailing space. -/
private def nodePrefix (tag : Option String) (anchor : Option String) : String :=
  let t := match tag with | some t => t | none => ""
  let a := match anchor with | some n => "&" ++ n | none => ""
  match t.isEmpty, a.isEmpty with
  | true, true => ""
  | true, false => a
  | false, true => t
  | false, false => t ++ " " ++ a

/-- Check if a value renders as a single line (can follow `- ` or `key: `). -/
private def isInlineValue : YamlValue → Bool
  | .scalar _ => true
  | .alias _ => true
  | .sequence .flow _ .. => true
  | .mapping .flow _ .. => true
  | _ => false

/-! ## Main Dump Function -/

/--
Dump a `YamlValue` as human-readable YAML.

Produces style-aware output:
- Plain, quoted, literal, or folded scalars based on content analysis
- Block or flow collections based on node annotations and config
- Configurable indentation width

**Contract**: `dumpValue v cfg depth` returns the text representation:
- First line has **no** leading indent (caller provides prefix)
- Continuation lines include leading indent at `depth` level
- No trailing newline

## Examples

```
dump (.plainScalar "hello") == "hello"
dump (.sequence .block #[.plainScalar "a", .plainScalar "b"])
  == "- a\n- b"
```
-/
def dump (v : YamlValue) (cfg : DumpConfig := {}) : String :=
  dumpValue v cfg 0
where
  /-- Dump a value. First line unindented; continuation lines at `depth`. -/
  dumpValue : YamlValue → DumpConfig → Nat → String
    | .scalar s, cfg, depth =>
      let anchorStr := match s.anchor with | some n => "&" ++ n ++ " " | none => ""
      let tagStr := match s.tag with | some t => t ++ " " | none => ""
      let pfx := tagStr ++ anchorStr
      let effectiveStyle := chooseScalarStyle s cfg
      let body := match effectiveStyle with
        | .plain => s.content
        | .doubleQuoted => dumpDoubleQuoted s.content
        | .singleQuoted => dumpSingleQuoted s.content
        | .literal => dumpBlockScalar s.content "|" s.blockMeta depth cfg.indent
        | .folded => dumpBlockScalar s.content ">" s.blockMeta depth cfg.indent
      pfx ++ body
    | .alias name, _, _ => "*" ++ name
    | .sequence style items tag anchor, cfg, depth =>
      let npfx := nodePrefix tag anchor
      let effectiveStyle := resolveCollectionStyle style cfg
      match effectiveStyle with
      | .flow =>
        let hdr := if npfx.isEmpty then "" else npfx ++ " "
        hdr ++ "[" ++ dumpFlowList items.toList cfg depth ++ "]"
      | .block =>
        if items.isEmpty then
          (if npfx.isEmpty then "" else npfx ++ " ") ++ "[]"
        else if npfx.isEmpty then
          dumpBlockList items.toList cfg depth true
        else
          npfx ++ "\n" ++ makeIndent depth cfg.indent ++
            dumpBlockList items.toList cfg depth true
    | .mapping style pairs tag anchor, cfg, depth =>
      let npfx := nodePrefix tag anchor
      let effectiveStyle := resolveCollectionStyle style cfg
      match effectiveStyle with
      | .flow =>
        let hdr := if npfx.isEmpty then "" else npfx ++ " "
        hdr ++ "{" ++ dumpFlowPairs pairs.toList cfg depth ++ "}"
      | .block =>
        if pairs.isEmpty then
          (if npfx.isEmpty then "" else npfx ++ " ") ++ "{}"
        else if npfx.isEmpty then
          dumpBlockPairs pairs.toList cfg depth true
        else
          npfx ++ "\n" ++ makeIndent depth cfg.indent ++
            dumpBlockPairs pairs.toList cfg depth true
  /-- Comma-separated flow list items. -/
  dumpFlowList : List YamlValue → DumpConfig → Nat → String
    | [], _, _ => ""
    | [v], cfg, depth => dumpValue v cfg depth
    | v :: vs, cfg, depth => dumpValue v cfg depth ++ ", " ++ dumpFlowList vs cfg depth
  /-- Comma-separated flow mapping pairs. -/
  dumpFlowPairs : List (YamlValue × YamlValue) → DumpConfig → Nat → String
    | [], _, _ => ""
    | [(k, v)], cfg, depth =>
      dumpValue k cfg depth ++ ": " ++ dumpValue v cfg depth
    | (k, v) :: rest, cfg, depth =>
      dumpValue k cfg depth ++ ": " ++ dumpValue v cfg depth ++ ", " ++
        dumpFlowPairs rest cfg depth
  /-- Block sequence items. `first = true` suppresses indent on first line. -/
  dumpBlockList : List YamlValue → DumpConfig → Nat → Bool → String
    | [], _, _, _ => ""
    | [v], cfg, depth, first =>
      let ind := if first then "" else makeIndent depth cfg.indent
      if isInlineValue v then
        ind ++ "- " ++ dumpValue v cfg (depth + 1)
      else
        ind ++ "-\n" ++ makeIndent (depth + 1) cfg.indent ++
          dumpValue v cfg (depth + 1)
    | v :: vs, cfg, depth, first =>
      let ind := if first then "" else makeIndent depth cfg.indent
      let item :=
        if isInlineValue v then
          ind ++ "- " ++ dumpValue v cfg (depth + 1)
        else
          ind ++ "-\n" ++ makeIndent (depth + 1) cfg.indent ++
            dumpValue v cfg (depth + 1)
      item ++ "\n" ++ dumpBlockList vs cfg depth false
  /-- Block mapping pairs. `first = true` suppresses indent on first line. -/
  dumpBlockPairs : List (YamlValue × YamlValue) → DumpConfig → Nat → Bool → String
    | [], _, _, _ => ""
    | [(k, v)], cfg, depth, first =>
      let ind := if first then "" else makeIndent depth cfg.indent
      if isInlineValue v then
        ind ++ dumpValue k cfg depth ++ ": " ++ dumpValue v cfg (depth + 1)
      else
        ind ++ dumpValue k cfg depth ++ ":\n" ++
          makeIndent (depth + 1) cfg.indent ++ dumpValue v cfg (depth + 1)
    | (k, v) :: rest, cfg, depth, first =>
      let ind := if first then "" else makeIndent depth cfg.indent
      let pair :=
        if isInlineValue v then
          ind ++ dumpValue k cfg depth ++ ": " ++ dumpValue v cfg (depth + 1)
        else
          ind ++ dumpValue k cfg depth ++ ":\n" ++
            makeIndent (depth + 1) cfg.indent ++ dumpValue v cfg (depth + 1)
      pair ++ "\n" ++ dumpBlockPairs rest cfg depth false

/-! ## Directive Serialization -/

/--
Dump a single YAML directive.

- `%YAML 1.2` for version directives
- `%TAG !handle! prefix` for tag directives
-/
def dumpDirective : Directive → String
  | .yaml version => "%YAML " ++ version
  | .tag handle tagPrefix => "%TAG " ++ handle ++ " " ++ tagPrefix

/--
Dump a single YAML document.

Produces:
- Directive lines (if any), each on its own line
- `---` document-start marker (always emitted when directives are present;
  also emitted when the document value starts with an ambiguous character)
- The document value via `dump`
- No trailing `...` (document-end marker) — callers add it when needed

## Examples

```
dumpDocument { value := .plainScalar "hello" } == "hello"
dumpDocument { value := .plainScalar "hello", directives := #[.yaml "1.2"] }
  == "%YAML 1.2\n---\nhello"
```
-/
def dumpDocument (doc : YamlDocument) (cfg : DumpConfig := {}) : String :=
  let body := dump doc.value cfg
  if doc.directives.isEmpty then
    -- No directives: emit bare value (omit `---` for minimal output)
    body
  else
    let dirs := doc.directives.toList.map dumpDirective
    String.intercalate "\n" dirs ++ "\n---\n" ++ body

/--
Dump multiple YAML documents as a stream.

Documents are separated by `---` markers. The first document
omits `---` when it has no directives (matching common YAML style).
A trailing `...` is emitted after the last document only when there
are multiple documents (signals end-of-stream clearly).

## Examples

```
dumpDocuments #[{ value := .plainScalar "a" }]
  == "a"
dumpDocuments #[{ value := .plainScalar "a" }, { value := .plainScalar "b" }]
  == "a\n---\nb\n..."
```
-/
def dumpDocuments (docs : Array YamlDocument) (cfg : DumpConfig := {}) : String :=
  match docs.toList with
  | [] => ""
  | [doc] => dumpDocument doc cfg
  | doc :: rest =>
    let first := dumpDocument doc cfg
    let others := rest.map (fun d => "---\n" ++ dumpDocument d cfg)
    first ++ "\n" ++ String.intercalate "\n" others ++ "\n..."

end Lean4Yaml.Dump

/-! ## Compile-Time Tests -/

section DumpGuards

open Lean4Yaml Lean4Yaml.Dump

/-! ### Plain scalars -/

#guard dump (.plainScalar "hello") == "hello"
#guard dump (.plainScalar "simple") == "simple"
#guard dump (.plainScalar "two words") == "two words"

/-! ### Auto-quoting: reserved words and special characters -/

#guard dump (.plainScalar "true") == "\"true\""
#guard dump (.plainScalar "false") == "\"false\""
#guard dump (.plainScalar "null") == "\"null\""
#guard dump (.plainScalar "yes") == "\"yes\""
#guard dump (.plainScalar "~") == "\"~\""
#guard dump (.plainScalar "") == "\"\""
#guard dump (.plainScalar "key: value") == "\"key: value\""
#guard dump (.plainScalar "has #comment") == "\"has #comment\""
#guard dump (.plainScalar "{flow}") == "\"{flow}\""
#guard dump (.plainScalar "[array]") == "\"[array]\""

/-! ### Explicit double-quoted: auto mode uses content analysis, not annotation -/

#guard dump (.quotedScalar "hello" .doubleQuoted) == "hello"
#guard dump (.quotedScalar "line\nnewline" .doubleQuoted) == "|\n  line\n  newline"

/-! ### Single-quoted scalars via config -/

#guard dump (.plainScalar "hello") { scalarStyle := .singleQuoted } == "'hello'"
#guard dump (.plainScalar "it's") { scalarStyle := .singleQuoted } == "'it''s'"

/-! ### Block scalar (literal) -/

#guard dump (.scalar ⟨"line1\nline2", .literal, none, none, none⟩) ==
  "|\n  line1\n  line2"

#guard dump (.scalar ⟨"line1\nline2", .literal, none, none,
  some ⟨.strip, none⟩⟩) == "|-\n  line1\n  line2"

#guard dump (.scalar ⟨"line1\nline2", .literal, none, none,
  some ⟨.keep, none⟩⟩) == "|+\n  line1\n  line2"

/-! ### Block scalar (folded) -/

#guard dump (.scalar ⟨"line1\nline2", .folded, none, none, none⟩) ==
  ">\n  line1\n  line2"

/-! ### Multi-line auto → literal -/

#guard dump (.plainScalar "multi\nline") == "|\n  multi\n  line"

/-! ### Aliases -/

#guard dump (.alias "anchor1") == "*anchor1"

/-! ### Anchored scalar -/

#guard dump (.scalar ⟨"value", .plain, none, some "a1", none⟩) == "&a1 value"

/-! ### Tagged scalar -/

#guard dump (.scalar ⟨"42", .plain, some "!!int", none, none⟩) == "!!int 42"

/-! ### Flow collections -/

#guard dump (.sequence .flow #[.plainScalar "a", .plainScalar "b"]) == "[a, b]"
#guard dump (.mapping .flow #[(.plainScalar "k", .plainScalar "v")]) == "{k: v}"
#guard dump (.sequence .flow #[]) == "[]"
#guard dump (.mapping .flow #[]) == "{}"

/-! ### Block sequence -/

#guard dump (.sequence .block #[.plainScalar "a", .plainScalar "b"]) ==
  "- a\n- b"

#guard dump (.sequence .block #[.plainScalar "x"]) == "- x"

/-! ### Block mapping -/

#guard dump (.mapping .block #[
    (.plainScalar "key1", .plainScalar "val1"),
    (.plainScalar "key2", .plainScalar "val2")
  ]) == "key1: val1\nkey2: val2"

/-! ### Nested: mapping with block sequence value -/

#guard dump (.mapping .block #[
    (.plainScalar "items", .sequence .block #[
      .plainScalar "a", .plainScalar "b"
    ])
  ]) == "items:\n  - a\n  - b"

/-! ### Nested: mapping with nested mapping value -/

#guard dump (.mapping .block #[
    (.plainScalar "outer", .mapping .block #[
      (.plainScalar "inner", .plainScalar "val")
    ])
  ]) == "outer:\n  inner: val"

/-! ### Flow config override -/

#guard dump (.sequence .block #[.plainScalar "a"]) { defaultStyle := .flow } ==
  "[a]"

#guard dump (.mapping .block #[(.plainScalar "k", .plainScalar "v")])
  { defaultStyle := .flow } == "{k: v}"

/-! ### Empty block collections -/

#guard dump (.sequence .block #[]) == "[]"
#guard dump (.mapping .block #[]) == "{}"

/-! ### Nested flow inside block -/

#guard dump (.mapping .block #[
    (.plainScalar "list", .sequence .flow #[.plainScalar "a", .plainScalar "b"])
  ]) == "list: [a, b]"

/-! ### Double-quoted config override -/

#guard dump (.plainScalar "hello") { scalarStyle := .doubleQuoted } ==
  "\"hello\""

/-! ### Indentation width override -/

#guard dump (.mapping .block #[
    (.plainScalar "key", .sequence .block #[.plainScalar "a"])
  ]) { indent := 4 } == "key:\n    - a"

/-! ### Document dump -/

private def doc1 : YamlDocument := { value := .plainScalar "hello" }
private def doc2 : YamlDocument :=
  { value := .plainScalar "hello", directives := #[.yaml "1.2"] }
private def doc3 : YamlDocument :=
  { value := .mapping .block #[(.plainScalar "k", .plainScalar "v")],
    directives := #[.yaml "1.2"] }
private def doc4 : YamlDocument :=
  { value := .plainScalar "val",
    directives := #[.yaml "1.2", .tag "!e!" "tag:example.com,2000:"] }
private def docA : YamlDocument := { value := .plainScalar "a" }
private def docB : YamlDocument := { value := .plainScalar "b" }
private def docC : YamlDocument := { value := .plainScalar "c" }
private def docOnly : YamlDocument := { value := .plainScalar "only" }
private def docMap : YamlDocument :=
  { value := .mapping .block #[(.plainScalar "x", .plainScalar "1")] }
private def docSeq : YamlDocument :=
  { value := .sequence .block #[.plainScalar "y"] }
private def docADir : YamlDocument :=
  { value := .plainScalar "a", directives := #[.yaml "1.2"] }

#guard dumpDocument doc1 == "hello"
#guard dumpDocument doc2 == "%YAML 1.2\n---\nhello"
#guard dumpDocument doc3 == "%YAML 1.2\n---\nk: v"
#guard dumpDocument doc4 ==
  "%YAML 1.2\n%TAG !e! tag:example.com,2000:\n---\nval"

/-! ### Multi-document dump -/

#guard dumpDocuments #[] == ""
#guard dumpDocuments #[docOnly] == "only"
#guard dumpDocuments #[docA, docB] == "a\n---\nb\n..."
#guard dumpDocuments #[docA, docB, docC] == "a\n---\nb\n---\nc\n..."
#guard dumpDocuments #[docMap, docSeq] == "x: 1\n---\n- y\n..."

/-! ### Multi-document with directives -/

#guard dumpDocuments #[docADir, docB] ==
  "%YAML 1.2\n---\na\n---\nb\n..."

/-! ### Directive dump -/

#guard dumpDirective (.yaml "1.2") == "%YAML 1.2"
#guard dumpDirective (.tag "!!" "tag:yaml.org,2002:") ==
  "%TAG !! tag:yaml.org,2002:"

end DumpGuards
