import Lean.Data.Json
import L4YAML.Spec.Types

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

namespace L4YAML.Dump

open Lean L4YAML

/-! ## Style Preferences -/

/--
Dump context: tracks whether we are currently emitting inside a flow
collection or at block level. Threaded through `dumpValue` so that
`chooseScalarStyle` and `resolveCollectionStyle` can make context-aware
decisions.

- `block`: top-level or inside a block collection
- `flowIn`: inside a flow sequence or flow mapping value position
- `flowKey`: inside a flow mapping key position
-/
inductive DumpContext where
  | block
  | flowIn
  | flowKey
  deriving Repr, BEq, Inhabited, DecidableEq

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
  /-- Allow YAML reserved words (`true`, `false`, `null`, `yes`, `no`, `~`)
      to be emitted as plain scalars without quoting.
      When `false` (default), reserved words are double-quoted for safety.
      Set to `true` when the consumer (e.g., YAML 1.2 core schema) can
      distinguish booleans/nulls from strings by context. -/
  allowReservedPlain : Bool := false
  /-- Omit mapping fields whose values are empty sequences (`[]`) or
      empty mappings (`{}`). Useful for producing minimal YAML output
      that omits default-valued collection fields. -/
  omitEmpty : Bool := false
  /-- Use compact block collection notation for sequences of mappings.
      When `true`, a block mapping item in a block sequence is rendered
      as `- key: value` (compact) instead of the expanded form with `-`
      on its own line.  The compact form is the conventional YAML style
      used by most serializers and config files. -/
  compactSequenceMap : Bool := false
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
    let allowReservedPlain := match json.getObjValAs? Bool "allowReservedPlain" with
      | .ok v => v | _ => false
    let omitEmpty := match json.getObjValAs? Bool "omitEmpty" with
      | .ok v => v | _ => false
    let compactSequenceMap := match json.getObjValAs? Bool "compactSequenceMap" with
      | .ok v => v | _ => false
    .ok { indent, defaultStyle, scalarStyle, lineWidth, sortKeys,
          allowReservedPlain, omitEmpty, compactSequenceMap }

/-! ## Private Helpers -/

/-- Build an indentation string: `depth × width` spaces. -/
def makeIndent (depth : Nat) (width : Nat) : String :=
  String.ofList (List.replicate (depth * width) ' ')

/--
Escape a character for double-quoted YAML scalars (§5.7).

Same table as `Emit.escapeChar`; duplicated here to avoid a
dependency cycle (`Dump` imports only `Types`).
-/
def escapeChar (c : Char) : String :=
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
def escapeString (s : String) : String :=
  s.foldl (fun acc c => acc ++ escapeChar c) ""

/-- Emit a double-quoted scalar. -/
def dumpDoubleQuoted (s : String) : String :=
  "\"" ++ escapeString s ++ "\""

/-- Emit a single-quoted scalar. Only `'` is escaped (as `''`). -/
def dumpSingleQuoted (s : String) : String :=
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

/-- Determine if string content is safe for plain scalar style.
    When `allowReserved` is `true`, reserved words like `true`, `false`, `null`
    are treated as plain-safe (useful for boolean/null values that should
    not be quoted). -/
def isPlainSafe (s : String) (allowReserved : Bool := false) : Bool :=
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
      -- Must not have leading/trailing whitespace or trailing `:`
      -- Trailing `:` is interpreted as a mapping value indicator (§7.3.3)
      c != ' ' && c != '\t' &&
      (match chars.getLast? with
       | some last => last != ' ' && last != '\t' && last != ':'
       | none => true) &&
      -- Must not be a reserved word (unless allowed)
      (allowReserved || !isReservedWord s)

/-- Check if string contains newlines. -/
def hasNewlines (s : String) : Bool :=
  s.any (· == '\n')

/-- Check if string content is unsafe as a plain scalar in flow context.
    Flow context forbids additional characters beyond what `isPlainSafe` checks:
    - Any `:` (not just `: `), since `:` followed by `,`, `}`, `]` is a mapping indicator
    - Trailing `-` or trailing space (block indicator ambiguity)
    See YAML §7.3.3 [128] ns-plain-safe(flow-in). -/
def isFlowUnsafe (s : String) : Bool :=
  s.any (· == ':') ||
  (match s.toList.getLast? with
   | some c => c == '-' || c == ' '
   | none => false)

/-- Choose effective scalar style based on content, config, and dump context.
    In flow context, additional characters require quoting (see `isFlowUnsafe`). -/
def chooseScalarStyle (s : Scalar) (cfg : DumpConfig)
    (ctx : DumpContext := .block) : ScalarStyle :=
  -- Honor explicit block scalar style when content has newlines AND we're in block context
  if (s.style == .literal || s.style == .folded) && hasNewlines s.content
      && ctx == .block then
    s.style
  else match cfg.scalarStyle with
    | .doubleQuoted => .doubleQuoted
    | .singleQuoted =>
      -- Single-quoted cannot represent newlines
      if hasNewlines s.content then .doubleQuoted else .singleQuoted
    | .plain =>
      if isPlainSafe s.content cfg.allowReservedPlain &&
          (ctx == .block || !isFlowUnsafe s.content) then
        .plain
      else .doubleQuoted
    | .auto =>
      if s.content.isEmpty then .doubleQuoted
      else if hasNewlines s.content then
        if ctx != .block then
          -- Flow context: block scalars are invalid, force double-quoted
          .doubleQuoted
        else
          -- Block context: use block scalar style from annotation, or default to literal
          if s.style == .literal || s.style == .folded then s.style else .literal
      else if isPlainSafe s.content cfg.allowReservedPlain &&
              (ctx == .block || !isFlowUnsafe s.content) then
        .plain
      else .doubleQuoted

/-- Resolve collection style from node annotation, config, and dump context.
    When context is flow, block collections are forced to flow (YAML §8.1
    forbids block collections inside flow context). -/
def resolveCollectionStyle (nodeStyle : CollectionStyle) (cfg : DumpConfig)
    (ctx : DumpContext := .block) : CollectionStyle :=
  -- Flow context: always force flow style regardless of annotation or config
  if ctx == .flowIn || ctx == .flowKey then .flow
  else match cfg.defaultStyle with
  | .flow => .flow
  | .block => nodeStyle
  | .auto => nodeStyle

/--
Emit a block scalar (literal `|` or folded `>`).

Returns the header + newline + indented content lines.
Content lines are indented at `max(1, depth) × indentWidth` spaces
to satisfy YAML's minimum 1-space content indent requirement.
-/
def dumpBlockScalar (content : String) (indicator : String)
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
def nodePrefix (tag : Option String) (anchor : Option String) : String :=
  let t := match tag with | some t => t | none => ""
  let a := match anchor with | some n => "&" ++ n | none => ""
  match t.isEmpty, a.isEmpty with
  | true, true => ""
  | true, false => a
  | false, true => t
  | false, false => t ++ " " ++ a

/-- Check if a value is an empty collection (sequence or mapping with no items). -/
def isEmptyCollection : YamlValue → Bool
  | .sequence _ items .. => items.isEmpty
  | .mapping _ pairs .. => pairs.isEmpty
  | _ => false

/-- Check if a value renders as a single line (can follow `- ` or `key: `). -/
def isInlineValue : YamlValue → Bool
  | .scalar _ => true
  | .alias _ => true
  | .sequence .flow _ .. => true
  | .mapping .flow _ .. => true
  | _ => false

/-- Check if a value is a block mapping (eligible for compact
    sequence notation where the first key shares the `- ` line). -/
def isCompactableMapping : YamlValue → Bool
  | .mapping .block _ _ _ => true
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
  dumpValue v cfg 0 .block
where
  /-- Dump a value. First line unindented; continuation lines at `depth`.
      `ctx` tracks whether we are inside a flow collection. -/
  dumpValue : YamlValue → DumpConfig → Nat → DumpContext → String
    | .scalar s, cfg, depth, ctx =>
      let anchorStr := match s.anchor with | some n => "&" ++ n ++ " " | none => ""
      let tagStr := match s.tag with | some t => t ++ " " | none => ""
      let pfx := tagStr ++ anchorStr
      let effectiveStyle := chooseScalarStyle s cfg ctx
      let body := match effectiveStyle with
        | .plain => s.content
        | .doubleQuoted => dumpDoubleQuoted s.content
        | .singleQuoted => dumpSingleQuoted s.content
        | .literal => dumpBlockScalar s.content "|" s.blockMeta depth cfg.indent
        | .folded => dumpBlockScalar s.content ">" s.blockMeta depth cfg.indent
      pfx ++ body
    | .alias name, _, _, _ => "*" ++ name
    | .sequence style items tag anchor, cfg, depth, ctx =>
      let npfx := nodePrefix tag anchor
      let effectiveStyle := resolveCollectionStyle style cfg ctx
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
    | .mapping style pairs tag anchor, cfg, depth, ctx =>
      let npfx := nodePrefix tag anchor
      let effectiveStyle := resolveCollectionStyle style cfg ctx
      match effectiveStyle with
      | .flow =>
        let hdr := if npfx.isEmpty then "" else npfx ++ " "
        hdr ++ "{" ++ dumpFlowPairs pairs.toList cfg depth ++ "}"
      | .block =>
        if pairs.isEmpty then
          (if npfx.isEmpty then "" else npfx ++ " ") ++ "{}"
        else
          let result := dumpBlockPairs pairs.toList cfg depth true
          -- When omitEmpty filters out all pairs, emit empty mapping
          if result.isEmpty then
            (if npfx.isEmpty then "" else npfx ++ " ") ++ "{}"
          else if npfx.isEmpty then
            result
          else
            npfx ++ "\n" ++ makeIndent depth cfg.indent ++ result
  /-- Comma-separated flow list items (always in flow context). -/
  dumpFlowList : List YamlValue → DumpConfig → Nat → String
    | [], _, _ => ""
    | [v], cfg, depth => dumpValue v cfg depth .flowIn
    | v :: vs, cfg, depth => dumpValue v cfg depth .flowIn ++ ", " ++ dumpFlowList vs cfg depth
  /-- Comma-separated flow mapping pairs (keys in flowKey context, values in flowIn). -/
  dumpFlowPairs : List (YamlValue × YamlValue) → DumpConfig → Nat → String
    | [], _, _ => ""
    | [(k, v)], cfg, depth =>
      dumpValue k cfg depth .flowKey ++ ": " ++ dumpValue v cfg depth .flowIn
    | (k, v) :: rest, cfg, depth =>
      dumpValue k cfg depth .flowKey ++ ": " ++ dumpValue v cfg depth .flowIn ++ ", " ++
        dumpFlowPairs rest cfg depth
  /-- Block sequence items. `first = true` suppresses indent on first line.
      When `cfg.compactSequenceMap` is true, non-empty block mapping items
      share the `- ` line with their first key (compact notation). -/
  dumpBlockList : List YamlValue → DumpConfig → Nat → Bool → String
    | [], _, _, _ => ""
    | [v], cfg, depth, first =>
      let ind := if first then "" else makeIndent depth cfg.indent
      if isInlineValue v ||
          (cfg.compactSequenceMap && isCompactableMapping v) then
        ind ++ "- " ++ dumpValue v cfg (depth + 1) .block
      else
        ind ++ "-\n" ++ makeIndent (depth + 1) cfg.indent ++
          dumpValue v cfg (depth + 1) .block
    | v :: vs, cfg, depth, first =>
      let ind := if first then "" else makeIndent depth cfg.indent
      let item :=
        if isInlineValue v ||
            (cfg.compactSequenceMap && isCompactableMapping v) then
          ind ++ "- " ++ dumpValue v cfg (depth + 1) .block
        else
          ind ++ "-\n" ++ makeIndent (depth + 1) cfg.indent ++
            dumpValue v cfg (depth + 1) .block
      item ++ "\n" ++ dumpBlockList vs cfg depth false
  /-- Block mapping pairs. `first = true` suppresses indent on first line.
      When `cfg.omitEmpty` is true, pairs whose value is an empty collection
      are silently skipped. -/
  dumpBlockPairs : List (YamlValue × YamlValue) → DumpConfig → Nat → Bool → String
    | [], _, _, _ => ""
    | [(k, v)], cfg, depth, first =>
      if cfg.omitEmpty && isEmptyCollection v then ""
      else
        let ind := if first then "" else makeIndent depth cfg.indent
        if isInlineValue v then
          ind ++ dumpValue k cfg depth .block ++ ": " ++ dumpValue v cfg (depth + 1) .block
        else
          ind ++ dumpValue k cfg depth .block ++ ":\n" ++
            makeIndent (depth + 1) cfg.indent ++ dumpValue v cfg (depth + 1) .block
    | (k, v) :: rest, cfg, depth, first =>
      if cfg.omitEmpty && isEmptyCollection v then
        dumpBlockPairs rest cfg depth first
      else
        let ind := if first then "" else makeIndent depth cfg.indent
        let pair :=
          if isInlineValue v then
            ind ++ dumpValue k cfg depth .block ++ ": " ++ dumpValue v cfg (depth + 1) .block
          else
            ind ++ dumpValue k cfg depth .block ++ ":\n" ++
              makeIndent (depth + 1) cfg.indent ++ dumpValue v cfg (depth + 1) .block
        let tail := dumpBlockPairs rest cfg depth false
        if tail.isEmpty then pair
        else pair ++ "\n" ++ tail

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

end L4YAML.Dump

/-! ## Comment-Aware Dump

Extension of the style-aware dump that preserves comments from the
`YamlDocument.comments` side-channel. Comments are emitted at their
classified position:

- `.before` → `# text\n` lines before the associated content
- `.inline` → ` # text` appended to the end of the value's first line
- `.after`  → `# text\n` lines after the associated content

For document-level output, before-comments appear before `---` (or the value),
inline comments follow the first content line, and after-comments trail the value.
-/

namespace L4YAML.Dump

open L4YAML

/-- Emit a single comment as a `# text` line (no trailing newline). -/
def dumpCommentLine (c : Comment) : String :=
  "#" ++ c.text

/-- Emit comment lines with a given position filter.
    Returns `""` when no comments match. -/
def dumpCommentsOfPosition (comments : Array (YamlPos × Comment))
    (pos : CommentPosition) : String :=
  let matching := comments.filter fun (_, c) => c.position == pos
  if matching.isEmpty then ""
  else
    let lines := matching.toList.map fun (_, c) => dumpCommentLine c
    String.intercalate "\n" lines ++ "\n"

/--
Dump a YAML document with comments preserved.

Like `dumpDocument` but integrates comments from `doc.comments`:
- **Before** comments appear before the value (or directives + `---`)
- **Inline** comments are appended to the first content line
- **After** comments appear after the value body

When the document has no comments, the output is identical to `dumpDocument`.
-/
def dumpDocumentWithComments (doc : YamlDocument) (cfg : DumpConfig := {}) : String :=
  if doc.comments.isEmpty then
    dumpDocument doc cfg
  else
    let beforeStr := dumpCommentsOfPosition doc.comments .before
    let afterStr := dumpCommentsOfPosition doc.comments .after
    let inlineComments := doc.comments.filter fun (_, c) => c.position == .inline
    let body := dump doc.value cfg
    -- Append inline comments to the first line of the body
    let bodyWithInline :=
      if inlineComments.isEmpty then body
      else
        let inlineSuffix := String.intercalate " " <|
          inlineComments.toList.map fun (_, c) => " " ++ dumpCommentLine c
        -- Find the first newline and insert inline comment before it
        match body.splitOn "\n" with
        | [] => body ++ inlineSuffix
        | [single] => single ++ inlineSuffix
        | first :: rest => first ++ inlineSuffix ++ "\n" ++ String.intercalate "\n" rest
    if doc.directives.isEmpty then
      beforeStr ++ bodyWithInline ++ (if afterStr.isEmpty then "" else "\n" ++ afterStr)
    else
      let dirs := doc.directives.toList.map dumpDirective
      beforeStr ++ String.intercalate "\n" dirs ++ "\n---\n" ++ bodyWithInline ++
        (if afterStr.isEmpty then "" else "\n" ++ afterStr)

/--
Dump multiple YAML documents with comments preserved.

Like `dumpDocuments` but uses `dumpDocumentWithComments` for each document.
-/
def dumpDocumentsWithComments (docs : Array YamlDocument) (cfg : DumpConfig := {}) : String :=
  match docs.toList with
  | [] => ""
  | [doc] => dumpDocumentWithComments doc cfg
  | doc :: rest =>
    let first := dumpDocumentWithComments doc cfg
    let others := rest.map (fun d => "---\n" ++ dumpDocumentWithComments d cfg)
    first ++ "\n" ++ String.intercalate "\n" others ++ "\n..."

end L4YAML.Dump

/-! ## Compile-Time Tests -/

section DumpGuards

open L4YAML L4YAML.Dump

/-! ### Plain scalars -/


/-! ### Auto-quoting: reserved words and special characters -/


/-! ### allowReservedPlain: reserved words emitted unquoted -/


/-! ### Explicit double-quoted: auto mode uses content analysis, not annotation -/


/-! ### Single-quoted scalars via config -/


/-! ### Block scalar (literal) -/


/-! ### Block scalar (folded) -/


/-! ### Multi-line auto → literal -/


/-! ### Aliases -/


/-! ### Anchored scalar -/


/-! ### Tagged scalar -/


/-! ### Flow collections -/


/-! ### Block sequence -/


/-! ### Block mapping -/


/-! ### Nested: mapping with block sequence value -/


/-! ### Nested: mapping with nested mapping value -/


/-! ### Flow config override -/


/-! ### Empty block collections -/


/-! ### omitEmpty: empty collection fields are omitted -/


/-! ### Nested flow inside block -/


/-! ### Double-quoted config override -/


/-! ### Indentation width override -/


/-! ### Document dump -/


/-! ### Multi-document dump -/


/-! ### Multi-document with directives -/


/-! ### Directive dump -/


/-! ### compactSequenceMap: block mapping items share the `- ` line -/


end DumpGuards
