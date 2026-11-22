module

public import Lean.Data.Json
public import L4YAML.Spec.Types
public import L4YAML.Spec.CharPredicates
public import L4YAML.Schema.Schema

@[expose] public section Blanket

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
- `preserve`: honor each node's own `Scalar.style` when representable
  (falling back like `auto` where it is not). Content-based styles
  (`auto`) re-quote from scratch, which changes the TYPE a core-schema
  consumer resolves: a parsed `'42'` re-emitted plain reads back as an
  integer. `preserve` keeps quoted scalars quoted; combine with
  `allowReservedPlain := true` so plain `true`/`null` also stay plain.
-/
inductive ScalarPref where
  | plain
  | doubleQuoted
  | singleQuoted
  | auto
  | preserve
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
  /-- Emit a plain scalar tagged `!!null`/`!!bool`/`!!int`/`!!float` whose content
      already resolves to that type under the Core Schema as the bare scalar
      (`true`, `null`, `-7`): the tag is redundant for a Core Schema reader, and
      the reserved-word quoting does not apply because the value is not a
      string.  This is how `toYaml` marks non-string primitives.  When `false`
      the tag is written out (`!!bool true`). -/
  plainCoreScalars : Bool := true
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
    let plainCoreScalars := match json.getObjValAs? Bool "plainCoreScalars" with
      | .ok v => v | _ => true
    .ok { indent, defaultStyle, scalarStyle, lineWidth, sortKeys,
          allowReservedPlain, omitEmpty, compactSequenceMap, plainCoreScalars }

/-! ## Private Helpers -/

/-- Build an indentation string: `depth × width` spaces. -/
def makeIndent (depth : Nat) (width : Nat) : String :=
  "".pushn ' ' (depth * width)

/--
Append the double-quoted escape of `c` (§5.7) to `acc`.

Same table as `Emit.escapeChar`; duplicated here to avoid a
dependency cycle (`Dump` imports only `Types`).  Printable characters
are pushed in place rather than going through a one-character `String`.
-/
def pushEscaped (acc : String) (c : Char) : String :=
  match c with
  | '\x00' => acc ++ "\\0"
  | '\x07' => acc ++ "\\a"
  | '\x08' => acc ++ "\\b"
  | '\t'   => acc ++ "\\t"
  | '\n'   => acc ++ "\\n"
  | '\x0b' => acc ++ "\\v"
  | '\x0c' => acc ++ "\\f"
  | '\r'   => acc ++ "\\r"
  | '\x1b' => acc ++ "\\e"
  | '\\'   => acc ++ "\\\\"
  | '"'    => acc ++ "\\\""
  | c      =>
    if CharPredicates.isPrintableBool c then acc.push c
    else
      -- Non-printable (c-printable [1] excluded): YAML §5.7 numeric escapes.
      -- Raw controls are invalid inside double quotes (nb-json [2]), so the
      -- scanner would reject them; escape by code point instead.
      let hex := fun (n w : Nat) =>
        let ds := String.ofList ((Nat.toDigits 16 n).map Char.toUpper)
        String.ofList (List.replicate (w - ds.length) '0') ++ ds
      if c.toNat ≤ 0xFF then acc ++ "\\x" ++ hex c.toNat 2
      else if c.toNat ≤ 0xFFFF then acc ++ "\\u" ++ hex c.toNat 4
      else acc ++ "\\U" ++ hex c.toNat 8

/-- Escape a character for double-quoted YAML scalars (§5.7). -/
def escapeChar (c : Char) : String :=
  pushEscaped "" c

/-- Escape a string for double-quoted context. -/
def escapeString (s : String) : String :=
  s.foldl pushEscaped ""

/-- Append `s` as a double-quoted scalar to `acc`. -/
def pushDoubleQuoted (acc : String) (s : String) : String :=
  (s.foldl pushEscaped (acc.push '"')).push '"'

/-- Emit a double-quoted scalar. -/
def dumpDoubleQuoted (s : String) : String :=
  pushDoubleQuoted "" s

/-- Append `s` as a single-quoted scalar to `acc`. Only `'` is escaped (as `''`). -/
def pushSingleQuoted (acc : String) (s : String) : String :=
  (s.foldl (fun acc c => if c == '\'' then acc ++ "''" else acc.push c) (acc.push '\'')).push '\''

/-- Emit a single-quoted scalar. Only `'` is escaped (as `''`). -/
def dumpSingleQuoted (s : String) : String :=
  pushSingleQuoted "" s

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

/-- Check if string contains `: ` or ` #` (unsafe in plain scalars).
    One pass; state = previous char was `:` (1) / space (2), or matched (3). -/
def hasUnsafeSubsequence (s : String) : Bool :=
  s.foldl step 0 == 3
where
  step (st : UInt8) (c : Char) : UInt8 :=
    if st == 3 then 3
    else if (st == 1 && c == ' ') || (st == 2 && c == '#') then 3
    else if c == ':' then 1
    else if c == ' ' then 2
    else 0

/-- Determine if string content is safe for plain scalar style.
    When `allowReserved` is `true`, reserved words like `true`, `false`, `null`
    are treated as plain-safe (useful for boolean/null values that should
    not be quoted). -/
def isPlainSafe (s : String) (allowReserved : Bool := false) : Bool :=
  if s.isEmpty then false
  else
    let c := s.front
    let last := s.back
    -- First character must not be a YAML indicator
    !isIndicator c &&
    -- Must not contain flow indicators or newlines; every char must be
    -- ns-char [34] eligible (printable, not BOM) or the scanner would
    -- terminate the plain scalar early on read-back
    !s.any (fun ch => ch == '{' || ch == '}' || ch == '[' || ch == ']' ||
                       ch == ',' || ch == '\n' || ch == '\r' ||
                       ch == '﻿' || !CharPredicates.isPrintableBool ch) &&
    -- Must not contain `: ` or ` #`
    !hasUnsafeSubsequence s &&
    -- Must not have leading/trailing whitespace or trailing `:`
    -- Trailing `:` is interpreted as a mapping value indicator (§7.3.3)
    c != ' ' && c != '\t' &&
    last != ' ' && last != '\t' && last != ':' &&
    -- Must not be a reserved word (unless allowed)
    (allowReserved || !isReservedWord s)

/-- A plain scalar whose Core Schema tag (`!!null`/`!!bool`/`!!int`/`!!float`) says
    exactly what implicit resolution of its content would say anyway, and whose
    content can be written plain.  Such a scalar may be emitted bare: a Core
    Schema reader recovers the same type, and quoting (which would make it a
    string) must not happen. -/
def isRedundantCoreTag (s : Scalar) : Bool :=
  s.style == .plain &&
  (match s.tag with
   | some t =>
     let ty := Schema.resolveImplicit s.content
     match Schema.normalizeTag t with
     | "tag:yaml.org,2002:null"  => ty.isNull
     | "tag:yaml.org,2002:bool"  => ty.isBool
     | "tag:yaml.org,2002:int"   => ty.isInt
     | "tag:yaml.org,2002:float" => ty.isFloat
     | _ => false
   | none => false)

/-- An untagged scalar whose own style is not plain means a *string* (§10.3.2);
    writing it plain would hand its content to implicit resolution, so plain is
    allowed only when that resolution is a string anyway.  (`toYaml "42"` is such
    a scalar: it must come out as `"42"`, not `42`.) -/
def plainWouldRetype (s : Scalar) : Bool :=
  s.style != .plain && s.tag.isNone && !(Schema.resolveImplicit s.content).isStr

/-- Check if string contains newlines. -/
def hasNewlines (s : String) : Bool :=
  s.any (· == '\n')

/-- `ns-plain-first` refinement used only by `ScalarPref.preserve`:
    `isPlainSafe` rejects every leading indicator, but YAML [126]
    permits a leading `-` when followed by a non-space character
    (`-1`, `-.inf`). Without this, a parsed plain `-1` would be
    re-emitted quoted — changing its core-schema type to string.
    Kept separate from `isPlainSafe` so the existing prefs (and the
    output calibrated to them) are untouched. -/
def isPlainSafePreserve (s : String) (allowReserved : Bool := false) : Bool :=
  isPlainSafe s allowReserved ||
  (s.front == '-' &&
    (let rest := (s.drop 1).toString
     !rest.isEmpty && rest.front != ' ' && rest.front != '\t' &&
       isPlainSafe rest allowReserved))

/-- Whether `s` can be written plain without changing what it means.  For an
    untagged plain scalar whose content resolves to a non-string (`-7`, `-1.5`,
    `-.inf`), the leading sign YAML [126] allows is accepted, since quoting it
    would turn the number into a string; everything else goes through
    `isPlainSafe` unchanged. -/
def plainKeepsType (s : Scalar) (allowReserved : Bool) : Bool :=
  if s.style == .plain && s.tag.isNone && !(Schema.resolveImplicit s.content).isStr then
    isPlainSafePreserve s.content allowReserved
  else
    isPlainSafe s.content allowReserved && !plainWouldRetype s

/-- Whether content can be carried VERBATIM inside single quotes:
    printable characters only (plus tab; C0, DEL, and C1 excluded per
    c-printable §5.1). A raw CR reparses as line folding (silent
    corruption) and other controls are invalid YAML there;
    double-quoting escapes them instead. -/
def singleQuotedRepresentable (s : String) : Bool :=
  s.all (fun c => c == '\t' ||
    (0x20 ≤ c.toNat && c.toNat != 0x7F &&
     !(0x80 ≤ c.toNat && c.toNat ≤ 0x9F)))

/-- Whether content can be carried VERBATIM in a literal/folded block
    scalar: every character must be `nb-char` [27] (printable, not BOM)
    or LF. A raw CR would be normalized by `b-break` on re-scan (silent
    corruption) and other non-printables are invalid YAML there;
    double-quoting escapes them instead. -/
def blockScalarRepresentable (s : String) : Bool :=
  s.all (fun c => c == '\n' ||
    (CharPredicates.isPrintableBool c && c != '﻿'))

/-- Check if string content is unsafe as a plain scalar in flow context.
    Flow context forbids additional characters beyond what `isPlainSafe` checks:
    - Any `:` (not just `: `), since `:` followed by `,`, `}`, `]` is a mapping indicator
    - Trailing `-` or trailing space (block indicator ambiguity)
    See YAML §7.3.3 [128] ns-plain-safe(flow-in). -/
def isFlowUnsafe (s : String) : Bool :=
  s.any (· == ':') ||
  (!s.isEmpty && (s.back == '-' || s.back == ' '))

/-- Choose effective scalar style based on content, config, and dump context.
    In flow context, additional characters require quoting (see `isFlowUnsafe`). -/
def chooseScalarStyle (s : Scalar) (cfg : DumpConfig)
    (ctx : DumpContext := .block) : ScalarStyle :=
  -- Honor explicit block scalar style when content has newlines AND we're in block context
  if (s.style == .literal || s.style == .folded) && hasNewlines s.content
      && ctx == .block && blockScalarRepresentable s.content then
    s.style
  else match cfg.scalarStyle with
    | .doubleQuoted => .doubleQuoted
    | .singleQuoted =>
      -- Single-quoted cannot represent newlines or non-printables
      if hasNewlines s.content || !singleQuotedRepresentable s.content then
        .doubleQuoted
      else .singleQuoted
    | .plain =>
      if plainKeepsType s cfg.allowReservedPlain &&
          (ctx == .block || !isFlowUnsafe s.content) then
        .plain
      else .doubleQuoted
    | .auto =>
      if s.content.isEmpty then .doubleQuoted
      else if hasNewlines s.content then
        if ctx != .block || !blockScalarRepresentable s.content then
          -- Flow context (block scalars invalid) or content a block scalar
          -- cannot carry verbatim (nb-char [27]): force double-quoted
          .doubleQuoted
        else
          -- Block context: use block scalar style from annotation, or default to literal
          if s.style == .literal || s.style == .folded then s.style else .literal
      else if plainKeepsType s cfg.allowReservedPlain &&
              (ctx == .block || !isFlowUnsafe s.content) then
        .plain
      else .doubleQuoted
    | .preserve =>
      -- Honor the node's own quoting style when representable.
      match s.style with
      | .doubleQuoted => .doubleQuoted
      | .singleQuoted =>
        -- Newlines/controls cannot be carried verbatim in single quotes
        if singleQuotedRepresentable s.content then .singleQuoted
        else .doubleQuoted
      | .plain =>
        if !hasNewlines s.content &&
            isPlainSafePreserve s.content cfg.allowReservedPlain &&
            (ctx == .block || !isFlowUnsafe s.content) then
          .plain
        else .doubleQuoted
      | _ =>
        -- A literal/folded style NOT honored by the outer newline+block
        -- case (no newline in content, or flow context): block scalars
        -- always resolve to strings (§10.3.2), so quote — re-emitting
        -- plain could flip the type (`>- 42` must not become `42`).
        .doubleQuoted

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
Append a block scalar (literal `|` or folded `>`) to `acc`.

Writes the header + newline + indented content lines.
Content lines are indented at `max(1, depth) × indentWidth` spaces
to satisfy YAML's minimum 1-space content indent requirement.
-/
def pushBlockScalar (acc : String) (content : String) (indicator : String)
    (bsMeta : Option BlockScalarMeta) (depth : Nat) (indentWidth : Nat) : String :=
  let chomp := match bsMeta with | some m => m.chomp | none => .clip
  let chompStr := match chomp with | .clip => "" | .strip => "-" | .keep => "+"
  -- Block scalar content must be indented ≥ 1 space from the indicator
  let effectiveDepth := if depth == 0 then 1 else depth
  let ind := makeIndent effectiveDepth indentWidth
  let pushLine := fun (acc : String) (line : String) =>
    if line.isEmpty then acc else acc ++ ind ++ line
  let acc := acc ++ indicator ++ chompStr ++ "\n"
  match content.splitOn "\n" with
  | [] => acc
  | line :: rest =>
    rest.foldl (fun acc line => pushLine (acc.push '\n') line) (pushLine acc line)

/-- Emit a block scalar (literal `|` or folded `>`); see `pushBlockScalar`. -/
def dumpBlockScalar (content : String) (indicator : String)
    (bsMeta : Option BlockScalarMeta) (depth : Nat) (indentWidth : Nat) : String :=
  pushBlockScalar "" content indicator bsMeta depth indentWidth

/-- Build tag + anchor prefix for a node. No trailing space. -/
def nodePrefix (tag : Option String) (anchor : Option String) : String :=
  let t := match tag with | some t => t | none => ""
  let a := match anchor with | some n => "&" ++ n | none => ""
  match t.isEmpty, a.isEmpty with
  | true, true => ""
  | true, false => a
  | false, true => t
  | false, false => t ++ " " ++ a

/-- Append `&anchor ` (with its trailing space) to `acc` when present. -/
def pushAnchor (acc : String) : Option String → String
  | some n => acc ++ "&" ++ n ++ " "
  | none => acc

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

**Contract**: `dumpValueInto acc v cfg depth ctx` appends the text
representation of `v` to `acc` and returns the result:
- First line has **no** leading indent (caller provides prefix)
- Continuation lines include leading indent at `depth` level
- No trailing newline

The whole document is written into one accumulator `String`, so every
item is appended in place to a uniquely referenced buffer and the cost is
linear in the size of the output.

## Examples

```
dump (.plainScalar "hello") == "hello"
dump (.sequence .block #[.plainScalar "a", .plainScalar "b"])
  == "- a\n- b"
```
-/
def dump (v : YamlValue) (cfg : DumpConfig := {}) : String :=
  dumpValueInto "" v cfg 0 .block
where
  /-- Append a value to `acc`. First line unindented; continuation lines at
      `depth`. `ctx` tracks whether we are inside a flow collection. -/
  dumpValueInto (acc : String) (v : YamlValue) (cfg : DumpConfig) (depth : Nat)
      (ctx : DumpContext) : String :=
    match v with
    | .scalar s =>
      if cfg.plainCoreScalars && isRedundantCoreTag s &&
          isPlainSafePreserve s.content true &&
          (ctx == .block || !isFlowUnsafe s.content) then
        -- A `toYaml`-style non-string primitive: bare, untagged, never quoted.
        pushAnchor acc s.anchor ++ s.content
      else
        let acc := match s.tag with | some t => acc ++ t ++ " " | none => acc
        let acc := pushAnchor acc s.anchor
        match chooseScalarStyle s cfg ctx with
        | .plain => acc ++ s.content
        | .doubleQuoted => pushDoubleQuoted acc s.content
        | .singleQuoted => pushSingleQuoted acc s.content
        | .literal => pushBlockScalar acc s.content "|" s.blockMeta depth cfg.indent
        | .folded => pushBlockScalar acc s.content ">" s.blockMeta depth cfg.indent
    | .alias name => acc ++ "*" ++ name
    | .sequence style items tag anchor =>
      let npfx := nodePrefix tag anchor
      match resolveCollectionStyle style cfg ctx with
      | .flow =>
        let acc := if npfx.isEmpty then acc else acc ++ npfx ++ " "
        (dumpFlowListInto (acc.push '[') items 0 cfg depth).push ']'
      | .block =>
        if items.isEmpty then
          (if npfx.isEmpty then acc else acc ++ npfx ++ " ") ++ "[]"
        else
          let acc :=
            if npfx.isEmpty then acc
            else (acc ++ npfx ++ "\n").pushn ' ' (depth * cfg.indent)
          dumpBlockListInto acc items 0 cfg depth
    | .mapping style pairs tag anchor =>
      let npfx := nodePrefix tag anchor
      match resolveCollectionStyle style cfg ctx with
      | .flow =>
        let acc := if npfx.isEmpty then acc else acc ++ npfx ++ " "
        (dumpFlowPairsInto (acc.push '{') pairs 0 cfg depth).push '}'
      | .block =>
        -- No pairs, or omitEmpty skips every pair: emit empty mapping
        if pairs.isEmpty || (cfg.omitEmpty && pairs.all (fun p => isEmptyCollection p.2)) then
          (if npfx.isEmpty then acc else acc ++ npfx ++ " ") ++ "{}"
        else
          let acc :=
            if npfx.isEmpty then acc
            else (acc ++ npfx ++ "\n").pushn ' ' (depth * cfg.indent)
          dumpBlockPairsInto acc pairs 0 cfg depth true
  termination_by (sizeOf v, 0)
  decreasing_by all_goals simp_wf <;> exact Prod.Lex.left _ _ (by simp +arith)
  /-- Comma-separated flow list items from index `i` on (always in flow context). -/
  dumpFlowListInto (acc : String) (items : Array YamlValue) (i : Nat)
      (cfg : DumpConfig) (depth : Nat) : String :=
    if h : i < items.size then
      let acc := if i == 0 then acc else acc ++ ", "
      dumpFlowListInto (dumpValueInto acc items[i] cfg depth .flowIn) items (i + 1) cfg depth
    else acc
  termination_by (sizeOf items, items.size - i)
  decreasing_by
    all_goals simp_wf
    · exact Prod.Lex.left _ _ (Array.sizeOf_getElem items i h)
    · exact Prod.Lex.right _ (by omega)
  /-- Comma-separated flow mapping pairs from index `i` on
      (keys in flowKey context, values in flowIn). -/
  dumpFlowPairsInto (acc : String) (pairs : Array (YamlValue × YamlValue)) (i : Nat)
      (cfg : DumpConfig) (depth : Nat) : String :=
    if h : i < pairs.size then
      match hp : pairs[i] with
      | (k, v) =>
        let acc := if i == 0 then acc else acc ++ ", "
        let acc := dumpValueInto acc k cfg depth .flowKey ++ ": "
        dumpFlowPairsInto (dumpValueInto acc v cfg depth .flowIn) pairs (i + 1) cfg depth
    else acc
  termination_by (sizeOf pairs, pairs.size - i)
  decreasing_by
    all_goals simp_wf
    all_goals have hs := Array.sizeOf_getElem pairs i h
    all_goals rw [hp] at hs
    all_goals simp at hs
    · exact Prod.Lex.left _ _ (by omega)
    · exact Prod.Lex.left _ _ (by omega)
    · exact Prod.Lex.right _ (by omega)
  /-- Block sequence items from index `i` on; items after the first start on
      a new line indented at `depth`.
      When `cfg.compactSequenceMap` is true, non-empty block mapping items
      share the `- ` line with their first key (compact notation). -/
  dumpBlockListInto (acc : String) (items : Array YamlValue) (i : Nat)
      (cfg : DumpConfig) (depth : Nat) : String :=
    if h : i < items.size then
      let acc := if i == 0 then acc else (acc.push '\n').pushn ' ' (depth * cfg.indent)
      let acc :=
        if isInlineValue items[i] ||
            (cfg.compactSequenceMap && isCompactableMapping items[i]) then
          dumpValueInto (acc ++ "- ") items[i] cfg (depth + 1) .block
        else
          dumpValueInto ((acc ++ "-\n").pushn ' ' ((depth + 1) * cfg.indent))
            items[i] cfg (depth + 1) .block
      dumpBlockListInto acc items (i + 1) cfg depth
    else acc
  termination_by (sizeOf items, items.size - i)
  decreasing_by
    all_goals simp_wf
    · exact Prod.Lex.left _ _ (Array.sizeOf_getElem items i h)
    · exact Prod.Lex.left _ _ (Array.sizeOf_getElem items i h)
    · exact Prod.Lex.right _ (by omega)
  /-- Block mapping pairs from index `i` on. `first = true` until a pair has
      been written; later pairs start on a new line indented at `depth`.
      When `cfg.omitEmpty` is true, pairs whose value is an empty collection
      are silently skipped. -/
  dumpBlockPairsInto (acc : String) (pairs : Array (YamlValue × YamlValue)) (i : Nat)
      (cfg : DumpConfig) (depth : Nat) (first : Bool) : String :=
    if h : i < pairs.size then
      match hp : pairs[i] with
      | (k, v) =>
        if cfg.omitEmpty && isEmptyCollection v then
          dumpBlockPairsInto acc pairs (i + 1) cfg depth first
        else
          let acc := if first then acc else (acc.push '\n').pushn ' ' (depth * cfg.indent)
          let acc := dumpValueInto acc k cfg depth .block
          let acc :=
            if isInlineValue v then
              dumpValueInto (acc ++ ": ") v cfg (depth + 1) .block
            else
              dumpValueInto ((acc ++ ":\n").pushn ' ' ((depth + 1) * cfg.indent))
                v cfg (depth + 1) .block
          dumpBlockPairsInto acc pairs (i + 1) cfg depth false
    else acc
  termination_by (sizeOf pairs, pairs.size - i)
  decreasing_by
    all_goals simp_wf
    all_goals have hs := Array.sizeOf_getElem pairs i h
    all_goals rw [hp] at hs
    all_goals simp at hs
    · exact Prod.Lex.right _ (by omega)
    · exact Prod.Lex.left _ _ (by omega)
    · exact Prod.Lex.left _ _ (by omega)
    · exact Prod.Lex.left _ _ (by omega)
    · exact Prod.Lex.right _ (by omega)

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

end Blanket
