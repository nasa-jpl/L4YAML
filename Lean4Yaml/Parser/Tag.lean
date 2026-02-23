/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.YamlSpec

/-!
# YAML Tag Parsers

Parsers for YAML tags as node properties.

**YAML 1.2.2**: [95]-[98] c-ns-tag-property (§6.9.1, https://yaml.org/spec/1.2.2/#691-node-tags)
- [95] c-ns-tag-property
- [96] c-verbatim-tag: `!<uri>`
- [97] c-ns-shorthand-tag: `!suffix`, `!!suffix`, `!handle!suffix`
- [98] c-non-specific-tag: `!`

## Tag Forms

YAML tags come in several forms:

1. **Verbatim tags** `!<uri>` — the URI is used directly
2. **Secondary handle** `!!suffix` — shorthand for `tag:yaml.org,2002:suffix`
3. **Primary handle** `!suffix` — shorthand for `!suffix` (local tag)
4. **Named handles** `!handle!suffix` — resolved via `%TAG` directives
5. **Non-specific tag** `!` — marks a node for type resolution

## Design

**Tags are metadata**: Tags annotate the node but don't change the AST
@[yaml_spec "6.9.1" 95 "-"]
structure. After parsing a tag prefix, the caller parses the value normally
and applies the tag to the result using `YamlValue.withTag`.

**No tag resolution**: We store tags as-is in the AST for now. The
yaml-test-suite compares JSON output, which doesn't include tags, so
tag presence doesn't affect test pass/fail. Tag resolution (e.g.,
`!!str` → `tag:yaml.org,2002:str`) is a schema concern, not a parser
concern.

**Interaction with anchors**: Per §6.9, node properties (tags and anchors)
can appear in either order:
- `!tag &anchor value`
- `&anchor !tag value`

Both orderings are handled at the call site (dispatchByChar, flowValue,
blockMappingKey), not in this module.

## Spec References

- §6.8.1 Tag Directives: https://yaml.org/spec/1.2.2/#681-tag-directives
- §6.8.2 Tag Handles: https://yaml.org/spec/1.2.2/#682-tag-handles
- §6.9.1 Node Tags: https://yaml.org/spec/1.2.2/#691-node-tags
-/

namespace Lean4Yaml.Parse

open Parser
open Parser.Char
open Lean4Yaml

/-! ## Tag Character Classification -/

/--
Characters allowed in tag suffixes.

**YAML 1.2.2**: [40] ns-tag-char (§6.8.2)

Per YAML §6.8.2, tag characters include URI characters (alphanumeric,
`-`, `.`, `_`, `~`, `/`, `:`, `@`, `!`, `$`, `&`, `*`, `+`, `=`, etc.)
but exclude flow indicators and whitespace.
-/
@[yaml_spec "6.8.2" 40 "ns-tag-char"]
def isTagChar (c : Char) : Bool :=
  c.isAlphanum || c ∈ ['-', '.', '_', '~', '/', ':', '@', '!', '$',
                         '&', '*', '+', '=', '%', '^', '(', ')']

/--
Characters allowed in tag handle names (the part between `!` delimiters).

**YAML 1.2.2**: [86] c-tag-handle (§6.8.2)
- [88] c-named-tag-handle: `!` word-char+ `!`

Handle names are word characters: `[a-zA-Z0-9-]`.
-/
@[yaml_spec "6.8.2" 86 "c-tag-handle"]
def isTagHandleChar (c : Char) : Bool :=
  c.isAlphanum || c == '-'

/--
Characters allowed inside verbatim tag URIs (`!<...>`).

**YAML 1.2.2**: [96] c-verbatim-tag (§6.9.1)

All printable non-whitespace characters except `>`.
-/
@[yaml_spec "6.9.1" 96 "c-verbatim-tag"]
def isVerbatimTagChar (c : Char) : Bool :=
  c != '>' && !isWhiteSpace c && !isLineBreak c && c.val >= 0x20

/-! ## Tag Parsing -/

/--
Parse a YAML tag prefix starting with `!`.

**YAML 1.2.2**: [95] c-ns-tag-property (§6.9.1, https://yaml.org/spec/1.2.2/#691-node-tags)
- [96] c-verbatim-tag: `!<uri>`
- [97] c-ns-shorthand-tag: `!!suffix`, `!handle!suffix`, `!suffix`
- [98] c-non-specific-tag: `!` alone

Handles all tag forms:
- `!<uri>` — verbatim tag
- `!!suffix` — secondary handle (standard YAML types)
- `!handle!suffix` — named handle (resolved via %TAG)
- `!suffix` — primary handle (local tag)
- `!` alone — non-specific tag

Returns the tag string as-is.

§6.9.1 (https://yaml.org/spec/1.2.2/#691-node-tags)
-/
@[yaml_spec "6.9.1" 95 "c-ns-tag-property"]
def parseTagPrefix : YamlParser String :=
  withErrorMessage "expected tag (!...)" do
    let _ ← char '!'
    -- Check what follows the initial `!`
    match ← option? (lookAhead anyToken) with
    | none =>
      -- `!` at end of input: non-specific tag
      return "!"
    | some '<' =>
      -- Verbatim tag: `!<uri>`
      let _ ← char '<'
      let chars ← takeMany1 (tokenFilter isVerbatimTagChar)
      let _ ← char '>'
      skipHWhitespace
      return s!"!<{String.ofList chars.toList}>"
    | some '!' =>
      -- Secondary handle: `!!suffix`
      let _ ← char '!'
      let suffix ← takeMany1 (tokenFilter isTagChar)
      skipHWhitespace
      return s!"!!{String.ofList suffix.toList}"
    | some c =>
      if isWhiteSpace c || isLineBreak c then
        -- Non-specific tag `!` followed by whitespace
        skipHWhitespace
        return "!"
      else if isTagHandleChar c then
        -- Could be `!handle!suffix` or `!suffix`
        let chars ← takeMany1 (tokenFilter isTagHandleChar)
        let handleOrSuffix := String.ofList chars.toList
        -- Check for second `!` (named handle)
        match ← option? (char '!') with
        | some _ =>
          -- Named handle: `!handle!suffix`
          let handle := s!"!{handleOrSuffix}!"
          -- P10 fix (QLJ7): §6.8.2 — validate that the tag handle was
          -- defined by a %TAG directive in the current document.
          let defined ← isTagHandleDefined handle
          if !defined then
            setValidationError
              s!"undefined tag handle '{handle}' (not declared by %TAG in this document)"
          match ← option? (takeMany1 (tokenFilter isTagChar)) with
          | some suffixChars =>
            let suffix := String.ofList suffixChars.toList
            skipHWhitespace
            return s!"{handle}{suffix}"
          | none =>
            -- `!handle!` with no suffix
            skipHWhitespace
            return handle
        | none =>
          -- Primary local tag: `!suffix`
          skipHWhitespace
          return s!"!{handleOrSuffix}"
      else
        -- `!` followed by something unexpected: treat as non-specific tag
        return "!"

end Lean4Yaml.Parse
