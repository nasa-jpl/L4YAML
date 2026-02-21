/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators

/-!
# YAML Tag Parsers

Parsers for YAML tags as node properties
(YAML 1.2.2 §6.9.2, https://yaml.org/spec/1.2.2/#692-node-tags).

## Tag Forms

YAML tags come in several forms:

1. **Verbatim tags** `!<uri>` — the URI is used directly
2. **Secondary handle** `!!suffix` — shorthand for `tag:yaml.org,2002:suffix`
3. **Primary handle** `!suffix` — shorthand for `!suffix` (local tag)
4. **Named handles** `!handle!suffix` — resolved via `%TAG` directives
5. **Non-specific tag** `!` — marks a node for type resolution

## Design

**Tags are metadata**: Tags annotate the node but don't change the AST
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

Per YAML §6.8.2, tag characters include URI characters (alphanumeric,
`-`, `.`, `_`, `~`, `/`, `:`, `@`, `!`, `$`, `&`, `*`, `+`, `=`, etc.)
but exclude flow indicators and whitespace.
-/
def isTagChar (c : Char) : Bool :=
  c.isAlphanum || c ∈ ['-', '.', '_', '~', '/', ':', '@', '!', '$',
                         '&', '*', '+', '=', '%', '^', '(', ')']

/--
Characters allowed in tag handle names (the part between `!` delimiters).

Handle names are word characters: `[a-zA-Z0-9-]`.
-/
def isTagHandleChar (c : Char) : Bool :=
  c.isAlphanum || c == '-'

/--
Characters allowed inside verbatim tag URIs (`!<...>`).

All printable non-whitespace characters except `>`.
-/
def isVerbatimTagChar (c : Char) : Bool :=
  c != '>' && !isWhiteSpace c && !isLineBreak c && c.val >= 0x20

/-! ## Tag Parsing -/

/--
Parse a YAML tag prefix starting with `!`.

Handles all tag forms:
- `!<uri>` — verbatim tag
- `!!suffix` — secondary handle (standard YAML types)
- `!handle!suffix` — named handle (resolved via %TAG)
- `!suffix` — primary handle (local tag)
- `!` alone — non-specific tag

Returns the tag string as-is.

§6.9.1 (https://yaml.org/spec/1.2.2/#691-node-tags)
-/
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
