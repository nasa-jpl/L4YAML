/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Parser.Composition

/-!
# YAML Test-Suite Event Stream Emitter

Serializes the L4YAML representation graph (`YamlValue` / `YamlDocument`) into the
[yaml-test-suite](https://github.com/yaml/yaml-test-suite) **event stream**
notation — the same format the [YAML matrix](https://matrix.yaml.info) uses to
compare processors against each test's expected `tree:` (a.k.a. `test.event`).

Grammar of the notation:

```
+STR                    stream start
+DOC [---]              document start (`---` iff explicit)
+MAP [{}] [&anchor] [<tag>]   mapping start (`{}` iff flow)
+SEQ [[]] [&anchor] [<tag>]   sequence start (`[]` iff flow)
=VAL [&anchor] [<tag>] <style><value>   scalar
=ALI *anchor            alias
-MAP / -SEQ             collection end
-DOC [...]              document end (`...` iff explicit)
-STR                    stream end
```

Scalar style char: `:` plain, `'` single-quoted, `"` double-quoted,
`|` literal, `>` folded.  Values are escaped: `\` → `\\`, and the control
characters newline/tab/CR/backspace become `\n`/`\t`/`\r`/`\b`.

The emitter runs over the **raw** parse (`parseYamlRaw`) so that `.alias`
nodes and `anchor` fields survive: the event stream reports `=ALI *a`, it does
not inline the aliased value.  Explicit document markers (`---` / `...`) are not
stored on `YamlDocument`, so `parseStreamMarked` mirrors `TokenParser.parseStream`
to capture them without touching the core type.
-/

namespace L4YAML.Events

open L4YAML L4YAML.TokenParser

/-! ## Escaping and property rendering -/

/-- Backspace character (0x08), escaped as `\b` in the event stream. -/
private def backspace : String := String.singleton (Char.ofNat 8)

/-- Escape a scalar's content for the event stream.  Backslash is escaped first
    so the backslashes introduced by the control-character rules are not doubled. -/
def escapeEventValue (s : String) : String :=
  s.replace "\\" "\\\\"
   |>.replace "\n" "\\n"
   |>.replace "\t" "\\t"
   |>.replace "\r" "\\r"
   |>.replace backspace "\\b"

/-- Render a stored tag into the resolved form shown inside `<…>` in the event
    stream.  The raw (`TokenParser`) parser keeps tags in shorthand form, so the
    two standard core handles are expanded to their full URIs; verbatim `tag:`
    URIs and local (`!foo`) tags are passed through unchanged. -/
def resolveTagForEvent (t : String) : String :=
  if t.startsWith "tag:" then t
  else if t.startsWith "!<" && t.endsWith ">" then
    -- verbatim tag `!<uri>` → uri
    String.ofList (t.toList.drop 2 |>.dropLast)
  else if t.startsWith "!!" then
    "tag:yaml.org,2002:" ++ String.ofList (t.toList.drop 2)
  else t  -- local tag `!foo`, non-specific `!`, or already-resolved

/-- Render the optional `&anchor` property. -/
private def anchorStr (a : Option String) : String :=
  match a with | some x => s!" &{x}" | none => ""

/-- Render the optional `<tag>` property. -/
private def tagStr (t : Option String) : String :=
  match t with | some x => s!" <{resolveTagForEvent x}>" | none => ""

/-- The style character for a scalar. -/
private def styleChar : ScalarStyle → String
  | .plain        => ":"
  | .singleQuoted => "'"
  | .doubleQuoted => "\""
  | .literal      => "|"
  | .folded       => ">"

/-! ## Value emission -/

/-- Emit the event lines for a single `YamlValue`. -/
partial def emitValue (v : YamlValue) : Array String :=
  match v with
  | .scalar s =>
    #[s!"=VAL{anchorStr s.anchor}{tagStr s.tag} {styleChar s.style}{escapeEventValue s.content}"]
  | .alias name =>
    #[s!"=ALI *{name}"]
  | .sequence style items tag anchor =>
    let flow := if style == .flow then " []" else ""
    let body := items.foldl (fun acc it => acc ++ emitValue it) #[]
    #[s!"+SEQ{flow}{anchorStr anchor}{tagStr tag}"] ++ body ++ #["-SEQ"]
  | .mapping style pairs tag anchor =>
    let flow := if style == .flow then " {}" else ""
    let body := pairs.foldl (fun acc kv => acc ++ emitValue kv.1 ++ emitValue kv.2) #[]
    #[s!"+MAP{flow}{anchorStr anchor}{tagStr tag}"] ++ body ++ #["-MAP"]

/-! ## Document markers (additive parallel path)

`YamlDocument` does not record whether its `---` / `...` markers were explicit,
so we mirror `TokenParser.parseStream` here purely to capture them.  All parsing
is delegated to the existing `parseDocument`; only the boundary bookkeeping is
duplicated. -/

/-- A parsed document together with its explicit-marker flags. -/
structure MarkedDoc where
  doc : YamlDocument
  explicitStart : Bool
  explicitEnd : Bool
  deriving Inhabited

/-- Does the document beginning at `ps` open with an explicit `---`?
    Directives (`%YAML`, `%TAG`) may precede it; a directive-led document is
    always explicit per §9.1.5. -/
private def explicitStartAt (ps : ParseState) : Bool :=
  let rec go (i : Nat) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      if i < ps.tokens.size then
        match ps.tokens[i]!.val with
        | .versionDirective _ _ => go (i + 1) fuel
        | .tagDirective _ _     => go (i + 1) fuel
        | .documentStart        => true
        | _                     => false
      else false
  go ps.pos ps.tokens.size

/-- Mirror of `TokenParser.parseStreamLoop` that additionally records explicit
    `---` / `...` markers for each document. -/
private def parseStreamMarkedLoop (ps : ParseState) (acc : Array MarkedDoc)
    (streamState : StreamState) (fuel : Nat) : Except ScanError (Array MarkedDoc) :=
  match fuel with
  | 0 => .ok acc
  | fuel + 1 =>
    match ps.peek? with
    | some .streamEnd => .ok acc
    | none => .ok acc
    | some tok =>
      if !streamState.validNextToken tok then
        let pos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
        .error (.invalidBareDocument pos.line pos.col)
      else
        let explicitStart := explicitStartAt ps
        let savedPos := ps.pos
        match parseDocument ps with
        | .error e => .error e
        | .ok (doc, ps') =>
          let ps := { ps' with anchors := #[], nodePositions := #[], currentPath := #[] }
          let (consumed, ps) := ps.tryConsume .documentEnd
          let acc := acc.push { doc, explicitStart, explicitEnd := consumed }
          let streamState := if consumed then .afterDocumentEnd else .afterDocument
          if ps.pos == savedPos then .ok acc
          else parseStreamMarkedLoop ps acc streamState fuel

/-- Parse a YAML stream into documents tagged with their explicit markers.
    Uses the raw parser so aliases/anchors are preserved for event output. -/
def parseYamlRawMarked (input : String) : Except ScanError (Array MarkedDoc) := do
  let tokens ← Scanner.scanFiltered input
  let ps : ParseState := { tokens := tokens }
  let ps ← ps.expect .streamStart "STREAM-START"
  parseStreamMarkedLoop ps #[] .initial tokens.size

/-! ## Stream emission -/

/-- Emit the event lines for one marked document. -/
def emitDoc (md : MarkedDoc) : Array String :=
  let startLine := if md.explicitStart then "+DOC ---" else "+DOC"
  let endLine := if md.explicitEnd then "-DOC ..." else "-DOC"
  #[startLine] ++ emitValue md.doc.value ++ #[endLine]

/-- Emit the full event stream for a list of marked documents (no trailing newline). -/
def emitStream (docs : Array MarkedDoc) : String :=
  let lines := #["+STR"] ++ docs.foldl (fun acc d => acc ++ emitDoc d) #[] ++ #["-STR"]
  String.intercalate "\n" lines.toList

/-- Parse `input` and produce its test-suite event stream (with trailing newline),
    or a scan/parse error. -/
def streamToEvents (input : String) : Except ScanError String :=
  match parseYamlRawMarked input with
  | .ok docs => .ok (emitStream docs ++ "\n")
  | .error e => .error e

end L4YAML.Events
