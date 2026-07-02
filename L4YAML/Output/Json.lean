/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Parser.Composition
import L4YAML.Schema.Schema

/-!
# YAML → JSON (Core Schema)

Serializes L4YAML's representation graph to JSON matching the yaml-test-suite
`in.json` oracle, applying the YAML 1.2 **Core Schema** (§10.3) to resolve plain
scalars to `null` / `bool` / `int` / `float` / `str`.  This is the JSON axis the
[YAML matrix](https://matrix.yaml.info) compares against `in.json`.

Uses `TokenParser.parseYaml`, which composes the representation graph and
**resolves aliases**, so the emitted JSON inlines aliased values (as `in.json`
does).  Resolution is style-aware: only *plain* scalars are type-resolved;
quoted/literal/folded scalars are always strings (unless an explicit tag says
otherwise).
-/

namespace L4YAML.Json

open L4YAML L4YAML.Schema

/-- Four-digit lowercase hex for a `\uXXXX` JSON escape. -/
private def toHex4 (n : Nat) : String :=
  let digits := "0123456789abcdef".toList
  let d (k : Nat) : Char := digits[(n / (16 ^ k)) % 16]!
  String.ofList [d 3, d 2, d 1, d 0]

/-- Escape and quote a string as a JSON string literal. -/
def escapeJsonString (s : String) : String :=
  let esc (c : Char) : String :=
    match c with
    | '"'  => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c =>
      if c.toNat < 0x20 then "\\u" ++ toHex4 c.toNat
      else String.singleton c
  "\"" ++ String.join (s.toList.map esc) ++ "\""

/-- A `FloatValue` as a JSON number.  `Infinity` / `-Infinity` / `NaN` are the
    forms Python's `json.loads` (used by the matrix comparison) accepts. -/
def floatToJson : FloatValue → String
  | .finite f => toString f
  | .inf true => "Infinity"
  | .inf false => "-Infinity"
  | .nan => "NaN"

/-- Normalize a stored tag to the full-URI form `resolveScalar` matches on.

    The composed parser keeps the two default core handles in shorthand form
    (`!!int`, `!!str`, …) and verbatim tags as `!<uri>` (see
    `Parser.State.resolveTag`).  `resolveScalar` only recognizes the expanded
    `tag:yaml.org,2002:…` URIs, so `!!int 42` would otherwise fall through to a
    string.  Expand both forms here; local tags (`!foo`) and already-resolved
    URIs pass through unchanged (and `resolveScalar` maps unknown tags to str). -/
def normalizeTag (t : String) : String :=
  if t.startsWith "tag:" then t
  else if t.startsWith "!<" && t.endsWith ">" then
    String.ofList (t.toList.drop 2 |>.dropLast)
  else if t.startsWith "!!" then
    "tag:yaml.org,2002:" ++ String.ofList (t.toList.drop 2)
  else t

/-- Core-schema type of a scalar, respecting presentation style: quoted/literal/
    folded scalars are strings; only plain scalars are implicitly resolved.  An
    explicit tag always takes precedence. -/
def scalarType (s : Scalar) : YamlType :=
  match s.tag with
  | some t => resolveScalar s.content (some (normalizeTag t))
  | none =>
    match s.style with
    | .plain => resolveImplicit s.content
    | _      => .str s.content

mutual
/-- Serialize a `YamlValue` to a JSON document string. -/
partial def yamlToJson (v : YamlValue) : String :=
  match v with
  | .scalar s =>
    match scalarType s with
    | .null    => "null"
    | .bool b  => if b then "true" else "false"
    | .int n   => toString n
    | .float f => floatToJson f
    | .str t   => escapeJsonString t
    | _        => "null"
  | .sequence _ items _ _ =>
    "[" ++ String.intercalate "," (items.toList.map yamlToJson) ++ "]"
  | .mapping _ pairs _ _ =>
    "{" ++ String.intercalate ","
      (pairs.toList.map (fun p => keyToJson p.1 ++ ":" ++ yamlToJson p.2)) ++ "}"
  | .alias _ => "null"

/-- A JSON object key: JSON keys are strings, so scalar keys are stringified
    (matching `json.dumps`, which coerces `1` → `"1"`, `true` → `"true"`). -/
partial def keyToJson (k : YamlValue) : String :=
  match k with
  | .scalar s =>
    match scalarType s with
    | .null    => escapeJsonString "null"
    | .bool b  => escapeJsonString (if b then "true" else "false")
    | .int n   => escapeJsonString (toString n)
    | .float f => escapeJsonString (floatToJson f)
    | .str t   => escapeJsonString t
    | _        => escapeJsonString s.content
  | _ => escapeJsonString (yamlToJson k)  -- complex key: best-effort
end

/-- Serialize a stream of documents; each document's JSON on its own line. -/
def docsToJson (docs : Array YamlDocument) : String :=
  String.intercalate "\n" (docs.toList.map (fun d => yamlToJson d.value))

/-- Parse `input` and produce its Core-Schema JSON, or a scan/parse error. -/
def streamToJson (input : String) : Except ScanError String :=
  match L4YAML.TokenParser.parseYaml input with
  | .ok docs => .ok (docsToJson docs)
  | .error e => .error e

end L4YAML.Json
