import Lean4Yaml.Types

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# YAML Schema and Typed Values

Implements YAML 1.2.2 schema resolution and typed value conversion.

## Architecture

Two-layer system inspired by Lean's JSON implementation:
1. **Parser layer**: `YamlValue` — Untyped parse tree (Phases 1–6)
2. **Schema layer**: `YamlType` — Typed values with Core Schema resolution

## YAML 1.2.2 Schemas (§10)

- **Failsafe Schema** (§10.1): Minimal (only strings, sequences, mappings)
- **JSON Schema** (§10.2): JSON compatibility (null, bool, number, string)
- **Core Schema** (§10.3): Full typing with implicit resolution

This module implements the Core Schema.

## Design Principles

- **Pure functions on inductive types.** Every schema function is total, has no IO,
  no state, and no parser dependency. This makes them kernel-reducible and directly
  provable — the ideal target for formal verification.
- **No exceptions for decisions.** Schema resolution errors are values (`Except`),
  not exceptions. The `resolve` function is total — every `YamlValue` produces a
  `YamlType`.
- **Make implicit state explicit.** Resolution precedence (null → bool → int → float
  → str) is encoded as a match chain — each arm is a provable case.
-/

namespace Lean4Yaml.Schema

/-! ## Typed Value Representation -/

/-- Special float values (infinity and NaN) per YAML 1.2.2 §10.3.2 -/
inductive FloatValue where
  | finite (f : Float)
  | inf (positive : Bool)  -- .inf or -.inf
  | nan
  deriving Repr, BEq, Inhabited

namespace FloatValue

def toFloat : FloatValue → Float
  | .finite f => f
  | .inf true => 1.0 / 0.0   -- +infinity
  | .inf false => -1.0 / 0.0  -- -infinity
  | .nan => 0.0 / 0.0         -- NaN

instance : ToString FloatValue where
  toString := fun
    | .finite f => toString f
    | .inf true => ".inf"
    | .inf false => "-.inf"
    | .nan => ".nan"

end FloatValue

/-- Typed YAML value with resolved types according to Core Schema (§10.3) -/
inductive YamlType where
  | null
  | bool (b : Bool)
  | int (n : Int)
  | float (f : FloatValue)
  | str (s : String)
  | seq (items : Array YamlType)
  | map (pairs : Array (YamlType × YamlType))
  deriving Repr, BEq, Inhabited

/-! ## Type Resolution (Core Schema §10.3) -/

/-- Check if string represents null in Core Schema (§10.3.2).
    Matches: `""`, `"null"`, `"Null"`, `"NULL"`, `"~"` -/
def isNull (s : String) : Bool :=
  s == "" || s == "null" || s == "Null" || s == "NULL" || s == "~"

/-- Check if string represents boolean in Core Schema (§10.3.2).
    Matches: `"true"`, `"True"`, `"TRUE"`, `"false"`, `"False"`, `"FALSE"` -/
def isBool (s : String) : Option Bool :=
  match s with
  | "true" | "True" | "TRUE" => some true
  | "false" | "False" | "FALSE" => some false
  | _ => none

/-- Parse hexadecimal string to integer.
    Total via structural recursion on `List Char`. -/
def parseHex (s : String) : Option Int :=
  let rec go (acc : Int) : List Char → Option Int
    | [] => some acc
    | c :: cs =>
        if '0' ≤ c ∧ c ≤ '9' then
          let val := (c.val - '0'.val).toNat
          go (acc * 16 + val) cs
        else if 'a' ≤ c ∧ c ≤ 'f' then
          let val := (c.val - 'a'.val).toNat + 10
          go (acc * 16 + val) cs
        else if 'A' ≤ c ∧ c ≤ 'F' then
          let val := (c.val - 'A'.val).toNat + 10
          go (acc * 16 + val) cs
        else
          none
  go 0 s.toList

/-- Parse octal string to integer.
    Total via structural recursion on `List Char`. -/
def parseOctal (s : String) : Option Int :=
  let rec go (acc : Int) : List Char → Option Int
    | [] => some acc
    | c :: cs =>
        if '0' ≤ c ∧ c ≤ '7' then
          let val := (c.val - '0'.val).toNat
          go (acc * 8 + val) cs
        else
          none
  go 0 s.toList

/-- Check if string represents integer in Core Schema (§10.3.2).
    Handles decimal, hexadecimal (`0x`), and octal (`0o`) formats,
    with optional sign prefix (`+` or `-`). -/
def isInt (s : String) : Option Int :=
  -- Handle sign
  let (isNeg, rest) := if s.startsWith "-" then
    (true, s.drop 1)
  else if s.startsWith "+" then
    (false, s.drop 1)
  else
    (false, s)

  -- Check for hex prefix (0x or 0X)
  if rest.startsWith "0x" || rest.startsWith "0X" then
    let hexPart := (rest.drop 2).toString
    match parseHex hexPart with
    | some n => some (if isNeg then -n else n)
    | none => none
  -- Check for octal prefix (0o or 0O)
  else if rest.startsWith "0o" || rest.startsWith "0O" then
    let octPart := (rest.drop 2).toString
    match parseOctal octPart with
    | some n => some (if isNeg then -n else n)
    | none => none
  -- Otherwise, try decimal
  else
    match rest.toString.toInt? with
    | some n => some (if isNeg then -n else n)
    | none => none

/-! ### Float Parsing Helpers -/

/-- Parse the mantissa (base) part of a float -/
private def parseMantissa? (s : String) : Option Float :=
  if s.isEmpty then none
  else if s == "0." || s == "0.0" then some 0.0
  else if s.startsWith "." then
    -- Handle .5 format
    let fracStr := (s.drop 1).toString
    match fracStr.toNat? with
    | some n => some (Float.ofNat n / Float.ofNat (10 ^ fracStr.length))
    | none => none
  else if s.contains '.' then
    -- Decimal: int.frac
    let parts := s.splitOn "."
    match parts with
    | [intPart, fracPart] =>
        match (intPart.toInt?, fracPart.toNat?) with
        | (some i, some f) =>
            let base := Float.ofInt i
            let frac := Float.ofNat f / Float.ofNat (10 ^ fracPart.length)
            some (if i >= 0 then base + frac else base - frac)
        | _ => none
    | _ => none
  else
    -- Integer
    match s.toInt? with
    | some n => some (Float.ofInt n)
    | none => none

/-- Parse the exponent part after `e` or `E` -/
private def parseExponent? (s : String) : Option Int :=
  if s.isEmpty then none
  else
    -- Handle optional sign
    let (isNeg, rest) := if s.startsWith "-" then (true, s.drop 1)
                         else if s.startsWith "+" then (false, s.drop 1)
                         else (false, s)
    match rest.toNat? with
    | some n => some (if isNeg then -(n : Int) else (n : Int))
    | none => none

/-- Parse a float from a string.
    Handles standard decimal, scientific notation (`1.5e3`), and integer forms. -/
def parseFloat? (s : String) : Option Float :=
  if s.isEmpty then none
  else
    -- Handle sign
    let (isNeg, rest) := if s.startsWith "-" then (true, s.drop 1)
                         else if s.startsWith "+" then (false, s.drop 1)
                         else (false, s)

    -- Check for scientific notation: split on 'e' or 'E'
    let hasE := rest.contains 'e' || rest.contains 'E'

    if hasE then
      -- Scientific notation: mantissa[eE][+-]?exponent
      let parts := if rest.contains 'e' then rest.toString.splitOn "e"
                   else rest.toString.splitOn "E"
      match parts with
      | [mantissaStr, expStr] =>
          match (parseMantissa? mantissaStr, parseExponent? expStr) with
          | (some mantissa, some exp) =>
              let signedMantissa := if isNeg then -mantissa else mantissa
              let result := signedMantissa * (Float.pow 10.0 (Float.ofInt exp))
              some result
          | _ => none
      | _ => none
    else
      -- No scientific notation — standard decimal/integer
      match parseMantissa? rest.toString with
      | some value => some (if isNeg then -value else value)
      | none => none

/-- Check if string represents float in Core Schema (§10.3.2).
    Includes special values: `.inf`, `-.inf`, `.nan` -/
def isFloat (s : String) : Option FloatValue :=
  match s with
  | ".inf" | ".Inf" | ".INF" | "+.inf" | "+.Inf" | "+.INF" => some (.inf true)
  | "-.inf" | "-.Inf" | "-.INF" => some (.inf false)
  | ".nan" | ".NaN" | ".NAN" => some .nan
  | _ => parseFloat? s |>.map FloatValue.finite

/-- Resolve plain scalar with implicit typing (Core Schema precedence).

    **Resolution order** (YAML 1.2.2 §10.3.2):
    1. null → 2. bool → 3. int → 4. float → 5. str (fallback)

    This is the core function — every plain scalar passes through here. -/
def resolveImplicit (s : String) : YamlType :=
  if isNull s then .null
  else if let some b := isBool s then .bool b
  else if let some i := isInt s then .int i
  else if let some f := isFloat s then .float f
  else .str s

/-- Resolve scalar with optional explicit tag.

    When an explicit tag is present (`!!str`, `!!int`, etc.), it takes
    precedence over implicit resolution. Unknown tags fall through to
    string representation. -/
def resolveScalar (content : String) (tag? : Option String) : YamlType :=
  match tag? with
  | some "tag:yaml.org,2002:null" => .null
  | some "tag:yaml.org,2002:bool" =>
      match isBool content with
      | some b => .bool b
      | none => .str content
  | some "tag:yaml.org,2002:int" =>
      match isInt content with
      | some i => .int i
      | none => .str content
  | some "tag:yaml.org,2002:float" =>
      match isFloat content with
      | some f => .float f
      | none => .str content
  | some "tag:yaml.org,2002:str" => .str content
  | some _ => .str content  -- unknown tag → string
  | none => resolveImplicit content

/-! ## Recursive Resolution

`resolve` walks the `YamlValue` tree, applying schema resolution at each node.
Total via structural recursion on `List` (converting `Array` to `List` for
the recursive cases — the same pattern used throughout the verified project
for `YamlValue`'s `Array`-based children).
-/

/-- Resolve complete `YamlValue` to `YamlType` using Core Schema.

    - Scalars: dispatched to `resolveScalar` (tag-aware implicit/explicit resolution)
    - Sequences: recursively resolve each element
    - Mappings: recursively resolve each key and value
    - Aliases: resolved as null (aliases should be expanded before schema resolution) -/
def resolve (v : YamlValue) : YamlType :=
  match v with
  | .scalar s => resolveScalar s.content s.tag
  | .sequence _ items _ _ => .seq (resolveList items.toList).toArray
  | .mapping _ pairs _ _ => .map (resolvePairs pairs.toList).toArray
  | .alias _ => .null  -- aliases should be resolved via compose before schema resolution
where
  /-- Resolve a list of YAML values. -/
  resolveList : List YamlValue → List YamlType
    | [] => []
    | v :: vs => resolve v :: resolveList vs
  /-- Resolve a list of key-value pairs. -/
  resolvePairs : List (YamlValue × YamlValue) → List (YamlType × YamlType)
    | [] => []
    | (k, v) :: rest => (resolve k, resolve v) :: resolvePairs rest

/-! ## Convenience Functions -/

namespace YamlType

def isNull : YamlType → Bool | .null => true | _ => false
def isBool : YamlType → Bool | .bool _ => true | _ => false
def isInt : YamlType → Bool | .int _ => true | _ => false
def isFloat : YamlType → Bool | .float _ => true | _ => false
def isStr : YamlType → Bool | .str _ => true | _ => false
def isSeq : YamlType → Bool | .seq _ => true | _ => false
def isMap : YamlType → Bool | .map _ => true | _ => false

def getBool? : YamlType → Option Bool | .bool b => some b | _ => none
def getInt? : YamlType → Option Int | .int n => some n | _ => none
def getFloat? : YamlType → Option Float | .float f => some f.toFloat | _ => none
def getStr? : YamlType → Option String | .str s => some s | _ => none
def getSeq? : YamlType → Option (Array YamlType) | .seq items => some items | _ => none
def getMap? : YamlType → Option (Array (YamlType × YamlType)) | .map pairs => some pairs | _ => none

end YamlType

end Lean4Yaml.Schema
