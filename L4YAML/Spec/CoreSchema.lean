module

public import L4YAML.Init

@[expose] public section Blanket

/-!
# YAML 1.2.2 Core Schema — lexical tag requirements

An independent transcription of the ordered regular-expression table in
YAML 1.2.2 §10.3.2 (https://yaml.org/spec/1.2.2/#1032-tag-resolution).
This module does not import `L4YAML.Schema.Schema` and does not interpret
the numeric value: recognition and valuation are distinct obligations.

Only the `?` non-specific tag on a *plain scalar* is in scope. Explicit
tags, `!` non-specific tags, collections and native-value construction
have separate requirements. The decimal integer rule takes priority over
the numeric float rule, which also accepts digit-only spellings.
-/

namespace L4YAML.Spec.CoreSchema

inductive Tag where
  | null | bool | int | float | str
  deriving Repr, DecidableEq, BEq, Inhabited

def asciiDigit (c : Char) : Bool := decide ('0' ≤ c ∧ c ≤ '9')

def asciiOctal (c : Char) : Bool := decide ('0' ≤ c ∧ c ≤ '7')

def asciiHex (c : Char) : Bool :=
  asciiDigit c || decide ('a' ≤ c ∧ c ≤ 'f') || decide ('A' ≤ c ∧ c ≤ 'F')

def oneOrMore (p : Char → Bool) (cs : List Char) : Bool :=
  !cs.isEmpty && cs.all p

def withoutSign : List Char → List Char
  | '+' :: rest | '-' :: rest => rest
  | rest => rest

/-- The Core integer rows: signed decimal, unsigned lowercase `0o`, `0x`. -/
def integerSpelling (s : String) : Bool :=
  let cs := s.toList
  let decimal := oneOrMore asciiDigit (withoutSign cs)
  let octal := match cs with
    | '0' :: 'o' :: rest => oneOrMore asciiOctal rest
    | _ => false
  let hex := match cs with
    | '0' :: 'x' :: rest => oneOrMore asciiHex rest
    | _ => false
  decimal || octal || hex

def splitExponent : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | 'e' :: rest | 'E' :: rest => ([], some rest)
  | c :: rest =>
    let (mantissa, exponent) := splitExponent rest
    (c :: mantissa, exponent)

def mantissaSpelling (cs : List Char) : Bool :=
  match cs with
  | '.' :: fraction => oneOrMore asciiDigit fraction
  | _ =>
    let (whole, tail) := cs.span asciiDigit
    oneOrMore asciiDigit whole &&
      match tail with
      | [] => true
      | '.' :: fraction => fraction.all asciiDigit
      | _ => false

/-- The Core finite-float regex, including its optional exponent and decimal dot. -/
def numberSpelling (s : String) : Bool :=
  let (mantissa, exponent) := splitExponent (withoutSign s.toList)
  mantissaSpelling mantissa &&
    match exponent with
    | none => true
    | some rest => oneOrMore asciiDigit (withoutSign rest)

def infinitySpelling (s : String) : Bool :=
  let suffix := String.ofList (withoutSign s.toList)
  suffix == ".inf" || suffix == ".Inf" || suffix == ".INF"

def nanSpelling (s : String) : Bool :=
  s == ".nan" || s == ".NaN" || s == ".NAN"

/-- The complete Core float rows. An integer row can also match `numberSpelling`,
    so use `tag` to apply the table's ordering. -/
def floatSpelling (s : String) : Bool :=
  numberSpelling s || infinitySpelling s || nanSpelling s

def nullSpelling (s : String) : Bool :=
  s == "" || s == "~" || s == "null" || s == "Null" || s == "NULL"

def boolSpelling (s : String) : Bool :=
  s == "true" || s == "True" || s == "TRUE" ||
    s == "false" || s == "False" || s == "FALSE"

/-- The *first matching row* of YAML 1.2.2 Core §10.3.2 for plain scalar
    content with the `?` non-specific tag. The default row is string. -/
def tag (s : String) : Tag :=
  if nullSpelling s then .null
  else if boolSpelling s then .bool
  else if integerSpelling s then .int
  else if floatSpelling s then .float
  else .str

end L4YAML.Spec.CoreSchema

end Blanket
