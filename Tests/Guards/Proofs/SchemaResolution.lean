module

public import L4YAML.Proofs.Schema.SchemaResolution
public meta import L4YAML.Proofs.Schema.SchemaResolution
public import L4YAML.Spec.CoreSchema
public meta import L4YAML.Spec.CoreSchema

@[expose] public section Blanket

namespace L4YAML.Schema.Proofs

open L4YAML.Schema
open L4YAML

-- Spec-side checks cover every §10.3.2 class and near-miss. The predicate
-- is intentionally independent of the production numeric parsers.
#guard Spec.CoreSchema.tag "" == .null
#guard Spec.CoreSchema.tag "True" == .bool
#guard Spec.CoreSchema.tag "123" == .int  -- first match, despite the float regex
#guard Spec.CoreSchema.tag "0o7" == .int
#guard Spec.CoreSchema.tag "0xFF" == .int
#guard Spec.CoreSchema.tag "1." == .float
#guard Spec.CoreSchema.tag ".5" == .float
#guard Spec.CoreSchema.tag "+12e03" == .float
#guard Spec.CoreSchema.tag "-.Inf" == .float
#guard Spec.CoreSchema.tag ".NaN" == .float
#guard Spec.CoreSchema.tag "1_000" == .str
#guard Spec.CoreSchema.tag "0x" == .str
#guard Spec.CoreSchema.tag "0XFF" == .str
#guard Spec.CoreSchema.tag "+0x2" == .str
#guard Spec.CoreSchema.tag "1.5_0" == .str
#guard Spec.CoreSchema.tag "+.nan" == .str
#guard Spec.CoreSchema.tag "0e" == .str
#guard Spec.CoreSchema.tag "0e+" == .str
#guard Spec.CoreSchema.tag "0e309" == .float
#guard Spec.CoreSchema.tag "0o" == .str
#guard Spec.CoreSchema.tag "0O7" == .str
#guard Spec.CoreSchema.tag "-0o7" == .str
#guard Spec.CoreSchema.tag "+0xFF" == .str
#guard Spec.CoreSchema.tag "0b101" == .str
#guard Spec.CoreSchema.tag ".5_0" == .str
#guard Spec.CoreSchema.tag "1e+" == .str
#guard Spec.CoreSchema.tag "1.e+2" == .float

-- These directly instantiate the stated *spec-to-implementation* obligation,
-- rather than independently checking two lists of examples. The unbounded
-- universal proposition remains an explicit proof residual.
#guard L4YAML.Proofs.SchemaResolution.scalarTag? (resolveImplicit "1_000") ==
  some (Spec.CoreSchema.tag "1_000")
#guard L4YAML.Proofs.SchemaResolution.scalarTag? (resolveImplicit "0x") ==
  some (Spec.CoreSchema.tag "0x")
#guard L4YAML.Proofs.SchemaResolution.scalarTag? (resolveImplicit "1.") ==
  some (Spec.CoreSchema.tag "1.")
#guard L4YAML.Proofs.SchemaResolution.scalarTag? (resolveImplicit "0x3A") ==
  some (Spec.CoreSchema.tag "0x3A")
#guard L4YAML.Proofs.SchemaResolution.scalarTag? (resolveImplicit "-.Inf") ==
  some (Spec.CoreSchema.tag "-.Inf")
#guard L4YAML.Proofs.SchemaResolution.scalarTag? (resolveImplicit ".NaN") ==
  some (Spec.CoreSchema.tag ".NaN")
#guard L4YAML.Proofs.SchemaResolution.scalarTag? (resolveImplicit "0e309") ==
  some (Spec.CoreSchema.tag "0e309")

-- Bounded exhaustive decoder check across 41,371 spellings of length 0–4
-- over a 14-character alphabet chosen to exercise signs, bases, exponents,
-- decimal points, underscores and letter case. This is finite evidence,
-- not a proof of `coreTagCorrespondenceAll` over arbitrary strings.
private def coreSchemaProbeAlphabet : List Char :=
  ['+', '-', '0', '1', '7', '8', 'x', 'X', 'o', 'O', 'e', 'E', '.', '_']

private def coreSchemaWordsOfLength : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => coreSchemaProbeAlphabet.flatMap fun c =>
      (coreSchemaWordsOfLength n).map (c :: ·)

private def coreSchemaBoundedMatches : Bool :=
  ((List.range 5).flatMap coreSchemaWordsOfLength).all fun chars =>
    let s := String.ofList chars
    L4YAML.Proofs.SchemaResolution.scalarTag? (resolveImplicit s) ==
      some (Spec.CoreSchema.tag s)

#guard ((List.range 5).flatMap coreSchemaWordsOfLength).length == 41371
#guard coreSchemaBoundedMatches

-- Non-vacuous instances of the conditional universal bridge: one integer row
-- and one float row actually satisfy the decoder-success hypotheses.
example : L4YAML.Proofs.SchemaResolution.coreTagCorrespondence "0xFF" := by
  apply L4YAML.Proofs.SchemaResolution.coreTagCorrespondence_at_of_recognizers
  · decide
  · decide

example : L4YAML.Proofs.SchemaResolution.coreTagCorrespondence "1." := by
  apply L4YAML.Proofs.SchemaResolution.coreTagCorrespondence_at_of_recognizers
  · decide
  · decide

-- Null resolution
#guard resolveImplicit "" == .null
#guard resolveImplicit "null" == .null
#guard resolveImplicit "~" == .null
#guard resolveImplicit "Null" == .null
#guard resolveImplicit "NULL" == .null

-- Boolean resolution
#guard resolveImplicit "true" == .bool true
#guard resolveImplicit "false" == .bool false
#guard resolveImplicit "True" == .bool true
#guard resolveImplicit "False" == .bool false
#guard resolveImplicit "TRUE" == .bool true
#guard resolveImplicit "FALSE" == .bool false

-- Integer resolution
#guard resolveImplicit "0" == .int 0
#guard resolveImplicit "42" == .int 42
#guard resolveImplicit "-17" == .int (-17)
#guard resolveImplicit "+3" == .int 3
#guard resolveImplicit "0xFF" == .int 255
#guard resolveImplicit "0o17" == .int 15

-- YAML 1.2.2 Core §10.3.2 requires exact lexical matches, not merely a
-- successful numerical conversion. These must fail on the pre-repair source.
#guard resolveImplicit "1_000" == .str "1_000"
#guard resolveImplicit "0x" == .str "0x"
#guard (resolveImplicit "1.").isFloat
#guard resolveImplicit "1." == .float (.finite 1.0)
#guard resolveImplicit "0XFF" == .str "0XFF"
#guard resolveImplicit "+0x2" == .str "+0x2"
#guard resolveImplicit "1.5_0" == .str "1.5_0"
#guard resolveImplicit "0o" == .str "0o"
#guard resolveImplicit "0O7" == .str "0O7"
#guard resolveImplicit "-0o7" == .str "-0o7"
#guard resolveImplicit "+0xFF" == .str "+0xFF"
#guard resolveImplicit ".5_0" == .str ".5_0"
#guard resolveImplicit "1e+" == .str "1e+"
#guard (resolveImplicit "1.e+2").isFloat

-- String fallback
#guard resolveImplicit "hello" == .str "hello"
#guard resolveImplicit "Hello World" == .str "Hello World"
#guard resolveImplicit "yes" == .str "yes"   -- NOT bool in YAML 1.2.2

-- Explicit tag override
#guard resolveScalar "42" (some "tag:yaml.org,2002:str") == .str "42"
#guard resolveScalar "true" (some "tag:yaml.org,2002:str") == .str "true"
#guard resolveScalar "" (some "tag:yaml.org,2002:str") == .str ""
#guard resolveScalar "42" (some "tag:yaml.org,2002:int") == .int 42
#guard resolveScalar "hello" (some "tag:yaml.org,2002:null") == .null

-- Resolve on YamlValue (isXxx Boolean checks)
#guard (resolve (.scalar { content := "hello", style := .plain })).isStr
#guard (resolve (.scalar { content := "42", style := .plain })).isInt
#guard (resolve (.scalar { content := "true", style := .plain })).isBool
#guard (resolve (.scalar { content := "null", style := .plain })).isNull
#guard (resolve (.sequence .block #[] none none)).isSeq
#guard (resolve (.mapping .block #[] none none)).isMap

-- Float resolution (§10.3.2)
#guard resolveImplicit ".inf" == .float (.inf true)
#guard resolveImplicit "-.inf" == .float (.inf false)
#guard resolveImplicit ".nan" == .float .nan
#guard resolveImplicit "foo bar" == .str "foo bar"

-- resolve on complete YamlValue constructors (equality)
#guard resolve (.scalar ⟨"42", .plain, none, none, none⟩) == .int 42
#guard resolve (.scalar ⟨"true", .plain, none, none, none⟩) == .bool true
#guard resolve (.scalar ⟨"hello", .plain, none, none, none⟩) == .str "hello"

-- Style-aware resolution (§10.3.2): only plain untagged scalars are typed
#guard resolve (.scalar ⟨"42", .doubleQuoted, none, none, none⟩) == .str "42"
#guard resolve (.scalar ⟨"true", .singleQuoted, none, none, none⟩) == .str "true"
#guard resolve (.scalar ⟨"null", .doubleQuoted, none, none, none⟩) == .str "null"
#guard resolve (.scalar ⟨"42", .literal, none, none, none⟩) == .str "42"
#guard resolve (.scalar ⟨"42", .folded, none, none, none⟩) == .str "42"
-- An explicit tag wins over style, in shorthand or URI form
#guard resolve (.scalar ⟨"42", .doubleQuoted, some "!!int", none, none⟩) == .int 42
#guard resolve (.scalar ⟨"42", .plain, some "tag:yaml.org,2002:str", none, none⟩) == .str "42"
#guard resolve (.scalar ⟨"42", .plain, some "!<tag:yaml.org,2002:str>", none, none⟩) == .str "42"

-- Explicit tag overrides via resolve
#guard resolve (.scalar ⟨"true", .plain, some "tag:yaml.org,2002:str", none, none⟩) == .str "true"
#guard resolve (.scalar ⟨"42", .plain, some "tag:yaml.org,2002:str", none, none⟩) == .str "42"
#guard resolve (.scalar ⟨"hello", .plain, some "tag:yaml.org,2002:null", none, none⟩) == .null

end L4YAML.Schema.Proofs

end Blanket
