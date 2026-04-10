/-
  FFI Export Layer — C-callable wrappers for the verified YAML parser

  This module wraps the safe parsing and dumping API into functions
  exported via `@[export]`, making them callable from C (and transitively
  from Python, Rust, etc.) through `libl4yaml.so`.

  All exported functions operate on opaque `lean_object *` handles or
  flat C-compatible scalars (`UInt8`, `UInt32`, `USize`).  The C shim
  (`ffi/l4yaml_shim.c`) converts between `const char *` and Lean
  `String` at the boundary.

  See `C_PYTHON_APIs.md` for the full design.
-/
import L4YAML.Types
import L4YAML.Limits
import L4YAML.Dump
import L4YAML.Config

set_option autoImplicit false

namespace L4YAML.FFI

open L4YAML
open L4YAML.Dump (dump dumpDocumentsWithComments DumpConfig)
open L4YAML.Config (parseConfigYaml)

/-! ## Preset Lookup -/

/-- Map a `UInt8` preset code to `ParserLimits`.

    | Code | Preset |
    |------|--------|
    | 0    | default |
    | 1    | strict |
    | 2    | permissive |
    | 3    | unlimited |
    | 4    | safeTagsOnly |
    | _    | default |
-/
def presetToLimits (preset : UInt8) : ParserLimits :=
  match preset with
  | 1 => ParserLimits.strict
  | 2 => ParserLimits.permissive
  | 3 => ParserLimits.unlimited
  | 4 => ParserLimits.safeTagsOnly
  | _ => {}

/-! ## Parsing -/

/-- Parse a YAML string into an array of documents with limit enforcement.

    Returns `Except ParseError (Array YamlDocument)` as an opaque handle.
    Caller inspects the result via `l4yaml_result_is_ok` etc. -/
@[export l4yaml_parse_safe]
def parseSafe (input : @& String) (preset : UInt8) : Except ParseError (Array YamlDocument) :=
  parseYamlSafe input (presetToLimits preset)

/-- Parse a YAML string expecting a single document.

    Returns `Except ParseError YamlValue` as an opaque handle. -/
@[export l4yaml_parse_single_safe]
def parseSingleSafe (input : @& String) (preset : UInt8) : Except ParseError YamlValue :=
  parseYamlSingleSafe input (presetToLimits preset)

/-! ## Result Inspection -/

/-- Check whether a parse result is `Except.ok`.  Returns 1 for ok, 0 for error. -/
@[export l4yaml_result_is_ok_impl]
def resultIsOk (result : @& Except ParseError (Array YamlDocument)) : UInt8 :=
  match result with
  | .ok _ => 1
  | .error _ => 0

/-- Check whether a single-value parse result is `Except.ok`. -/
@[export l4yaml_result_single_is_ok_impl]
def resultSingleIsOk (result : @& Except ParseError YamlValue) : UInt8 :=
  match result with
  | .ok _ => 1
  | .error _ => 0

/-- Extract the error message from a failed multi-doc parse result.
    Returns the empty string if the result is actually ok. -/
@[export l4yaml_result_get_error]
def resultGetError (result : @& Except ParseError (Array YamlDocument)) : String :=
  match result with
  | .error e => toString e
  | .ok _ => ""

/-- Extract the error message from a failed single-value parse result. -/
@[export l4yaml_result_single_get_error]
def resultSingleGetError (result : @& Except ParseError YamlValue) : String :=
  match result with
  | .error e => toString e
  | .ok _ => ""

/-- Extract the `Array YamlDocument` from a successful multi-doc result.
    Panics if the result is an error (caller must check `resultIsOk` first). -/
@[export l4yaml_result_docs_impl]
def resultGetDocs (result : @& Except ParseError (Array YamlDocument)) : Array YamlDocument :=
  match result with
  | .ok docs => docs
  | .error _ => #[]

/-- Extract the `YamlValue` from a successful single-value result.
    Returns `YamlValue.null` if the result is an error. -/
@[export l4yaml_result_value_impl]
def resultGetValue (result : @& Except ParseError YamlValue) : YamlValue :=
  match result with
  | .ok v => v
  | .error _ => YamlValue.null

/-! ## Document Array Access -/

/-- Number of documents in a parsed array. -/
@[export l4yaml_docs_count_impl]
def docsCount (docs : @& Array YamlDocument) : UInt32 :=
  docs.size.toUInt32

/-- Get the i-th document from the array.  Returns a default document if out of bounds. -/
@[export l4yaml_docs_get_impl]
def docsGet (docs : @& Array YamlDocument) (i : UInt32) : YamlDocument :=
  let idx := i.toNat
  if h : idx < docs.size then docs[idx] else { value := YamlValue.null }

/-- Root value of a document. -/
@[export l4yaml_doc_root_impl]
def docValue (doc : @& YamlDocument) : YamlValue :=
  doc.value

/-! ## Value Inspection -/

/-- Node kind tag: 0 = scalar, 1 = sequence, 2 = mapping, 3 = alias. -/
@[export l4yaml_value_kind_impl]
def valueTag (val : @& YamlValue) : UInt8 :=
  match val with
  | .scalar _ => 0
  | .sequence .. => 1
  | .mapping .. => 2
  | .alias _ => 3

/-- Scalar content as a String.  Returns the empty string for non-scalar values. -/
@[export l4yaml_value_as_string]
def valueAsString (val : @& YamlValue) : String :=
  match val with
  | .scalar s => s.content
  | _ => ""

/-- Number of items in a sequence.  Returns 0 for non-sequence values. -/
@[export l4yaml_value_seq_length_impl]
def valueSeqLength (val : @& YamlValue) : UInt32 :=
  match val with
  | .sequence _ items .. => items.size.toUInt32
  | _ => 0

/-- Get the i-th element from a sequence.  Returns `YamlValue.null` if
    the value is not a sequence or the index is out of bounds. -/
@[export l4yaml_value_seq_get_impl]
def valueSeqGet (val : @& YamlValue) (i : UInt32) : YamlValue :=
  match val with
  | .sequence _ items .. =>
    let idx := i.toNat
    if h : idx < items.size then items[idx] else YamlValue.null
  | _ => YamlValue.null

/-- Number of key-value pairs in a mapping.  Returns 0 for non-mapping values. -/
@[export l4yaml_value_map_length_impl]
def valueMapLength (val : @& YamlValue) : UInt32 :=
  match val with
  | .mapping _ pairs .. => pairs.size.toUInt32
  | _ => 0

/-- Get the key of the i-th pair in a mapping.  Returns `YamlValue.null` if
    the value is not a mapping or the index is out of bounds. -/
@[export l4yaml_value_map_key_impl]
def valueMapKey (val : @& YamlValue) (i : UInt32) : YamlValue :=
  match val with
  | .mapping _ pairs .. =>
    let idx := i.toNat
    if h : idx < pairs.size then pairs[idx].1 else YamlValue.null
  | _ => YamlValue.null

/-- Get the value of the i-th pair in a mapping.  Returns `YamlValue.null` if
    the value is not a mapping or the index is out of bounds. -/
@[export l4yaml_value_map_val_impl]
def valueMapVal (val : @& YamlValue) (i : UInt32) : YamlValue :=
  match val with
  | .mapping _ pairs .. =>
    let idx := i.toNat
    if h : idx < pairs.size then pairs[idx].2 else YamlValue.null
  | _ => YamlValue.null

/-- Look up a key in a mapping by string content.
    Returns the value wrapped in `Option`, as an opaque handle.
    `none` means key not found or the value is not a mapping. -/
@[export l4yaml_value_lookup_raw]
def valueLookup (val : @& YamlValue) (key : @& String) : Option YamlValue :=
  val.lookup? key

/-- Get the YAML tag string of a value.  Returns `Option String`:
    `some tag` if the value carries an explicit tag, `none` otherwise. -/
@[export l4yaml_value_tag_raw]
def valueYamlTag (val : @& YamlValue) : Option String :=
  match val with
  | .scalar s => s.tag
  | .sequence _ _ tag _ => tag
  | .mapping _ _ tag _ => tag
  | .alias _ => none

/-- Get the anchor name of a value.  Returns `Option String`:
    `some name` if the value carries an anchor, `none` otherwise. -/
@[export l4yaml_value_anchor_raw]
def valueAnchor (val : @& YamlValue) : Option String :=
  match val with
  | .scalar s => s.anchor
  | .sequence _ _ _ anchor => anchor
  | .mapping _ _ _ anchor => anchor
  | .alias _ => none

/-! ## Option Inspection (for lookup results) -/

/-- Check whether an `Option YamlValue` is `some`. Returns 1 for some, 0 for none. -/
@[export l4yaml_option_is_some_impl]
def optionIsSome (opt : @& Option YamlValue) : UInt8 :=
  match opt with
  | some _ => 1
  | none => 0

/-- Extract the value from `Option YamlValue`.
    Returns `YamlValue.null` for `none`. -/
@[export l4yaml_option_get_impl]
def optionGet (opt : @& Option YamlValue) : YamlValue :=
  match opt with
  | some v => v
  | none => YamlValue.null

/-! ## Dumping -/

/-- Dump a `YamlValue` to a YAML string with default config. -/
@[export l4yaml_dump_raw]
def dumpValue (val : @& YamlValue) : String :=
  dump val

/-- Dump an `Array YamlDocument` to a YAML string (multi-document stream). -/
@[export l4yaml_dump_docs_raw]
def dumpDocs (docs : @& Array YamlDocument) : String :=
  dumpDocumentsWithComments docs

/-! ## String Utilities -/

/-- UTF-8 byte length of a Lean `String`. -/
@[export l4yaml_string_byte_length_impl]
def stringByteLength (s : @& String) : UInt32 :=
  s.utf8ByteSize.toUInt32

/-! ## Config Deserialization (self-hosted) -/

/-- Parse a YAML string into `ParserLimits`.  Uses hardcoded strict limits
    for the bootstrap parse (the parser safely parsing its own config).

    Returns `Except String ParserLimits` as an opaque handle. -/
@[export l4yaml_parse_limits_yaml_impl]
def parseLimitsYaml (input : @& String) : Except String ParserLimits :=
  parseConfigYaml ParserLimits input

/-- Parse a YAML string into `DumpConfig`.  Same bootstrap strategy. -/
@[export l4yaml_parse_dump_config_yaml_impl]
def parseDumpConfigYaml (input : @& String) : Except String DumpConfig :=
  parseConfigYaml DumpConfig input

/-- Check whether a config parse result is ok. -/
@[export l4yaml_config_result_is_ok_impl]
def configResultIsOk (result : @& Except String ParserLimits) : UInt8 :=
  match result with
  | .ok _ => 1
  | .error _ => 0

/-- Extract error message from a failed config parse.
    Returns empty string on success. -/
@[export l4yaml_config_result_get_error_impl]
def configResultGetError (result : @& Except String ParserLimits) : String :=
  match result with
  | .error e => e
  | .ok _ => ""

/-- Extract ParserLimits from a successful config parse.
    Returns default limits if the result is an error. -/
@[export l4yaml_config_result_get_limits_impl]
def configResultGetLimits (result : @& Except String ParserLimits) : ParserLimits :=
  match result with
  | .ok v => v
  | .error _ => {}

/-- Parse a YAML string with custom limits from a YAML config string.
    Two-step bootstrap: first parse the config YAML into ParserLimits,
    then parse the input YAML with those limits.

    Config parse errors are surfaced as scan errors with the config
    error message embedded.

    Returns `Except ParseError (Array YamlDocument)` as an opaque handle. -/
@[export l4yaml_parse_with_yaml_config_impl]
def parseWithYamlConfig (input : @& String) (configYaml : @& String)
    : Except ParseError (Array YamlDocument) :=
  match parseConfigYaml ParserLimits configYaml with
  | .error _ => parseYamlSafe input {}  -- fall back to defaults on config error
  | .ok limits => parseYamlSafe input limits

/-- Dump a YamlValue with a YAML-configured DumpConfig.
    Falls back to default DumpConfig on config parse error. -/
@[export l4yaml_dump_with_yaml_config_impl]
def dumpWithYamlConfig (val : @& YamlValue) (configYaml : @& String) : String :=
  let cfg := match parseConfigYaml DumpConfig configYaml with
    | .ok c => c
    | .error _ => {}
  dump val cfg

end L4YAML.FFI
