/-
  Parser Security: Limits and Tag Validation

  YAML 1.2.2 §3.1 — Processes: The Load step (Parse + Compose) must be
  safe against adversarial input.  This module implements configurable
  limits that prevent:

  1. **Denial-of-Service (DoS)**: Billion-laugh alias expansion,
     excessive nesting, oversized scalars/collections.
  2. **Arbitrary Code Execution (ACE)**: Language-specific tags
     (`!!python/object`, `!!ruby/object`, etc.) that downstream
     consumers might deserialize unsafely.

  ## Usage

  ```lean
  -- Safe mode (recommended for untrusted input):
  parseYamlSafe input                -- default limits
  parseYamlSafe input .strict        -- strict limits

  -- Unlimited mode (backward-compatible, trusted input only):
  parseYaml input                    -- unchanged, no limits
  ```

  See `LIMITS.md` for threat model and design rationale.
-/
import L4YAML.Types
import L4YAML.Token
import L4YAML.Scanner
import L4YAML.TokenParser

namespace L4YAML

/-! ## Limit Configuration Types -/

/-- Limits on alias (anchor/`*ref`) resolution.
    Prevents billion-laugh exponential expansion and cyclic references. -/
structure AliasLimits where
  /-- Maximum depth of alias resolution chains.
      Example: `a: &a *b, b: &b *c, c: "x"` → depth 3.
      Default: 50 -/
  maxAliasDepth : Nat := 50
  /-- Maximum total alias substitution steps per document.
      Each `.alias` → value replacement counts as one.
      Default: 10,000 -/
  maxAliasExpansions : Nat := 10_000
  /-- Maximum total nodes in the resolved tree.
      Default: 100,000 -/
  maxResolvedNodes : Nat := 100_000
  /-- Detect and reject cyclic aliases (`a: &a [*a]`).
      Default: true -/
  rejectCycles : Bool := true
  deriving Repr, BEq, Inhabited

/-- Limits on tree structure (depth, collection sizes, scalar sizes). -/
structure StructuralLimits where
  /-- Maximum nesting depth of collections.
      Default: 100 -/
  maxDepth : Nat := 100
  /-- Maximum elements in a single sequence.
      Default: 100,000 -/
  maxSequenceLength : Nat := 100_000
  /-- Maximum key-value pairs in a single mapping.
      Default: 100,000 -/
  maxMappingSize : Nat := 100_000
  /-- Maximum scalar value length in bytes.
      Default: 10 MB -/
  maxScalarBytes : Nat := 10_485_760
  /-- Maximum total nodes across all documents.
      Default: 1,000,000 -/
  maxTotalNodes : Nat := 1_000_000
  deriving Repr, BEq, Inhabited

/-- Limits on the document stream. -/
structure DocumentLimits where
  /-- Maximum documents in a stream.
      Default: 100 -/
  maxDocuments : Nat := 100
  /-- Maximum anchors per document.
      Default: 10,000 -/
  maxAnchors : Nat := 10_000
  /-- Maximum input size in bytes.
      Default: 100 MB -/
  maxInputBytes : Nat := 104_857_600
  deriving Repr, BEq, Inhabited

/-- Tag validation policy. -/
inductive TagPolicy where
  /-- Accept all tags (**UNSAFE** — only for trusted input). -/
  | allowAll
  /-- Reject all explicit tags; only implicit typing allowed. -/
  | rejectAll
  /-- Only accept tags in the `allowed` list. -/
  | whitelist (allowed : List String)
  /-- Reject tags whose prefix matches the `forbidden` list. -/
  | blacklist (forbidden : List String)
  /-- Only YAML 1.2 Core Schema tags. -/
  | coreSchemaOnly
  deriving Repr, BEq, Inhabited

/-- Tag security limits. -/
structure TagLimits where
  /-- Tag validation policy.  Default: `coreSchemaOnly`. -/
  policy : TagPolicy := .coreSchemaOnly
  /-- Reject language-specific tags (`!!python/*`, etc.).
      Default: true -/
  rejectLanguageTags : Bool := true
  /-- Maximum tag string length in bytes.  Default: 1024 -/
  maxTagLength : Nat := 1_024
  /-- Maximum unique tags per document.  Default: 100 -/
  maxUniqueTags : Nat := 100
  /-- Reject custom `%TAG` handles.  Default: false -/
  rejectCustomHandles : Bool := false
  /-- Maximum `%TAG` handle prefix length in bytes.  Default: 256 -/
  maxHandlePrefixLength : Nat := 256
  deriving Repr, BEq, Inhabited

/-- Combined parser limits. -/
structure ParserLimits where
  alias : AliasLimits := {}
  structural : StructuralLimits := {}
  document : DocumentLimits := {}
  tag : TagLimits := {}
  /-- Master switch — `false` disables all checks.  Default: true -/
  enabled : Bool := true
  deriving Repr, BEq, Inhabited

namespace ParserLimits

/-- Conservative limits for untrusted input (web APIs, user uploads). -/
def strict : ParserLimits := {
  alias := { maxAliasDepth := 20, maxAliasExpansions := 1_000,
             maxResolvedNodes := 10_000 }
  structural := { maxDepth := 50, maxSequenceLength := 10_000,
                  maxMappingSize := 10_000, maxScalarBytes := 1_048_576,
                  maxTotalNodes := 100_000 }
  document := { maxDocuments := 10, maxAnchors := 1_000,
                maxInputBytes := 10_485_760 }
  tag := { policy := .coreSchemaOnly, rejectLanguageTags := true,
           maxTagLength := 256, maxUniqueTags := 20,
           rejectCustomHandles := true }
}

/-- Permissive limits for trusted internal use. -/
def permissive : ParserLimits := {
  alias := { maxAliasDepth := 500, maxAliasExpansions := 1_000_000,
             maxResolvedNodes := 10_000_000 }
  structural := { maxDepth := 1000, maxSequenceLength := 10_000_000,
                  maxMappingSize := 10_000_000, maxScalarBytes := 1_073_741_824,
                  maxTotalNodes := 100_000_000 }
  document := { maxDocuments := 10_000, maxAnchors := 1_000_000,
                maxInputBytes := 10_737_418_240 }
  tag := { policy := .coreSchemaOnly, rejectLanguageTags := true,
           maxTagLength := 1024, maxUniqueTags := 1000,
           rejectCustomHandles := false }
}

/-- All checks disabled.  **Do not use with untrusted input.** -/
def unlimited : ParserLimits := { enabled := false }

/-- No resource limits but strict tag validation. -/
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
           maxTagLength := 256, maxUniqueTags := 100,
           rejectCustomHandles := true }
}

end ParserLimits

/-! ## Error Types -/

/-- Errors during alias resolution. -/
inductive AliasLimitError where
  | cyclicAlias (name : String) (path : List String)
  | depthExceeded (depth : Nat) (limit : Nat) (aliasName : String)
  | expansionCountExceeded (count : Nat) (limit : Nat)
  | nodeCountExceeded (count : Nat) (limit : Nat)
  deriving Repr, BEq, Inhabited

def AliasLimitError.toString : AliasLimitError → String
  | .cyclicAlias name path =>
    s!"Cyclic alias detected: '{name}' (resolution path: {" → ".intercalate path})"
  | .depthExceeded depth limit aliasName =>
    s!"Alias resolution depth exceeded: {depth} > {limit} (resolving '{aliasName}')"
  | .expansionCountExceeded count limit =>
    s!"Alias expansion count exceeded: {count} > {limit}"
  | .nodeCountExceeded count limit =>
    s!"Resolved node count exceeded: {count} > {limit}"

instance : ToString AliasLimitError where toString := AliasLimitError.toString

/-- Errors for structural limits. -/
inductive StructuralLimitError where
  | depthExceeded (depth : Nat) (limit : Nat) (path : YamlPath)
  | sequenceTooLarge (length : Nat) (limit : Nat) (path : YamlPath)
  | mappingTooLarge (size : Nat) (limit : Nat) (path : YamlPath)
  | scalarTooLarge (bytes : Nat) (limit : Nat) (path : YamlPath)
  | totalNodesExceeded (count : Nat) (limit : Nat)
  deriving Repr, BEq, Inhabited

def pathToString (path : YamlPath) : String :=
  if path.size == 0 then "root"
  else path.foldl (fun acc seg =>
    match seg with
    | .index i => s!"{acc}[{i}]"
    | .key k => s!"{acc}.{k}") ""

def StructuralLimitError.toString : StructuralLimitError → String
  | .depthExceeded depth limit path =>
    s!"Nesting depth exceeded: {depth} > {limit} at {pathToString path}"
  | .sequenceTooLarge length limit path =>
    s!"Sequence too large: {length} elements > {limit} at {pathToString path}"
  | .mappingTooLarge size limit path =>
    s!"Mapping too large: {size} pairs > {limit} at {pathToString path}"
  | .scalarTooLarge bytes limit path =>
    s!"Scalar too large: {bytes} bytes > {limit} at {pathToString path}"
  | .totalNodesExceeded count limit =>
    s!"Total node count exceeded: {count} > {limit}"

instance : ToString StructuralLimitError where toString := StructuralLimitError.toString

/-- Errors for document-level limits. -/
inductive DocumentLimitError where
  | tooManyDocuments (count : Nat) (limit : Nat)
  | tooManyAnchors (count : Nat) (limit : Nat) (docIndex : Nat)
  | inputTooLarge (bytes : Nat) (limit : Nat)
  deriving Repr, BEq, Inhabited

def DocumentLimitError.toString : DocumentLimitError → String
  | .tooManyDocuments count limit =>
    s!"Too many documents in stream: {count} > {limit}"
  | .tooManyAnchors count limit docIndex =>
    s!"Too many anchors in document {docIndex}: {count} > {limit}"
  | .inputTooLarge bytes limit =>
    s!"Input too large: {bytes} bytes > {limit}"

instance : ToString DocumentLimitError where toString := DocumentLimitError.toString

/-- Tag security errors — may indicate an attack attempt. -/
inductive TagSecurityError where
  | forbiddenTag (tag : String) (reason : String)
  | dangerousLanguageTag (tag : String) (language : String)
  | tagTooLong (bytes : Nat) (limit : Nat) (tag : String)
  | tooManyUniqueTags (count : Nat) (limit : Nat)
  | customHandleRejected (handle : String) (tagPrefix : String)
  | handlePrefixTooLong (bytes : Nat) (limit : Nat) (tagPrefix : String)
  | nonCoreSchemaTag (tag : String)
  deriving Repr, BEq, Inhabited

def TagSecurityError.extractLanguage (tag : String) : String :=
  if tag.startsWith "tag:yaml.org,2002:python/" || tag.startsWith "!!python/" then "Python"
  else if tag.startsWith "tag:yaml.org,2002:java/" || tag.startsWith "!!java/" then "Java"
  else if tag.startsWith "tag:yaml.org,2002:ruby/" || tag.startsWith "!!ruby/" then "Ruby"
  else if tag.startsWith "tag:yaml.org,2002:php/" || tag.startsWith "!!php/" then "PHP"
  else if tag.startsWith "tag:yaml.org,2002:perl/" || tag.startsWith "!!perl/" then "Perl"
  else "unknown"

def TagSecurityError.toString : TagSecurityError → String
  | .forbiddenTag tag reason =>
    s!"SECURITY: Forbidden tag '{tag}': {reason}"
  | .dangerousLanguageTag tag language =>
    s!"SECURITY: Dangerous {language} tag '{tag}' — potential code execution"
  | .tagTooLong bytes limit tag =>
    s!"SECURITY: Tag too long: {bytes} bytes > {limit} (tag: {tag.take 50}…)"
  | .tooManyUniqueTags count limit =>
    s!"SECURITY: Too many unique tags: {count} > {limit}"
  | .customHandleRejected handle tagPrefix =>
    s!"SECURITY: Custom tag handle rejected: {handle} → {tagPrefix}"
  | .handlePrefixTooLong bytes limit tagPrefix =>
    s!"SECURITY: Tag handle prefix too long: {bytes} bytes > {limit} (prefix: {tagPrefix.take 50}…)"
  | .nonCoreSchemaTag tag =>
    s!"SECURITY: Non-Core-Schema tag '{tag}'"

instance : ToString TagSecurityError where toString := TagSecurityError.toString

/-- Top-level error for all limit violations. -/
inductive LimitError where
  | aliasLimit (err : AliasLimitError)
  | structuralLimit (err : StructuralLimitError)
  | documentLimit (err : DocumentLimitError)
  | tagSecurity (err : TagSecurityError)
  deriving Repr, BEq, Inhabited

def LimitError.toString : LimitError → String
  | .aliasLimit err => s!"Alias limit violation: {err}"
  | .structuralLimit err => s!"Structural limit violation: {err}"
  | .documentLimit err => s!"Document limit violation: {err}"
  | .tagSecurity err => s!"{err}"

instance : ToString LimitError where toString := LimitError.toString

/-- Unified parse error: syntax errors *or* limit violations. -/
inductive ParseError where
  | scanError (err : ScanError)
  | limitError (err : LimitError)
  deriving Repr, BEq, Inhabited

def ParseError.toString : ParseError → String
  | .scanError err => s!"{err}"
  | .limitError err => s!"{err}"

instance : ToString ParseError where toString := ParseError.toString

/-! ## Tag Validation -/

/-- YAML 1.2 Core Schema safe tags (both full URI and shorthand forms). -/
def coreSchemaWhitelist : List String :=
  [ "tag:yaml.org,2002:str",   "!!str"
  , "tag:yaml.org,2002:int",   "!!int"
  , "tag:yaml.org,2002:float", "!!float"
  , "tag:yaml.org,2002:bool",  "!!bool"
  , "tag:yaml.org,2002:null",  "!!null"
  , "tag:yaml.org,2002:seq",   "!!seq"
  , "tag:yaml.org,2002:map",   "!!map"
  , "tag:yaml.org,2002:binary", "!!binary"
  , "tag:yaml.org,2002:timestamp", "!!timestamp"
  ]

/-- Known dangerous tag prefixes (language-specific deserialization). -/
def dangerousTagPrefixes : List String :=
  [ "tag:yaml.org,2002:python/", "!!python/"
  , "tag:yaml.org,2002:java/",   "!!java/"
  , "tag:yaml.org,2002:ruby/",   "!!ruby/"
  , "tag:yaml.org,2002:php/",    "!!php/"
  , "tag:yaml.org,2002:perl/",   "!!perl/"
  ]

/-- Check a single tag against the tag limits.  Returns `unit` or a
    `TagSecurityError`. -/
def validateTag (tag : String) (limits : TagLimits) : Except TagSecurityError Unit := do
  -- Length check
  if tag.utf8ByteSize > limits.maxTagLength then
    throw (.tagTooLong tag.utf8ByteSize limits.maxTagLength tag)
  -- Language-specific tag check
  if limits.rejectLanguageTags then
    if dangerousTagPrefixes.any (fun pfx => tag.startsWith pfx) then
      throw (.dangerousLanguageTag tag (TagSecurityError.extractLanguage tag))
  -- Policy check
  match limits.policy with
  | .allowAll => pure ()
  | .rejectAll => throw (.forbiddenTag tag "all explicit tags rejected")
  | .whitelist allowed =>
    if allowed.contains tag then pure ()
    else throw (.forbiddenTag tag "not in whitelist")
  | .blacklist forbidden =>
    if forbidden.any (fun pfx => tag.startsWith pfx) then
      throw (.forbiddenTag tag "matches blacklist pattern")
    else pure ()
  | .coreSchemaOnly =>
    if coreSchemaWhitelist.contains tag then pure ()
    else throw (.nonCoreSchemaTag tag)

/-- Validate `%TAG` directives against tag limits. -/
def validateDirectives (directives : Array Directive) (limits : TagLimits)
    : Except TagSecurityError Unit := do
  for d in directives do
    match d with
    | .tag handle tagPrefix =>
      if limits.rejectCustomHandles then
        throw (.customHandleRejected handle tagPrefix)
      if tagPrefix.utf8ByteSize > limits.maxHandlePrefixLength then
        throw (.handlePrefixTooLong tagPrefix.utf8ByteSize limits.maxHandlePrefixLength tagPrefix)
    | .yaml _ => pure ()

/-! ## Collecting Tags from a Value Tree -/

/-- Extract the tag from a `YamlValue`, if present. -/
def getNodeTag : YamlValue → Option String
  | .scalar s => s.tag
  | .sequence _ _ tag _ => tag
  | .mapping _ _ tag _ => tag
  | .alias _ => none

/-- Collect all explicit tags in a value tree (unique). -/
partial def collectTags (v : YamlValue) : List String :=
  go v [] |>.eraseDups
where
  go : YamlValue → List String → List String
    | .scalar s, acc => match s.tag with | some t => t :: acc | none => acc
    | .sequence _ items tag _, acc =>
      let acc := match tag with | some t => t :: acc | none => acc
      items.foldl (fun a item => go item a) acc
    | .mapping _ pairs tag _, acc =>
      let acc := match tag with | some t => t :: acc | none => acc
      pairs.foldl (fun a (k, v) => go v (go k a)) acc
    | .alias _, acc => acc

/-- Validate all tags in a value tree against tag limits. -/
def validateValueTags (v : YamlValue) (limits : TagLimits) : Except TagSecurityError Unit := do
  let tags := collectTags v
  -- Unique tag count
  if tags.length > limits.maxUniqueTags then
    throw (.tooManyUniqueTags tags.length limits.maxUniqueTags)
  -- Validate each tag
  for tag in tags do
    validateTag tag limits

/-! ## Alias Resolution with Limits -/

/-- Mutable state threaded through limited alias resolution. -/
structure AliasResolveState where
  expansions : Nat := 0
  nodeCount : Nat := 0

/-- Resolve aliases with depth, expansion, node-count, and cycle limits.

    Unlike `YamlValue.resolveAliases` (which has no bounds), this version
    tracks resolution depth and total expansion count, failing with an
    `AliasLimitError` when any limit is exceeded. -/
partial def resolveAliasesLimited (v : YamlValue) (anchors : Array (String × YamlValue))
    (limits : AliasLimits) : Except AliasLimitError YamlValue := do
  let (result, _) ← go v anchors limits 0 [] { expansions := 0, nodeCount := 0 }
  return result
where
  go (v : YamlValue) (anchors : Array (String × YamlValue)) (limits : AliasLimits)
     (depth : Nat) (visiting : List String) (st : AliasResolveState)
     : Except AliasLimitError (YamlValue × AliasResolveState) := do
    -- Node count
    let st := { st with nodeCount := st.nodeCount + 1 }
    if st.nodeCount > limits.maxResolvedNodes then
      throw (.nodeCountExceeded st.nodeCount limits.maxResolvedNodes)
    match v with
    | .scalar _ => return (v, st)
    | .sequence style items tag anchor => do
      let (items', st) ← goList items.toList anchors limits depth visiting st
      return (.sequence style items'.toArray tag anchor, st)
    | .mapping style pairs tag anchor => do
      let (pairs', st) ← goPairs pairs.toList anchors limits depth visiting st
      return (.mapping style pairs'.toArray tag anchor, st)
    | .alias name => do
      -- Cycle detection
      if limits.rejectCycles && visiting.contains name then
        throw (.cyclicAlias name visiting)
      -- Depth check
      if depth ≥ limits.maxAliasDepth then
        throw (.depthExceeded depth limits.maxAliasDepth name)
      -- Expansion count
      let st := { st with expansions := st.expansions + 1 }
      if st.expansions > limits.maxAliasExpansions then
        throw (.expansionCountExceeded st.expansions limits.maxAliasExpansions)
      -- Resolve
      match anchors.findSome? (fun (n, val) => if n == name then some val else none) with
      | some val => go val anchors limits (depth + 1) (name :: visiting) st
      | none => return (v, st)  -- unresolved alias: preserve as-is
  goList (vs : List YamlValue) (anchors : Array (String × YamlValue)) (limits : AliasLimits)
      (depth : Nat) (visiting : List String) (st : AliasResolveState)
      : Except AliasLimitError (List YamlValue × AliasResolveState) := do
    match vs with
    | [] => return ([], st)
    | v :: rest => do
      let (v', st) ← go v anchors limits depth visiting st
      let (rest', st) ← goList rest anchors limits depth visiting st
      return (v' :: rest', st)
  goPairs (ps : List (YamlValue × YamlValue)) (anchors : Array (String × YamlValue))
      (limits : AliasLimits) (depth : Nat) (visiting : List String) (st : AliasResolveState)
      : Except AliasLimitError (List (YamlValue × YamlValue) × AliasResolveState) := do
    match ps with
    | [] => return ([], st)
    | (k, v) :: rest => do
      let (k', st) ← go k anchors limits depth visiting st
      let (v', st) ← go v anchors limits depth visiting st
      let (rest', st) ← goPairs rest anchors limits depth visiting st
      return ((k', v') :: rest', st)

/-! ## Structural Validation -/

/-- Count total nodes in a value tree. -/
partial def countNodes (v : YamlValue) : Nat :=
  match v with
  | .scalar _ => 1
  | .sequence _ items _ _ =>
    1 + items.foldl (fun acc item => acc + countNodes item) 0
  | .mapping _ pairs _ _ =>
    1 + pairs.foldl (fun acc (k, v) => acc + countNodes k + countNodes v) 0
  | .alias _ => 1

/-- Validate structural limits on a resolved value tree. -/
partial def validateStructure (v : YamlValue) (limits : StructuralLimits) (path : YamlPath := #[])
    (depth : Nat := 0) : Except StructuralLimitError Unit := do
  match v with
  | .scalar s =>
    if s.content.utf8ByteSize > limits.maxScalarBytes then
      throw (.scalarTooLarge s.content.utf8ByteSize limits.maxScalarBytes path)
  | .sequence _ items _ _ =>
    if depth > limits.maxDepth then
      throw (.depthExceeded depth limits.maxDepth path)
    if items.size > limits.maxSequenceLength then
      throw (.sequenceTooLarge items.size limits.maxSequenceLength path)
    goSeq items.toList 0 limits path depth
  | .mapping _ pairs _ _ =>
    if depth > limits.maxDepth then
      throw (.depthExceeded depth limits.maxDepth path)
    if pairs.size > limits.maxMappingSize then
      throw (.mappingTooLarge pairs.size limits.maxMappingSize path)
    goMap pairs.toList 0 limits path depth
  | .alias _ => pure ()
where
  goSeq (items : List YamlValue) (idx : Nat) (limits : StructuralLimits)
      (path : YamlPath) (depth : Nat) : Except StructuralLimitError Unit := do
    match items with
    | [] => pure ()
    | v :: rest =>
      validateStructure v limits (path.push (.index idx)) (depth + 1)
      goSeq rest (idx + 1) limits path depth
  goMap (pairs : List (YamlValue × YamlValue)) (idx : Nat) (limits : StructuralLimits)
      (path : YamlPath) (depth : Nat) : Except StructuralLimitError Unit := do
    match pairs with
    | [] => pure ()
    | (k, v) :: rest =>
      let keyStr := match k with | .scalar s => s.content | _ => s!"[{idx}]"
      validateStructure k limits (path.push (.key keyStr)) (depth + 1)
      validateStructure v limits (path.push (.key keyStr)) (depth + 1)
      goMap rest (idx + 1) limits path depth

/-! ## Limited Compose -/

/-- Compose a document (resolve aliases + strip anchors) with limit enforcement.

    This is the safe counterpart of `YamlDocument.compose`. -/
def composeLimited (doc : YamlDocument) (limits : ParserLimits) (docIndex : Nat := 0)
    : Except LimitError YamlDocument := do
  -- Anchor count
  if limits.enabled && doc.anchors.size > limits.document.maxAnchors then
    throw (.documentLimit (.tooManyAnchors doc.anchors.size limits.document.maxAnchors docIndex))
  -- Anchor value node count (catches billion-laugh expanded during parsing)
  if limits.enabled then
    let anchorNodes := doc.anchors.foldl (fun acc (_, v) => acc + countNodes v) 0
    if anchorNodes > limits.alias.maxResolvedNodes then
      throw (.aliasLimit (.nodeCountExceeded anchorNodes limits.alias.maxResolvedNodes))
  -- Directive validation (tag handles)
  if limits.enabled then
    match validateDirectives doc.directives limits.tag with
    | .ok () => pure ()
    | .error e => throw (.tagSecurity e)
  -- Tag validation on raw tree (before resolution)
  if limits.enabled then
    match validateValueTags doc.value limits.tag with
    | .ok () => pure ()
    | .error e => throw (.tagSecurity e)
  -- Resolve aliases
  let resolved ←
    if limits.enabled then
      match resolveAliasesLimited doc.value doc.anchors limits.alias with
      | .ok v => pure v
      | .error e => throw (.aliasLimit e)
    else
      pure (doc.value.resolveAliases doc.anchors)
  -- Structural validation on resolved tree
  if limits.enabled then
    match validateStructure resolved limits.structural with
    | .ok () => pure ()
    | .error e => throw (.structuralLimit e)
    -- Total node count
    let nodeCount := countNodes resolved
    if nodeCount > limits.structural.maxTotalNodes then
      throw (.structuralLimit (.totalNodesExceeded nodeCount limits.structural.maxTotalNodes))
  -- Tag validation on resolved tree (aliases may introduce new tags)
  if limits.enabled then
    match validateValueTags resolved limits.tag with
    | .ok () => pure ()
    | .error e => throw (.tagSecurity e)
  return { doc with
    value := resolved.stripAnchors
    anchors := #[] }

/-! ## Safe Parsing API -/

/-- Parse YAML with limit enforcement (**representation graph**).

    This is the safe counterpart of `TokenParser.parseYaml`.  All limit
    categories (input size, document count, alias expansion, structural,
    tag security) are enforced.

    ```lean
    -- Use default limits (suitable for most untrusted input):
    parseYamlSafe input
    -- Use strict limits (web APIs, user uploads):
    parseYamlSafe input .strict
    -- Disable limits (testing only):
    parseYamlSafe input .unlimited
    ``` -/
def parseYamlSafe (input : String) (limits : ParserLimits := {})
    : Except ParseError (Array YamlDocument) := do
  -- Input size check
  if limits.enabled && input.utf8ByteSize > limits.document.maxInputBytes then
    throw (.limitError (.documentLimit (.inputTooLarge input.utf8ByteSize limits.document.maxInputBytes)))
  -- Parse (scan + grammar)
  let docs ← match TokenParser.parseYamlRaw input with
    | .ok docs => pure docs
    | .error e => throw (.scanError e)
  -- Document count check
  if limits.enabled && docs.size > limits.document.maxDocuments then
    throw (.limitError (.documentLimit (.tooManyDocuments docs.size limits.document.maxDocuments)))
  -- Compose each document with limits
  let results ← docs.foldlM (init := (#[] : Array YamlDocument)) fun acc doc =>
    match composeLimited doc limits acc.size with
    | .ok d => pure (acc.push d)
    | .error e => throw (.limitError e)
  return results

/-- Parse YAML expecting one document, with limit enforcement.

    Safe counterpart of `TokenParser.parseYamlSingle`. -/
def parseYamlSingleSafe (input : String) (limits : ParserLimits := {})
    : Except ParseError YamlValue := do
  let docs ← parseYamlSafe input limits
  if docs.size == 0 then return YamlValue.null
  else if docs.size == 1 then return docs[0]!.value
  else throw (.scanError (.multipleDocuments docs.size))

/-- Parse YAML expecting one document, returning the raw document with limits.

    Safe counterpart of `TokenParser.parseYamlSingleRaw`. -/
def parseYamlSingleRawSafe (input : String) (limits : ParserLimits := {})
    : Except ParseError YamlDocument := do
  let docs ← parseYamlSafe input limits
  if docs.size == 0 then return { value := YamlValue.null }
  else if docs.size == 1 then return docs[0]!
  else throw (.scanError (.multipleDocuments docs.size))

end L4YAML
