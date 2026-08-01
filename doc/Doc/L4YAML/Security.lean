/-
  L4YAML Documentation — Security and Parser Limits
-/
import VersoManual

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Security" =>
%%%
tag := "security"
%%%

{index}[security]
YAML parsing is a well-known attack surface.
L4YAML addresses this with configurable parser limits, preset
security profiles, and formal verification of the parsing logic itself.

# Threat Model
%%%
tag := "threat-model"
%%%

YAML parsers face several categories of attack:

 * _Billion-laugh attacks_ — deeply nested aliases that expand
   exponentially, exhausting memory
 * _Denial of service_ — extremely long strings, deeply nested
   structures, or very large collections that consume excessive resources
 * _Arbitrary code execution_ — YAML tags that trigger object
   deserialization in languages with unsafe constructors
   (e.g., Python's `!!python/object`)
 * _Duplicate key confusion_ — multiple identical keys in a mapping,
   where different consumers may pick different values

L4YAML mitigates all of these through its `ParserLimits` configuration.

# ParserLimits
%%%
tag := "parser-limits"
%%%

{index}[ParserLimits]
The `ParserLimits` structure groups four limit families (`alias`,
`structural`, `document`, `tag`) plus a master `enabled` switch
(`L4YAML/Config/Limits.lean`):

:::table +header
*
  * Parameter
  * Default
  * Purpose
*
  * `structural.maxDepth`
  * 100
  * Maximum collection nesting depth
*
  * `structural.maxScalarBytes`
  * 10 MB
  * Maximum scalar value length in bytes — DoS prevention
*
  * `structural.maxSequenceLength`
  * 100,000
  * Maximum elements in a single sequence
*
  * `structural.maxMappingSize`
  * 100,000
  * Maximum key-value pairs in a single mapping
*
  * `structural.maxTotalNodes`
  * 1,000,000
  * Maximum total nodes across all documents
*
  * `alias.maxAliasDepth`
  * 50
  * Maximum alias chain depth
*
  * `alias.maxAliasExpansions`
  * 10,000
  * Maximum alias substitution steps — billion-laugh prevention
*
  * `alias.maxResolvedNodes`
  * 100,000
  * Maximum nodes in the resolved tree
*
  * `alias.rejectCycles`
  * `true`
  * Detect and reject cyclic aliases (`a: &a [*a]`)
*
  * `document.maxDocuments`
  * 100
  * Maximum documents in a stream
*
  * `document.maxAnchors`
  * 10,000
  * Maximum anchors per document
*
  * `document.maxInputBytes`
  * 100 MB
  * Maximum input size in bytes
*
  * `tag.policy`
  * `coreSchemaOnly`
  * Which tags are permitted (rejects e.g. `!!python/object`)
*
  * `tag.rejectLanguageTags`
  * `true`
  * Explicit rejection of language-specific object tags
*
  * `tag.maxTagLength`
  * 1,024
  * Maximum tag length in bytes
:::

(Duplicate-key acceptance is configured separately via
`DuplicateKeyPolicy` in `LoadConfig`, not through `ParserLimits`.)

# Preset Configurations
%%%
tag := "presets"
%%%

{index}[presets]
Four preset configurations are provided for common use cases:

 * *`strict`* — all protections enabled at conservative thresholds.
   Recommended for processing untrusted input (e.g., user uploads,
   network-received configuration).

 * *`default`* — balanced settings suitable for most applications.
   Limits are generous enough for typical configuration files while
   still preventing resource exhaustion.

 * *`permissive`* — reduced validation for trusted input.
   Useful when parsing known-good YAML from controlled sources.

 * *`unlimited`* — all limits disabled.
   Explicitly dangerous; intended only for testing or for processing
   input that has already been validated externally.

The FFI layer exposes presets via `presetToLimits`, which maps a
`UInt8` preset code to the corresponding `ParserLimits` configuration.

# Verification of Security Properties
%%%
tag := "security-verification"
%%%

The formal proofs establish that the parser correctly enforces
its configured limits:

 * Nesting depth is checked on every recursive call
 * String length is checked during scalar accumulation
 * Collection sizes are checked during sequence/mapping construction
 * Alias depth is bounded during resolution

Because the parser is written in pure Lean 4 with no unsafe FFI
in the core, there is no possibility of buffer overflows, use-after-free,
or other memory safety violations in the parsing logic.
The Lean runtime provides automatic memory management via
reference-counted garbage collection.
