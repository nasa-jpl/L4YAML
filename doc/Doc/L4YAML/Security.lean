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
The `ParserLimits` structure provides 11 configurable threat mitigations:

:::table +header
*
  * Parameter
  * Default
  * Purpose
*
  * `nestingDepth`
  * 250
  * Maximum recursion depth — prevents billion-laugh expansion
*
  * `maxStringLength`
  * 10 MB
  * Maximum scalar string length — DoS prevention
*
  * `maxArrayLength`
  * 100,000
  * Maximum sequence element count
*
  * `maxObjectSize`
  * 10 MB
  * Maximum total mapping size
*
  * `maxAliasDepth`
  * 50
  * Maximum alias chain depth — recursive cycle protection
*
  * `allowDuplicateKeys`
  * `false`
  * Whether duplicate mapping keys are accepted
*
  * `allowedTagHandles`
  * customizable
  * Restricts which tag handles (`!`, `!!`, custom) are permitted
*
  * `forbiddenTags`
  * customizable
  * Explicit rejection of dangerous tags (e.g., `!!python/object`)
*
  * `parseErrorPolicy`
  * `strict`
  * Whether non-conformant input is rejected or best-effort parsed
*
  * `commentEncoding`
  * explicit
  * Character encoding validation for comments
*
  * `literalNewlineHandling`
  * standard
  * Newline normalization in literal scalars
:::

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
