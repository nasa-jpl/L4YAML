/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Indexed.Range
import L4YAML.Token.Token

/-! # `TokenStream input` — indexed L2 event/token stream

The L2 event/token stream parameterised by the input string.
Tokens carry positions that are byte offsets into `input`.

## Indexing discipline

- `input : String` is a type parameter. A `TokenStream input₁` and
  a `TokenStream input₂` with `input₁ ≠ input₂` are different
  types.
- Each token's position is constrained (by a side-channel proof, or
  by the `Range input` of its associated source span) to be a valid
  offset into `input`.

## Phase 2 scope (this file)

Type signature only. The `parse : (s : String) → Subtype (validScan s)`
function and the `present : TokenStream input → String` function
land in Phase 3 (Stage C scanner cutover).

## Counterpart (legacy)

The legacy `Positioned YamlToken` (Token/Token.lean, used by
`Scanner/Scanner.lean`) is the unindexed precursor. Phase 3's
scanner cutover replaces the legacy `Array (Positioned YamlToken)`
with `TokenStream input` end-to-end (Guardrail 1: legacy deleted in
the cutover commit).
-/

namespace L4YAML.Indexed

open L4YAML

/-- A positioned token whose start position is bounded by the input's
    UTF-8 byte size. The bound is the type-level disjointness
    guardrail: positions valid for one input cannot be passed off as
    positions of another. -/
structure IxToken (input : String) where
  start  : YamlPos
  /-- The token value (re-uses the existing `YamlToken`). -/
  token  : YamlToken
  /-- The end position is exclusive: the first byte after the last
      character consumed by the token. -/
  stop   : YamlPos
  /-- Well-formedness: the token's positions are valid offsets. -/
  startLEStop  : start.offset ≤ stop.offset
  stopLEInput  : stop.offset ≤ input.utf8ByteSize

/-- The L2 event/token stream indexed by the input string.

    **Phase 2 stub**: a flat `Array (IxToken input)`. Phase 3's
    scanner produces this directly; Phase 4's parser consumes it.

    The shape is intentionally close to the legacy
    `Array (Positioned YamlToken)` to ease the cutover (D5 test
    corpus reuses the existing scanner test harness). -/
structure TokenStream (input : String) where
  tokens : Array (IxToken input)
  deriving Inhabited

namespace TokenStream

/-- The number of tokens in the stream. -/
@[inline] def size {input : String} (ts : TokenStream input) : Nat :=
  ts.tokens.size

/-- The empty token stream. -/
def empty (input : String) : TokenStream input where
  tokens := #[]

end TokenStream

end L4YAML.Indexed
