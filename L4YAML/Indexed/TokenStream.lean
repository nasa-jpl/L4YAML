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

## Phase 2 → Phase 3 evolution

Phase 2 landed type signatures only. Phase 3 Step 1 adds the basic
container operations the new scanner needs:

- `IxToken.mk'` — bound-discharging convenience constructor;
- `TokenStream.push`, `append`, `last?`, `isEmpty`, `singleton`.

The `parse : (s : String) → Subtype (validScan s)` function and the
`present : TokenStream input → String` function land later in
Phase 3 (Steps 2–5).

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

namespace IxToken

/-- Explicit constructor that names the bound obligations. Used by
    Phase 3 Step 2+ scanner code which holds the bound proofs locally
    (typically as the `posBound` field of an `IxCursor`). -/
def mk' {input : String} (start : YamlPos) (token : YamlToken) (stop : YamlPos)
    (hOrder : start.offset ≤ stop.offset) (hBound : stop.offset ≤ input.utf8ByteSize) :
    IxToken input where
  start := start
  token := token
  stop  := stop
  startLEStop := hOrder
  stopLEInput := hBound

/-- The byte-length of the source span the token occupies. -/
@[inline] def byteSize {input : String} (t : IxToken input) : Nat :=
  t.stop.offset - t.start.offset

/-- `Inhabited (IxToken input)` via a zero-positioned `streamStart` default.

    This instance is **proof-only**: production code uses `[i]'h` explicit-
    bounds indexing (Reflection 61), never `[i]!`. Proof-side bridging
    lemmas (`peek_some_val_ix`, `peek_of_pos_val_ix` in
    `Proofs/Parser/IndexedWellBehaved.lean` §5d₃ / emitter-bridge) state
    their results in `[i]!` shape to interface with legacy proof patterns
    keyed on `Inhabited (Positioned YamlToken)`; this instance lets those
    statements type-check.

    Type-level disjointness is unaffected: the default is still of type
    `IxToken input`, not `IxToken input'` for `input' ≠ input`. -/
instance (input : String) : Inhabited (IxToken input) where
  default :=
    { start := default
    , token := .streamStart
    , stop  := default
    , startLEStop := Nat.le_refl _
    , stopLEInput := Nat.zero_le _ }

end IxToken

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

/-- Whether the stream contains no tokens. -/
@[inline] def isEmpty {input : String} (ts : TokenStream input) : Bool :=
  ts.tokens.isEmpty

/-- A single-token stream. -/
def singleton {input : String} (t : IxToken input) : TokenStream input where
  tokens := #[t]

/-- Append a token to the end of the stream. -/
@[inline] def push {input : String} (ts : TokenStream input)
    (t : IxToken input) : TokenStream input where
  tokens := ts.tokens.push t

/-- Concatenate two token streams over the same input. -/
@[inline] def append {input : String} (ts₁ ts₂ : TokenStream input) :
    TokenStream input where
  tokens := ts₁.tokens ++ ts₂.tokens

/-- Overwrite the token at index `i` with `t`, leaving the stream
    unchanged if `i` is out of bounds. Mirrors
    `Array.setIfInBounds`; used by the scanner's simple-key
    resolution (overwrites placeholders reserved by `saveSimpleKey`
    with the final `blockMappingStart`/`key` tokens). -/
@[inline] def setIfInBounds {input : String} (ts : TokenStream input) (i : Nat)
    (t : IxToken input) : TokenStream input where
  tokens := ts.tokens.setIfInBounds i t

/-- The last token in the stream, if any. -/
@[inline] def last? {input : String} (ts : TokenStream input) :
    Option (IxToken input) :=
  ts.tokens.back?

/-- Look up the `i`-th token. -/
@[inline] def get? {input : String} (ts : TokenStream input) (i : Nat) :
    Option (IxToken input) :=
  ts.tokens[i]?

/-- `GetElem` instance: a `TokenStream` indexes like its underlying array.

    With this, `ts[i]'h` (where `h : i < ts.size`) returns `IxToken input`,
    matching the shape parser proofs (Phase 3 Step 6d) expect when porting
    legacy lemmas keyed on `Array (Positioned YamlToken)` to the indexed
    `Indexed.TokenStream input` substrate. -/
instance {input : String} :
    GetElem (TokenStream input) Nat (IxToken input) (fun ts i => i < ts.size) where
  getElem ts i h := ts.tokens[i]'h

theorem getElem_eq_tokens_getElem {input : String}
    (ts : TokenStream input) (i : Nat) (h : i < ts.size) :
    ts[i]'h = ts.tokens[i]'h := rfl

@[simp] theorem size_empty (input : String) :
    size (empty input) = 0 := rfl

@[simp] theorem size_singleton {input : String} (t : IxToken input) :
    size (singleton t) = 1 := rfl

@[simp] theorem size_push {input : String} (ts : TokenStream input)
    (t : IxToken input) :
    size (push ts t) = size ts + 1 := by
  simp [size, push]

@[simp] theorem size_append {input : String} (ts₁ ts₂ : TokenStream input) :
    size (append ts₁ ts₂) = size ts₁ + size ts₂ := by
  simp [size, append]

@[simp] theorem isEmpty_empty (input : String) :
    isEmpty (empty input) = true := rfl

end TokenStream

end L4YAML.Indexed
