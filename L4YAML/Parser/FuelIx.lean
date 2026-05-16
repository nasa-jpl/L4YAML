/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Indexed.TokenStream

/-! # `FuelIx` — Phase 3 Step 6b indexed parser fuel (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 Step 6f cutover commit.

## Role

Indexed twin of `L4YAML/Parser/Fuel.lean`: the named fuel formula
the indexed token parser (Step 6b) uses when invoking `parseNode`
from `parseDocument`.

The arithmetic is identical to the legacy formula
(`4 * tokens.size + 4`); the only change is the input type
(`Indexed.TokenStream input` rather than
`Array (Positioned YamlToken)`).

## Indexing discipline

`initialFuelIx` is keyed on `Indexed.TokenStream.size`, which
reads the underlying `Array (IxToken input)`'s `size` field. The
formula does not depend on the type parameter `input` beyond
what the token-stream container already carries, so the resulting
`Nat` is plain (no `input` parameter) — exactly the shape the
mutual block in `Parser/TokenParserIx.lean` expects.

## Phase 3 Step 6f cutover

At cutover, `FuelIx.lean` is renamed to `Parser/Fuel.lean`
(overwriting the legacy file) and the `Indexed` suffix on
`initialFuelIx` is dropped — see Blueprint Step 6f.
-/

namespace L4YAML.TokenParser.Indexed

open L4YAML L4YAML.Indexed

/-- Initial fuel for `parseNode` invoked by `parseDocument` over an
    indexed token stream.

    Value: `4 * tokens.size + 4`.

    **Why `4 * N + 4`**: each token may trigger at most one collection
    open (`parseBlockSequence`, …), one collection-loop entry
    (`parseBlockSequenceLoop`, …), one node dispatch (`parseNode`),
    and one content dispatch (`parseNodeContent`).  The trailing `+ 4`
    absorbs the leading dispatch chain before the first token is
    consumed.

    Mirrors `L4YAML.TokenParser.initialFuel`; the only change is the
    container type (`Indexed.TokenStream input` rather than
    `Array (Positioned YamlToken)`). -/
def initialFuelIx {input : String} (tokens : Indexed.TokenStream input) : Nat :=
  4 * tokens.size + 4

end L4YAML.TokenParser.Indexed
