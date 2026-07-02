/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Indexed.TokenStream

/-! # `IndexedPresenter` — Phase 3 Step 5c `present : TokenStream input → String` (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 cutover commit (Step 6).

## Role in the four-stage pipeline

`present` is the L3 → L2 down-conversion from the four-stage table
(Stage C in Blueprint 08): given a `TokenStream input`, render a
String that, when re-scanned by `scanIx`, recovers the original
token stream — the roundtrip `scanIx (present ts) = .ok ts` is
exercised over a fixed corpus in
`L4YAML/Proofs/Scanner/IndexedRoundtrip.lean`.

## Design — hybrid case analysis

The indexed scanner emits indicator tokens (the `:`/`,`/`[`/`]`/
`{`/`}`/`-`/`?` characters and the `---`/`...` document markers)
as zero-width points at the cursor *before* consuming the
character (`emit` + `advance`). Their `[start, stop)` source span
is therefore degenerate (`start = stop`) and a pure source-span
fold cannot recover the indicator character.

`present` dispatches on the token constructor:

- **Virtual** (`streamStart`, `streamEnd`, `placeholder`,
  `blockSequenceStart`, `blockMappingStart`, `blockEnd`): no
  contribution.
- **Single-character indicators** (`flowSequenceStart`,
  `flowSequenceEnd`, `flowMappingStart`, `flowMappingEnd`,
  `flowEntry`, `blockEntry`, `key`, `value`): push the
  corresponding literal character.
- **Multi-character markers** (`documentStart`, `documentEnd`):
  push the literal `"---"` / `"..."` triple.
- **Content tokens** (`scalar`, `anchor`, `alias`, `tag`,
  `comment`, `versionDirective`, `tagDirective`): emit
  `input.extract [start, stop)` — the source bytes the scanner
  consumed for the token, which faithfully reproduce the
  character sequence (including escapes inside double-quoted
  scalars, the block-scalar header, etc.).

The hybrid design holds the corpus invariant *for plain scalars
and flow-context indicators* (the inputs in the Step 5c corpus).
Inputs whose source contains inter-token whitespace are deferred:
they require interpolating gap bytes from the type parameter
`input`, which is a Phase 4+ refinement (the full bidirectional
`compose ∘ parse ∘ present ∘ serialize` roundtrip).

## Indexing discipline

`present` consumes `TokenStream input` and produces `String`. The
type parameter `input` is used inside the body (every token's
positions are valid offsets into `input`), but the result is a
plain `String` — the L3 → L2 step erases the type-level binding,
exactly as the four-stage table prescribes (the L2 String can then
be re-scanned at any new `input'`).

## Counterpart (legacy)

The legacy scanner has no `present`: the legacy `Array (Positioned
YamlToken)` doesn't carry source positions tight enough to
reconstruct the source by extraction. The indexed token stream
makes the roundtrip possible because every token's `[start, stop)`
is a verified offset into `input` and the per-constructor
character mapping is total.
-/

namespace L4YAML.Scanner.Indexed

open L4YAML

/-- Render a single token to its source-character contribution.
    See the module header for the dispatch rationale (zero-width
    indicator tokens vs. source-span content tokens).

    `key` and `value` tokens are omitted: the scanner emits them
    in both explicit (`?`/`:` written in source) and implicit
    (simple-key resolution in flow context, block-mapping value
    discovery) cases, with no constructor-level distinction. The
    Step 5c corpus is restricted to inputs whose `key`/`value`
    tokens are all implicit; downstream `present` refinements
    (Phase 4+) re-introduce them via source-span inspection. -/
def renderToken {input : String} (tok : Indexed.IxToken input) : String :=
  match tok.token with
  | .streamStart | .streamEnd | .placeholder
  | .blockSequenceStart | .blockMappingStart | .blockEnd
  | .key | .value => ""
  | .flowSequenceStart => "["
  | .flowSequenceEnd   => "]"
  | .flowMappingStart  => "{"
  | .flowMappingEnd    => "}"
  | .flowEntry         => ","
  | .blockEntry        => "-"
  | .documentStart     => "---"
  | .documentEnd       => "..."
  | _ => String.Pos.Raw.extract input ⟨tok.start.offset⟩ ⟨tok.stop.offset⟩

/-- Render a token stream back to a YAML source string.

    **Roundtrip law (corpus)**: for each `input` in the fixed test
    corpus, `scanIx input = .ok ts → present ts = input` (and so
    `scanIx (present ts) = .ok ts`). The corpus is restricted to
    inputs whose token streams cover every byte of `input` with no
    inter-token whitespace gaps — see
    `L4YAML/Proofs/Scanner/IndexedRoundtrip.lean`.

    **Phase 3 Step 5c — staging**: this file is not imported by
    `L4YAML.lean` until the cutover commit (Step 6). -/
def present {input : String} (ts : Indexed.TokenStream input) : String :=
  ts.tokens.foldl (init := "") fun acc tok => acc ++ renderToken tok

@[simp] theorem present_empty (input : String) :
    present (Indexed.TokenStream.empty input) = "" := rfl

end L4YAML.Scanner.Indexed
