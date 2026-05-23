/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.IndexedDispatch
import L4YAML.Parser.TokenParserIx

/-! # `IndexedComposition` — Phase 3 Step 6e indexed pipeline (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 Step 6f cutover commit.

## Role

Indexed twin of the `scanAndParse` half of
`L4YAML/Parser/Composition.lean`: chains `Scanner.Indexed.scanIx`
into `TokenParser.Indexed.parseStreamIx` to expose a single
`scanAndParseIx : String → Except ScanError (Array YamlDocument)`
entry point.

Mirrors the match-based shape of the legacy `scanAndParse`. Both
stages already speak `ScanError`, so no error translation is
required. The indexed pipeline does **not** strip
`.placeholder` tokens between scan and parse — both the legacy
and indexed token parsers classify `.placeholder` as a
directive-prelude skip token, so the unfiltered stream is
accepted directly.

The legacy `scanAndParse` (via `scanFiltered`) keeps the
placeholder-strip step, but the indexed parser already handles
the residual placeholders inline, which lets `scanAndParseIx`
chain `scanIx` and `parseStreamIx` directly without an
intermediate filter pass.

## Phase 3 Step 6f cutover

At cutover, this file is renamed to `Parser/Composition.lean`
(overwriting the legacy file) and the namespace
`L4YAML.TokenParser.Indexed` reverts to `L4YAML.TokenParser`.
The legacy `scanAndParse` is rebound to `scanAndParseIx`'s body
at that point.
-/

set_option autoImplicit false

namespace L4YAML.TokenParser.Indexed

open L4YAML
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.TokenParser.Indexed

/-! ## Convenience: Full Indexed Pipeline -/

/-- **Indexed Load pipeline**: scan an input `String` with `scanIx`
    and parse the resulting indexed token stream with
    `parseStreamIx`.

    Both stages return `Except ScanError ...` so the composition is
    a plain match-propagate: scanner errors bubble out unchanged,
    parser errors bubble out unchanged.

    Indexed twin of `L4YAML.TokenParser.scanAndParse` (legacy). The
    legacy variant goes through `Scanner.scanFiltered` (which strips
    `.placeholder` tokens); the indexed twin does not need that step
    because `parseStreamIx`'s prelude classifier already treats
    `.placeholder` as a skip token. -/
def scanAndParseIx (input : String) : Except ScanError (Array YamlDocument) :=
  match scanIx input with
  | .ok tokens => parseStreamIx tokens
  | .error e => .error e

end L4YAML.TokenParser.Indexed
