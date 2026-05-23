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
`L4YAML/Parser/Composition.lean`: chains
`Scanner.Indexed.scanFilteredIx` into
`TokenParser.Indexed.parseStreamIx` to expose a single
`scanAndParseIx : String → Except ScanError (Array YamlDocument)`
entry point.

Mirrors the match-based shape of the legacy `scanAndParse`. Both
stages already speak `ScanError`, so no error translation is
required. The indexed pipeline strips `.placeholder` tokens
between scan and parse via `scanFilteredIx`, matching legacy's
`scanFiltered` boundary.

## Step 6f.0 — placeholder filter restoration

Step 6e wired `scanIx` directly into `parseStreamIx`, on the
hypothesis that `parseStreamIx`'s `validNextToken` classifier
would absorb the placeholder-skip step (Reflection 97). That
hypothesis was wrong: `validNextToken` *permits* but does not
*consume* placeholders, so unfiltered streams either stall or
mis-route through `parseNodeContent`'s `_` fallback (emitting an
empty scalar). Step 6f.0 reintroduces the filter via
`scanFilteredIx` and retracts Reflection 97. The architectural
symmetry with legacy is now restored:
`parseStreamIx`-level proofs reason about an arbitrary
`TokenStream input`, leaving the filter as a `scanAndParseIx`-
level concern (zero proof impact).

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

/-- **Indexed Load pipeline**: scan an input `String` with
    `scanFilteredIx` (which drops `.placeholder` tokens) and parse
    the resulting indexed token stream with `parseStreamIx`.

    Both stages return `Except ScanError ...` so the composition is
    a plain match-propagate: scanner errors bubble out unchanged,
    parser errors bubble out unchanged.

    Indexed twin of `L4YAML.TokenParser.scanAndParse` (legacy).
    Step 6f.0 restored the placeholder filter (`scanFilteredIx`)
    after Step 6e's direct `scanIx` wiring produced empty-scalar
    parses for plain root scalars (`validNextToken` permits but
    does not consume `.placeholder`; the parser fell through to
    `parseNodeContent`'s `_` fallback). -/
def scanAndParseIx (input : String) : Except ScanError (Array YamlDocument) :=
  match scanFilteredIx input with
  | .ok tokens => parseStreamIx tokens
  | .error e => .error e

/-! ## Public API — indexed twins of `L4YAML.TokenParser.parseYaml*`

These are the externally-visible entry points that consumers
(`L4YAML/Schema/*`, `L4YAML/Config/Limits.lean`, the production
proof stack) call. The legacy versions live in `Parser/Composition.lean`
under namespace `L4YAML.TokenParser`. At Step 6f cutover, the indexed
namespace flattens and these functions become the production
`parseYaml*` symbols on the rebound body.

`parseYamlWithCommentsIx` is provided here (Step 6f.3): it uses the
parallel comment-preserving scan path `scanWithCommentsIx` and the
existing indexed `parseStreamIx` to produce comment-attached
documents. This unblocks the migration of
`Proofs/RoundTrip/CommentRoundTrip.lean` away from legacy
`parseYamlWithComments`.
-/

/-- Indexed twin of `L4YAML.TokenParser.parseYamlRaw`. Returns
    serialization-tree documents (aliases preserved, anchor fields
    populated). Behaviourally identical to `scanAndParseIx`. -/
def parseYamlRawIx (input : String) : Except ScanError (Array YamlDocument) :=
  scanAndParseIx input

/-- Indexed twin of `L4YAML.TokenParser.parseYaml`. Applies the
    §3.1 *Compose* step (`YamlDocument.compose`) to each document
    from `parseYamlRawIx`. -/
def parseYamlIx (input : String) : Except ScanError (Array YamlDocument) :=
  match parseYamlRawIx input with
  | .ok docs => .ok (docs.map YamlDocument.compose)
  | .error e => .error e

/-- Indexed twin of `L4YAML.TokenParser.parseYamlSingleRaw`.
    Errors with `multipleDocuments` if the input has more than one. -/
def parseYamlSingleRawIx (input : String) : Except ScanError YamlDocument :=
  match parseYamlRawIx input with
  | .ok docs =>
    if docs.size == 0 then .ok { value := YamlValue.null }
    else if docs.size == 1 then .ok docs[0]!
    else .error (.multipleDocuments docs.size)
  | .error e => .error e

/-- Indexed twin of `L4YAML.TokenParser.parseYamlSingle`.
    Returns just the composed `YamlValue` of a single-document
    stream. Errors with `multipleDocuments` if the input has more
    than one. -/
def parseYamlSingleIx (input : String) : Except ScanError YamlValue :=
  match parseYamlIx input with
  | .ok docs =>
    if docs.size == 0 then .ok YamlValue.null
    else if docs.size == 1 then .ok docs[0]!.value
    else .error (.multipleDocuments docs.size)
  | .error e => .error e

/-! ## Comment attachment

Helpers ported from legacy `Parser/Composition.lean`. They are pure
on `YamlDocument` and `YamlPos`, so they don't change between the
legacy and indexed pipelines.
-/

/-- Classify a comment's position relative to its nearest node.
    See `L4YAML.TokenParser.classifyCommentPosition` for the legacy
    docstring; the algorithm is unchanged. -/
def classifyCommentPosition (cPos : YamlPos)
    (nodePositions : Array (YamlPath × YamlPos × YamlPos)) : CommentPosition :=
  if nodePositions.any fun (_, startPos, _) => startPos.line == cPos.line then
    .inline
  else if nodePositions.any fun (_, startPos, _) => cPos.line < startPos.line then
    .before
  else
    .after

/-- Replace each comment's `.inline` placeholder with the
    `.before`/`.inline`/`.after` classification derived from the
    document's `nodePositions`. -/
def classifyDocumentComments (doc : YamlDocument) : YamlDocument :=
  { doc with comments := doc.comments.map fun (pos, c) =>
      (pos, { c with position := classifyCommentPosition pos doc.nodePositions }) }

/-- Partition raw comments by document span (multi-document streams).
    For single-document streams, all comments go to the single
    document. -/
def partitionCommentsByDocument (rawComments : Array (YamlPos × String))
    (docs : Array YamlDocument) : Array (Array (YamlPos × String)) :=
  if docs.size ≤ 1 then
    #[rawComments]
  else
    let spans : Array (Nat × Nat) := docs.map fun doc =>
      match doc.nodePositions.find? (fun (p, _, _) => p == #[]) with
      | some (_, startPos, endPos) => (startPos.offset, endPos.offset)
      | none => (0, 0)
    docs.mapIdx fun i _ =>
      let (startOff, endOff) := spans[i]!
      rawComments.filter fun (cPos, _) =>
        if i == 0 then cPos.offset ≤ endOff
        else if i == docs.size - 1 then cPos.offset ≥ startOff
        else startOff ≤ cPos.offset && cPos.offset ≤ endOff

/-- Indexed twin of `L4YAML.TokenParser.parseYamlWithComments`.
    Uses the comment-preserving scan entry point `scanWithCommentsIx`
    and the indexed `parseStreamIx` (with `trackPositions := true`)
    to produce composed documents carrying their attached comments. -/
def parseYamlWithCommentsIx (input : String) : Except ScanError (Array YamlDocument) :=
  match scanWithCommentsIx input with
  | .ok (tokens, rawComments) =>
    match parseStreamIx tokens (trackPositions := true) with
    | .ok docs =>
      let partitioned := partitionCommentsByDocument rawComments docs
      .ok (docs.mapIdx fun i doc =>
        let docComments := partitioned[i]!
        let comments : Array (YamlPos × Comment) :=
          docComments.map fun (pos, text) => (pos, ⟨text, .inline⟩)
        let composed := { doc.compose with
          comments := comments
          nodePositions := doc.nodePositions }
        classifyDocumentComments composed)
    | .error e => .error e
  | .error e => .error e

end L4YAML.TokenParser.Indexed
