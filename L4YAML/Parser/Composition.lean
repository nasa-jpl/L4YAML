/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.Scanner
import L4YAML.Parser.TokenParser

/-!
# Parser — Pipeline Composition (Load = Parse + Compose)

User-facing entry points that compose `Scanner.scan*` with
`parseStream`, plus the §3.1 *Compose* step (alias resolution, anchor
stripping) and the comment-attachment helpers used by
`parseYamlWithComments`.

Split from the monolithic `Parser/TokenParser.lean` during Blueprint
Initiative 1 Phase 3 (Parser split).  See
`Blueprint/03-code-organization.md`.

## Spec mapping

YAML 1.2.2 §3.1 defines **Load** as the composition of two processes:
- **Parse**  : character stream → serialization event tree
- **Compose**: serialization event tree → representation node graph

The *Raw* variants (`parseYamlRaw`, `parseYamlSingleRaw`) return the
serialization tree (anchors + aliases preserved).  The standard
variants (`parseYaml`, `parseYamlSingle`) apply *Compose* via
`YamlDocument.compose`.

## Scope

- `scanAndParse` — internal scan ∘ parseStream pipeline.
- `parseYamlRaw`, `parseYaml`, `parseYamlSingleRaw`, `parseYamlSingle`.
- `classifyCommentPosition`, `classifyDocumentComments`,
  `partitionCommentsByDocument`.
- `parseYamlWithComments` — comment-preserving variant.

The mutual block and `parseStream` itself live in
[`L4YAML.Parser.TokenParser`].  The `ParseState` substrate lives in
[`L4YAML.Parser.State`].
-/

namespace L4YAML.TokenParser

open L4YAML

/-! ## Convenience: Full Pipeline -/

/-- Internal: scan + parse pipeline returning structured `ScanError`.

    **Implements**: Complete YAML Load pipeline (scan + parse).
    Composes `Scanner.scan` and `parseStream` into a single function.

    Callers who need machine-inspectable errors (e.g., for testing specific
    error categories) should use this directly. The public `parseYaml*`
    functions also return `Except ScanError` for machine-inspectable
    error handling. -/
def scanAndParse (input : String) : Except ScanError (Array YamlDocument) :=
  match Scanner.scanFiltered input with
  | .ok tokens => parseStream tokens
  | .error e => .error e

/--
Parse a YAML string into an array of documents (**serialization tree**).

**Implements** (YAML 1.2.2 §3.1):
- **Parse** step only — character stream → serialization event tree.

Returns documents with `.alias name` nodes and `anchor` fields preserved.
Each `YamlDocument` includes an `anchors` map that can be used by
`YamlDocument.compose` to resolve aliases. -/
def parseYamlRaw (input : String) : Except ScanError (Array YamlDocument) :=
  match Scanner.scanFiltered input with
  | .ok tokens => parseStream tokens
  | .error e => .error e

/--
Parse a YAML string into an array of documents (**representation graph**).

**Implements** (YAML 1.2.2 §3.1):
- Full **Load** = Parse (→ serialization tree) + Compose (→ representation graph).

Aliases are resolved and anchor annotations are stripped.
This is the main entry point for most use cases. -/
def parseYaml (input : String) : Except ScanError (Array YamlDocument) :=
  match parseYamlRaw input with
  | .ok docs => .ok (docs.map YamlDocument.compose)
  | .error e => .error e

/--
Parse a YAML string expecting exactly one document (**serialization tree**).

Returns the raw document with `.alias` nodes and `anchor` fields preserved.
**Error**: `multipleDocuments` if more than one document is found. -/
def parseYamlSingleRaw (input : String) : Except ScanError YamlDocument :=
  match parseYamlRaw input with
  | .ok docs =>
    if docs.size == 0 then .ok { value := YamlValue.null }
    else if docs.size == 1 then .ok docs[0]!
    else .error (.multipleDocuments docs.size)
  | .error e => .error e

/--
Parse a YAML string expecting exactly one document (**representation graph**).

Returns the value of the single document with aliases resolved and
anchor annotations stripped.
**Error**: `multipleDocuments` if more than one document is found. -/
def parseYamlSingle (input : String) : Except ScanError YamlValue :=
  match parseYaml input with
  | .ok docs =>
    if docs.size == 0 then .ok YamlValue.null
    else if docs.size == 1 then .ok docs[0]!.value
    else .error (.multipleDocuments docs.size)
  | .error e => .error e

/-! ## Comment Attachment -/

/--
Classify a comment's position relative to its nearest node.

§6.6 / §6.9: Comments are a presentation detail. For round-trip fidelity
we classify each comment as:
- `.inline` — same line as a node's start position
- `.before` — on a line preceding all content (or the next node)
- `.after`  — on a line following all content

The classification uses `nodePositions` from the parser's position-tracking
pass (enabled by `trackPositions := true`).
-/
def classifyCommentPosition (cPos : YamlPos)
    (nodePositions : Array (YamlPath × YamlPos × YamlPos)) : CommentPosition :=
  -- If comment shares a line with any node start → inline
  if nodePositions.any fun (_, startPos, _) => startPos.line == cPos.line then
    .inline
  -- If some node starts after the comment line → before that node
  else if nodePositions.any fun (_, startPos, _) => cPos.line < startPos.line then
    .before
  -- Otherwise: after all nodes
  else
    .after

/--
Classify all comments in a document using its node positions.

Replaces the `.inline` default assigned during initial attachment
with the correct `.before`/`.inline`/`.after` classification.
-/
def classifyDocumentComments (doc : YamlDocument) : YamlDocument :=
  { doc with comments := doc.comments.map fun (pos, c) =>
      (pos, { c with position := classifyCommentPosition pos doc.nodePositions }) }

/--
Partition raw comments by document span.

For multi-document streams, each comment is assigned to the document
whose root node span contains the comment's byte offset. Comments
outside all spans go to the nearest document (first or last).

For single-document streams, all comments go to the single document.
-/
def partitionCommentsByDocument (rawComments : Array (YamlPos × String))
    (docs : Array YamlDocument) : Array (Array (YamlPos × String)) :=
  if docs.size ≤ 1 then
    #[rawComments]
  else
    -- Build byte-offset spans from each document's root nodePosition
    let spans : Array (Nat × Nat) := docs.map fun doc =>
      match doc.nodePositions.find? (fun (p, _, _) => p == #[]) with
      | some (_, startPos, endPos) => (startPos.offset, endPos.offset)
      | none => (0, 0)  -- no root position: will collect nothing
    -- Assign each comment to the containing document
    docs.mapIdx fun i _ =>
      let (startOff, endOff) := spans[i]!
      -- First doc captures everything before its end;
      -- last doc captures everything after its start
      rawComments.filter fun (cPos, _) =>
        if i == 0 then cPos.offset ≤ endOff
        else if i == docs.size - 1 then cPos.offset ≥ startOff
        else startOff ≤ cPos.offset && cPos.offset ≤ endOff

/--
Parse a YAML string with comment preservation (**representation graph**).

Like `parseYaml` but also collects comments discovered during scanning.
Each composed document carries scanner-collected comments in its
`comments` field (as `Array (YamlPos × Comment)`).

**Comment lifecycle** (v0.2.7):
1. Scanner collects comments as `(YamlPos × String)` side-channel
2. Comments are partitioned by document span for multi-doc streams
3. Each comment is classified as `.before`/`.inline`/`.after` based on
   the document's `nodePositions` (from `trackPositions := true`)
4. Classified comments are attached to the composed document
-/
def parseYamlWithComments (input : String) : Except ScanError (Array YamlDocument) :=
  match Scanner.scanWithComments input with
  | .ok (tokens, rawComments) =>
    match parseStream tokens (trackPositions := true) with
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

end L4YAML.TokenParser
