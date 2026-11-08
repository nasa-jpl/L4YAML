/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Output.Events
public import L4YAML.Parser.IndexedComposition

@[expose] public section Blanket

/-!
# Event Stream Emitter — indexed-pipeline twin

`streamToEventsIx` produces the same yaml-test-suite event notation as
`streamToEvents`, but scans and parses through the **indexed** pipeline
(`scanFilteredIx` → `TokenParser.Indexed`) instead of the legacy one.
It exists so the yaml-test-suite matrix can score the indexed pipeline —
the one consumers of `parseYaml*Ix` actually run — against the same
`test.event` oracles the legacy pipeline scores 402/402 on (DOCS.md
§ Indexed-pipeline parity gap, plan item 5).

`parseStreamMarkedLoopIx` mirrors `TokenParser.Indexed.parseStreamLoop`
arm-for-arm, **not** the legacy `parseStreamMarkedLoop`: if the two
stream loops ever differ, the divergence must show up in the matrix
score rather than be papered over by the measurement harness.  (The
bare-`...` document-suffix arm, fix C1, was ported to the indexed loop
on 2026-08-05 — this mirror gained it in the same commit.)  All event
*emission* (`emitStream`, `emitValue`, tag percent-decoding) is shared with
the legacy emitter, so any score difference is attributable to scan/parse
alone.
-/

namespace L4YAML.Events

open L4YAML
open L4YAML.TokenParser.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx

/-- Indexed twin of `explicitStartAt`: does the document beginning at `ps`
    open with an explicit `---`?  Directives may precede it; a directive-led
    document is always explicit per §9.1.5. -/
def explicitStartAtIx {input : String} (ps : ParseStateIx input) : Bool :=
  let rec go (i : Nat) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      match ps.tokens.get? i with
      | some t =>
        match t.token with
        | .versionDirective _ _ => go (i + 1) fuel
        | .tagDirective _ _     => go (i + 1) fuel
        | .documentStart        => true
        | _                     => false
      | none => false
  go ps.pos ps.tokens.size

/-- Mirror of `TokenParser.Indexed.parseStreamLoop` that additionally records
    explicit `---` / `...` markers for each document.  Arm-for-arm with the
    *indexed* loop (see module docstring), including its bare-`...`
    document-suffix arm (fix C1). -/
def parseStreamMarkedLoopIx {input : String} (ps : ParseStateIx input)
    (acc : Array MarkedDoc) (streamState : StreamState) (fuel : Nat) :
    Except ScanError (Array MarkedDoc) :=
  match fuel with
  | 0 => .ok acc
  | fuel + 1 =>
    match ps.peek? with
    | some .streamEnd => .ok acc
    | none => .ok acc
    | some .documentEnd =>
      -- Mirror of the indexed `parseStreamLoop`'s suffix handling: a bare
      -- `...` is a document *suffix* (§9.2 [205]), not an empty document.
      -- Consume and continue without recording a spurious empty `MarkedDoc`.
      let (_, ps) := ps.tryConsume .documentEnd
      parseStreamMarkedLoopIx ps acc .afterDocumentEnd fuel
    | some tok =>
      if !streamState.validNextToken tok then
        let pos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
        .error (.invalidBareDocument pos.line pos.col)
      else
        let explicitStart := explicitStartAtIx ps
        let savedPos := ps.pos
        match parseDocument ps with
        | .error e => .error e
        | .ok (doc, ps') =>
          let ps := { ps' with anchors := #[], anchorIndex := .empty, declaredAnchors := #[], declaredIndex := .empty,
                               nodePositions := #[], currentPath := #[] }
          let (consumed, ps) := ps.tryConsume .documentEnd
          let acc := acc.push { doc, explicitStart, explicitEnd := consumed }
          let streamState := if consumed then .afterDocumentEnd else .afterDocument
          if ps.pos == savedPos then
            let pos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
            .error (.trailingContent pos.line pos.col)
          else parseStreamMarkedLoopIx ps acc streamState fuel

/-- Indexed twin of `parseYamlRawMarked`: parse a YAML stream into documents
    tagged with their explicit markers, via the indexed scanner and parser.
    Raw parse, so aliases/anchors are preserved for event output. -/
def parseYamlRawMarkedIx (input : String) : Except ScanError (Array MarkedDoc) := do
  let tokens ← scanFilteredIx input
  let ps : ParseStateIx input := { tokens := tokens }
  let ps ← ps.expect .streamStart "STREAM-START"
  parseStreamMarkedLoopIx ps #[] .initial tokens.size

/-- Indexed twin of `streamToEvents`: parse `input` through the indexed
    pipeline and produce its test-suite event stream (with trailing newline),
    or a scan/parse error. -/
def streamToEventsIx (input : String) : Except ScanError String :=
  match parseYamlRawMarkedIx input with
  | .ok docs => .ok (emitStream docs ++ "\n")
  | .error e => .error e

end L4YAML.Events

end Blanket
