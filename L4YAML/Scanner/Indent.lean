/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.State

/-!
# Scanner — Indentation Management

Virtual BLOCK-START / BLOCK-END token generation via the scanner's
indentation stack.

Split from `Scanner.lean` during Blueprint Initiative 1 Phase 2.

YAML 1.2.2 does not have explicit BLOCK-START/BLOCK-END terminals in the
grammar; they are derived from indentation (§6.1, §8.2).  This module
owns the stack-based bookkeeping that materializes those virtual tokens:

- `unwindIndents` — pop entries whose column is deeper than the current
  column, emitting `blockEnd` for each (spec-style: `s-indent(<n)` /
  `s-indent(≤n)` transitions, §6.1 [64]/[65]).
- `pushSequenceIndent` — open a new block sequence level, emitting
  `blockSequenceStart` (§8.2.1 [183] `l+block-sequence`).
- `pushMappingIndent` — open a new block mapping level, emitting
  `blockMappingStart` (§8.2.2 [187] `l+block-mapping`).
-/

namespace L4YAML.Scanner

open L4YAML

/-! ## Indentation Management -/

/-- Helper for unwindIndents using structural recursion.

    **Termination**: Structurally recursive on `fuel`.
    **Invariant**: At most `fuel` iterations, each popping one indent entry. -/
@[yaml_spec "6.1",
  yaml_spec "6.1" 64 "s-indent(<n)",
  yaml_spec "6.1" 65 "s-indent(≤n)"]
def unwindIndentsLoop (s : ScannerState) (col : Int) (fuel : Nat) : ScannerState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    if s.currentIndent > col && s.indents.size > 1 then
      let s' := s.emit .blockEnd
      let s' := { s' with indents := s'.indents.pop }
      unwindIndentsLoop s' col fuel'
    else
      s
termination_by fuel

/-- Unwind the indentation stack, emitting `blockEnd` tokens for each closed block.

    **Implements**: Virtual BLOCK-END generation (libyaml, not a single YAML production).
    The scanner's indentation stack encodes the nesting structure of block collections;
    when the current column is at or left of a block's indent, that block is closed.

    **Pre**: `col` is the column of the next content character (or -1 for stream/document end).
    **Post**: All indent entries deeper than `col` are popped; a `blockEnd` token is emitted for each.
    **Error**: None (pure computation). -/
@[yaml_spec "6.1",
  yaml_spec "6.1" 64 "s-indent(<n)",
  yaml_spec "6.1" 65 "s-indent(≤n)"]
def unwindIndents (s : ScannerState) (col : Int) : ScannerState :=
  unwindIndentsLoop s col s.indents.size

/-- Push a new block sequence indent level if `col` is deeper than `currentIndent`.

    **Implements**: Virtual BLOCK-SEQUENCE-START generation.
    Emits `blockSequenceStart` and pushes `{ column := col, isSequence := true }` onto the stack.

    **Pre**: `col` is the column of the `-` block entry indicator.
    **Post**: If `col > currentIndent`, emits `blockSequenceStart` and pushes indent entry. -/
@[yaml_spec "8.2.1" 183 "l+block-sequence"]
def pushSequenceIndent (s : ScannerState) (col : Int) : ScannerState :=
  if col > s.currentIndent then
    let s' := s.emit .blockSequenceStart
    { s' with indents := s'.indents.push { column := col, isSequence := true } }
  else s

/-- Push a new block mapping indent level if `col` is deeper than `currentIndent`.

    **Implements**: Virtual BLOCK-MAPPING-START generation.
    Emits `blockMappingStart` and pushes `{ column := col, isSequence := false }` onto the stack.

    **Pre**: `col` is the implicit key's column or the `?`/`:` indicator's column.
    **Post**: If `col > currentIndent`, emits `blockMappingStart` and pushes indent entry. -/
@[yaml_spec "8.2.2" 187 "l+block-mapping"]
def pushMappingIndent (s : ScannerState) (col : Int) : ScannerState :=
  if col > s.currentIndent then
    let s' := s.emit .blockMappingStart
    { s' with indents := s'.indents.push { column := col, isSequence := false } }
  else s

end L4YAML.Scanner
