/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Basic

/-! # `FlowMonoChain.Preserve.DpInv` — Phase 3 Step 6f.3b3.flowmono.preserve.dpinv

**Sub-session 2 of `.flowmono.preserve`** (legacy
`Proofs/Output/EmitterScannability.lean` lines 2166–2745, ~580 LOC).
State-level `directivesPresent` / `indents` / `explicitKeyLine`
preservation lemmas for the primitives that compose into the
double-quoted scalar pipeline.

## Indexed simplification (Reflection 124)

Legacy lines 2166–2745 prove **36 theorems** — 12 functions
(`advance`, `consumeNewline`, `skipSpaces`, `skipWhitespace`, `emitAt`,
`collectHexDigitsLoop`, `parseHexEscape`, `processEscape`,
`foldQuotedNewlinesLoop`, `foldQuotedNewlines`,
`collectDoubleQuotedLoop`, `scanDoubleQuoted`) × 3 fields. Each is a
non-trivial induction over fuel / case-split over `Except` injections.

The indexed substrate splits the same surface into two *kinds*:

  * **Cursor-level functions** (10 of 12 legacy entries) —
    `consumeLineBreak`, `skipSpaces`, `skipWhitespace`,
    `collectHexDigitsLoopIx`, `parseHexEscapeIx`, `processEscapeIx`,
    `skipBlankLinesLoopIx`, `foldQuotedNewlinesIx`,
    `collectDoubleQuotedLoopIx`, `scanDoubleQuotedIx`. These operate
    on `IxCursor input`, which carries **no** `directivesPresent` /
    `indents` / `explicitKeyLine` fields. Preservation is *vacuous*:
    the only way these can affect a `ScannerStateIx` is via a
    `{ s with cursor := c }` record update in the dispatcher
    (`IndexedDispatch.scanContentDispatchIx`'s `"`-branch wraps
    `scanDoubleQuotedIx` exactly this way), which preserves all
    unmentioned fields by Lean's record-update semantics.

  * **State-level primitives** (2 of 12 legacy entries, plus the
    state-wrappers for whitespace skips) — `ScannerStateIx.advance`,
    `ScannerStateIx.advanceN`, `ScannerStateIx.emit`,
    `ScannerStateIx.emitAt`, `ScannerStateIx.skipSpacesS`,
    `ScannerStateIx.skipWhitespaceS`. Each is defined by a single
    record update touching only `cursor` and/or `tokens`, so
    preservation reduces to one `rfl`.

The 36 legacy theorems collapse to **18 one-line `rfl` lemmas** plus
this documentation note. Downstream consumers (`.helpers` sub-session
onward) chase preservation through double-quoted scalar dispatch by
`simp` with the `@[simp]` lemmas below — no per-scanner preservation
theorem is needed because the post-`scanDoubleQuotedIx` state is built
explicitly by `{ s with cursor := cAfter }.emitAt startPos tok h`,
which `simp` normalizes against the lemmas in this file.

## Scope

  * **§1** — `directivesPresent` preservation for `advance`,
    `advanceN`, `emit`, `emitAt`, `skipSpacesS`, `skipWhitespaceS`.
  * **§2** — `indents` preservation, same six primitives. (Note:
    `pushSequenceIndentIx` / `pushMappingIndentIx` / `unwindIndentsIx`
    intentionally *do* mutate `indents` — they are the indent-stack
    manipulators, not stage-pass-throughs, and their chain-invariant
    properties live in `Step.lean`.)
  * **§3** — `explicitKeyLine` preservation, same six primitives.

All proofs are `rfl`. Tagged `@[simp]` so that `simp` discharges
dispatcher-level preservation obligations automatically.

## Legacy mapping

Mirrors the structure of `EmitterScannability.lean` lines 2166–2745,
collapsed by the substrate split above. See Reflection 124 for the
detailed accounting.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx

variable {input : String}

/-! ## §1  `directivesPresent` preservation -/

@[simp] lemma advance_directivesPresent (s : ScannerStateIx input) :
    s.advance.directivesPresent = s.directivesPresent := rfl

@[simp] lemma advanceN_directivesPresent (s : ScannerStateIx input) (n : Nat) :
    (s.advanceN n).directivesPresent = s.directivesPresent := rfl

@[simp] lemma emit_directivesPresent (s : ScannerStateIx input) (tok : YamlToken) :
    (s.emit tok).directivesPresent = s.directivesPresent := rfl

@[simp] lemma emitAt_directivesPresent (s : ScannerStateIx input)
    (startPos : YamlPos) (tok : YamlToken)
    (h : startPos.offset ≤ s.cursor.pos.offset) :
    (s.emitAt startPos tok h).directivesPresent = s.directivesPresent := rfl

@[simp] lemma skipSpacesS_directivesPresent (s : ScannerStateIx input) :
    s.skipSpacesS.1.directivesPresent = s.directivesPresent := rfl

@[simp] lemma skipWhitespaceS_directivesPresent (s : ScannerStateIx input) :
    s.skipWhitespaceS.directivesPresent = s.directivesPresent := rfl

/-! ## §2  `indents` preservation -/

@[simp] lemma advance_indents (s : ScannerStateIx input) :
    s.advance.indents = s.indents := rfl

@[simp] lemma advanceN_indents (s : ScannerStateIx input) (n : Nat) :
    (s.advanceN n).indents = s.indents := rfl

@[simp] lemma emit_indents (s : ScannerStateIx input) (tok : YamlToken) :
    (s.emit tok).indents = s.indents := rfl

@[simp] lemma emitAt_indents (s : ScannerStateIx input)
    (startPos : YamlPos) (tok : YamlToken)
    (h : startPos.offset ≤ s.cursor.pos.offset) :
    (s.emitAt startPos tok h).indents = s.indents := rfl

@[simp] lemma skipSpacesS_indents (s : ScannerStateIx input) :
    s.skipSpacesS.1.indents = s.indents := rfl

@[simp] lemma skipWhitespaceS_indents (s : ScannerStateIx input) :
    s.skipWhitespaceS.indents = s.indents := rfl

/-! ## §3  `explicitKeyLine` preservation -/

@[simp] lemma advance_explicitKeyLine (s : ScannerStateIx input) :
    s.advance.explicitKeyLine = s.explicitKeyLine := rfl

@[simp] lemma advanceN_explicitKeyLine (s : ScannerStateIx input) (n : Nat) :
    (s.advanceN n).explicitKeyLine = s.explicitKeyLine := rfl

@[simp] lemma emit_explicitKeyLine (s : ScannerStateIx input) (tok : YamlToken) :
    (s.emit tok).explicitKeyLine = s.explicitKeyLine := rfl

@[simp] lemma emitAt_explicitKeyLine (s : ScannerStateIx input)
    (startPos : YamlPos) (tok : YamlToken)
    (h : startPos.offset ≤ s.cursor.pos.offset) :
    (s.emitAt startPos tok h).explicitKeyLine = s.explicitKeyLine := rfl

@[simp] lemma skipSpacesS_explicitKeyLine (s : ScannerStateIx input) :
    s.skipSpacesS.1.explicitKeyLine = s.explicitKeyLine := rfl

@[simp] lemma skipWhitespaceS_explicitKeyLine (s : ScannerStateIx input) :
    s.skipWhitespaceS.explicitKeyLine = s.explicitKeyLine := rfl

end L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
