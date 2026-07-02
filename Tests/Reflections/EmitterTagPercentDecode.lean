import L4YAML.Output.Events

/-!
# Reflection — INHABITATION / BIRTH probe for the tag percent-decode fix (matrix defect D, 6CK3)

Matrix defect **D** (`YAML_MATRIX_100PCT_ASSESSMENT.md`): the event emitter rendered a
resolved tag suffix's percent-escape verbatim — `!e!tag%21` under
`%TAG !e! tag:example.com,2000:app/` resolved to `tag:example.com,2000:app/tag%21` and was
emitted with the literal `%21` instead of the decoded `!`. The fix adds
`L4YAML.Events.percentDecodeTag` (a NEW, to-be-CONSTRUCTED `def`) and routes the
shorthand-resolved branches of `resolveTagForEvent` through it.

Per the **inhabitation-debt discipline** ([[feedback-inhabitation-debt-validate-target-defs]]) a
newly-constructed `def` is validated by type-checking only as WELL-FORMED, never as doing what it
is meant to. `percentDecodeTag` is an executable transform (Lean verifies its totality-shape, not
its meaning), so the analog of "probe at birth on the smallest concrete witness" is a runnable
regression probe that reads the transform back on real data. This file is that probe. Because
`percentDecodeBytes` is a `partial def`, the kernel cannot reduce it — every check is
`native_decide` (compiled evaluation), the same route `ValueRecoveryPosition` takes for its
`scanFiltered`-backed facts.

The probes are organised by the discipline's rules:

* **Rule 1 (probe at birth, concrete witness).** `pdt_ascii` / `pdt_multibyte` pin
  `percentDecodeTag` on the exact 6CK3 escape (`%21`→`!`) and on a multi-byte escape
  (`%E2%9C%93`→✓) — the latter is the reason the loop decodes UTF-8 BYTES then re-validates,
  not `Char`s.
* **Rule 2 (probe the BOUNDARY, per behaviour).** A decoder's characteristic boundaries are the
  MALFORMED escapes, not the comfortable interior: `pdt_lone_percent` (a `%` at end-of-string),
  `pdt_bad_hex` (`%ZZ`, not two hex digits), and `pdt_escaped_percent` (`%25`→`%`, the
  escape-of-the-escape) each show a `%` that must survive. `resolve_verbatim_not_decoded` is the
  ONE branch where decoding must NOT happen — a verbatim `!<uri>` tag is taken literally by §6.8.1,
  so its `%21` stays put; a whole-tag decoder that ignored this would silently corrupt verbatim
  tags.
* **Branch enumeration.** `resolveTagForEvent` has four arms; `resolve_custom` (custom `%TAG`
  handle → `tag:` URI, decoded), `resolve_core` (`!!str` → core URI), `resolve_local`
  (`!local`, no escape, unchanged) and the verbatim probe above exercise each, so no arm is left
  as an untested hypothesis.
* **Rule 5 (ground on REAL emission).** `streamToEvents_6ck3_ok` / `streamToEvents_6ck3_correct`
  run the FULL pipeline — `scanFiltered` (which processes the `%TAG` directive) → `parseYamlRaw`
  → `emitStream` — on the byte-for-byte 6CK3 input, and pin the ENTIRE event stream, so the
  decoded `<tag:example.com,2000:app/tag!>` is verified where it is actually produced, not just on
  a hand-written tag string.
-/

namespace EmitterTagPercentDecode

open L4YAML.Events

/-! ## Rule 1 — birth probe on the concrete witness -/

/-- The exact 6CK3 escape: `%21` is the percent-encoding of `!`. -/
theorem pdt_ascii :
    percentDecodeTag "tag:example.com,2000:app/tag%21" = "tag:example.com,2000:app/tag!" := by
  native_decide

/-- A multi-byte escape round-trips because decoding is byte-level then UTF-8 re-validated:
    `%E2%9C%93` is the UTF-8 of `✓` (U+2713). -/
theorem pdt_multibyte : percentDecodeTag "tag:x/%E2%9C%93" = "tag:x/✓" := by native_decide

/-! ## Rule 2 — boundary probes: malformed escapes must survive -/

/-- A lone `%` at the very end (no two following digits) is left literal. -/
theorem pdt_lone_percent : percentDecodeTag "tag:x/trailing%" = "tag:x/trailing%" := by
  native_decide

/-- `%ZZ` is not two hex digits, so it is passed through unchanged. -/
theorem pdt_bad_hex : percentDecodeTag "tag:x/a%ZZb" = "tag:x/a%ZZb" := by native_decide

/-- The escape-of-the-escape: `%25` decodes to a literal `%`, so `50%25off` → `50%off`. -/
theorem pdt_escaped_percent : percentDecodeTag "tag:x/50%25off" = "tag:x/50%off" := by
  native_decide

/-! ## `resolveTagForEvent` — every arm exercised -/

/-- Custom `%TAG` handle already resolved to a `tag:` URI: decode the suffix escape. -/
theorem resolve_custom :
    resolveTagForEvent "tag:example.com,2000:app/tag%21" = "tag:example.com,2000:app/tag!" := by
  native_decide

/-- Core secondary handle `!!str` expands to the standard URI (no escape present). -/
theorem resolve_core : resolveTagForEvent "!!str" = "tag:yaml.org,2002:str" := by native_decide

/-- Local tag with no escape is unchanged. -/
theorem resolve_local : resolveTagForEvent "!local" = "!local" := by native_decide

/-- THE boundary of the design: a verbatim `!<uri>` tag is taken literally (§6.8.1), so its
    `%21` is NOT decoded — this is the arm a naive whole-output decoder would corrupt. -/
theorem resolve_verbatim_not_decoded :
    resolveTagForEvent "!<tag:foo%21>" = "tag:foo%21" := by native_decide

/-! ## Rule 5 — grounded end-to-end on the real 6CK3 bytes

The `%TAG !e! …` directive means the decode can only be validated through the real scanner +
parser, not on a hand-built tag: the resolved `tag:example.com,2000:app/tag%21` is produced by
`%TAG`-handle expansion inside the pipeline. -/

/-- The byte-for-byte 6CK3 input (`data/6CK3/in.yaml`). -/
def in6ck3 : String :=
  "%TAG !e! tag:example.com,2000:app/\n---\n- !local foo\n- !!str bar\n- !e!tag%21 baz\n"

/-- The expected 6CK3 event stream (`data/6CK3/test.event`, with `streamToEvents`' trailing `\n`)
    — the third `=VAL` carries the DECODED `tag!`. -/
def out6ck3 : String :=
  "+STR\n+DOC ---\n+SEQ\n=VAL <!local> :foo\n=VAL <tag:yaml.org,2002:str> :bar\n" ++
  "=VAL <tag:example.com,2000:app/tag!> :baz\n-SEQ\n-DOC\n-STR\n"

/-- The pipeline succeeds on the real input (the antecedent of the correctness pin is satisfiable,
    so the pin below is non-vacuous). -/
def streamOk6ck3 : Bool :=
  match streamToEvents in6ck3 with | .ok _ => true | .error _ => false

theorem streamToEvents_6ck3_ok : streamOk6ck3 = true := by native_decide

/-- End-to-end: the full event stream emitted for the real 6CK3 bytes equals the expected stream,
    pinning the decoded `<tag:example.com,2000:app/tag!>` where it is actually produced. -/
def out6ck3Actual : String :=
  match streamToEvents in6ck3 with | .ok s => s | .error _ => "«parse-error»"

theorem streamToEvents_6ck3_correct : out6ck3Actual = out6ck3 := by native_decide

-- Axiom audit — the end-to-end pin runs the real parse pipeline, which routes through the
-- `Except`-monad + `parseStreamMarkedLoop` machinery (`Classical.choice`, `Quot.sound`, same as
-- the `ValueRecoveryPosition` sibling), and is closed by `native_decide` (the per-theorem
-- `…_native.native_decide.ax_1_1`). Crucially NO `sorryAx`: the decoded tag is genuinely produced.
/-- info: 'EmitterTagPercentDecode.streamToEvents_6ck3_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 streamToEvents_6ck3_correct._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms streamToEvents_6ck3_correct

end EmitterTagPercentDecode
