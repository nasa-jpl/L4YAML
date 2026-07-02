import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity
import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner

/-!
# Reflection 576 — INHABITATION PROBE for Front B's value-recovery trace, brick 2 last link (part 2)

This file is the inhabitation test the [[feedback-inhabitation-debt-validate-target-defs]] discipline
demands for the **first-document position-pinning** lemma `parseStream_first_doc_at_pos_one` (in
`ContentFidelity.lean` §5.7) and its structural helpers `parseStreamLoop_preserves_head` /
`parseStreamLoop_first_doc_from_entry` / `expect_pos_succ`.

§5.6 lifted the outer shape through `parseDocument`, but only when the lookahead is the flow opener —
which lives at position 1 (the emitter's leading `[` / `{`). This link pins that position for the
FIRST document: `parseStream` runs `expect .streamStart` (pos 0 -> 1) then enters `parseStreamLoop`
with an empty accumulator, so the first document it produces came from `parseDocument` on the loop's
entry state, at pos 1.

## Why this probe (the inhabitation-debt risk for a CONCLUSION lemma with TWO antecedents)

`parseStream_first_doc_at_pos_one` is a CONCLUSION
`(parseStream tokens = .ok docs) -> (0 < docs.size) -> (exists ps ps', ...)`, so Lean proves it TRUE —
but a conclusion is worthless if its antecedents are never *jointly* satisfiable on real data: it
would type-check yet never fire. The R573 sharpening of the inhabitation-debt discipline says TWO
antecedents must be probed for **joint** satisfiability on the SAME real datum, not separately. So the
witnesses below run on ONE token array per shape — `seqTokens` / `mapTokens` — built from REAL
emitted+scanned bytes (`emit` then `scanFiltered`), exactly what `parseYamlRaw` feeds the parser.

* `seqStreamOkSizeOne_fires` / `mapStreamOkSizeOne_fires` — both antecedents are satisfiable JOINTLY on
  the SAME `seqTokens` / `mapTokens`: `parseStream` succeeds AND the document array has size exactly 1
  (so `0 < docs.size`). The lemma is therefore NOT vacuously true.
* `seqEntryAtPosOnePeeksOpen_fires` / `mapEntryAtPosOnePeeksOpen_fires` — the CONCLUSION is meaningful:
  the recovered entry state (pos 1) really does peek the emitter's leading `[` / `{`, i.e. exactly the
  `.flowSequenceStart` / `.flowMappingStart` lookahead §5.6 needs. Position pinning is not idle.
* `seqPosOneParseDocIsFlowSeq_fires` / `mapPosOneParseDocIsFlowMap_fires` — end-to-end on real bytes:
  the pos-1 `parseDocument` (the lemma's conclusion) yields a flow collection with default tag/anchor —
  the shape §5.6's `parseDocument_flow{Seq,Map}Start_produces_{sequence,mapping}` recovers. The two
  links compose on real data.
* `seqTokens_first_doc_at_pos_one` / `mapTokens_first_doc_at_pos_one` — the actual lemma applied to the
  REAL token arrays, with both antecedents satisfiable by the witnesses above: a genuine, non-vacuous
  use exposing the first document's `parseDocument` at pos 1.
-/

namespace ValueRecoveryPosition

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-- A genuine grammable flow sequence `["x"]`. -/
def seqValue : YamlValue := .sequence .flow #[.scalar { content := "x", style := .doubleQuoted }]

/-- A genuine grammable flow mapping `{"a":"b"}`. -/
def mapValue : YamlValue :=
  .mapping .flow #[(.scalar { content := "a", style := .doubleQuoted },
                    .scalar { content := "b", style := .doubleQuoted })]

/-- REAL tokens from the emitted+scanned bytes of `seqValue` — exactly what `parseStream` parses.
    (`#[]` is unreachable: scanning emitter output succeeds, witnessed by `seqStreamOkSizeOne_fires`.) -/
def seqTokens : Array (Positioned YamlToken) :=
  match scanFiltered (emit seqValue) with
  | .ok t => t
  | .error _ => #[]

/-- Mirror: REAL tokens from the emitted+scanned bytes of `mapValue`. -/
def mapTokens : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapValue) with
  | .ok t => t
  | .error _ => #[]

/-- Both antecedents JOINTLY: `parseStream seqTokens` succeeds AND yields exactly one document
    (so `0 < docs.size`). -/
def seqStreamOkSizeOne : Bool :=
  match parseStream seqTokens with
  | .ok docs => docs.size == 1
  | .error _ => false

/-- Mirror for the mapping token array. -/
def mapStreamOkSizeOne : Bool :=
  match parseStream mapTokens with
  | .ok docs => docs.size == 1
  | .error _ => false

theorem seqStreamOkSizeOne_fires : seqStreamOkSizeOne = true := by native_decide
theorem mapStreamOkSizeOne_fires : mapStreamOkSizeOne = true := by native_decide

/-- The entry state `parseStream` hands the first `parseDocument`: `{ tokens := seqTokens }` advanced
    once past `streamStart`, i.e. position 1. -/
def seqEntryPS : ParseState := ({ tokens := seqTokens } : ParseState).advance

/-- Mirror entry state for the mapping token array. -/
def mapEntryPS : ParseState := ({ tokens := mapTokens } : ParseState).advance

/-- The CONCLUSION is meaningful: at pos 1 the lookahead IS the emitter's leading `[`
    (`.flowSequenceStart`) — the exact hypothesis §5.6's `parseDocument` dispatch consumes. -/
def seqEntryAtPosOnePeeksOpen : Bool :=
  (seqEntryPS.pos == 1) &&
  (match seqEntryPS.peek? with | some .flowSequenceStart => true | _ => false)

/-- Mirror: at pos 1 the mapping entry state peeks the leading `{` (`.flowMappingStart`). -/
def mapEntryAtPosOnePeeksOpen : Bool :=
  (mapEntryPS.pos == 1) &&
  (match mapEntryPS.peek? with | some .flowMappingStart => true | _ => false)

theorem seqEntryAtPosOnePeeksOpen_fires : seqEntryAtPosOnePeeksOpen = true := by native_decide
theorem mapEntryAtPosOnePeeksOpen_fires : mapEntryAtPosOnePeeksOpen = true := by native_decide

/-- End-to-end on real bytes: the pos-1 `parseDocument` (the lemma's conclusion) yields a flow sequence
    with default tag/anchor — the shape §5.6 recovers. The position-pinning and dispatch links compose. -/
def seqPosOneParseDocIsFlowSeq : Bool :=
  match parseDocument seqEntryPS with
  | .ok (doc, _) =>
    match doc.value with
    | .sequence .flow _ none none => true
    | _ => false
  | .error _ => false

/-- Mirror: the pos-1 `parseDocument` on the mapping bytes yields a flow mapping with default
    tag/anchor. -/
def mapPosOneParseDocIsFlowMap : Bool :=
  match parseDocument mapEntryPS with
  | .ok (doc, _) =>
    match doc.value with
    | .mapping .flow _ none none => true
    | _ => false
  | .error _ => false

theorem seqPosOneParseDocIsFlowSeq_fires : seqPosOneParseDocIsFlowSeq = true := by native_decide
theorem mapPosOneParseDocIsFlowMap_fires : mapPosOneParseDocIsFlowMap = true := by native_decide

/-- The actual lemma `parseStream_first_doc_at_pos_one` applied to the REAL `seqTokens`. Both
    hypotheses are satisfiable here (witnessed jointly above), so this is a genuine, non-vacuous use:
    `parseStream` succeeding with a non-empty document array yields a `parseDocument` at pos 1
    producing the first document — the position-pinning link of brick 2's wrapping. -/
theorem seqTokens_first_doc_at_pos_one
    (docs : Array YamlDocument)
    (h_parse : parseStream seqTokens = .ok docs)
    (h_ne : 0 < docs.size) :
    ∃ ps ps', ps.tokens = seqTokens ∧ ps.pos = 1 ∧ parseDocument ps = .ok (docs[0]!, ps') :=
  -- The C1 guard `seqTokens[1]!.val ≠ .documentEnd` is genuinely true (it is
  -- `.flowSequenceStart`), so this stays a non-vacuous use of the lemma.
  parseStream_first_doc_at_pos_one seqTokens docs h_parse h_ne (by native_decide)

/-- Mirror: the lemma applied to the REAL mapping token array. -/
theorem mapTokens_first_doc_at_pos_one
    (docs : Array YamlDocument)
    (h_parse : parseStream mapTokens = .ok docs)
    (h_ne : 0 < docs.size) :
    ∃ ps ps', ps.tokens = mapTokens ∧ ps.pos = 1 ∧ parseDocument ps = .ok (docs[0]!, ps') :=
  -- The C1 guard `mapTokens[1]!.val ≠ .documentEnd` is genuinely true (it is
  -- `.flowMappingStart`), so this stays a non-vacuous use of the lemma.
  parseStream_first_doc_at_pos_one mapTokens docs h_parse h_ne (by native_decide)

-- Axiom audit — the position-pinning lemma and its loop traces route through `parseStreamLoop` /
-- `parseDocument` and the `Except`-monad simp machinery, so they carry `Classical.choice` (same
-- profile as bricks 1 / 2(a) / 2(b)-part-1, §5.6). `expect_pos_succ` is a pure structural inversion
-- of `expect` and audits `[propext]` ALONE. None depend on `Lean.ofReduceBool` (the firing probes
-- above are separate `native_decide` lemmas).
/-- info: 'L4YAML.Proofs.EmitterScannability.parseStream_first_doc_at_pos_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parseStream_first_doc_at_pos_one

/-- info: 'L4YAML.Proofs.EmitterScannability.parseStreamLoop_preserves_head' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parseStreamLoop_preserves_head

/-- info: 'L4YAML.Proofs.EmitterScannability.parseStreamLoop_first_doc_from_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parseStreamLoop_first_doc_from_entry

/-- info: 'L4YAML.Proofs.EmitterScannability.expect_pos_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms expect_pos_succ

end ValueRecoveryPosition
