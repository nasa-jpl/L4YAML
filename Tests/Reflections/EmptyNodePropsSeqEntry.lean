import L4YAML.Output.Events

/-!
# Reflection — INHABITATION / BOUNDARY probe for the empty-node seq-entry fix (matrix defect C2)

Matrix defect **C2** (100%-matrix campaign, 2026-07; FH7J / PW8X): a node carrying only
properties (`- !!str`, `- &a`) that is followed by a *sibling* block entry at the same indent was
parsed as an empty **sequence** that swallowed the siblings, instead of an empty **scalar** whose
`blockEntry` belongs to the parent sequence.

The obvious fix first proposed during that campaign — "if properties were present, return the empty scalar" —
is **wrong**: it regresses `57H4` (Spec Example 8.22, *Block Collection Nodes*) and `SKE5` (*Anchor
before a zero-indented sequence*), where a node's properties legitimately tag/anchor a same-indent
block sequence that IS its content. Those two inputs have properties too, so `hadProps` cannot tell
them apart from FH7J/PW8X.

The correct discriminator is the parser's **context** (§8.2.1 BLOCK-IN vs BLOCK-OUT): a node reached
directly from a block sequence entry is preceded by a `blockEntry` token, whereas a mapping value is
preceded by a `value` token. `parseNode` derives `isSeqEntry` from `ps.tokens[prePropPos - 1]` and
passes it to `parseNodeContent`; only in the sequence-entry context does a following `blockEntry`
become an empty scalar (`L4YAML/Parser/TokenParser.lean`).

This is a textbook [[feedback-inhabitation-debt-validate-target-defs]] episode: the newly-constructed
branch *type-checked* under the naive gate, but a birth probe on real data (the four inputs below)
is what exposed that it did the wrong thing. This file is that probe — the two POSITIVE cases it
fixes and the two BOUNDARY cases it must NOT disturb, each pinned by its full emitted event stream so
the fix is verified where the events are actually produced. Because the pipeline runs through
`scanFiltered`/`parseStream` (a `partial def` chain), every check is `native_decide`.
-/

namespace EmptyNodePropsSeqEntry

open L4YAML.Events

/-- The full event stream `streamToEvents` emits for `input`, or a fixed error marker. -/
private def run (input : String) : String :=
  match streamToEvents input with | .ok s => s | .error _ => "«parse-error»"

/-! ## Rule 5 (positive) — the two inputs C2 fixes, grounded on real bytes

`- !!str` / `- &a` followed by a sibling `-` at the same indent must be an *empty scalar sibling*,
so the parent sequence keeps every entry rather than collapsing into one nested sequence. -/

/-- `data/FH7J/in.yaml` — empty `!!str`/`!!null` nodes as sequence entries and map keys/values. -/
def inFH7J : String := "- !!str\n-\n  !!null : a\n  b: !!str\n- !!str : !!null\n"

def outFH7J : String :=
  "+STR\n+DOC\n+SEQ\n=VAL <tag:yaml.org,2002:str> :\n+MAP\n" ++
  "=VAL <tag:yaml.org,2002:null> :\n=VAL :a\n=VAL :b\n=VAL <tag:yaml.org,2002:str> :\n-MAP\n" ++
  "+MAP\n=VAL <tag:yaml.org,2002:str> :\n=VAL <tag:yaml.org,2002:null> :\n-MAP\n-SEQ\n-DOC\n-STR\n"

theorem fh7j_correct : run inFH7J = outFH7J := by native_decide

/-- `data/PW8X/in.yaml` — a `&a` anchor entry followed by siblings, plus explicit-key maps. -/
def inPW8X : String :=
  "- &a\n- a\n-\n  &a : a\n  b: &b\n-\n  &c : &a\n-\n  ? &d\n-\n  ? &e\n  : &a\n"

def outPW8X : String :=
  "+STR\n+DOC\n+SEQ\n=VAL &a :\n=VAL :a\n+MAP\n=VAL &a :\n=VAL :a\n=VAL :b\n=VAL &b :\n-MAP\n" ++
  "+MAP\n=VAL &c :\n=VAL &a :\n-MAP\n+MAP\n=VAL &d :\n=VAL :\n-MAP\n" ++
  "+MAP\n=VAL &e :\n=VAL &a :\n-MAP\n-SEQ\n-DOC\n-STR\n"

theorem pw8x_correct : run inPW8X = outPW8X := by native_decide

/-! ## Rule 2 (boundary) — the two inputs the naive `hadProps` gate would have BROKEN

Here the properties belong to a same-indent block sequence that is the node's *content* (map-value
context). The pins carry `+SEQ <tag:…>` / `+SEQ &anchor` — the tag/anchor on the COLLECTION — so a
regression to "empty scalar" (which would emit `=VAL <…> :`) is caught. -/

/-- `data/57H4/in.yaml` — Spec Example 8.22: `sequence: !!seq` tags the same-indent block sequence. -/
def in57H4 : String := "sequence: !!seq\n- entry\n- !!seq\n - nested\nmapping: !!map\n foo: bar\n"

def out57H4 : String :=
  "+STR\n+DOC\n+MAP\n=VAL :sequence\n+SEQ <tag:yaml.org,2002:seq>\n=VAL :entry\n" ++
  "+SEQ <tag:yaml.org,2002:seq>\n=VAL :nested\n-SEQ\n-SEQ\n=VAL :mapping\n" ++
  "+MAP <tag:yaml.org,2002:map>\n=VAL :foo\n=VAL :bar\n-MAP\n-MAP\n-DOC\n-STR\n"

theorem ex57h4_seq_not_scalar : run in57H4 = out57H4 := by native_decide

/-- `data/SKE5/in.yaml` — `&anchor` on its own line anchors the following zero-indented sequence. -/
def inSKE5 : String := "---\nseq:\n &anchor\n- a\n- b\n"

def outSKE5 : String :=
  "+STR\n+DOC ---\n+MAP\n=VAL :seq\n+SEQ &anchor\n=VAL :a\n=VAL :b\n-SEQ\n-MAP\n-DOC\n-STR\n"

theorem ske5_seq_not_scalar : run inSKE5 = outSKE5 := by native_decide

-- Axiom audit — the pins run the real parse pipeline (`Except`-monad + `parseStreamMarkedLoop`,
-- hence `Classical.choice`/`Quot.sound`, same as the `ValueRecoveryPosition` sibling), closed by
-- `native_decide` (the per-theorem `…_native.native_decide.ax_1_1`).  No `sorryAx`.
/-- info: 'EmptyNodePropsSeqEntry.fh7j_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 fh7j_correct._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms fh7j_correct

end EmptyNodePropsSeqEntry
