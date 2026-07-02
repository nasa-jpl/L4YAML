import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity

/-!
# Reflection 583 — BIRTH PROBE for Front B's brick-3 producer char-list segment peel (§5.13)

Reflection 582 landed the *string* closed form `emit.emitList l = ", ".intercalate (l.map emit)`
(§5.12). But the scanner never consumes strings — every predicate in the `EmitListScansInFlow` family
(`ScanChainGrowth.lean:166`) is stated over the **char list** `(emit.emitList items).toList ++ rest`,
and the per-element scan recursion (`emitList_scans_nonempty`, `ScanChainGrowth.lean:203`) peels one
element off the FRONT at a time: `(emit v).toList ++ [',', ' '] ++ …`. **Reflection 583 factors that
peel** (currently an ad-hoc inline at `ScanChainGrowth.lean:222`) as two reusable `toList`-level lemmas
(`ContentFidelity.lean` §5.13):

* `emitList_toList_cons_of_ne_nil` / `emitPairList_toList_cons_of_ne_nil` — the single-step head peel
  `(emit.emitList (v :: tail)).toList = (emit v).toList ++ [',', ' '] ++ (emit.emitList tail).toList`
  (`tail ≠ []`), exposing the first element's emission chars as a prefix and the literal `[',', ' ']`
  separator the comma/space scan steps consume; and
* `emit_sequence_toList_bracket` / `emit_mapping_toList_bracket` — the whole-stream bracket char form
  `(emit (.sequence …)).toList = '[' :: (body.toList ++ [']'])`, the framing the producer enters the
  body scan with.

This is the `toList`-level bridge from §5.12's string form to the `toList ++ rest` shape the scanner
producer's span-locality recursion peels — the LAST emission-only prerequisite. The next sub-link must
cross into scanner machinery: the span-locality identity that each peeled `(emit v).toList` segment
scans to the standalone `scanFiltered (emit v)` token run.

## Why this probe (inhabitation debt for a VERIFIED-BUT-UNCONSUMED producer sub-link)

The §5.13 lemmas are equations, so Lean verifies them — they carry no inhabitation debt of their own.
But the discipline still bites for a *verified-but-unconsumed* artifact whose only future role is to be
CONSUMED by the span-locality producer:
1. **Rule 2 (boundary AND non-degenerate).** A head peel that the producer applied where the separator
   `[',', ' ']` never appears would be vacuous. The peel lemma REQUIRES `tail ≠ []` precisely because
   the singleton body `emit.emitList [v] = emit v` has NO separator (`emitList_singleton_no_sep`); so
   probe that boundary AND a non-degenerate `≥ 2`-element body where the `[',', ' ']` genuinely appears
   (`seq_head_peel_assembled`, `map_head_peel_assembled`, applied on real data with `tail ≠ []`).
2. **Rule 5 (ground against real emission).** A char form that did not match what `emit` actually
   produces would let the producer localize char-spans that aren't there. The `*_concrete` /
   `seq3_chars_literal` probes `native_decide` the real char lists — note plain scalars DOUBLE-QUOTE,
   so `emit a = "\"a\""` and the body chars literally interleave `'"' … '"'` runs with `',' ' '`
   separators. The fully expanded `seq3_chars_literal` exhibits the entire `'[' … ']'` char list so the
   per-element sub-spans the producer will split on are visible.

The lemmas are then APPLIED end-to-end (boundary, non-degenerate head peel, whole-stream bracket form,
abstract `*_shape` contract), proving the sub-link is genuinely consumable, not orphan scaffolding.

The `#print axioms` audits certify the four source lemmas land at `[propext, Classical.choice,
Quot.sound]` — sorry-free. `Classical.choice` appears even though §5.13 is pure `String.toList`/`++`
rewriting with NO `Except` monad: it is pulled by the core `String` simp lemmas. Same lesson as
§5.11/§5.12 — a sorry-free structural lemma is routinely choice-dependent; `#print axioms` it, never
assume.
-/

namespace CharListSegmentPeel

open L4YAML
open L4YAML.Emit
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures: plain scalars and key/value pairs (so `emit` is the bare double-quoted content). -/

def a : YamlValue := .scalar { content := "a", style := .plain }
def b : YamlValue := .scalar { content := "b", style := .plain }
def c : YamlValue := .scalar { content := "c", style := .plain }

def ka : YamlValue := .scalar { content := "k1", style := .plain }
def va : YamlValue := .scalar { content := "v1", style := .plain }
def kb : YamlValue := .scalar { content := "k2", style := .plain }
def vb : YamlValue := .scalar { content := "v2", style := .plain }

/-! ## Concrete grounding (rule 5): the `toList` peel IS the real emission char list — the head
    element's chars, the literal `[',', ' ']` separator, then the tail's chars. -/

theorem seq_head_peel_concrete :
    (emit.emitList [a, b, c]).toList
      = (emit a).toList ++ [',', ' '] ++ (emit.emitList [b, c]).toList := by native_decide

theorem seq_bracket_concrete :
    (emit (.sequence .flow #[a, b, c])).toList
      = '[' :: ((emit.emitList [a, b, c]).toList ++ [']']) := by native_decide

theorem map_head_peel_concrete :
    (emit.emitPairList [(ka, va), (kb, vb)]).toList
      = (emit ka).toList ++ [':', ' '] ++ (emit va).toList ++ [',', ' ']
        ++ (emit.emitPairList [(kb, vb)]).toList := by native_decide

theorem map_bracket_concrete :
    (emit (.mapping .flow #[(ka, va), (kb, vb)])).toList
      = '{' :: ((emit.emitPairList [(ka, va), (kb, vb)]).toList ++ ['}']) := by native_decide

/-- The whole flow-sequence char list, fully expanded — the per-element sub-spans the span-locality
    producer will split on are exhibited literally (`'"' … '"'` runs separated by `',' ' '`). -/
theorem seq3_chars_literal :
    (emit (.sequence .flow #[a, b, c])).toList
      = ['[', '"', 'a', '"', ',', ' ', '"', 'b', '"', ',', ' ', '"', 'c', '"', ']'] := by
  native_decide

/-! ## Boundary (rule 2): the singleton body has NO separator — `emit.emitList [v] = emit v` — which is
    exactly why the head peel lemma REQUIRES `tail ≠ []`. -/

theorem emitList_singleton_no_sep : (emit.emitList [a]).toList = (emit a).toList := by native_decide

/-! ## Non-degenerate (rule 2): `≥ 2`-element bodies — the `[',', ' ']` separator genuinely appears, so
    the peel is NOT a vacuous restatement. The lemma is APPLIED on real data (`tail ≠ []`). -/

theorem seq_head_peel_assembled :
    (emit.emitList [a, b, c]).toList
      = (emit a).toList ++ [',', ' '] ++ (emit.emitList [b, c]).toList :=
  emitList_toList_cons_of_ne_nil a [b, c] (by simp)

theorem map_head_peel_assembled :
    (emit.emitPairList [(ka, va), (kb, vb)]).toList
      = (emit ka).toList ++ [':', ' '] ++ (emit va).toList ++ [',', ' ']
        ++ (emit.emitPairList [(kb, vb)]).toList :=
  emitPairList_toList_cons_of_ne_nil ka va [(kb, vb)] (by simp)

/-! ## The producer-facing framing: the WHOLE emitted char list as `'[' :: body ++ [']']` — the shape
    the producer enters the body scan with (`'['` opens the flow level, trailing `']'` closes it). -/

theorem seq_bracket_assembled :
    (emit (.sequence .flow #[a, b, c])).toList
      = '[' :: ((emit.emitList (#[a, b, c] : Array YamlValue).toList).toList ++ [']']) :=
  emit_sequence_toList_bracket .flow #[a, b, c] none none

theorem map_bracket_assembled :
    (emit (.mapping .flow #[(ka, va), (kb, vb)])).toList
      = '{' :: ((emit.emitPairList (#[(ka, va), (kb, vb)] : Array (YamlValue × YamlValue)).toList).toList
          ++ ['}']) :=
  emit_mapping_toList_bracket .flow #[(ka, va), (kb, vb)] none none

/-! ## Abstract residual contract: the producer's char-level peel, for ANY non-empty tail / any
    sequence — the whole emitted body decomposes one element at a time, the whole stream is bracketed. -/

theorem emitList_peel_shape (v : YamlValue) (tail : List YamlValue) (h : tail ≠ []) :
    (emit.emitList (v :: tail)).toList
      = (emit v).toList ++ [',', ' '] ++ (emit.emitList tail).toList :=
  emitList_toList_cons_of_ne_nil v tail h

theorem emit_sequence_bracket_shape
    (style : CollectionStyle) (items : Array YamlValue) (tag anchor : Option String) :
    (emit (.sequence style items tag anchor)).toList
      = '[' :: ((emit.emitList items.toList).toList ++ [']']) :=
  emit_sequence_toList_bracket style items tag anchor

/-! ## Axiom audit: the four §5.13 lemmas are sorry-free (`[propext, Classical.choice, Quot.sound]`).
    `Classical.choice` enters via the core `String` simp lemmas even though §5.13 is pure
    `String.toList`/`++` rewriting with NO `Except` monad — `#print axioms` it, never assume. -/

/-- info: 'L4YAML.Proofs.EmitterScannability.emitList_toList_cons_of_ne_nil' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms emitList_toList_cons_of_ne_nil

/-- info: 'L4YAML.Proofs.EmitterScannability.emitPairList_toList_cons_of_ne_nil' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms emitPairList_toList_cons_of_ne_nil

/-- info: 'L4YAML.Proofs.EmitterScannability.emit_sequence_toList_bracket' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms emit_sequence_toList_bracket

/-- info: 'L4YAML.Proofs.EmitterScannability.emit_mapping_toList_bracket' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms emit_mapping_toList_bracket

end CharListSegmentPeel
