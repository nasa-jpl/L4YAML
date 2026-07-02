import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity
import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner

/-!
# Reflection 580 — INHABITATION PROBE for Front B's brick-3 link (b) scaffold (§5.10)

Reflection 579 landed brick 3's *step algebra* (§5.9): extending two content-equal lists by one
content-equal element preserves `contentEqList` / `contentEqPairList`. **Reflection 580 lands the first
link of brick 3 (b)** — the purely *structural* scaffold the content-tracking loop induction hangs on:
`parseFlowSequenceLoop_result_append` / `parseFlowMappingLoop_result_append` (`ContentFidelity.lean`
§5.10). Each says a successful `parseFlowSequenceLoop ps fuel acc` / `parseFlowMappingLoop ps fuel acc`
returns an array whose `toList` is `acc.toList ++ extra`, where `extra` is the (existentially
quantified) list of entries parsed in this call. It is the list refinement of
`parseFlowMappingLoop_pairs_grow` (`ParserWellBehaved.lean:2107`, which tracks only the SIZE `≥`), proved
by fuel induction over the loop definition ALONE — no bracket balance / fuel adequacy / `ParseNodeFlowSeqOk`
machinery (every branch either returns the accumulator, `extra := []`, or recurses on `acc.push v`,
`extra := v :: …`, via `Array.toList_push`).

Instantiated at `acc := #[]` (where §5.8's trace enters the loop), this gives `items''.toList = extra`
— the scaffold on which brick 3's two residual conjuncts hang (size `items.size = extra.length`, content
`contentEqList items.toList extra` via §5.9's step algebra, once each `extra` element is characterized by
the per-element round-trip IH).

## Why this probe (inhabitation debt for an EXISTENTIAL CONCLUSION)

These two §5.10 lemmas are **genuinely sorry-free**, so the obligation is the standard sorry-free
birth-probe — but the conclusion is now an EXISTENTIAL (`∃ extra, …`), so the debt is non-vacuity:
confirm the antecedent (`parseFlow…Loop … = .ok result`) is REACHABLE on real emitted data (else the
lemma is vacuously applicable), AND that the witness `extra` is a GENUINE list, not a degenerate one.
Per inhabitation-debt rule 2 (probe the boundary AND a non-degenerate case), both branches of the
lemma's own case analysis are exercised:

* `seqLoopEmptyDecomp_fires` / `mapLoopEmptyDecomp_fires` — entered EMPTY at the flow body start, the
  loop parses every entry, so `extra` is the full **non-empty** parsed list (the recursive
  `extra := v :: …` branch fires; the `acc.toList = []` prefix is the boundary).
* `seqLoopSeedDecomp_fires` / `mapLoopSeedDecomp_fires` — entered with a **non-empty** seed accumulator
  positioned just before a separator, the loop both PRESERVES the seed as the genuine `acc.toList`
  prefix AND appends the parsed tail, so `acc.toList ++ extra` has BOTH parts non-trivial (the fully
  non-degenerate decomposition — the rule-2 case the empty-accumulator probe alone would skip).

The fixtures use scalars that are content-equal but differ in `style` (`.plain` vs `.doubleQuoted`),
matching the rest of the brick-3 demo corpus. The `#print axioms` audits certify the two source lemmas
land at `[propext, Classical.choice, Quot.sound]` — sorry-free (no `sorryAx`); the `Classical.choice`
(absent from §5.9's `[propext]`-only step algebra) is inherited from the loop induction's `Except`-monad
`simp`, NOT from `native_decide`, which the probes below carry separately.
-/

namespace LoopResultAppend

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-! ## Style-blind content-equal fixtures and real loop-entry `ParseState`s -/

def sx' : YamlValue := .scalar { content := "x", style := .doubleQuoted }
def sy' : YamlValue := .scalar { content := "y", style := .doubleQuoted }
def seqValue2 : YamlValue := .sequence .flow #[sx', sy']

def ka' : YamlValue := .scalar { content := "a", style := .doubleQuoted }
def vb' : YamlValue := .scalar { content := "b", style := .doubleQuoted }
def kc' : YamlValue := .scalar { content := "c", style := .doubleQuoted }
def vd' : YamlValue := .scalar { content := "d", style := .doubleQuoted }
def mapValue2 : YamlValue := .mapping .flow #[(ka', vb'), (kc', vd')]

/-- The real tokens of `seqValue2`, scanned from its emitted bytes. -/
def seqTokens : Array (Positioned YamlToken) :=
  match scanFiltered (emit seqValue2) with
  | .ok t => t
  | .error _ => #[]

def mapTokens : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapValue2) with
  | .ok t => t
  | .error _ => #[]

/-- The real `ParseState` at the flow-sequence BODY start — past `streamStart` and `[` (two advances),
    exactly where `parseFlowSequence` enters `parseFlowSequenceLoop` with an empty accumulator. -/
def seqBodyEntry : ParseState := ({ tokens := seqTokens } : ParseState).advance.advance
/-- The real `ParseState` at the SEPARATOR (the `flowEntry` between the two entries) — one further
    advance, where a seeded loop both keeps its accumulator and parses the next entry. -/
def seqSepEntry : ParseState := ({ tokens := seqTokens } : ParseState).advance.advance.advance

def mapBodyEntry : ParseState := ({ tokens := mapTokens } : ParseState).advance.advance
/-- The `flowEntry` separator in `{a:b,c:d}` is at index 6 (`key scalar value scalar` per entry), so
    the seeded mapping loop enters here to both keep its accumulator and parse the next entry. -/
def mapSepEntry : ParseState :=
  ({ tokens := mapTokens } : ParseState).advance.advance.advance.advance.advance.advance

/-! ## Position pins (so a wrong advance count fails legibly here, not deep in a `native_decide`) -/

def seqBodyEntryPeek : Bool := match seqBodyEntry.peek? with | some (.scalar _ _) => true | _ => false
def seqSepEntryPeek : Bool := match seqSepEntry.peek? with | some .flowEntry => true | _ => false
def mapBodyEntryPeek : Bool := match mapBodyEntry.peek? with | some .key => true | _ => false
def mapSepEntryPeek : Bool := match mapSepEntry.peek? with | some .flowEntry => true | _ => false

theorem seqBodyEntryPeek_fires : seqBodyEntryPeek = true := by native_decide
theorem seqSepEntryPeek_fires : seqSepEntryPeek = true := by native_decide
theorem mapBodyEntryPeek_fires : mapBodyEntryPeek = true := by native_decide
theorem mapSepEntryPeek_fires : mapSepEntryPeek = true := by native_decide

/-! ## Probe (sequence): antecedent reachable + existential witness genuine, both branches -/

def seqSeed : YamlValue := .scalar { content := "seed", style := .plain }

/-- Antecedent reachable: the loop succeeds on real emitted body tokens. -/
def seqLoopEmptyOk : Bool := match parseFlowSequenceLoop seqBodyEntry 100 #[] with | .ok _ => true | _ => false
theorem seqLoopEmptyOk_fires : seqLoopEmptyOk = true := by native_decide

/-- Boundary (`acc := #[]`): the recovered list IS `[] ++ extra` with a genuine NON-EMPTY `extra` (the
    recursive `extra := v :: …` branch; both entries parsed). -/
def seqLoopEmptyDecomp : Bool :=
  match parseFlowSequenceLoop seqBodyEntry 100 #[] with
  | .ok (items, _) =>
      let extra := items.toList.drop 0
      (items.toList == ([] : List YamlValue) ++ extra) && (extra.length == 2)
  | .error _ => false
theorem seqLoopEmptyDecomp_fires : seqLoopEmptyDecomp = true := by native_decide

/-- Non-degenerate (`acc := #[seqSeed]` at the separator): `acc.toList ++ extra` with BOTH parts
    non-trivial — the seed is the genuine prefix (`items[0]? = some seqSeed`) and the parsed tail is
    the non-empty `extra`. -/
def seqLoopSeedDecomp : Bool :=
  match parseFlowSequenceLoop seqSepEntry 100 #[seqSeed] with
  | .ok (items, _) =>
      let extra := items.toList.drop 1
      (items.toList == ([seqSeed] : List YamlValue) ++ extra) && (extra.length == 1)
        && (items[0]? == some seqSeed)
  | .error _ => false
theorem seqLoopSeedDecomp_fires : seqLoopSeedDecomp = true := by native_decide

/-! ## Probe (mapping): the same two branches over the pair loop -/

def mapSeed : YamlValue × YamlValue :=
  (.scalar { content := "sk", style := .plain }, .scalar { content := "sv", style := .plain })

def mapLoopEmptyOk : Bool := match parseFlowMappingLoop mapBodyEntry 100 #[] with | .ok _ => true | _ => false
theorem mapLoopEmptyOk_fires : mapLoopEmptyOk = true := by native_decide

def mapLoopEmptyDecomp : Bool :=
  match parseFlowMappingLoop mapBodyEntry 100 #[] with
  | .ok (pairs, _) =>
      let extra := pairs.toList.drop 0
      (pairs.toList == ([] : List (YamlValue × YamlValue)) ++ extra) && (extra.length == 2)
  | .error _ => false
theorem mapLoopEmptyDecomp_fires : mapLoopEmptyDecomp = true := by native_decide

def mapLoopSeedDecomp : Bool :=
  match parseFlowMappingLoop mapSepEntry 100 #[mapSeed] with
  | .ok (pairs, _) =>
      let extra := pairs.toList.drop 1
      (pairs.toList == ([mapSeed] : List (YamlValue × YamlValue)) ++ extra) && (extra.length == 1)
        && (pairs[0]? == some mapSeed)
  | .error _ => false
theorem mapLoopSeedDecomp_fires : mapLoopSeedDecomp = true := by native_decide

/-! ## Apply the actual lemmas to the real loop runs (non-vacuous, antecedent witnessed above) -/

/-- The actual §5.10 lemma applied at the real sequence body entry with `acc := #[]`: from any
    successful loop run there, the recovered list decomposes as `[] ++ extra`. Non-vacuous —
    `seqLoopEmptyOk_fires` witnesses the antecedent is reachable on this very state. -/
theorem seqLoopAppend_applied :
    ∀ result, parseFlowSequenceLoop seqBodyEntry 100 #[] = .ok result →
      ∃ extra, result.1.toList = ([] : List YamlValue) ++ extra := by
  intro result h_ok
  exact parseFlowSequenceLoop_result_append seqBodyEntry 100 #[] result h_ok

/-- Mapping mirror. -/
theorem mapLoopAppend_applied :
    ∀ result, parseFlowMappingLoop mapBodyEntry 100 #[] = .ok result →
      ∃ extra, result.1.toList = ([] : List (YamlValue × YamlValue)) ++ extra := by
  intro result h_ok
  exact parseFlowMappingLoop_result_append mapBodyEntry 100 #[] result h_ok

/-! ## Axiom audit: the two §5.10 lemmas are sorry-free (`[propext, Classical.choice, Quot.sound]`)

Sorry-free (no `sorryAx`); `Classical.choice` is inherited from the loop induction's `Except`-monad
`simp` (contrast §5.9's `[propext]`-only pure decidable list algebra), NOT from `native_decide`. -/

/-- info: 'L4YAML.Proofs.EmitterScannability.parseFlowSequenceLoop_result_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parseFlowSequenceLoop_result_append

/-- info: 'L4YAML.Proofs.EmitterScannability.parseFlowMappingLoop_result_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parseFlowMappingLoop_result_append

end LoopResultAppend
