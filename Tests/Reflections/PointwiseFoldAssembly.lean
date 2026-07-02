import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity

/-!
# Reflection 581 — INHABITATION PROBE for Front B's brick-3 content-half consumer joint (§5.11)

Reflection 579 landed brick 3's *incremental* step algebra (§5.9 — extend two content-equal lists by
one content-equal element); Reflection 580 landed the *structural* append scaffold (§5.10 — the loop
only appends, so the recovered body `items''.toList = extra`). **Reflection 581 lands the consumer
joint for brick 3's content half** — `contentEqList_of_pointwise` / `contentEqPairList_of_pointwise`
(`ContentFidelity.lean` §5.11): two equal-length value (resp. pair) lists that are *pointwise*
content-equal are `contentEqList` (resp. `contentEqPairList`) equal.

It is the *dual decomposition* to §5.9. §5.9 threads one element per loop iteration (an inductive
producer); §5.11 lets the producer collect ALL its per-element facts first — `∀ i, contentEq items[i]
extra[i]` (one application of the per-element round-trip IH at each index) plus `items.size =
extra.length` — and assembles them in one shot. This RETYPES brick 3's content residual from "prove the
fold `contentEqList items.toList extra`" to "prove the pointwise family + the length", which is the
genuine producer contract the remaining (hard) span-locality / compositionality bridge owes.

## Why this probe (inhabitation debt for a CONSUMER JOINT with a universal hypothesis)

The §5.11 lemmas are sorry-free, so the obligation is the standard birth-probe — but the lemma is a
*consumer joint* whose hypothesis is itself a `∀`-quantified per-element family. The debt for such a
lemma is **double**: (1) is the hypothesis SATISFIABLE on the REAL recovery data — i.e. on lists that
are content-equal but genuinely DIFFER (in `style`, exactly the parser's plain→double-quoted shift),
else the lemma is never applicable in brick 3; (2) is the conclusion NON-TRIVIAL — not secretly
reflexivity (`contentEqList_refl` already covers equal lists). Both are exercised here on style-differing
fixtures, and the lemma is APPLIED end-to-end (discharging the `∀`-hypothesis with a real per-index
proof) — proving it is genuinely consumable, not orphan debt.

Per inhabitation-debt rule 2 (probe the boundary AND a non-degenerate case): the **boundary** is the
empty list (the `∀`-hypothesis is vacuous, the fold trivially `true`); the **non-degenerate** case is a
length-2 list whose every element is content-equal but style-divergent (`seq_lists_differ` /
`map_lists_differ` witness `(orig == rec) = false`, so the fold-`= true` the joint produces is NOT
reflexivity). The abstract `*_retype_shape` theorems pin the EXACT residual boundary the joint
discharges: any equal-length pointwise-content-equal `(items, extra)` assembles into the fold.

The `#print axioms` audits certify both source lemmas land at `[propext, Classical.choice, Quot.sound]`
— sorry-free (no `sorryAx`). The `Classical.choice` appears even though §5.11 is PURE list structural
induction with NO `Except` monad (contrast §5.10, whose choice was attributed to the loop's monadic
`simp`): it is pulled by `omega` / `simpa` / `getElem` decidability. The lesson generalizes — a
sorry-free structural lemma is routinely choice-dependent; `#print axioms` it, never assume.
-/

namespace PointwiseFoldAssembly

open L4YAML
open L4YAML.Emit
open L4YAML.Proofs.EmitterScannability

/-! ## Style-differing, content-equal fixtures (the brick-3 recovery scenario shape)

"Originals" carry `.plain` scalars (as authored); "recovered" carry the SAME content double-quoted
(what the parser actually yields). Content-equal, but genuinely different values. -/

def origSeq : List YamlValue :=
  [.scalar { content := "x", style := .plain }, .scalar { content := "y", style := .plain }]
def recSeq : List YamlValue :=
  [.scalar { content := "x", style := .doubleQuoted }, .scalar { content := "y", style := .doubleQuoted }]

def origMap : List (YamlValue × YamlValue) :=
  [(.scalar { content := "a", style := .plain }, .scalar { content := "b", style := .plain }),
   (.scalar { content := "c", style := .plain }, .scalar { content := "d", style := .plain })]
def recMap : List (YamlValue × YamlValue) :=
  [(.scalar { content := "a", style := .doubleQuoted }, .scalar { content := "b", style := .doubleQuoted }),
   (.scalar { content := "c", style := .doubleQuoted }, .scalar { content := "d", style := .doubleQuoted })]

/-! ## Non-triviality: the two lists are genuinely DIFFERENT (style), so a fold `= true` is NOT reflexivity.
    `BEq YamlValue` is full structural equality (includes `style`), so these are `false`. -/

theorem seq_lists_differ : (origSeq == recSeq) = false := by native_decide
theorem map_lists_differ : (origMap == recMap) = false := by native_decide

/-! ## The per-element deliverable IS satisfiable on this real data (pointwise content-eq, every index).
    This is the `∀`-hypothesis the consumer joint consumes — discharged here by a core-Lean index match
    (no Mathlib `interval_cases`). -/

theorem seq_pointwise_holds :
    ∀ (i : Nat) (_h₁ : i < origSeq.length) (_h₂ : i < recSeq.length),
      contentEq origSeq[i] recSeq[i] = true := by
  intro i h₁ h₂
  have hb : i < 2 := by simp only [origSeq, List.length_cons, List.length_nil] at h₁; exact h₁
  match i, hb with
  | 0, _ => native_decide +revert
  | 1, _ => native_decide +revert
  | n + 2, h => omega

theorem map_pointwise_holds :
    ∀ (i : Nat) (_h₁ : i < origMap.length) (_h₂ : i < recMap.length),
      contentEq origMap[i].1 recMap[i].1 = true ∧ contentEq origMap[i].2 recMap[i].2 = true := by
  intro i h₁ h₂
  have hb : i < 2 := by simp only [origMap, List.length_cons, List.length_nil] at h₁; exact h₁
  match i, hb with
  | 0, _ => exact ⟨by native_decide +revert, by native_decide +revert⟩
  | 1, _ => exact ⟨by native_decide +revert, by native_decide +revert⟩
  | n + 2, h => omega

theorem seq_len : origSeq.length = recSeq.length := by native_decide
theorem map_len : origMap.length = recMap.length := by native_decide

/-! ## APPLY the consumer joint: pointwise + length assemble into the fold (non-vacuous — the antecedent
    is witnessed satisfiable above, on style-differing data). -/

theorem seq_assembled : contentEq.contentEqList origSeq recSeq = true :=
  contentEqList_of_pointwise origSeq recSeq seq_len seq_pointwise_holds

theorem map_assembled : contentEq.contentEqPairList origMap recMap = true :=
  contentEqPairList_of_pointwise origMap recMap map_len map_pointwise_holds

/-! ## Boundary (rule 2): empty lists — the `∀`-hypothesis is vacuous, the fold trivially `true`. -/

theorem seq_empty_assembled : contentEq.contentEqList ([] : List YamlValue) [] = true :=
  contentEqList_of_pointwise [] [] rfl (by intro i h₁ h₂; simp at h₁)

theorem map_empty_assembled :
    contentEq.contentEqPairList ([] : List (YamlValue × YamlValue)) [] = true :=
  contentEqPairList_of_pointwise [] [] rfl (by intro i h₁ h₂; simp at h₁)

/-! ## The exact residual boundary the joint discharges (abstract): brick 3's content half reduces to
    its producer contract — ANY equal-length pointwise-content-equal `(items, extra)` assembles. -/

theorem seq_retype_shape (items extra : List YamlValue)
    (h_len : items.length = extra.length)
    (h_pt : ∀ (i : Nat) (h₁ : i < items.length) (h₂ : i < extra.length),
              contentEq items[i] extra[i] = true) :
    contentEq.contentEqList items extra = true :=
  contentEqList_of_pointwise items extra h_len h_pt

theorem map_retype_shape (pairs extra : List (YamlValue × YamlValue))
    (h_len : pairs.length = extra.length)
    (h_pt : ∀ (i : Nat) (h₁ : i < pairs.length) (h₂ : i < extra.length),
              contentEq pairs[i].1 extra[i].1 = true ∧ contentEq pairs[i].2 extra[i].2 = true) :
    contentEq.contentEqPairList pairs extra = true :=
  contentEqPairList_of_pointwise pairs extra h_len h_pt

/-! ## Axiom audit: the two §5.11 lemmas are sorry-free (`[propext, Classical.choice, Quot.sound]`).

Sorry-free (no `sorryAx`); `Classical.choice` is pulled by `omega` / `simpa` / `getElem` even though
§5.11 is pure list structural induction with NO `Except` monad — `#print axioms` it, never assume. -/

/-- info: 'L4YAML.Proofs.EmitterScannability.contentEqList_of_pointwise' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms contentEqList_of_pointwise

/-- info: 'L4YAML.Proofs.EmitterScannability.contentEqPairList_of_pointwise' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms contentEqPairList_of_pointwise

end PointwiseFoldAssembly
